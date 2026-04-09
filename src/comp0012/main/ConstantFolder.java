package comp0012.main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ArithmeticInstruction;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.ConstantPushInstruction;
import org.apache.bcel.generic.DADD;
import org.apache.bcel.generic.DDIV;
import org.apache.bcel.generic.DMUL;
import org.apache.bcel.generic.DNEG;
import org.apache.bcel.generic.DREM;
import org.apache.bcel.generic.DSUB;
import org.apache.bcel.generic.FADD;
import org.apache.bcel.generic.FDIV;
import org.apache.bcel.generic.FMUL;
import org.apache.bcel.generic.FNEG;
import org.apache.bcel.generic.FREM;
import org.apache.bcel.generic.FSUB;
import org.apache.bcel.generic.IADD;
import org.apache.bcel.generic.IDIV;
import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.IMUL;
import org.apache.bcel.generic.INEG;
import org.apache.bcel.generic.IREM;
import org.apache.bcel.generic.ISUB;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionFactory;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.InstructionTargeter;
import org.apache.bcel.generic.LADD;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC2_W;
import org.apache.bcel.generic.LDIV;
import org.apache.bcel.generic.LMUL;
import org.apache.bcel.generic.LNEG;
import org.apache.bcel.generic.LREM;
import org.apache.bcel.generic.LSUB;
import org.apache.bcel.generic.LoadInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.StoreInstruction;
import org.apache.bcel.generic.TargetLostException;
import org.apache.bcel.generic.Type;
import java.util.Set;

public class ConstantFolder
{
	ClassParser parser = null;
	ClassGen gen = null;

	JavaClass original = null;
	JavaClass optimized = null;

	public ConstantFolder(String classFilePath)
	{
		try{
			this.parser = new ClassParser(classFilePath);
			this.original = this.parser.parse();
			this.gen = new ClassGen(this.original);
		} catch(IOException e){
			e.printStackTrace();
		}
	}

	public void optimize()
	{
		ClassGen cgen = new ClassGen(original);
		cgen.setMajor(49);
		cgen.setMinor(0);
		ConstantPoolGen cpgen = cgen.getConstantPool();
		InstructionFactory factory = new InstructionFactory(cgen, cpgen);

		for (Method method : cgen.getMethods()) {
			if (method.isAbstract() || method.isNative()) {
				continue;
			}

			MethodGen methodGen = new MethodGen(method, cgen.getClassName(), cpgen);
			InstructionList instructionList = methodGen.getInstructionList();
			if (instructionList == null) {
				continue;
			}

			boolean changed;
			do {
				changed = false;
				changed |= replaceLoadsForSingleAssignmentConstants(instructionList, cpgen, factory);
				changed |= replaceLoadsForDynamicConstants(instructionList, cpgen, factory);
				changed |= foldConstantArithmetic(instructionList, cpgen, factory);
				changed |= eliminateDeadStores(instructionList, cpgen);
			} while (changed);

			methodGen.setMaxStack();
			methodGen.setMaxLocals();
			cgen.replaceMethod(method, methodGen.getMethod());
		}

		this.gen = cgen;
		this.optimized = cgen.getJavaClass();
	}

	private boolean foldConstantArithmetic(InstructionList instructionList, ConstantPoolGen cpgen,
			InstructionFactory factory)
	{
		boolean changedAny = false;
		boolean changed;

		do {
			changed = false;

			for (InstructionHandle handle = instructionList.getStart(); handle != null; handle = handle.getNext()) {
				Instruction instruction = handle.getInstruction();
				if (!(instruction instanceof ArithmeticInstruction)) {
					continue;
				}

				if (isUnaryArithmetic(instruction)) {
					InstructionHandle operandHandle = handle.getPrev();
					Number operand = getNumericConstant(operandHandle, cpgen);

					if (operand == null) {
						continue;
					}

					Number result = evaluateUnary(instruction, operand);
					replaceInstructions(instructionList, operandHandle, handle, factory.createConstant(result));
					changedAny = true;
					changed = true;
					break;
				}

				InstructionHandle rightHandle = handle.getPrev();
				InstructionHandle leftHandle = rightHandle == null ? null : rightHandle.getPrev();
				Number left = getNumericConstant(leftHandle, cpgen);
				Number right = getNumericConstant(rightHandle, cpgen);

				if (left == null || right == null) {
					continue;
				}

				Number result = evaluateBinary(instruction, left, right);
				if (result == null) {
					continue;
				}

				replaceInstructions(instructionList, leftHandle, handle, factory.createConstant(result));
				changedAny = true;
				changed = true;
				break;
			}
		} while (changed);

		return changedAny;
	}

	private boolean replaceLoadsForSingleAssignmentConstants(InstructionList instructionList, ConstantPoolGen cpgen,
			InstructionFactory factory)
	{
		Map<Integer, StoreInfo> stores = new HashMap<Integer, StoreInfo>();

		for (InstructionHandle handle = instructionList.getStart(); handle != null; handle = handle.getNext()) {
			Instruction instruction = handle.getInstruction();
			if (instruction instanceof IINC) {
				IINC increment = (IINC) instruction;
				StoreInfo info = stores.get(increment.getIndex());
				if (info == null) {
					info = new StoreInfo();
					stores.put(increment.getIndex(), info);
				}
				info.count += 1;
				info.constant = null;
				continue;
			}

			if (!(instruction instanceof StoreInstruction)) {
				continue;
			}

			StoreInstruction store = (StoreInstruction) instruction;
			if (!isNumericType(store.getType(cpgen))) {
				continue;
			}

			int index = store.getIndex();
			StoreInfo info = stores.get(index);
			if (info == null) {
				info = new StoreInfo();
				stores.put(index, info);
			}

			info.count += 1;
			if (info.count == 1) {
				info.constant = getNumericConstant(handle.getPrev(), cpgen);
				info.storeHandle = handle;
			} else {
				info.constant = null;
				info.storeHandle = null;
			}
		}

		boolean changed = false;
		for (InstructionHandle handle = instructionList.getStart(); handle != null; handle = handle.getNext()) {
			Instruction instruction = handle.getInstruction();
			if (!(instruction instanceof LoadInstruction)) {
				continue;
			}

			LoadInstruction load = (LoadInstruction) instruction;
			if (!isNumericType(load.getType(cpgen))) {
				continue;
			}

			StoreInfo info = stores.get(load.getIndex());
			if (info == null || info.count != 1 || info.constant == null || info.storeHandle == null) {
				continue;
			}

			if (!comesAfter(handle, info.storeHandle)) {
				continue;
			}

			replaceInstructions(instructionList, handle, handle, factory.createConstant(info.constant));
			changed = true;
		}

		return changed;
	}

	private boolean replaceLoadsForDynamicConstants(InstructionList instructionList, ConstantPoolGen cpgen,
			InstructionFactory factory) {
		boolean changed = false;
		Map<Integer, Number> knownVariables = new HashMap<>();

		InstructionHandle handle = instructionList.getStart();
		while (handle != null) {
			InstructionHandle next = handle.getNext();
			Instruction inst = handle.getInstruction();

			InstructionTargeter[] targeters = handle.getTargeters();
			if (targeters != null && targeters.length > 0) {
				knownVariables.clear();
			}

			if (inst instanceof BranchInstruction) {
				knownVariables.clear();
			}

			if (inst instanceof StoreInstruction) {
 				StoreInstruction store = (StoreInstruction) inst;
				int index = store.getIndex();

				Number val = getNumericConstant(handle.getPrev(), cpgen);

				if (val != null && isNumericType(store.getType(cpgen))) {
					knownVariables.put(index, val);
				} else {
					knownVariables.remove(index);
				}
			} else if (inst instanceof IINC) {
				knownVariables.remove(((IINC) inst).getIndex());
			} else if (inst instanceof LoadInstruction) {
				LoadInstruction load = (LoadInstruction) inst;
				int index = load.getIndex();

				if (knownVariables.containsKey(index) && isNumericType(load.getType(cpgen))) {
					Number currentVal = knownVariables.get(index);
					Number existing = getNumericConstant(handle, cpgen);

					if (existing == null || !existing.equals(currentVal)) {
						replaceInstructions(instructionList, handle, handle, factory.createConstant(currentVal));
						changed = true;
					}
				}
			}
			handle = next;
		}

		return changed;
	}

	private boolean eliminateDeadStores(InstructionList instructionList, ConstantPoolGen cpgen) {
		boolean changed = false;
		Set<Integer> neededSlots = new HashSet<>();

		InstructionHandle handle = instructionList.getEnd();
		while (handle != null) {
			InstructionHandle prev = handle.getPrev();  // save before possible deletion
			Instruction ins = handle.getInstruction();

			if (ins instanceof LoadInstruction) {
				neededSlots.add(((LoadInstruction) ins).getIndex());
			} else if (ins instanceof StoreInstruction) {
				int slot = ((StoreInstruction) ins).getIndex();
				if (neededSlots.contains(slot)) {
					neededSlots.remove(slot);  // store is alive
				} else {
					InstructionHandle pushHandle = handle.getPrev();
					InstructionHandle nextHandle = handle.getNext();
					try {
						if (pushHandle != null && getNumericConstant(pushHandle, cpgen) != null) {
							instructionList.delete(pushHandle, handle);  // delete both
						} else {
							instructionList.delete(handle);  // delete just the store
						}
						changed = true;
					} catch (TargetLostException e) {
						for (InstructionHandle lost : e.getTargets()) {
							for (InstructionTargeter targeter : lost.getTargeters()) {
								targeter.updateTarget(lost, nextHandle);
							}
						}
						changed = true;
					}
					prev = pushHandle == null ? null : pushHandle.getPrev();
				}
			}

			handle = prev;
		}

		return changed;
	}


	private boolean comesAfter(InstructionHandle current, InstructionHandle anchor)
	{
		if (current == null || anchor == null || current == anchor) {
			return false;
		}

		for (InstructionHandle cursor = anchor.getNext(); cursor != null; cursor = cursor.getNext()) {
			if (cursor == current) {
				return true;
			}
		}

		return false;
	}

	private boolean isNumericType(Type type)
	{
		return Type.INT.equals(type)
				|| Type.LONG.equals(type)
				|| Type.FLOAT.equals(type)
				|| Type.DOUBLE.equals(type);
	}

	private boolean isUnaryArithmetic(Instruction instruction)
	{
		return instruction instanceof INEG
				|| instruction instanceof LNEG
				|| instruction instanceof FNEG
				|| instruction instanceof DNEG;
	}

	private Number getNumericConstant(InstructionHandle handle, ConstantPoolGen cpgen)
	{
		if (handle == null) {
			return null;
		}

		Instruction instruction = handle.getInstruction();
		if (instruction instanceof ConstantPushInstruction) {
			return ((ConstantPushInstruction) instruction).getValue();
		}
		if (instruction instanceof LDC) {
			Object value = ((LDC) instruction).getValue(cpgen);
			return value instanceof Number ? (Number) value : null;
		}
		if (instruction instanceof LDC2_W) {
			return ((LDC2_W) instruction).getValue(cpgen);
		}

		return null;
	}

	private Number evaluateUnary(Instruction instruction, Number operand)
	{
		if (instruction instanceof INEG) {
			return Integer.valueOf(-operand.intValue());
		}
		if (instruction instanceof LNEG) {
			return Long.valueOf(-operand.longValue());
		}
		if (instruction instanceof FNEG) {
			return Float.valueOf(-operand.floatValue());
		}
		if (instruction instanceof DNEG) {
			return Double.valueOf(-operand.doubleValue());
		}

		return null;
	}

	private Number evaluateBinary(Instruction instruction, Number left, Number right)
	{
		if (instruction instanceof IADD) {
			return Integer.valueOf(left.intValue() + right.intValue());
		}
		if (instruction instanceof ISUB) {
			return Integer.valueOf(left.intValue() - right.intValue());
		}
		if (instruction instanceof IMUL) {
			return Integer.valueOf(left.intValue() * right.intValue());
		}
		if (instruction instanceof IDIV) {
			if (right.intValue() == 0) {
				return null;
			}
			return Integer.valueOf(left.intValue() / right.intValue());
		}
		if (instruction instanceof IREM) {
			if (right.intValue() == 0) {
				return null;
			}
			return Integer.valueOf(left.intValue() % right.intValue());
		}

		if (instruction instanceof LADD) {
			return Long.valueOf(left.longValue() + right.longValue());
		}
		if (instruction instanceof LSUB) {
			return Long.valueOf(left.longValue() - right.longValue());
		}
		if (instruction instanceof LMUL) {
			return Long.valueOf(left.longValue() * right.longValue());
		}
		if (instruction instanceof LDIV) {
			if (right.longValue() == 0L) {
				return null;
			}
			return Long.valueOf(left.longValue() / right.longValue());
		}
		if (instruction instanceof LREM) {
			if (right.longValue() == 0L) {
				return null;
			}
			return Long.valueOf(left.longValue() % right.longValue());
		}

		if (instruction instanceof FADD) {
			return Float.valueOf(left.floatValue() + right.floatValue());
		}
		if (instruction instanceof FSUB) {
			return Float.valueOf(left.floatValue() - right.floatValue());
		}
		if (instruction instanceof FMUL) {
			return Float.valueOf(left.floatValue() * right.floatValue());
		}
		if (instruction instanceof FDIV) {
			return Float.valueOf(left.floatValue() / right.floatValue());
		}
		if (instruction instanceof FREM) {
			return Float.valueOf(left.floatValue() % right.floatValue());
		}

		if (instruction instanceof DADD) {
			return Double.valueOf(left.doubleValue() + right.doubleValue());
		}
		if (instruction instanceof DSUB) {
			return Double.valueOf(left.doubleValue() - right.doubleValue());
		}
		if (instruction instanceof DMUL) {
			return Double.valueOf(left.doubleValue() * right.doubleValue());
		}
		if (instruction instanceof DDIV) {
			return Double.valueOf(left.doubleValue() / right.doubleValue());
		}
		if (instruction instanceof DREM) {
			return Double.valueOf(left.doubleValue() % right.doubleValue());
		}

		return null;
	}

	private void replaceInstructions(InstructionList instructionList, InstructionHandle start,
			InstructionHandle end, Instruction replacement)
	{
		InstructionHandle replacementHandle = instructionList.insert(start, replacement);

		try {
			instructionList.delete(start, end);
		} catch (TargetLostException e) {
			for (InstructionHandle lostHandle : e.getTargets()) {
				InstructionTargeter[] targeters = lostHandle.getTargeters();
				if (targeters == null) {
					continue;
				}

				for (InstructionTargeter targeter : targeters) {
					targeter.updateTarget(lostHandle, replacementHandle);
				}
			}
		}
	}

	public void write(String optimisedFilePath)
	{
		this.optimize();

		try {
			FileOutputStream out = new FileOutputStream(new File(optimisedFilePath));
			this.optimized.dump(out);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private static final class StoreInfo {
		private int count;
		private Number constant;
		private InstructionHandle storeHandle;
	}
}