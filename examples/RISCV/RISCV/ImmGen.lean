import Lean
import RISCV.Basic

namespace ImmGen

/--
- `instruction`: instruction to decode immediate from
- return: sign-extended immediate
-/
def immGen (instruction : BitVec 32): BitVec 32 :=
  let instruction' := instruction.reverse.toVector
  let opcode := instruction'[0:7]
  match opcode.reverse.toBitVec with
  -- I-type arithmetic instructions
  | 0b0010011 => instruction'[20:32] |>.reverse.toBitVec |>.signExtend _
  -- lw
  | 0b0000011 => instruction'[20:32] |>.reverse.toBitVec |>.signExtend _
  -- sw
  | 0b0100011 => instruction'[7:12] ++ instruction'[25:32] |>.reverse.toBitVec |>.signExtend _
  -- lui
  | 0b0110111 => instruction'[12:32].reverse.toBitVec ++ 0#12 |>.signExtend _
  -- beq
  | 0b1100011 => (0#1).toVector ++ instruction'[8:12] ++ instruction'[25:31] ++ instruction'[7] ++ instruction'[31] |>.reverse.toBitVec |>.signExtend _
  -- jal
  | 0b1101111 => (0#1).toVector ++ instruction'[21:31] ++ instruction'[20] ++ instruction'[12:20] ++ instruction'[31] |>.reverse.toBitVec |>.signExtend _
  | _ => panic! "unsupported instruction"
