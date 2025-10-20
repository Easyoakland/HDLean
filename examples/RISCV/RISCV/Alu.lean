import RISCV.Types
import RISCV.Basic

def aluT (ctrl:AluCtrl) (a b : Word): Word×Bool := (alu_res, equals)
  where
    equals := a == b
    alu_res := match ctrl with
      | .and => a &&& b
      | .or => a ||| b
      | .add => a + b
      | .sll => a <<< b
      | .srl => a >>> b
      | .sub => a - b
        -- Sets the destination register to 1 if the first source register is less than
        -- the second source register when both are treated as signed numbers, otherwise it sets
        -- the destination register to 0.
      | .slt => a.slt b
      | .xor => a ^^^ b
      | .sltu => a.ult b
      | .sra => a.sshiftRight' b
        -- Load the upper 20 bits. The intermediate generation unit will output the already shifted and corrected value. The ALU only needs to pass on the already shifted value since the ImmGen doesn't directly connect to `reg_w_data`. Also note the intermediate output goes to input `i_alu_b` not `i_alu_a`.
      | .lui => b
