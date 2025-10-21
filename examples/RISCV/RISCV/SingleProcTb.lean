import RISCV.SingleCycleProc
import Hdlean

open RISCV Hdlean SingleCycle

abbrev InstructionMem := Vector Instruction 40
abbrev DataMem := Std.HashMap Ptr Word

def instructionMemArray : InstructionMem :=
--#v[0x000002b3]

#v[
        0x000002b3 --add t0,zero,zero
        , 0xfeedc3b7 --lui t2,0xfeedc
        , 0xeef38393 --addi t2,t2,-273 # feedbeef <exitLoop+0xfeedbe9f>
        , 0x0072a023 --sw t2,0(t0)
        , 0x00428313 --addi t1,t0,4
        , 0x0002a403 --lw s0,0(t0)
        , 0x00832023 --sw s0,0(t1)
        , 0x00630333 --add t1,t1,t1
        , 0x0080006f --j 28 <jumpTarget>
        , 0x0003f393 --andi t2,t2,0
         --jumpTarget:
        , 0x00732023 --sw t2,0(t1)
        , 0x00047393 --andi t2,s0,0
        , 0x00732223 --sw t2,4(t1)
        , 0x000003b3 --add t2,zero,zero
        , 0x01006293 --ori t0,zero,16
        , 0x00844433 --xor s0,s0,s0
        --loop:
        , 0x00140413 --addi s0,s0,1
        , 0x00538663 --beq t2,t0,50 <exitLoop>
        , 0x00138393 --addi t2,t2,1
        , 0xff5ff06f --j 40 <loop>
        --exitLoop:
        , 0x00732423 --sw t2,8(t1)
        , 0x00832623 --sw s0,12(t1)
        , 0x00c32403 --lw s0,12(t1)
        , 0x00241413 --slli s0,s0,0x2
        , 0x00832823 --sw s0,16(t1)
        , 0x00145493 --srli s1,s0,0x1
        , 0x00932a23 --sw s1,20(t1)
        , 0x00106393 --ori t2,zero,1
        , 0x0003e2b3 --or t0,t2,zero
        , 0xfff2c293 --not t0,t0
        , 0x0053b433 --sltu s0,t2,t0
        , 0x00832c23 --sw s0,24(t1)
        , 0x0072b433 --sltu s0,t0,t2
        , 0x00832e23 --sw s0,28(t1)
        , 0xfff2b413 --sltiu s0,t0,-1
        , 0x02832023 --sw s0,32(t1)
        , 0xfff3b413 --sltiu s0,t2,-1
        , 0x02832223 --sw s0,36(t1)
        , 0x0053a433 --slt s0,t2,t0
        , 0x02832423 --sw s0,40(t1)
    ]

def singleProcTb : Mealy (Option (Word × Ptr)):=
  let instrMem := instructionMemArray
  Mealy.pure () |>.scan (reset:=(instructionMemArray[0],default,default)) fun () (((nextInstr : Instruction), (dataMem:DataMem), (processorState : ProcessorState))) =>
    let (processorO, processorState) := SingleCycle.processorT
      { instruction := nextInstr
        data_mem_r_data := fun (addr:BitVec 32) => (dataMem)[if addr % 4 != 0 then panic! "non-word aligned load" else ((addr >>> 2 : BitVec _) <<< 2 : BitVec _)]?.getD 0 }
        processorState
    let nextInstr := instrMem[(processorO.pc >>> 2).toFin]?.getD 0
    let memWrite : Option .. := if !processorO.mem_w_en then .none else .some (processorO.mem_addr, processorO.mem_w_data)
    let dataMem := if let .some (addr, data) := memWrite then dataMem.insert addr data else dataMem
    (memWrite,nextInstr,dataMem,processorState)

open NotSynthesizable in
#eval simulate singleProcTb 100 |>.filterMap fun x =>
  if x.1.value.isNone then .none else
  .some <| x.1.repr 0 |> ToString.toString

open NotSynthesizable in
#eval simulate' singleProcTb 100 |>.filterMap fun x =>
  if x.1.isNone then .none else
  .some <| x.1 |> ToString.toString

open NotSynthesizable in
def Main (n:Nat) := simulate singleProcTb n |>.filterMap fun x =>
  if x.1.value.isNone then .none else
  .some <| x.1.repr 0
  |> ToString.toString
