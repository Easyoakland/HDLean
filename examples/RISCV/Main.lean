import Hdlean
import RISCV
import RISCV.Alu
import RISCV.SingleProcTb
import RISCV.SingleCycleProc

open Hdlean

def mulAccStep [Add α] [Mul α] (acc:α) (xy:α × α) : α := acc + xy.1 * xy.2

def mulAccT [Add α][Mul α] (inp:α×α) (acc:α) : α×α :=
  let val := mulAccStep acc inp
  (val, val)

def mulAcc [Add o][Mul o][Inhabited o] (inp:Signal dom (o × o)): Signal dom o :=
  inp.scan mulAccT

def mulAcc_mono : Mealy (BitVec 10) := mulAcc (o:=BitVec 10) (dom:=default) (Mealy.pure (0,0))

def processorT_mono := RISCV.SingleCycle.processorT { instruction := 0x000002b3
                                                      data_mem_r_data := fun _ => 0 }

#eval do println! ← Compiler.emit ``mulAcc_mono
#eval do println! ← Compiler.emit ``aluT
set_option trace.hdlean.compiler true in
set_option trace.Meta.whnf true in
#eval do println! ← Compiler.emit ``processorT_mono

open Lean Lean.Compiler.LCNF in
def main : IO Unit := do
  -- println! ToString.toString (Main 145)
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution -- Need to run initializers for HDLean compilation to work correctly (e.g., needed by `implemented_by_hw`)
  let env ← importModules (loadExts:=true) #[{module := `Main}] {} (trustLevel := 0)
  let compilationOutput ← Compiler.emit ``aluT
    |>.run' {}
    |>.run' {fileName:=default,fileMap:=default} {env}
    |>.toIO'
  let compilationOutput ← match compilationOutput with
  | .ok x => pure x
  | .error e => IO.throwServerError s!"{← e.toMessageData.toString}"
  IO.FS.writeFile "output.sv" (ToString.toString compilationOutput)
  IO.println "Done. Wrote result to output.sv"
