import Hdlean
import Lean

open Lean Lean.Compiler.LCNF in
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Main}] {} (trustLevel := 0)
  let code: EIO Exception (Code × Core.State) := ReaderT.run <|
      let code := CompilerM.run <|
        toLCNF <| match env.constants.find! ``BitVec.add with
        | ConstantInfo.defnInfo val => val.value
        | _ => panic! ""
      code
    |>.run {fileName:=default,fileMap:=default}
    <| {env}
  let code ← match ← code.toIO' with
  | .ok x => pure x
  | .error e => return ← println! "error: {← e.toMessageData.toString}"
  println! code.fst
