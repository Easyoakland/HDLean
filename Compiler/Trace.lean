import Lean
import Lean.Environment
import Hdlean.Basic

namespace Hdlean

initialize
  Lean.registerTraceClass `hdlean.compiler (inherited:=true)
  Lean.registerTraceClass `hdlean.compiler.compileRecursor (inherited:=true)
  Lean.registerTraceClass `hdlean.compiler.compileCtor (inherited:=true)
  Lean.registerTraceClass `hdlean.compiler.compileValue (inherited:=true)
  Lean.registerTraceClass `hdlean.compiler.compileFun (inherited:=true)
  Lean.registerTraceClass `hdlean.compiler.compileFieldProj (inherited:=true)

-- register_option trace.hdlean.compiler : Bool := {
--   defValue := Bool.true
-- }
-- register_option trace.hdlean.compiler.compileRecursor : Bool := {
--   defValue := Bool.true
-- }
-- register_option trace.hdlean.compiler.compileCtor : Bool := {
--   defValue := Bool.true
-- }
-- register_option trace.hdlean.compiler.compileValue : Bool := {
--   defValue := Bool.true
-- }
