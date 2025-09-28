import Lean

namespace Hdlean

section OrphanInstances

@[instance low]
def instToStringOfRepr [Repr α]: ToString α :=
 {toString self := ToString.toString $ Repr.reprPrec self 0}

instance (a:Nat) (s:Std.Range): Decidable (a ∈ s) := instDecidableAnd

deriving instance Repr for
  Lean.ConstantKind,
  Lean.ConstantVal,
  Lean.AxiomVal,
  Lean.ReducibilityHints,
  Lean.DefinitionVal,
  Lean.TheoremVal,
  Lean.OpaqueVal,
  Lean.QuotKind,
  Lean.QuotVal,
  Lean.InductiveVal,
  Lean.ConstructorVal,
  Lean.RecursorRule,
  Lean.RecursorVal,
  Lean.ConstantInfo

instance : Repr Lean.Environment where
  reprPrec env p :=
  Id.run do
    let mut acc := #[]
    for (name, _info) in Lean.Environment.constants env do
      acc := acc.push name
    let constants ← Repr.reprPrec acc p
    Std.Format.text "Lean.Environment" ++ .bracket "{" ("constants = " ++ constants ++ Std.Format.line ++ "..") "}"

deriving instance Repr for
  Lean.ExternEntry,
  Lean.ExternAttrData,
  Lean.IR.DeclInfo,
  Lean.IR.LitVal,
  Lean.IR.Arg,
  Lean.IR.Expr,
  Lean.IR.FnBody,
  Lean.IR.Decl,
  Std.Format.FlattenBehavior,
  Std.Format,
  Lean.IR.LogEntry

deriving instance Repr for Lean.ConstMap
deriving instance Repr for
  Lean.LocalDecl,
  Lean.Meta.Match.DiscrInfo,
  Lean.Meta.Match.MatcherInfo

deriving instance Repr for Lean.StructureParentInfo
deriving instance Repr for
  Lean.Compiler.LCNF.Arg,
  Lean.Compiler.LCNF.LitValue,
  Lean.Compiler.LCNF.LetValue,
  Lean.Compiler.LCNF.LetDecl,
  Lean.Compiler.LCNF.Param,
  Lean.Compiler.LCNF.Code
deriving instance Repr for
  Lean.Meta.ReduceMatcherResult
deriving instance Repr for
  Lean.ExternEntry,
  Lean.ExternAttrData,
  Lean.Compiler.InlineAttributeKind,
  Lean.Compiler.LCNF.DeclValue,
  Lean.Compiler.LCNF.Decl

end OrphanInstances

-- Debug variant which doesn't return anything. Only works in `IO`.
elab "dbg!'" stx:term : term => do
  let str := String.trim <| match stx.raw.reprint with
    | .some str => str
    | .none => ToString.toString stx
  let str := Lean.Syntax.mkStrLit str

  let file ← Lean.MonadLog.getFileName
  let file := Lean.Syntax.mkStrLit file

  let ref_pos := stx.raw.getPos?
  let map ← Lean.MonadFileMap.getFileMap
  let lsp_pos := do
    let ⟨line, col⟩ := map.utf8PosToLspPos (← ref_pos)
    s!":{line+1}:{col+1}"
  let lsp_pos := Lean.Syntax.mkStrLit <| lsp_pos.getD ""

  let io_unit := .app (Lean.Expr.const ``IO []) (Lean.Expr.const ``Unit [])

  Lean.Elab.Term.elabTerm
    (← `(IO.println <| s!"[{$file}{$lsp_pos}] {$str} = {$stx}"))
    <| .some io_unit

/- -- Similar to Rust `dbg!` macro. Prints source info and value of an expression and evaluates to that expression.
elab "dbg!" stx:term : term => do
  let str := String.trim <| match stx.raw.reprint with
    | .some str => str
    | .none => ToString.toString stx
  let str := Lean.Syntax.mkStrLit str

  let file ← Lean.MonadLog.getFileName
  let file := Lean.Syntax.mkStrLit file

  let ref_pos := stx.raw.getPos?
  let map ← Lean.MonadFileMap.getFileMap
  let lsp_pos := do
    let ⟨line, col⟩ := map.utf8PosToLspPos (← ref_pos)
    s!":{line+1}:{col+1}"
  let lsp_pos := Lean.Syntax.mkStrLit <| lsp_pos.getD ""

  let ty ← Lean.Meta.inferType <| (← Lean.Elab.Term.elabTerm stx .none)

  let res := Lean.mkIdent `«res✝»
  Lean.Elab.Term.elabTerm
    (← `(
      let $res := $stx
      dbg_trace s!"[{$file}{$lsp_pos}] {$str} = {$res}"
      $res
    )) <| .some ty -/

elab "dbg_info_stmt" stx:term: term => do
  let str := String.trim <| match stx.raw.reprint with
    | .some str => str
    | .none => ToString.toString stx
  let str := Lean.Syntax.mkStrLit str

  let file ← Lean.MonadLog.getFileName
  let file := Lean.Syntax.mkStrLit file

  let ref_pos := stx.raw.getPos?
  let map ← Lean.MonadFileMap.getFileMap
  let lsp_pos := do
    let ⟨line, col⟩ := map.utf8PosToLspPos (← ref_pos)
    s!":{line+1}:{col+1}"
  let lsp_pos := Lean.Syntax.mkStrLit <| lsp_pos.getD ""

  let ty ← Lean.Meta.inferType <| (← Lean.Elab.Term.elabTerm stx .none)

  Lean.Elab.Term.elabTerm
    (← `(
      s!"[{$file}{$lsp_pos}] {$str} = {$stx}"
    )) <| .some ty

-- `dbg_trace` with line info.
-- declare_syntax_cat dbgTrace'Arg
-- syntax dbgTrace'Arg := interpolatedStr(term) <|> term
-- syntax:lead (interpolatedStr(term) <|> term) : dbgTrace'Arg
-- syntax:lead (name:=dbgTrace'Term) "dbg_trace' " dbgTrace'Arg optSemicolon(term) : term

-- TODO It looks like dbg_trace has special handling in the compiler to handle the ambiguity correctly. If we try to use `optSemicolon(term)` this consumes more than the `dbgTrace'Do` syntax, in a single syntax rule, and is thus chosen in do blocks with newlines, which is wrong. It then fails when expanding, but doesn't try the next syntax.
syntax:lead (name:=dbgTrace'Term) withPosition("dbg_trace' " (interpolatedStr(term) <|> term)) ";" term: term
syntax:lead (name:=dbgTrace'Do) "dbg_trace' " (interpolatedStr(term) <|> term): doElem

macro_rules (kind:=dbgTrace'Term)
  | `(dbg_trace' $stx:interpolatedStr; $rest) => `(dbg_trace (dbg_info_stmt s!$stx); $rest)
  | `(dbg_trace' $stx:term; $rest) => `(dbg_trace (dbg_info_stmt $stx); $rest)

macro_rules (kind:=dbgTrace'Do)
  | `(dbgTrace'Do| dbg_trace' $stx:interpolatedStr) => `(doElem| do dbg_trace (dbg_info_stmt s!$stx))
  | `(dbgTrace'Do| dbg_trace' $stx:term) => `(doElem| dbg_trace (dbg_info_stmt $stx))

-- Similar to Rust `dbg!` macro. Prints source info and value of an expression and evaluates to that expression.
macro "dbg!" stx:term : term => `(dbg_trace (dbg_info_stmt $stx); $stx)

-- def a : Nat := 1
-- def test : Nat := 4+a
-- #eval dbg!' 3+3+test
-- def b : Nat := dbg! 3 + 3 + test
-- #eval b
-- #eval dbg! 3+3+test
-- #eval dbg_trace' "test {3+3}";
--   3
-- #eval dbg_trace "test {3+3}"
--   3
-- #eval do
--   dbg_trace "test {3+3}"
--   -- if Bool.true then pure ()
--   pure 3
-- #eval do
--   dbg_trace' "test {3+3}"
--   -- if Bool.true then pure ()
--   pure 3
-- #eval do
--   dbg_trace' "test {3+3}"

-- #eval do
--   dbg_trace' "test {3+3}"
--   if Bool.true then pure ()
--   pure 3
