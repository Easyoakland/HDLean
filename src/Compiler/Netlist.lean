import Hdlean.Basic

def List.strJoin [ToString α] [ToString β] (sep: α) (list:List β): String :=
  (list.foldl (init:=("", list.length))
    fun (acc, len) x => open ToString in
    (if len == 1 then acc ++ toString x else acc ++ toString x ++ toString sep, len-1))
  |>.fst

def String.replicate (n : Nat) (c : Char): String := String.mk <| List.replicate n c

namespace Hdlean.Compiler.Netlist

namespace SystemVerilog
open Lean Lean.Name

def tabwidth := 2

section BaseTypes

inductive Direction where
  | input
  | output
  | inout
deriving Repr, BEq, Hashable, Inhabited

def Direction.emit: Direction → String
  | input => "input"
  | output => "output"
  | inout => "inout"

inductive ActiveEdge where
  | posedge
  | negedge
  deriving Repr, BEq, Hashable

def ActiveEdge.emit: ActiveEdge → String
  | posedge => "posedge"
  | negedge => "negedge"

/-- Assignments are either blocking (further uses of the signal return the new value, primarily used in combinational blocks) or nonblocking (further uses in the block return the old value, primarily used in sequential/flip-flop blocks) -/
inductive AssignmentType where
  | blocking
  | nonblocking
  deriving Repr, BEq, Hashable

def AssignmentType.emit: AssignmentType → String
  | .blocking => "="
  | nonblocking => "<="

abbrev Identifier := Name

inductive SubstChar where
| keep
| replace (c:Char)
| remove

def _root_.String.substChar (s:String) (p: Char → SubstChar): String := Id.run do
  let mut acc := ""
  for c in s.data do match p c with
    | .keep => acc := acc.push c
    | .replace c => acc := acc.push c
    | .remove => ()
  acc

/-- `escape := true` to escape identifiers (start with `\` end with whitespace) to avoid keyword issues and invalid ascii characters and so on. -/
/- 5.6:
"The first character of a simple identifier shall not be a digit or $; it can be a letter or an underscore.
Identifiers shall be case sensitive."
"Escaped identifiers shall start with the backslash character (\) and end with white space (space, tab,
newline). They provide a means of including any of the printable ASCII characters in an identifier (the
decimal values 33 through 126, or 21 through 7E in hexadecimal)." -/
def Identifier.emit (ident:Identifier) (escape:=false): String :=
  let s := esc ++ ident.toStringWithSep "_" false |>.substChar f
  s.set 0 (start (s.get 0))
where
  esc := if escape then "\\" else ""
  start (c:Char): Char := if escape then c else
    if c.isDigit || c == '$' then '_' else c
  f (c:Char): SubstChar := if escape
  then
    if c.toNat ∈ [33:127] then .keep else .remove
  else
    if c.isAlphanum || c == '_' || c == '$' then .keep else .remove

abbrev Size := Nat

abbrev BitSlice := Std.Range
deriving instance Repr, BEq, Hashable for Std.Range

def BitSlice.emit (self:BitSlice): Option String :=
  if self.stop-self.start == 0 then .none
  else .some s!"[{self.stop}-1:{self.start}]"

inductive HWVariant where
  | logicVar
  | wire
  | reg
  | user (val:Identifier)
  deriving Repr, BEq, Hashable, Inhabited

def HWVariant.emit: HWVariant → String
  | logicVar => "logic var"
  | wire => "wire"
  | reg => "reg"
  | user s => s.emit

structure HWType where
  variant: HWVariant := default
  signed: Bool := default
  width: Nat
  deriving Repr, BEq, Hashable, Inhabited

def HWType.emit (self:HWType): Option String := do
  let signed := if self.signed then "signed " else ""
  let widthSlice ← if self.width != 0 then pure s!"[{self.width}-1:0]" else .none
  let type := self.variant.emit
  return s!"{signed}{type} {widthSlice}"

inductive BinOp where
  | add
  | sub
  | mul
  | div
  | mod
  | pow
  | and
  | or
  | xor
  | sll
  | srl
  | sra
  | lt
  | gt
  | le
  | ge
  | eq
  | neq
  deriving Repr, BEq, Hashable

def BinOp.emit : BinOp →  String
  | add => "+"
  | sub => "-"
  | mul => "*"
  | div => "/"
  | mod => "%"
  | pow => "**"
  | and => "&"
  | or => "|"
  | xor => "^"
  | sll => "<<"
  | srl => ">>"
  | sra => ">>>"
  | lt => "<"
  | gt => ">"
  | le => "<="
  | ge => ">="
  | eq => "=="
  | neq => "!="

inductive UnOp where
  /-- `if 0 then 1 else 0` -/
  | not
  /-- Flip all bits -/
  | invert
  /- Unary reduction operators -/
  | and
  | or
  | xor
  deriving Repr, BEq, Hashable

def UnOp.emit : UnOp → String
  | not => "!"
  | invert => "~"
  | and => "&"
  | or => "|"
  | xor => "^"

inductive CastOp
  | signed
  | unsigned
  deriving Repr, BEq, Hashable

/-- Emit prefix of the cast operation. Requires the casted value to additionally be wrapped in parens. -/
def CastOp.emit: CastOp → String
  | signed => "signed'"
  | unsigned => "unsigned'"

/-!
Borrows the terms "value", "space", "place" from [vine](https://vine.dev/docs/features/values-spaces-places.html?highlight=place#values-spaces-and-places)

  - a value represents some piece of data
  - a space represents somewhere that data can be put
  - a place is the combination of a value and a space.
-/

/-- Value consumer. Expression which can be used as the destination of a value. -/
inductive SpaceExpr : Type where
  | identifier (id : Identifier)
  | bitSelect (id : SpaceExpr) (bs : BitSlice)
  | concatenation (spaces : List SpaceExpr)
  deriving Repr, BEq, Hashable

def SpaceExpr.emit: SpaceExpr → Option String
  | identifier id => id.emit
  | bitSelect id bs => do s!"{← id.emit}{← bs.emit}"
  | concatenation spaces => do return "{" ++ ((←spaces.mapM (·.emit)).intersperseTR ", " |>.foldl (init:="") String.append) ++ "}"

-- #eval SpaceExpr.concatenation [SpaceExpr.identifier `a, .identifier `b |> (SpaceExpr.bitSelect . [1:3])] |>.emit |>.get!

mutual
inductive DynamicBitSlice where
  /-- Slice from `start` of `len` elements, where each element has size `scale`. -/
  | slice (start : ValueExpr) (len : Nat) (scale : Nat)
  deriving Repr, BEq, Hashable

/-- Value producer. Expression which represents a source of a piece of data. -/
inductive ValueExpr where
  | identifier (name : Identifier)
  | literal (val : String)
  | binaryOp (op : BinOp) (left : ValueExpr) (right : ValueExpr)
  | unaryOp (op : UnOp) (operand : ValueExpr)
  | castOp (op : CastOp) (operand : ValueExpr)
  | bitSelect (base : ValueExpr) (index : BitSlice)
  | dynamicBitSelect (base : ValueExpr) (index : DynamicBitSlice)
  /-- Stored from most to least significant order. -/
  | concatenation (parts : List ValueExpr)
  deriving Repr, BEq, Hashable, Inhabited
end

/-- The canonical way to represent a zero-sized `ValueExpr` -/
def ValueExpr.zst: ValueExpr := .concatenation []

def undefinedValue: ValueExpr := .literal "'x"

mutual
def DynamicBitSlice.emit (self:DynamicBitSlice): Option String :=
  match self with
  | .slice start len scale => if len == 0 || scale == 0 then .none else do pure s!"[{scale}*({← start.emit})+:{scale}*{len}]"

def ValueExpr.emit: ValueExpr → Option String
  | .identifier name => name.emit
  | .literal val => .some val
  | .binaryOp op l r => do s!"({← l.emit} {op.emit} {← r.emit})"
  | .unaryOp op x => do s!"({op.emit}{← x.emit})"
  | .castOp op x => do s!"({op.emit}({← x.emit}))"
  | .bitSelect b i => do s!"{← b.emit}{← i.emit}"
  | .dynamicBitSelect b i => do s!"{← b.emit}{← i.emit}"
  | .concatenation xs => if xs.length = 0 then .none else do return "{" ++ ((←xs.mapM (·.emit)).intersperseTR ", " |>.foldl String.append "") ++ "}"
end
-- #eval println! ValueExpr.binaryOp .add (ValueExpr.concatenation [ValueExpr.identifier `a, .identifier `b, .literal "'b101"]) (ValueExpr.unaryOp (.not) (ValueExpr.identifier `c)) |>.emit

end BaseTypes

section ModuleStructure

structure Port where
  name : Identifier
  type : HWType
  direction : Direction
  deriving Repr, BEq, Hashable, Inhabited

structure Parameter where
  name : Identifier
  /-- Parameters can have types optionally because of size inference. -/
  type : Option HWType
  deriving Repr, BEq, Hashable

/-- Declaration of a variable (i.e. a signal) -/
structure VarDeclaration where
  name : Identifier
  type : HWType
  init : Option ValueExpr := .none
  deriving Repr, BEq, Hashable

def VarDeclaration.emit (var:VarDeclaration): Option String := do
  let init ← match var.init with
    | .some x => pure s!" = {← x.emit}"
    | .none => pure ""
  s!"{← var.type.emit} {var.name.emit}{init};"

-- #eval VarDeclaration.mk (`name1) ({variant:=.logicVar, signed:=false, width:=3}) .none |>.emit
-- #eval VarDeclaration.mk (`name1) ({variant:=.logicVar, signed:=false, width:=3}) (.some <| ValueExpr.identifier `init) |>.emit

/-- Values to instantiate the signals of a `Module` with  -/
abbrev PortMap := List (Port× ValueExpr)
/-- Values to instantiate the parameters of a `Module` with  -/
abbrev ParamMap := List (Parameter× ValueExpr)

inductive Stmt
  /-- Unconditional assignment  -/
  | assignment (assign:AssignmentType) (space: SpaceExpr) (value:ValueExpr)
  /-- Conditional signal assignment. Represents both `if` and `case` statements in HDL.
  - `space`: Where to assign
  - `type`: Type of space and each alternatives result
  - `scrutinee`: Value compared for equality on for each case.
  - `cases`: list of compared to values and result if comparison is true
  - `default`: default value to use if none of the cases match
  -/
  | conditionalAssignment
    (assign:AssignmentType)
    (space:SpaceExpr)
    (type:HWType)
    (scrutinee:ValueExpr)
    (scrutineeType:HWType)
    (cases:List (ValueExpr×ValueExpr))
    (default: Option ValueExpr)
  deriving Repr, BEq, Hashable

open Std.Format in
def Stmt.emit : Stmt → Option Std.Format
  | assignment assign space val => do s!"{← space.emit} {assign.emit} {← val.emit};"
  | conditionalAssignment assign space _type scrutinee _scrutinee_type cases default => do
    let space_emit ← space.emit
    let cases := if cases.isEmpty then .none else cases.mapM (fun (cmp, res) => do return s!"{← cmp.emit}: {space_emit} {assign.emit} {← res.emit};")
    let cases := cases.map (joinSep · line)
    let default := default.bind (do s!"default: {space_emit} {assign.emit} {← ·.emit};")
    if cases.isNone && default.isNone then return panic! "space non-ZST but no cases or default"

    s!"case ({← scrutinee.emit})" ++ nest (1*tabwidth) (
      line ++ cases.getD "/* no case */"
      ++ line ++ default.getD "/* no default */"
    ) ++ line ++ text "endcase"

-- #eval Stmt.assignment .nonblocking (SpaceExpr.identifier `as) (ValueExpr.identifier `bs) |>.emit
-- #eval Stmt.assignment .blocking (SpaceExpr.identifier `as) (ValueExpr.identifier `bs) |>.emit
-- #eval println! Stmt.conditionalAssignment .blocking (SpaceExpr.identifier `a.b.c) default (ValueExpr.bitSelect (ValueExpr.identifier `b) ([1:2])) default [(ValueExpr.literal "'b1", ValueExpr.literal "'b0")] .none |>.emit.get!
-- #eval println! Stmt.conditionalAssignment .blocking (SpaceExpr.identifier `a.b.c) default (ValueExpr.bitSelect (ValueExpr.identifier `b) ([1:2])) default [(ValueExpr.literal "'b1", ValueExpr.literal "'b0"), (ValueExpr.literal "'b1", ValueExpr.literal "'b0")] .none |>.emit.get!
-- #eval println! Stmt.conditionalAssignment .nonblocking (SpaceExpr.identifier `a.b.c) default (ValueExpr.bitSelect (ValueExpr.identifier `b) ([1:4])) default [] (.some <| ValueExpr.identifier `def) |>.emit.get!

/-- Internals of a Module -/
inductive ModuleItem
  /-- Signal declaration -/
  | var (val: VarDeclaration)
  /-- Continuous signal assignment -/
  | assignment (space: SpaceExpr) (value:ValueExpr)
  /-- Statements running at simulator start -/
  | initial (stmts:List Stmt)
  /-- Always running combinational logic -/
  | alwaysComb (stmts:List Stmt)
  /-- Clocked sequential statements
  - clk: Clock expression.
  - stmts: Statements that execute on active clock edge.
  -/
  | alwaysClocked
      (edge:ActiveEdge)
      (clk:Identifier)
      (stmts:List Stmt)
  /-- Instantiation of another module -/
  | inst
      (module_name:Identifier)
      (inst_name:Identifier)
      (ports:PortMap)
      (parameters:ParamMap:={})
  deriving Repr, BEq, Hashable

open Std.Format in
def ModuleItem.emit: ModuleItem → Std.Format
  | .var val => val.emit.getD s!"/* ZST variable declaration: {val.name.emit} */"
  | .assignment space value => (do s!"assign {← space.emit} = {← value.emit};").getD ((do s!"/* ZST assign: {← space.emit} */").getD "/* ZST assign */")
  | .initial stmts => let stmts := stmts.map (·.emit)
    let stmts := stmts.filterMap id -- remove unrendered ZST statements
    if stmts.length = 0 then default else -- if no statements render nothing
    let start := "initial"
    let (start, stop) := if stmts.length != 1 then (start ++ " begin", "end") else (start, "")
    let stmts := joinSep stmts line
    start ++ group (nest (1*tabwidth) (
      line ++ stmts
    ) ++ if !stop.isEmpty then line else "") ++ stop
  | .alwaysComb stmts => let stmts := stmts.map (·.emit)
    let stmts := stmts.filterMap id -- remove unrendered ZST statements
    if stmts.length = 0 then default else -- if no statements render nothing
    let start := "always_comb"
    let (start, stop) := if stmts.length != 1 then (start ++ " begin", "end") else (start, "")
    let stmts := joinSep stmts line
    start ++ group (nest (1*tabwidth) (
      line ++ stmts
    ) ++ if !stop.isEmpty then line else "") ++ stop
  | .alwaysClocked edge clk stmts => let stmts := stmts.map (·.emit)
    let stmts := stmts.filterMap id -- remove unrendered ZST statements
    if stmts.length = 0 then default else -- if no statements render nothing
    let start := s!"always_ff @({edge.emit} {clk.emit})"
    let (start, stop) := if stmts.length != 1 then (start ++ " begin", "end") else (start, "")
    let stmts := joinSep stmts line
    start ++ group (nest (1*tabwidth) (
      line ++ stmts
    ) ++ if !stop.isEmpty then line else "") ++ stop
  | .inst mod_name inst_name ports params =>
    if params.length = 0 && ports.length = 0 then panic! "HDLean Error: params and ports both empty" else

    -- Use `align false` instead of `line` so flattening doesn't create a space character.
    let params := if params.length = 0 then text "" else
      text " #(" ++ nest (1*tabwidth) (
        align false ++ (joinSep (params.filterMap fun (param, value) => do
          return param.name.emit ++ " = " ++ (←value.emit))
        (align false ++ ", "))
      ) ++ align false ++ ")"

    let ports := if ports.length = 0 then text "" else
      text " (" ++ nest (1*tabwidth) (
        align false ++ (joinSep (ports.filterMap fun (port, value) => do
          return "." ++ port.name.emit ++ "(" ++ (←value.emit) ++ ")")
        (align false ++ ", "))
      ) ++ align false ++ ");"

    mod_name.emit ++ " " ++ inst_name.emit ++ group params ++ group ports

-- #eval println! ModuleItem.emit <| ModuleItem.alwaysComb [Stmt.assignment .blocking (SpaceExpr.identifier `a) (.identifier `b)]
-- #eval println! ModuleItem.emit <| ModuleItem.alwaysComb (List.replicate 3 (Stmt.assignment .blocking (SpaceExpr.identifier `a) (.identifier `b)))
-- #eval println! ModuleItem.emit <| ModuleItem.alwaysClocked .posedge `a [Stmt.assignment .blocking (SpaceExpr.identifier `a) (.identifier `b)]
-- #eval println! ModuleItem.emit <| ModuleItem.alwaysClocked .negedge `b (List.replicate 3 (Stmt.assignment .nonblocking (SpaceExpr.identifier `a) (.identifier `b)))
-- #eval println! ModuleItem.emit <| ModuleItem.inst `modname `u1_modname [(Port.mk `portname {variant:=.logicVar,signed:=false,width:=2} .output, .identifier `val)] []
-- #eval println! ModuleItem.emit <| ModuleItem.inst `modname `u1_modname (List.replicate 3 ((Port.mk `portname {variant:=.logicVar,signed:=false,width:=2} .output, .identifier `val))) []
-- #eval println! ModuleItem.emit <| ModuleItem.inst `modname `u1_modname (List.replicate 8 ((Port.mk `portname {variant:=.logicVar,signed:=false,width:=2} .output, .identifier `val))) []
-- #eval println! ModuleItem.emit <| ModuleItem.inst `modname `u1_modname (List.replicate 8 ((Port.mk `portname {variant:=.logicVar,signed:=false,width:=2} .output, .identifier `val))) [({name:=`a,type:={variant:=.logicVar,signed:=false,width:=4}},.some <| ValueExpr.identifier `value)]

/-- Module: base unit of a Netlist -/
structure Module where
  name : Identifier
  /-- Constant parameters. Act like a limited form of generics and evaluate at compile time. -/
  parameters : Array (Parameter× Option ValueExpr)
  /-- Input and output signals. -/
  ports : Array Port
  /-- Content of the module. -/
  items: Array ModuleItem
  deriving Repr, BEq, Hashable, Inhabited

end ModuleStructure

open Std.Format in
def Module.emit (self:Module): Std.Format :=
  let params := if self.parameters.size == 0 then text "" else
    text " #(" ++ nest (1*tabwidth) (
      align false ++ (joinSep
        (self.parameters.map fun (param, val) =>
          text "parameter " ++ param.name.emit ++ if let .some val := val>>=(·.emit) then " = " ++ val else "").toList
        (align false ++ ","))
    ) ++ align false ++ ")"

  let ports := if self.ports.size == 0 then text "" else
    text " (" ++ nest (1*tabwidth) (
      align false ++ (joinSep
        (self.ports.filterMap fun port => do
          return port.direction.emit ++ " " ++ (←port.type.emit) ++ " " ++ port.name.emit).toList
        (align false ++ ","))
    ) ++ align false ++ ");"

  let items := joinSep (self.items.map (·.emit)|>.toList) (line)

  "module " ++ self.name.emit ++ params ++ ports ++ nest (1*tabwidth) (line ++ items) ++ line ++ "endmodule"

-- #eval println! (default:Module).emit
-- #eval println! {
--   name:=`module_name,parameters:=#[(Parameter.mk `a {
--       variant:=HWVariant.logicVar,
--       signed:=false,
--       width:=3
--     }, Option.none), (Parameter.mk `b {
--       variant:=HWVariant.logicVar,
--       signed:=false,
--       width:=3
--     }, .some <| ValueExpr.identifier `bval)],
--   ports:=#[Port.mk `b {variant:=HWVariant.logicVar, signed:=true, width:=3} .output],
--   items:=#[
--     ModuleItem.var {name := `item1, type := {variant:=HWVariant.wire,width:=4}},
--     ModuleItem.var {name := `item2, type := {signed:=true,width:=0}},
--     ModuleItem.var {name := `item3, type := {width:=1}},
--     ModuleItem.alwaysComb [],
--     ModuleItem.alwaysComb [Stmt.assignment .blocking (.identifier `a) (.identifier `b)],
--     ModuleItem.alwaysComb (List.replicate 3 (Stmt.assignment .blocking (.identifier `a) (.identifier `b))),
--     ModuleItem.alwaysComb (List.replicate 15 (Stmt.assignment .blocking (.identifier `a) (.identifier `b))),
--     ModuleItem.alwaysClocked .posedge `clk [],
--     ModuleItem.alwaysClocked .negedge `clk [Stmt.assignment .blocking (.identifier `a) (.identifier `b)],
--     ModuleItem.alwaysClocked .posedge `clk (List.replicate 3 (Stmt.assignment .blocking (.identifier `a) (.identifier `b))),
--     ModuleItem.alwaysClocked .posedge `clk (List.replicate 15 (Stmt.assignment .blocking (.identifier `a) (.identifier `b))),
--     ModuleItem.assignment .blocking (.identifier `a) (.identifier `b),
--     ModuleItem.initial [],
--     ModuleItem.initial [Stmt.assignment .blocking (.identifier `a) (.identifier `b)],
--     ModuleItem.initial (List.replicate 3 (Stmt.assignment .blocking (.identifier `a) (.identifier `b))),
--     ModuleItem.initial (List.replicate 15 (Stmt.assignment .blocking (.identifier `a) (.identifier `b))),
--     ModuleItem.inst `toinstantitate `instname [({name:=`p1,type:={width:=4},direction:=Direction.input}, .identifier `val)] [],
--     ModuleItem.inst `toinstantitate3 `instname [({name:=`p1,type:={width:=4},direction:=Direction.input}, .identifier `val)] [({name:=`param1, type:={width:=5}}, .identifier `val)],
--   ]
--   :Module
-- }.emit

def ResetHWType: HWType := {width := 1}
def ClockHWType: HWType := {width := 1}

end SystemVerilog
