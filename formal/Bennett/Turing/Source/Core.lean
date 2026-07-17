import Bennett.Transition.Core
import Bennett.Turing.Tape
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Executable source Turing machines

A source quintuple `A T → T' σ A'` first checks control `A` and scanned symbol
`T`, then writes `T'`, moves by `σ`, and changes control to `A'`.  Programs use
intrinsic rule identifiers `Fin ruleCount`, which later serve as history records
and make the syntactic rule count definitionally inspectable.

The executable step selects the first indexed matching rule.  Its declarative
all-rule relation is defined separately: agreement between the two semantics is
proved only under syntactic unique-key assumptions.
-/

namespace Bennett.Turing

/-- A source-machine control state paired with one complete tape. -/
structure Configuration (Control Symbol : Type*) where
  control : Control
  tape : Tape Symbol
deriving DecidableEq

namespace Configuration

variable {Control Symbol : Type*}

/-- Symbol currently scanned by a source configuration. -/
def read (config : Configuration Control Symbol) : TapeSymbol Symbol :=
  config.tape.read

@[simp] theorem read_eq (config : Configuration Control Symbol) :
    config.read = config.tape.cells config.tape.head := rfl

end Configuration

/-- A source quintuple `source scanned → written move target`. -/
structure Quintuple (Control Symbol : Type*) where
  source : Control
  scanned : TapeSymbol Symbol
  written : TapeSymbol Symbol
  move : Move
  target : Control
deriving DecidableEq, Repr

namespace Quintuple

variable {Control Symbol : Type*}

/-- The control/read key determining whether a quintuple is applicable. -/
def key (rule : Quintuple Control Symbol) : Control × TapeSymbol Symbol :=
  (rule.source, rule.scanned)

/-- Applicability reads the complete pre-transition configuration. -/
def Matches (rule : Quintuple Control Symbol)
    (config : Configuration Control Symbol) : Prop :=
  rule.source = config.control ∧ rule.scanned = config.read

instance [DecidableEq Control] [DecidableEq Symbol]
    (rule : Quintuple Control Symbol) (config : Configuration Control Symbol) :
    Decidable (rule.Matches config) := by
  unfold Matches
  infer_instance

/-- Execute in the paper's order: write, move, then change control. -/
def execute (rule : Quintuple Control Symbol)
    (config : Configuration Control Symbol) : Configuration Control Symbol :=
  { control := rule.target
    tape := config.tape.writeMove rule.written rule.move }

theorem execute_order (rule : Quintuple Control Symbol)
    (config : Configuration Control Symbol) :
    rule.execute config =
      { control := rule.target
        tape := (config.tape.write rule.written).move rule.move } :=
  rfl

@[simp] theorem execute_control (rule : Quintuple Control Symbol)
    (config : Configuration Control Symbol) :
    (rule.execute config).control = rule.target := rfl

@[simp] theorem execute_head (rule : Quintuple Control Symbol)
    (config : Configuration Control Symbol) :
    (rule.execute config).tape.head =
      config.tape.head + rule.move.offset := rfl

@[simp] theorem execute_written_cell (rule : Quintuple Control Symbol)
    (config : Configuration Control Symbol) :
    (rule.execute config).tape.cells config.tape.head = rule.written := by
  simp [execute, Tape.writeMove]

end Quintuple

/-- Finite source syntax with intrinsic rule identifiers `Fin ruleCount`. -/
structure Machine (Control Symbol : Type*) where
  ruleCount : Nat
  rule : Fin ruleCount → Quintuple Control Symbol

namespace Machine

variable {Control Symbol : Type*}

/-- Intrinsic rule identifier type; its cardinality is `ruleCount`. -/
abbrev RuleId (machine : Machine Control Symbol) := Fin machine.ruleCount

@[simp] theorem ruleId_card (machine : Machine Control Symbol) :
    Fintype.card machine.RuleId = machine.ruleCount :=
  Fintype.card_fin machine.ruleCount

/-- No two rule identifiers have the same control/read key. -/
def SyntacticallyDeterministic (machine : Machine Control Symbol) : Prop :=
  Function.Injective fun index : machine.RuleId => (machine.rule index).key

/-- Select the least indexed matching rule, if one exists. -/
def select [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) (config : Configuration Control Symbol) :
    Option machine.RuleId :=
  Fin.find? fun index => decide ((machine.rule index).Matches config)

/-- Executable one-step semantics using the selected rule. -/
def step [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) : PartialStep (Configuration Control Symbol) :=
  fun config => (machine.select config).map fun index =>
    (machine.rule index).execute config

/-- Declarative semantics of all rules, without an implicit priority policy. -/
def StepRel (machine : Machine Control Symbol)
    (before after : Configuration Control Symbol) : Prop :=
  ∃ index : machine.RuleId,
    (machine.rule index).Matches before ∧
      (machine.rule index).execute before = after

end Machine
end Bennett.Turing
