import Bennett.Prelude
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Option

/-!
# Canonical two-way-infinite tapes

Tape positions are integers.  `TapeSymbol.blank` is the distinguished blank and
`TapeSymbol.mark symbol` is nonblank, so finite support is exactly the nonblank
cells.  Absolute head positions make distinct-cell resource accounting
independent of a zipper representation or trimming convention.
-/

namespace Bennett.Turing

/-- A tape alphabet obtained by adjoining one distinguished blank symbol. -/
inductive TapeSymbol (Symbol : Type*) where
  | blank
  | mark (symbol : Symbol)
deriving DecidableEq, Repr

instance {Symbol : Type*} : Zero (TapeSymbol Symbol) :=
  ⟨.blank⟩

@[simp] theorem TapeSymbol.zero_eq_blank {Symbol : Type*} :
    (0 : TapeSymbol Symbol) = .blank := rfl

/-- `TapeSymbol` is definitionally one blank plus the nonblank alphabet. -/
def TapeSymbol.equivOption {Symbol : Type*} :
    TapeSymbol Symbol ≃ Option Symbol where
  toFun
    | .blank => none
    | .mark symbol => some symbol
  invFun
    | none => .blank
    | some symbol => .mark symbol
  left_inv symbol := by cases symbol <;> rfl
  right_inv symbol := by cases symbol <;> rfl

instance {Symbol : Type*} [Fintype Symbol] : Fintype (TapeSymbol Symbol) :=
  Fintype.ofEquiv (Option Symbol) TapeSymbol.equivOption.symm

@[simp] theorem TapeSymbol.card {Symbol : Type*} [Fintype Symbol] :
    Fintype.card (TapeSymbol Symbol) = Fintype.card Symbol + 1 := by
  rw [Fintype.card_congr TapeSymbol.equivOption]
  simp

/-- The three source-machine head movements. -/
inductive Move where
  | left
  | stay
  | right
deriving DecidableEq, Repr

/-- Signed displacement of one head movement. -/
def Move.offset : Move → Int
  | .left => -1
  | .stay => 0
  | .right => 1

@[simp] theorem Move.offset_left : Move.left.offset = -1 := rfl
@[simp] theorem Move.offset_stay : Move.stay.offset = 0 := rfl
@[simp] theorem Move.offset_right : Move.right.offset = 1 := rfl

namespace CellStore

/--
Executable update of a finitely supported tape store.

Mathlib's general `Finsupp.update` is intentionally noncomputable.  Pattern
matching on the optional tape symbol makes blank deletion/nonblank insertion
computable without requiring equality on the nonblank alphabet.
-/
def set {Symbol : Type*} (cells : Int →₀ TapeSymbol Symbol)
    (position : Int) (value : TapeSymbol Symbol) : Int →₀ TapeSymbol Symbol where
  support := match value with
    | .blank => cells.support.erase position
    | .mark _ => insert position cells.support
  toFun index := if index = position then value else cells index
  mem_support_toFun index := by
    cases value <;> by_cases hindex : index = position <;>
      simp_all [Finsupp.mem_support_iff]

@[simp]
theorem set_apply_same {Symbol : Type*} (cells : Int →₀ TapeSymbol Symbol)
    (position : Int) (value : TapeSymbol Symbol) :
    set cells position value position = value := by
  simp [set]

@[simp]
theorem set_apply_of_ne {Symbol : Type*} (cells : Int →₀ TapeSymbol Symbol)
    {position index : Int} (hne : index ≠ position) (value : TapeSymbol Symbol) :
    set cells position value index = cells index := by
  simp [set, hne]

@[simp]
theorem support_set_blank {Symbol : Type*} (cells : Int →₀ TapeSymbol Symbol)
    (position : Int) :
    (set cells position .blank).support = cells.support.erase position :=
  rfl

@[simp]
theorem support_set_nonblank {Symbol : Type*}
    (cells : Int →₀ TapeSymbol Symbol) (position : Int) (symbol : Symbol) :
    (set cells position (.mark symbol)).support =
      insert position cells.support :=
  rfl

@[simp]
theorem set_current {Symbol : Type*} (cells : Int →₀ TapeSymbol Symbol)
    (position : Int) :
    set cells position (cells position) = cells := by
  ext index
  by_cases hindex : index = position
  · subst index
    simp
  · simp [hindex]

@[simp]
theorem set_set {Symbol : Type*} (cells : Int →₀ TapeSymbol Symbol)
    (position : Int) (first second : TapeSymbol Symbol) :
    set (set cells position first) position second =
      set cells position second := by
  ext index
  by_cases hindex : index = position
  · subst index
    simp
  · simp [hindex]

end CellStore

/-- A canonical finite-nonblank tape with an absolute integer head position. -/
structure Tape (Symbol : Type*) where
  cells : Int →₀ TapeSymbol Symbol
  head : Int
deriving DecidableEq

namespace Tape

variable {Symbol : Type*}

/-- A completely blank tape with its head at an explicit position. -/
def blankAt (position : Int) : Tape Symbol :=
  { cells := 0, head := position }

/-- A completely blank tape whose head is at the origin. -/
def blank : Tape Symbol := blankAt 0

/-- Symbol scanned by the head. -/
def read (tape : Tape Symbol) : TapeSymbol Symbol :=
  tape.cells tape.head

/-- Write the scanned cell without moving the head. -/
def write (tape : Tape Symbol) (value : TapeSymbol Symbol) : Tape Symbol :=
  { tape with cells := CellStore.set tape.cells tape.head value }

/-- Move the head without changing any tape cell. -/
def move (tape : Tape Symbol) (direction : Move) : Tape Symbol :=
  { tape with head := tape.head + direction.offset }

/-- Source-quintuple tape order: write the scanned cell, then move. -/
def writeMove (tape : Tape Symbol) (value : TapeSymbol Symbol)
    (direction : Move) : Tape Symbol :=
  (tape.write value).move direction

/-- The exact finite set of currently nonblank positions. -/
def nonblankPositions (tape : Tape Symbol) : Finset Int :=
  tape.cells.support

/-- Nonblank positions together with the currently scanned cell. -/
def activePositions (tape : Tape Symbol) : Finset Int :=
  insert tape.head tape.nonblankPositions

@[simp] theorem blankAt_cells (position : Int) :
    (blankAt position : Tape Symbol).cells = 0 := rfl

@[simp] theorem blankAt_head (position : Int) :
    (blankAt position : Tape Symbol).head = position := rfl

@[simp] theorem read_blankAt (position : Int) :
    (blankAt position : Tape Symbol).read = .blank := rfl

@[simp] theorem write_head (tape : Tape Symbol) (value : TapeSymbol Symbol) :
    (tape.write value).head = tape.head := rfl

@[simp] theorem read_write (tape : Tape Symbol) (value : TapeSymbol Symbol) :
    (tape.write value).read = value := by
  simp [read, write]

@[simp] theorem write_read (tape : Tape Symbol) :
    tape.write tape.read = tape := by
  cases tape
  simp [write, read]

@[simp] theorem write_write (tape : Tape Symbol)
    (first second : TapeSymbol Symbol) :
    (tape.write first).write second = tape.write second := by
  cases tape
  simp [write]

@[simp] theorem write_cells_same (tape : Tape Symbol)
    (value : TapeSymbol Symbol) :
    (tape.write value).cells tape.head = value := by
  simp [write]

@[simp] theorem write_cells_of_ne (tape : Tape Symbol)
    (value : TapeSymbol Symbol) {position : Int} (hne : position ≠ tape.head) :
    (tape.write value).cells position = tape.cells position := by
  simp [write, hne]

@[simp] theorem move_cells (tape : Tape Symbol) (direction : Move) :
    (tape.move direction).cells = tape.cells := rfl

@[simp] theorem move_head (tape : Tape Symbol) (direction : Move) :
    (tape.move direction).head = tape.head + direction.offset := rfl

@[simp] theorem move_stay (tape : Tape Symbol) :
    tape.move .stay = tape := by
  cases tape
  simp [move]

@[simp] theorem move_left_head (tape : Tape Symbol) :
    (tape.move .left).head = tape.head + (-1) := rfl

@[simp] theorem move_right_head (tape : Tape Symbol) :
    (tape.move .right).head = tape.head + 1 := rfl

@[simp] theorem writeMove_head (tape : Tape Symbol) (value : TapeSymbol Symbol)
    (direction : Move) :
    (tape.writeMove value direction).head = tape.head + direction.offset :=
  rfl

@[simp] theorem writeMove_old_cell (tape : Tape Symbol)
    (value : TapeSymbol Symbol) (direction : Move) :
    (tape.writeMove value direction).cells tape.head = value := by
  simp [writeMove]

end Tape
end Bennett.Turing
