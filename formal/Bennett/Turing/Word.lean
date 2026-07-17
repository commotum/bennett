import Bennett.Turing.Tape
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Int.Basic

/-!
# Standard finite words on a tape

The type parameter of `Tape Symbol` denotes nonblank symbols; the actual tape
alphabet is `TapeSymbol Symbol`, which adjoins exactly one blank.  Consequently
a `List Symbol` is blank-free by construction.  Empty words are deliberately
allowed here because Bennett's paper does not say whether to exclude them.

A standard word begins at absolute position `0` and its head scans position
`-1`, the blank immediately to its left.
-/

namespace Bennett.Turing
namespace Tape

variable {Symbol : Type*}

/-- Write a finite blank-free word beginning at an absolute position. -/
def cellsFrom : List Symbol → Int → Int →₀ TapeSymbol Symbol
  | [], _ => 0
  | symbol :: rest, start =>
      CellStore.set (cellsFrom rest (start + 1)) start (.mark symbol)

/-- Place a word beginning at `start`, with the head on its left delimiter. -/
def ofWordAt (word : List Symbol) (start : Int) : Tape Symbol :=
  { cells := cellsFrom word start, head := start + (-1) }

/-- Canonical standard tape: word at `0,1,…`, head on the blank at `-1`. -/
def ofWord (word : List Symbol) : Tape Symbol :=
  ofWordAt word 0

/-- Exact standard-format proposition, retaining the represented word. -/
def IsStandard (tape : Tape Symbol) (word : List Symbol) : Prop :=
  tape = ofWord word

@[simp] theorem cellsFrom_nil (start : Int) :
    cellsFrom ([] : List Symbol) start = 0 := rfl

@[simp] theorem cellsFrom_cons_start (symbol : Symbol) (rest : List Symbol)
    (start : Int) :
    cellsFrom (symbol :: rest) start start = .mark symbol := by
  simp [cellsFrom]

@[simp] theorem cellsFrom_cons_of_ne (symbol : Symbol) (rest : List Symbol)
    (start position : Int) (hne : position ≠ start) :
    cellsFrom (symbol :: rest) start position =
      cellsFrom rest (start + 1) position := by
  simp [cellsFrom, hne]

/-- Reading at natural offset `n` agrees with `List.getElem?`. -/
theorem cellsFrom_at_nat (word : List Symbol) (start : Int) (n : Nat) :
    cellsFrom word start (start + (n : Int)) =
      match word[n]? with
      | none => .blank
      | some symbol => .mark symbol := by
  induction word generalizing start n with
  | nil => simp [cellsFrom]
  | cons symbol rest ih =>
      cases n with
      | zero => simp [cellsFrom]
      | succ n =>
          rw [cellsFrom_cons_of_ne]
          · have hposition :
                start + ((n + 1 : Nat) : Int) = start + 1 + (n : Int) := by
              omega
            rw [hposition]
            simpa using ih (start + 1) n
          · omega

/-- Every position strictly before the word's start is blank. -/
theorem cellsFrom_of_lt (word : List Symbol) (start position : Int)
    (hposition : position < start) :
    cellsFrom word start position = .blank := by
  induction word generalizing start with
  | nil => rfl
  | cons symbol rest ih =>
      rw [cellsFrom_cons_of_ne]
      · exact ih (start + 1) (by omega)
      · omega

/-- The cell immediately left of a represented word is blank. -/
@[simp]
theorem cellsFrom_left_blank (word : List Symbol) (start : Int) :
    cellsFrom word start (start + (-1)) = .blank := by
  apply cellsFrom_of_lt
  omega

/-- The cell immediately after a represented word is blank. -/
@[simp]
theorem cellsFrom_right_blank (word : List Symbol) (start : Int) :
    cellsFrom word start (start + (word.length : Int)) = .blank := by
  rw [cellsFrom_at_nat]
  simp

/-- A represented word has exactly one nonblank support cell per list entry. -/
theorem support_card_cellsFrom (word : List Symbol) (start : Int) :
    (cellsFrom word start).support.card = word.length := by
  induction word generalizing start with
  | nil => rfl
  | cons symbol rest ih =>
      have hblank : cellsFrom rest (start + 1) start = .blank := by
        exact cellsFrom_of_lt rest (start + 1) start (by omega)
      have hnot : start ∉ (cellsFrom rest (start + 1)).support := by
        rw [Finsupp.notMem_support_iff]
        exact hblank
      simp [cellsFrom, hnot, ih]

@[simp] theorem ofWordAt_head (word : List Symbol) (start : Int) :
    (ofWordAt word start).head = start + (-1) := rfl

@[simp] theorem ofWord_head (word : List Symbol) :
    (ofWord word).head = -1 := rfl

@[simp] theorem read_ofWordAt (word : List Symbol) (start : Int) :
    (ofWordAt word start).read = .blank := by
  exact cellsFrom_left_blank word start

@[simp] theorem read_ofWord (word : List Symbol) :
    (ofWord word).read = .blank :=
  read_ofWordAt word 0

@[simp] theorem ofWord_nonblank_card (word : List Symbol) :
    (ofWord word).nonblankPositions.card = word.length :=
  support_card_cellsFrom word 0

/-- Empty words are represented, explicitly, by a blank tape at head `-1`. -/
@[simp] theorem ofWord_nil :
    ofWord ([] : List Symbol) = blankAt (-1) :=
  rfl

/-- Moving right from a nonempty standard word scans its first symbol. -/
@[simp] theorem read_move_right_ofWord_cons (symbol : Symbol)
    (rest : List Symbol) :
    ((ofWord (symbol :: rest)).move .right).read = .mark symbol := by
  simp [ofWord, ofWordAt, read, move]

end Tape
end Bennett.Turing
