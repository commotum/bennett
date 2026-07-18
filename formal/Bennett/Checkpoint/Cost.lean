import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Checkpoint segmentation and resource costs

This module separates three claims that Bennett's informal checkpoint argument
blends together:

* a constructive integer segmentation with longest block
  `steps ⌈/⌉ segments`;
* an exact discrete temporary-space and explicit dump-I/O time model; and
* the paper's noncomputable real-valued relaxation `v / n + n * s`.

The discrete temporary budget counts reusable primary history and intermediate
restart dumps.  It excludes permanent input/output and ordinary live machine
storage.  A dump-cell cost is caller supplied because a complete restart dump
must include every control, tape, head, and phase component needed to resume.
-/

namespace Bennett.Checkpoint.Cost

/-- The longest primary history when `steps` are split across `segments`. -/
def historyCells (steps segments : Nat) : Nat := steps ⌈/⌉ segments

/-- The number of nonpermanent restart dumps between the endpoints. -/
def intermediateDumpCount (segments : Nat) : Nat := segments - 1

/-- Exact temporary-cell budget of the discrete checkpoint cost model. -/
def temporaryCells (steps dumpCells segments : Nat) : Nat :=
  historyCells steps segments + intermediateDumpCount segments * dumpCells

/-- Integer-rounded storage using the paper's `segments`-dump convention. -/
def paperRoundedCells (steps dumpCells segments : Nat) : Nat :=
  historyCells steps segments + segments * dumpCells

/-- A positive segment count has enough ceiling-sized capacity for all steps. -/
theorem steps_le_segments_mul_historyCells
    {steps segments : Nat} (hsegments : 0 < segments) :
    steps ≤ segments * historyCells steps segments := by
  simpa [historyCells, nsmul_eq_mul] using
    (le_smul_ceilDiv (a := segments) (b := steps) hsegments)

/-!
## Realizable integer segment plans

The scalar covering inequality is not by itself a segmentation.  The bounded
partition proof below constructs the missing finite witness.  A plan may
contain zero-length segments when there are more segments than source steps;
the segment count is nevertheless required to be positive.  Under the natural
`segments ≤ steps` precondition, a stronger theorem makes every segment
nonempty.
-/

/-- A finite division of `steps` into exactly `segments` bounded lengths. -/
structure SegmentPlan (steps segments : Nat) where
  lengths : List Nat
  length_eq : lengths.length = segments
  sum_eq : lengths.sum = steps
  le_historyCells :
    ∀ length ∈ lengths, length ≤ historyCells steps segments

private theorem exists_bounded_partition
    (total slots capacity : Nat)
    (hcover : total ≤ slots * capacity) :
    ∃ parts : List Nat,
      parts.length = slots ∧
      parts.sum = total ∧
      ∀ part ∈ parts, part ≤ capacity := by
  induction slots generalizing total with
  | zero =>
      simp only [Nat.zero_mul] at hcover
      have htotal : total = 0 := Nat.eq_zero_of_le_zero hcover
      subst total
      exact ⟨[], rfl, rfl, by simp⟩
  | succ slots ih =>
      let first := min total capacity
      have hfirstTotal : first ≤ total := min_le_left _ _
      have hfirstCapacity : first ≤ capacity := min_le_right _ _
      have hrestCover : total - first ≤ slots * capacity := by
        by_cases hsmall : total ≤ capacity
        · rw [show first = total from min_eq_left hsmall]
          simp
        · have hcapacity : capacity ≤ total := Nat.le_of_not_ge hsmall
          rw [show first = capacity from min_eq_right hcapacity]
          calc
            total - capacity ≤ (slots + 1) * capacity - capacity :=
              Nat.sub_le_sub_right hcover capacity
            _ = slots * capacity := by
              rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel]
      obtain ⟨parts, hlength, hsum, hparts⟩ :=
        ih (total - first) hrestCover
      refine ⟨first :: parts, ?_, ?_, ?_⟩
      · simp [hlength]
      · simp only [List.sum_cons, hsum]
        exact Nat.add_sub_of_le hfirstTotal
      · intro part hpart
        rcases List.mem_cons.mp hpart with rfl | hpart
        · exact hfirstCapacity
        · exact hparts part hpart

/-- Every positive segment count has an exact plan with ceiling-sized blocks. -/
theorem exists_segmentPlan
    {steps segments : Nat} (hsegments : 0 < segments) :
    Nonempty (SegmentPlan steps segments) := by
  obtain ⟨lengths, hlength, hsum, hbound⟩ :=
    exists_bounded_partition steps segments (historyCells steps segments)
      (steps_le_segments_mul_historyCells hsegments)
  exact ⟨⟨lengths, hlength, hsum, hbound⟩⟩

/-- If there are no more segments than steps, every segment can be nonempty. -/
theorem exists_positive_segmentPlan
    {steps segments : Nat} (hsegments : 0 < segments)
    (hsegmentsSteps : segments ≤ steps) :
    ∃ plan : SegmentPlan steps segments,
      ∀ length ∈ plan.lengths, 0 < length := by
  let capacity := historyCells steps segments
  have hcover : steps ≤ segments * capacity :=
    steps_le_segments_mul_historyCells hsegments
  have hcapacity : 0 < capacity := by
    by_contra hnot
    have hzero : capacity = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero, Nat.mul_zero] at hcover
    omega
  have hextraCover : steps - segments ≤ segments * (capacity - 1) := by
    rw [Nat.sub_le_iff_le_add']
    calc
      steps ≤ segments * capacity := hcover
      _ = segments * ((capacity - 1) + 1) := by
        rw [Nat.sub_add_cancel hcapacity]
      _ = segments * (capacity - 1) + segments := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = segments + segments * (capacity - 1) := Nat.add_comm _ _
  obtain ⟨extras, hextrasLength, hextrasSum, hextrasBound⟩ :=
    exists_bounded_partition (steps - segments) segments (capacity - 1)
      hextraCover
  let lengths := extras.map fun extra => extra + 1
  have hlengthsLength : lengths.length = segments := by
    simp [lengths, hextrasLength]
  have hlengthsSum : lengths.sum = steps := by
    simp [lengths, List.sum_map_add, hextrasSum, hextrasLength,
      Nat.sub_add_cancel hsegmentsSteps]
  have hlengthsBound :
      ∀ length ∈ lengths, length ≤ historyCells steps segments := by
    intro length hlength
    obtain ⟨extra, hextra, rfl⟩ := List.mem_map.mp hlength
    have := hextrasBound extra hextra
    change extra + 1 ≤ capacity
    omega
  refine ⟨⟨lengths, hlengthsLength, hlengthsSum, hlengthsBound⟩, ?_⟩
  intro length hlength
  obtain ⟨extra, _, rfl⟩ := List.mem_map.mp hlength
  omega

/-- A plan for a positive segment count has at least one listed segment. -/
theorem SegmentPlan.lengths_ne_nil
    {steps segments : Nat} (plan : SegmentPlan steps segments)
    (hsegments : 0 < segments) : plan.lengths ≠ [] := by
  intro hempty
  have : plan.lengths.length = 0 := by simp [hempty]
  have := plan.length_eq
  omega

/-- Unfold the exact integer temporary-space formula. -/
theorem temporaryCells_eq
    (steps dumpCells segments : Nat) :
    temporaryCells steps dumpCells segments =
      steps ⌈/⌉ segments + (segments - 1) * dumpCells := rfl

/-- For a positive count, the paper convention charges one extra full dump. -/
theorem paperRoundedCells_eq_temporaryCells_add_dumpCells
    (steps dumpCells : Nat) {segments : Nat} (hsegments : 0 < segments) :
    paperRoundedCells steps dumpCells segments =
      temporaryCells steps dumpCells segments + dumpCells := by
  unfold paperRoundedCells temporaryCells intermediateDumpCount
  rw [Nat.add_assoc]
  congr 1
  calc
    segments * dumpCells = ((segments - 1) + 1) * dumpCells := by
      rw [Nat.sub_add_cancel hsegments]
    _ = (segments - 1) * dumpCells + dumpCells := by
      rw [Nat.add_mul, Nat.one_mul]

/-!
## Explicit time model

The unsegmented history method makes one forward and one reverse source-level
pass.  Checkpoint cleanup makes those two passes twice, hence four ideal
source-level passes.  Restart-dump traffic is not silently discarded: the
caller supplies the total transition charge per dumped cell for its concrete
write/read/erase protocol.
-/

/-- Ideal source-level work of the unsegmented forward/retrace baseline. -/
def unsegmentedIdealTime (steps : Nat) : Nat := 2 * steps

/-- Ideal source-level work of segmented checkpoint cleanup: four passes. -/
def segmentedIdealTime (steps : Nat) : Nat := 4 * steps

/-- Additive I/O charge for all intermediate restart-dump cells. -/
def dumpIOTime
    (dumpCells segments transitionsPerDumpCell : Nat) : Nat :=
  intermediateDumpCount segments * dumpCells * transitionsPerDumpCell

/-- Four ideal source passes plus the declared restart-dump I/O charge. -/
def checkpointTime
    (steps dumpCells segments transitionsPerDumpCell : Nat) : Nat :=
  segmentedIdealTime steps +
    dumpIOTime dumpCells segments transitionsPerDumpCell

/-- Four source passes are twice the unsegmented two-pass baseline. -/
theorem segmentedIdealTime_eq_two_unsegmented (steps : Nat) :
    segmentedIdealTime steps = 2 * unsegmentedIdealTime steps := by
  simp only [segmentedIdealTime, unsegmentedIdealTime]
  ring

/-- Exact time decomposition into ideal source work and restart-dump I/O. -/
theorem checkpointTime_eq_two_unsegmented_add_dumpIO
    (steps dumpCells segments transitionsPerDumpCell : Nat) :
    checkpointTime steps dumpCells segments transitionsPerDumpCell =
      2 * unsegmentedIdealTime steps +
        dumpIOTime dumpCells segments transitionsPerDumpCell := by
  rw [checkpointTime, segmentedIdealTime_eq_two_unsegmented]

/-- The paper's exact doubling is recovered only when dump I/O is set to zero. -/
theorem checkpointTime_ignoring_dumpIO
    (steps dumpCells segments : Nat) :
    checkpointTime steps dumpCells segments 0 =
      2 * unsegmentedIdealTime steps := by
  simp [checkpointTime_eq_two_unsegmented_add_dumpIO, dumpIOTime]

/-!
## Discrete square-root rounding

The rounded choice below supplies a useful checked bound.  It is not claimed
to be the exact minimizer of `temporaryCells`, whose `(segments - 1)` term and
ceiling make the discrete objective differ from the paper's relaxation.
-/

/-- Least integer at least the square root. -/
def ceilSqrt (n : Nat) : Nat :=
  if n ≤ Nat.sqrt n * Nat.sqrt n then Nat.sqrt n else Nat.sqrt n + 1

theorem le_ceilSqrt_sq (n : Nat) : n ≤ ceilSqrt n * ceilSqrt n := by
  unfold ceilSqrt
  split_ifs with h
  · exact h
  · have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) :=
      Nat.lt_succ_sqrt n
    omega

theorem ceilSqrt_eq_sqrt_of_sq (n : Nat)
    (h : n = Nat.sqrt n * Nat.sqrt n) : ceilSqrt n = Nat.sqrt n := by
  unfold ceilSqrt
  rw [if_pos h.le]

/-- Every smaller natural number has square strictly below the radicand. -/
theorem sq_lt_of_lt_ceilSqrt {candidate n : Nat}
    (hcandidate : candidate < ceilSqrt n) :
    candidate * candidate < n := by
  unfold ceilSqrt at hcandidate
  split at hcandidate
  next hsquare =>
    have hcandidatesqrt : candidate < Nat.sqrt n := by
      simpa only [if_pos hsquare] using hcandidate
    exact (Nat.mul_self_lt_mul_self hcandidatesqrt).trans_le
      (Nat.sqrt_le n)
  next hsquare =>
    have hcandidatesqrt : candidate ≤ Nat.sqrt n := by
      simpa only [if_neg hsquare, Nat.lt_succ_iff] using hcandidate
    have hsqrtlt : Nat.sqrt n * Nat.sqrt n < n := by
      exact (Nat.sqrt_le n).lt_of_not_ge hsquare
    exact (Nat.mul_self_le_mul_self hcandidatesqrt).trans_lt hsqrtlt

/-- `ceilSqrt n` is the least natural whose square covers `n`. -/
theorem ceilSqrt_le_iff {candidate n : Nat} :
    ceilSqrt n ≤ candidate ↔ n ≤ candidate * candidate := by
  constructor
  · intro hcandidate
    exact (le_ceilSqrt_sq n).trans
      (Nat.mul_self_le_mul_self hcandidate)
  · intro hsquare
    by_contra hcandidate
    have hlt : candidate < ceilSqrt n := Nat.lt_of_not_ge hcandidate
    exact (Nat.not_le_of_lt (sq_lt_of_lt_ceilSqrt hlt)) hsquare

/-- Positive rounded segment count balancing history and dump blocks. -/
def balancedSegments (steps dumpCells : Nat) : Nat :=
  max 1 (ceilSqrt (steps ⌈/⌉ dumpCells))

theorem balancedSegments_pos (steps dumpCells : Nat) :
    0 < balancedSegments steps dumpCells := by
  simp [balancedSegments]

theorem ceilDiv_le_balanced_sq
    (steps dumpCells : Nat) :
    steps ⌈/⌉ dumpCells ≤
      balancedSegments steps dumpCells * balancedSegments steps dumpCells := by
  have hsqrt := le_ceilSqrt_sq (steps ⌈/⌉ dumpCells)
  exact hsqrt.trans (Nat.mul_le_mul
    (Nat.le_max_right 1 (ceilSqrt (steps ⌈/⌉ dumpCells)))
    (Nat.le_max_right 1 (ceilSqrt (steps ⌈/⌉ dumpCells))))

theorem steps_le_balanced_sq_mul_dumpCells
    {steps dumpCells : Nat} (hdump : 0 < dumpCells) :
    steps ≤ balancedSegments steps dumpCells *
      balancedSegments steps dumpCells * dumpCells := by
  have hceil : steps ≤ dumpCells * (steps ⌈/⌉ dumpCells) :=
    by simpa [nsmul_eq_mul] using
      (le_smul_ceilDiv (a := dumpCells) (b := steps) hdump)
  have hsq := ceilDiv_le_balanced_sq steps dumpCells
  calc
    steps ≤ dumpCells * (steps ⌈/⌉ dumpCells) := hceil
    _ ≤ dumpCells *
        (balancedSegments steps dumpCells * balancedSegments steps dumpCells) :=
      Nat.mul_le_mul_left dumpCells hsq
    _ = balancedSegments steps dumpCells *
        balancedSegments steps dumpCells * dumpCells := by ac_rfl

/-- Minimality among positive segment counts satisfying the same square cover. -/
theorem balancedSegments_le_of_cover
    {steps dumpCells candidate : Nat}
    (hdump : 0 < dumpCells) (hcandidate : 0 < candidate)
    (hcover : steps ≤ candidate * candidate * dumpCells) :
    balancedSegments steps dumpCells ≤ candidate := by
  unfold balancedSegments
  apply max_le
  · exact hcandidate
  · rw [ceilSqrt_le_iff, ceilDiv_le_iff_le_mul hdump]
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcover

theorem historyCells_le_balanced_block
    {steps dumpCells : Nat} (hdump : 0 < dumpCells) :
    historyCells steps (balancedSegments steps dumpCells) ≤
      balancedSegments steps dumpCells * dumpCells := by
  rw [historyCells, ceilDiv_le_iff_le_mul
    (balancedSegments_pos steps dumpCells)]
  simpa [Nat.mul_assoc] using
    steps_le_balanced_sq_mul_dumpCells (steps := steps) hdump

theorem temporaryCells_balanced_le
    {steps dumpCells : Nat} (hdump : 0 < dumpCells) :
    temporaryCells steps dumpCells (balancedSegments steps dumpCells) ≤
      (2 * balancedSegments steps dumpCells - 1) * dumpCells := by
  rw [temporaryCells, intermediateDumpCount]
  have hhistory := historyCells_le_balanced_block (steps := steps) hdump
  calc
    historyCells steps (balancedSegments steps dumpCells) +
        (balancedSegments steps dumpCells - 1) * dumpCells ≤
      balancedSegments steps dumpCells * dumpCells +
        (balancedSegments steps dumpCells - 1) * dumpCells :=
      Nat.add_le_add_right hhistory _
    _ = (2 * balancedSegments steps dumpCells - 1) * dumpCells := by
      have hpositive := balancedSegments_pos steps dumpCells
      rw [← Nat.add_mul]
      congr 1
      omega

theorem temporaryCells_balanced_le_two_blocks
    {steps dumpCells : Nat} (hdump : 0 < dumpCells) :
    temporaryCells steps dumpCells (balancedSegments steps dumpCells) ≤
      2 * balancedSegments steps dumpCells * dumpCells := by
  refine (temporaryCells_balanced_le (steps := steps) hdump).trans ?_
  apply Nat.mul_le_mul_right
  omega

/-!
## Paper's continuous relaxation

This separate noncomputable real-valued model uses the paper's `n` full-dump
convention.  It does not replace the exact discrete `(n - 1)` formula and does
not construct an integer segmentation.  It verifies only the AM--GM claim
behind `2 * sqrt(v * s)`.
-/

/-- The paper's relaxed expression `v / n + n * s` over positive real `n`. -/
noncomputable def paperContinuousCells
    (steps dumpCells segments : Real) : Real :=
  steps / segments + segments * dumpCells

theorem paperContinuousCells_lower_bound
    {steps dumpCells segments : Real}
    (hsteps : 0 ≤ steps) (hdump : 0 ≤ dumpCells)
    (hsegments : 0 < segments) :
    2 * Real.sqrt (steps * dumpCells) ≤
      paperContinuousCells steps dumpCells segments := by
  let history := steps / segments
  let dumps := segments * dumpCells
  have hhistory : 0 ≤ history := div_nonneg hsteps hsegments.le
  have hdumps : 0 ≤ dumps := mul_nonneg hsegments.le hdump
  have hproduct : history * dumps = steps * dumpCells := by
    dsimp [history, dumps]
    field_simp
  have hsquare := sq_nonneg (Real.sqrt history - Real.sqrt dumps)
  have hsqrtHistory : (Real.sqrt history) ^ 2 = history :=
    Real.sq_sqrt hhistory
  have hsqrtDumps : (Real.sqrt dumps) ^ 2 = dumps :=
    Real.sq_sqrt hdumps
  have hsqrtProduct :
      Real.sqrt (steps * dumpCells) =
        Real.sqrt history * Real.sqrt dumps := by
    rw [← hproduct, Real.sqrt_mul hhistory]
  dsimp [paperContinuousCells, history, dumps] at *
  nlinarith

/-- Equality in the paper's relaxation occurs at the real square-root ratio. -/
theorem paperContinuousCells_at_sqrt_ratio
    {steps dumpCells : Real}
    (hsteps : 0 < steps) (hdump : 0 < dumpCells) :
    paperContinuousCells steps dumpCells
        (Real.sqrt (steps / dumpCells)) =
      2 * Real.sqrt (steps * dumpCells) := by
  let segments := Real.sqrt (steps / dumpCells)
  have hratio : 0 < steps / dumpCells := div_pos hsteps hdump
  have hsegments : 0 < segments := Real.sqrt_pos.2 hratio
  have hsquare : segments * segments = steps / dumpCells := by
    simpa [segments, pow_two] using Real.sq_sqrt hratio.le
  have hbalance : steps / segments = segments * dumpCells := by
    apply (div_eq_iff hsegments.ne').2
    calc
      steps = (steps / dumpCells) * dumpCells := by
        field_simp
      _ = (segments * segments) * dumpCells := by rw [hsquare]
      _ = (segments * dumpCells) * segments := by ring
  have hsqrt :
      Real.sqrt (steps * dumpCells) = segments * dumpCells := by
    rw [Real.sqrt_eq_iff_mul_self_eq
      (mul_nonneg hsteps.le hdump.le)
      (mul_nonneg hsegments.le hdump.le)]
    calc
      steps * dumpCells = ((steps / dumpCells) * dumpCells) * dumpCells := by
        field_simp
      _ = (segments * segments) * dumpCells * dumpCells := by rw [hsquare]
      _ = (segments * dumpCells) * (segments * dumpCells) := by ring
  change steps / segments + segments * dumpCells = _
  rw [hbalance, hsqrt]
  ring

end Bennett.Checkpoint.Cost
