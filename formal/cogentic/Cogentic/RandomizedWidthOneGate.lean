import Cogentic.RandomizedFiniteKnotCost
import Cogentic.RandomizedPrivateGates
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators

namespace Cogentic.RandomizedWidthOneGate

def roundedNext (previous current : ℕ) : ℕ :=
  current + (current ^ 2 - previous ^ 2) / (2 * current)

structure KnotState where
  previous : ℕ
  current : ℕ
  numerator : ℕ
  deriving DecidableEq

private def step (state : KnotState) : KnotState :=
  let next := roundedNext state.previous state.current
  ⟨state.current, next, state.numerator + state.current ^ 2 * (next - state.current)⟩

private def advance : ℕ → KnotState → KnotState
  | 0, state => state
  | n + 1, state => advance n (step state)

/-- After n advances, the state contains knots n and n+1. -/
def knotState (n : ℕ) : KnotState := advance n ⟨0, 10 ^ 15, 0⟩

private theorem advance_succ (n : ℕ) (s : KnotState) :
    advance (n + 1) s = step (advance n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [advance] using ih (step s)

private theorem knotState_succ (n : ℕ) : knotState (n + 1) = step (knotState n) :=
  advance_succ n _

/-- The integer knot sequence, before division by the final knot. -/
def knot : ℕ → ℕ
  | 0 => 0
  | n + 1 => (knotState n).current

private theorem previous_eq_knot (n : ℕ) : (knotState n).previous = knot n := by
  cases n with
  | zero => rfl
  | succ n => rw [knotState_succ]; rfl

theorem knot_succ_succ (n : ℕ) :
    knot (n + 2) = roundedNext (knot n) (knot (n + 1)) := by
  change (knotState (n + 1)).current = roundedNext (knot n) (knotState n).current
  rw [knotState_succ, ← previous_eq_knot]
  rfl

theorem knot_le_succ (n : ℕ) : knot n ≤ knot (n + 1) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => rw [knot_succ_succ]; exact Nat.le_add_right _ _

private theorem gap_antitone : Antitone (fun i => knot (i + 1) - knot i) := by
  apply antitone_nat_of_succ_le
  intro i
  change knot (i + 2) - knot (i + 1) ≤ knot (i + 1) - knot i
  rw [knot_succ_succ, roundedNext, Nat.add_sub_cancel_left]
  apply Nat.div_le_of_le_mul
  rw [Nat.pow_two_sub_pow_two]
  exact Nat.mul_le_mul_right _ (by have h := knot_le_succ i; omega)

theorem accumulated_eq_sum (n : ℕ) :
    (knotState n).numerator =
      ∑ i ∈ Finset.range (n + 1), knot i ^ 2 * (knot (i + 1) - knot i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    change (knotState (n + 1)).numerator = (knotState n).numerator +
      (knotState n).current ^ 2 * ((knotState (n + 1)).current - (knotState n).current)
    rw [knotState_succ]
    rfl

private theorem leftSquareSum_normalized (n : ℕ) (hfinal : (knot n : ℝ) ≠ 0) :
    Randomized.leftSquareSum n (fun i => (knot i : ℝ) / knot n) =
      ((∑ i ∈ Finset.range n, knot i ^ 2 * (knot (i + 1) - knot i) : ℕ) : ℝ) / (knot n : ℝ) ^ 3 := by
  rw [Randomized.leftSquareSum, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (knot_le_succ i)]
  field_simp [hfinal]

def fixedState : KnotState := knotState 4095

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
/-- The rounded recurrence and its left-sum numerator, checked in the kernel. -/
theorem fixedState_eq :
    fixedState = ⟨217699135391441059, 217734566210652601,
      3439691824435844481607735233005798030098536084536993⟩ := by decide

set_option maxRecDepth 65536 in
theorem fixed_knot_strict {i : ℕ} (hi : i < 4096) : knot i < knot (i + 1) := by
  have hprev : fixedState.previous = knot 4095 := previous_eq_knot 4095
  have hlast : 0 < knot (4095 + 1) - knot 4095 := by
    change 0 < fixedState.current - knot 4095
    rw [← hprev, fixedState_eq]
    decide
  exact Nat.sub_pos_iff_lt.mp (hlast.trans_le (gap_antitone (show i ≤ 4095 by omega)))

noncomputable def normalizedKnot (i : ℕ) : ℝ :=
  (knot i : ℝ) / fixedState.current

theorem normalizedKnot_strict {i : ℕ} (hi : i < 4096) :
    normalizedKnot i < normalizedKnot (i + 1) := by
  have hpos : 0 < (fixedState.current : ℝ) := by rw [fixedState_eq]; norm_num
  unfold normalizedKnot
  exact (div_lt_div_iff_of_pos_right hpos).2 (by exact_mod_cast fixed_knot_strict hi)

theorem normalizedKnot_last : normalizedKnot 4096 = 1 := by
  change (fixedState.current : ℝ) / fixedState.current = 1
  rw [fixedState_eq]
  norm_num

theorem fixed_leftSquareSum :
    Randomized.leftSquareSum 4096 normalizedKnot =
      (fixedState.numerator : ℝ) / (fixedState.current : ℝ) ^ 3 := by
  have hfinal : (fixedState.current : ℝ) ≠ 0 := by rw [fixedState_eq]; norm_num
  change Randomized.leftSquareSum 4096 (fun i => (knot i : ℝ) / knot 4096) =
    ((knotState 4095).numerator : ℝ) / (knot 4096 : ℝ) ^ 3
  rw [accumulated_eq_sum]
  exact leftSquareSum_normalized 4096 hfinal

noncomputable def rowCost : ℝ := (14197202620 / 10 ^ 10) * (6654900015 / 10 ^ 10)
noncomputable def moment : ℝ := (13732142239 / 10 ^ 10) * (14197202620 / 10 ^ 10) / 3
noncomputable def curve : ℝ := 584768315988 / 10 ^ 12
noncomputable def slack : ℝ := 1 / 10 ^ 7

theorem fixed_terminal_weight_pos :
    0 < moment - curve * Randomized.leftSquareSum 4096 normalizedKnot := by
  rw [fixed_leftSquareSum, fixedState_eq]
  norm_num [moment, curve]

/-- The strict private gate bound for the fixed width-1.01 witness. -/
theorem fixed_private_gate_lt :
    rowCost + moment + curve *
      (1 - (fixedState.numerator : ℝ) / (fixedState.current : ℝ) ^ 3) + slack <
      (1984578735 : ℝ) / 10 ^ 9 := by
  rw [fixedState_eq]
  norm_num [rowCost, moment, curve, slack]

/-- The same strict bound expressed using the actual normalized stage weights. -/
theorem fixed_stage_gate_lt {i : ℕ} (hi : i ≤ 4096) :
    rowCost + (curve * normalizedKnot i +
      (∑ j ∈ Finset.Ico i 4096, curve * (normalizedKnot (j + 1) - normalizedKnot j)) +
      (moment - curve * Randomized.leftSquareSum 4096 normalizedKnot)) + slack <
      (1984578735 : ℝ) / 10 ^ 9 := by
  rw [RandomizedPrivateGates.gate_equalization _ _ _ hi, normalizedKnot_last, fixed_leftSquareSum]
  convert fixed_private_gate_lt using 1
  ring

#print axioms knot_succ_succ
#print axioms accumulated_eq_sum
#print axioms fixedState_eq
#print axioms normalizedKnot_strict
#print axioms fixed_leftSquareSum
#print axioms fixed_terminal_weight_pos
#print axioms fixed_private_gate_lt
#print axioms fixed_stage_gate_lt

end Cogentic.RandomizedWidthOneGate
