import Cogentic.RandomizedPadeEuclid
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Cogentic.Randomized.PadeEuclid

open Finset Polynomial
open scoped BigOperators

/-- The degree gaps telescope, and each strict drop accounts for one division. -/
theorem sum_degree_gap_succ (d : ℕ → ℕ) (k : ℕ) (h : ∀ i < k, d (i+1) < d i) :
    d k + k ≤ d 0 ∧ (∑ i ∈ range k, (d i - d (i+1) + 1)) = d 0 - d k + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih fun i hi ↦ h i (Nat.lt_succ_of_lt hi)
    have hnext := h k (Nat.lt_succ_self k)
    rw [sum_range_succ, hprev.2]
    omega

/-- For a path starting at degree at most `2*n`, there are at most `4*n`
quotient coefficient slots, with each step charged by its quotient size. -/
theorem sum_degree_gap_succ_le (d : ℕ → ℕ) (n k : ℕ) (hstart : d 0 ≤ 2*n)
    (h : ∀ i < k, d (i+1) < d i) :
    (∑ i ∈ range k, (d i - d (i+1) + 1)) ≤ 4*n := by
  obtain ⟨hdepth, hsum⟩ := sum_degree_gap_succ d k h
  rw [hsum]
  omega

/-- A per-step cost bounded by a common coefficient width times the
quotient size gives a quadratic total along the Euclidean path. -/
theorem field_operations_le (d operations : ℕ → ℕ) (n k c : ℕ) (hstart : d 0 ≤ 2*n)
    (h : ∀ i < k, d (i+1) < d i)
    (hcost : ∀ i < k, operations i ≤ c*(2*n+1)*(d i - d (i+1) + 1)) :
    (∑ i ∈ range k, operations i) ≤ c*(2*n+1)*(4*n) := by
  calc
    _ ≤ ∑ i ∈ range k, c*(2*n+1)*(d i - d (i+1) + 1) :=
      sum_le_sum fun i hi ↦ hcost i (mem_range.mp hi)
    _ = c*(2*n+1)*(∑ i ∈ range k, (d i - d (i+1) + 1)) := by rw [mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left _ (sum_degree_gap_succ_le d n k hstart h)

/-- An explicit quadratic upper bound on the same arithmetic cost. -/
theorem field_operations_le_quadratic (d operations : ℕ → ℕ) (n k c : ℕ) (hstart : d 0 ≤ 2*n)
    (h : ∀ i < k, d (i+1) < d i)
    (hcost : ∀ i < k, operations i ≤ c*(2*n+1)*(d i - d (i+1) + 1)) :
    (∑ i ∈ range k, operations i) ≤ 12*c*n^2 := by
  apply (field_operations_le d operations n k c hstart h hcost).trans
  by_cases hn : n = 0
  · simp [hn]
  · calc
      _ ≤ c*(3*n)*(4*n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 2*n+1 ≤ 3*n by omega))
      _ = _ := by ring

variable {K : Type*} [Field K] {A : Polynomial K} {N : ℕ}

/-- The quotient of a nonterminal step has degree exactly the degree drop. -/
theorem State.quotient_natDegree_eq_gap (s : State A N) (hr : s.remainder ≠ 0) :
    (s.previous / s.remainder).natDegree = s.previous.natDegree - s.remainder.natDegree := by
  have hq : s.previous / s.remainder ≠ 0 := fun hz ↦
    (not_lt_of_ge s.remainder_lt.le) ((Polynomial.div_eq_zero_iff hr).1 hz)
  have h := degree_add_div hr s.remainder_lt.le
  rw [degree_eq_natDegree hr, degree_eq_natDegree hq,
    degree_eq_natDegree (ne_zero_of_degree_gt s.remainder_lt), ← Nat.cast_add] at h
  have hsum : s.remainder.natDegree + (s.previous / s.remainder).natDegree =
      s.previous.natDegree := WithBot.coe_inj.mp h
  omega

/-- Along the same recursion as `finish`, count the divisions and the total
quotient coefficient slots. The total equals the degree drop plus the count. -/
noncomputable def State.finishAccounting (s : State A N) (n : ℕ)
    (hprev : n ≤ s.previous.natDegree) :
    {w : ℕ × ℕ // let d := (s.finish n hprev).val.previous.natDegree
      d + w.1 ≤ s.previous.natDegree ∧ w.2 = s.previous.natDegree - d + w.1} := by
  if h : s.remainder.degree < (n : WithBot ℕ) then
    refine ⟨(0, 0), ?_⟩
    rw [State.finish.eq_1, dif_pos h]
    simp
  else
    have hdeg : (n : WithBot ℕ) ≤ s.remainder.degree := le_of_not_gt h
    have hnz := ne_zero_of_coe_le_degree hdeg
    have hnat : n ≤ s.remainder.natDegree := by
      rwa [degree_eq_natDegree hnz, Nat.cast_le] at hdeg
    let next := s.step hnz
    let w := next.finishAccounting n hnat
    let q := (s.previous / s.remainder).natDegree
    refine ⟨(w.val.1 + 1, w.val.2 + q + 1), ?_⟩
    rw [State.finish.eq_1, dif_neg h]
    let d := (next.finish n hnat).val.previous.natDegree
    change d + (w.val.1 + 1) ≤ s.previous.natDegree ∧
      w.val.2 + q + 1 = s.previous.natDegree - d + (w.val.1 + 1)
    have hw : d + w.val.1 ≤ next.previous.natDegree ∧
        w.val.2 = next.previous.natDegree - d + w.val.1 := w.property
    have hdrop : next.previous.natDegree < s.previous.natDegree :=
      natDegree_lt_natDegree hnz s.remainder_lt
    have hq : q = s.previous.natDegree - next.previous.natDegree :=
      s.quotient_natDegree_eq_gap hnz
    omega
termination_by s.previous.natDegree
decreasing_by all_goals exact natDegree_lt_natDegree hnz s.remainder_lt

/-- The cutoff `n` saves one half of the unrestricted degree budget. -/
theorem solve_accounting_le (A : Polynomial K) (n : ℕ) (hA : A.degree < (↑(2*n) : WithBot ℕ)) :
    let s := start A (2*n) hA
    let hprev : n ≤ s.previous.natDegree := by simp [s, start]; omega
    let w := (s.finishAccounting n hprev).val
    w.1 ≤ n ∧ w.2 ≤ 2*n := by
  dsimp only
  let s := start A (2*n) hA
  have hprev : n ≤ s.previous.natDegree := by simp [s, start]; omega
  let w := s.finishAccounting n hprev
  let d := (s.finish n hprev).val.previous.natDegree
  change w.val.1 ≤ n ∧ w.val.2 ≤ 2*n
  have hd : n ≤ d := (s.finish n hprev).property.1
  have hw : d + w.val.1 ≤ s.previous.natDegree ∧
      w.val.2 = s.previous.natDegree - d + w.val.1 := w.property
  have hstart : s.previous.natDegree = 2*n := by simp [s, start]
  omega

end Cogentic.Randomized.PadeEuclid
