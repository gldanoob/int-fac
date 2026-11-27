import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized.PadeEuclid

open Polynomial

variable {K : Type*} [Field K]

/-- Adjacent Euclidean remainder and Bézout coefficient columns for `(X^N, A)`. -/
structure State (A : Polynomial K) (N : ℕ) where
  previous : Polynomial K
  remainder : Polynomial K
  previousCoefficient : Polynomial K
  coefficient : Polynomial K
  remainder_lt : remainder.degree < previous.degree
  coefficient_ne_zero : coefficient ≠ 0
  coefficient_order : previousCoefficient.natDegree ≤ coefficient.natDegree
  coefficient_degree_sum : coefficient.natDegree + previous.natDegree = N
  previous_dvd : X^N ∣ previousCoefficient * A - previous
  remainder_dvd : X^N ∣ coefficient * A - remainder

noncomputable def start (A : Polynomial K) (N : ℕ) (hA : A.degree < (N : WithBot ℕ)) :
    State A N where
  previous := X^N
  remainder := A
  previousCoefficient := 0
  coefficient := 1
  remainder_lt := by simpa using hA
  coefficient_ne_zero := one_ne_zero
  coefficient_order := by simp
  coefficient_degree_sum := by simp
  previous_dvd := by simp
  remainder_dvd := by simp

/-- Advance the Euclidean algorithm by one division, preserving the two
congruences and the exact sum of coefficient and preceding remainder degrees. -/
noncomputable def State.step {A : Polynomial K} {N : ℕ} (s : State A N)
    (hr : s.remainder ≠ 0) : State A N := by
  let q := s.previous / s.remainder
  have hq : q ≠ 0 := fun hz ↦
    (not_lt_of_ge s.remainder_lt.le) ((Polynomial.div_eq_zero_iff hr).1 hz)
  have hqsum : s.remainder.natDegree + q.natDegree = s.previous.natDegree := by
    have h := degree_add_div hr s.remainder_lt.le
    change s.remainder.degree + q.degree = s.previous.degree at h
    rw [degree_eq_natDegree hr, degree_eq_natDegree hq,
      degree_eq_natDegree (ne_zero_of_degree_gt s.remainder_lt), ← Nat.cast_add] at h
    exact WithBot.coe_inj.mp h
  have hrlt := natDegree_lt_natDegree hr s.remainder_lt
  have hqpos : 0 < q.natDegree := by omega
  have hmul : (q * s.coefficient).natDegree = q.natDegree + s.coefficient.natDegree :=
    natDegree_mul hq s.coefficient_ne_zero
  have hlt : s.previousCoefficient.natDegree < (q * s.coefficient).natDegree := by
    have h := s.coefficient_order
    omega
  have hnext := natDegree_sub_eq_right_of_natDegree_lt hlt
  have hmod : s.previous % s.remainder = s.previous - q * s.remainder := by
    apply eq_sub_of_add_eq
    simpa only [q, add_comm, mul_comm] using EuclideanDomain.div_add_mod s.previous s.remainder
  refine {
    previous := s.remainder
    remainder := s.previous % s.remainder
    previousCoefficient := s.coefficient
    coefficient := s.previousCoefficient - q * s.coefficient
    remainder_lt := degree_mod_lt _ hr
    coefficient_ne_zero := sub_ne_zero.mpr (fun he ↦ (ne_of_lt hlt) (congrArg natDegree he))
    coefficient_order := by rw [hnext, hmul]; omega
    coefficient_degree_sum := by
      rw [hnext, hmul]
      have h := s.coefficient_degree_sum
      omega
    previous_dvd := s.remainder_dvd
    remainder_dvd := ?_ }
  calc
    X^N ∣ (s.previousCoefficient * A - s.previous) - q * (s.coefficient * A - s.remainder) :=
      dvd_sub s.previous_dvd (dvd_mul_of_dvd_right s.remainder_dvd q)
    _ = (s.previousCoefficient - q * s.coefficient) * A - s.previous % s.remainder := by
      rw [hmod]
      ring

/-- Follow the Euclidean steps until the first remainder with degree below the
cutoff. The preceding remainder still has degree at least the cutoff. -/
noncomputable def State.finish {A : Polynomial K} {N : ℕ} (s : State A N)
    (n : ℕ) (hprev : n ≤ s.previous.natDegree) :
    {t : State A N // n ≤ t.previous.natDegree ∧ t.remainder.degree < (n : WithBot ℕ)} :=
  if h : s.remainder.degree < (n : WithBot ℕ) then
    ⟨s, hprev, h⟩
  else
    have hdeg : (n : WithBot ℕ) ≤ s.remainder.degree := le_of_not_gt h
    have hnz := ne_zero_of_coe_le_degree hdeg
    have hnat : n ≤ s.remainder.natDegree := by
      rwa [degree_eq_natDegree hnz, Nat.cast_le] at hdeg
    (s.step hnz).finish n hnat
termination_by s.previous.natDegree
decreasing_by exact natDegree_lt_natDegree hnz s.remainder_lt

/-- Euclidean Padé solver at precision `2*n` with cutoff `n`. -/
noncomputable def solve (A : Polynomial K) (n : ℕ) (hA : A.degree < (↑(2*n) : WithBot ℕ)) :
    {t : State A (2*n) // n ≤ t.previous.natDegree ∧ t.remainder.degree < (n : WithBot ℕ)} :=
  (start A (2*n) hA).finish n (by simp [start]; omega)

/-- The first remainder below `n` gives a Padé pair with nonzero coefficient
of degree at most `n` and the required precision-`2*n` congruence. -/
theorem solve_spec (A : Polynomial K) (n : ℕ) (hA : A.degree < (↑(2*n) : WithBot ℕ)) :
    let t := (solve A n hA).val
    t.coefficient ≠ 0 ∧ t.coefficient.natDegree ≤ n ∧
      t.remainder.degree < (n : WithBot ℕ) ∧ X^(2*n) ∣ t.coefficient*A - t.remainder := by
  dsimp only
  let t := solve A n hA
  refine ⟨t.val.coefficient_ne_zero, ?_, t.property.2, t.val.remainder_dvd⟩
  change t.val.coefficient.natDegree ≤ n
  have hsum := t.val.coefficient_degree_sum
  have hprev := t.property.1
  omega

/-- A bounded Padé pair exists for any input truncated below precision `2*n`. -/
theorem exists_pade_pair (A : Polynomial K) (n : ℕ) (hA : A.degree < (↑(2*n) : WithBot ℕ)) :
    ∃ b r : Polynomial K, b ≠ 0 ∧ b.natDegree ≤ n ∧
      r.degree < (n : WithBot ℕ) ∧ X^(2*n) ∣ b*A - r :=
  ⟨(solve A n hA).val.coefficient, (solve A n hA).val.remainder, solve_spec A n hA⟩

end Cogentic.Randomized.PadeEuclid
