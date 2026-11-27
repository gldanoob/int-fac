import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Reverse

/-! Coefficient correspondence between truncated Padé products and finite recurrences. -/

namespace Cogentic.RandomizedPadeRecurrence

open Polynomial

variable {K : Type*} [Field K]

/-- The polynomial containing the first m scalar moments. -/
noncomputable def truncatedMoments (m : ℕ) (a : ℕ → K) : K[X] :=
  ∑ j ∈ Finset.range m, monomial j (a j)

/-- A candidate fits every shift for which its length-l coefficient window is available. -/
def FitsTruncatedRecurrence (m l : ℕ) (a : ℕ → K) (p : K[X]) : Prop :=
  ∀ k < m - l, ∑ i ∈ Finset.range (l + 1), p.coeff i * a (k + i) = 0

theorem coeff_truncatedMoments (m j : ℕ) (a : ℕ → K) :
    (truncatedMoments m a).coeff j = if j < m then a j else 0 := by
  simp [truncatedMoments, finsetSum_coeff, coeff_monomial]

/-- A product coefficient at index l+k is the shifted recurrence sum when the
    connection polynomial is reflected through length l. -/
theorem coeff_product_eq_shift (m l k : ℕ) (a : ℕ → K) (B : K[X])
    (hB : B.natDegree ≤ l) (hk : l + k < m) :
    (B * truncatedMoments m a).coeff (l + k) =
      ∑ i ∈ Finset.range (l + 1), (B.reflect l).coeff i * a (k + i) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    _ = ∑ j ∈ Finset.range (l + 1),
        B.coeff j * (truncatedMoments m a).coeff (l + k - j) := by
      symm
      apply Finset.sum_subset
      · intro j h
        simp only [Finset.mem_range] at h ⊢
        omega
      · intro j _ hj
        have hlt : B.natDegree < j := by
          simp only [Finset.mem_range] at hj
          omega
        rw [coeff_eq_zero_of_natDegree_lt hlt, zero_mul]
    _ = ∑ i ∈ Finset.range (l + 1),
        B.coeff (l - i) * (truncatedMoments m a).coeff (l + k - (l - i)) := by
      simpa using (Finset.sum_range_reflect
        (fun i => B.coeff i * (truncatedMoments m a).coeff (l + k - i)) (l + 1)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hil : i ≤ l := by simpa using hi
      have heq : l + k - (l - i) = k + i := by omega
      have him : k + i < m := by omega
      rw [coeff_reflect, revAt_le hil, heq, coeff_truncatedMoments, if_pos him]

/-- Modulo a power of X, coefficients below that power are unchanged. -/
theorem coeff_modByMonic_X_pow_of_lt (A : K[X]) (m j : ℕ) (hj : j < m) :
    (A %ₘ (X ^ m)).coeff j = A.coeff j := by
  have h := congrArg (fun f : K[X] => f.coeff j) (modByMonic_add_div A (X ^ m))
  simpa only [coeff_add, coeff_X_pow_mul', if_neg (not_le_of_gt hj), add_zero] using h

/-- The remainder modulo X^m has degree below l exactly when the reflected
    connection polynomial fits all available length-l windows. -/
theorem remainder_degree_lt_iff_fits (m l : ℕ) (a : ℕ → K) (B : K[X])
    (hB : B.natDegree ≤ l) :
    ((B * truncatedMoments m a) %ₘ (X ^ m)).degree < l ↔
      FitsTruncatedRecurrence m l a (B.reflect l) := by
  rw [degree_lt_iff_coeff_zero]
  constructor
  · intro h k hk
    rw [← coeff_product_eq_shift m l k a B hB (by omega),
      ← coeff_modByMonic_X_pow_of_lt _ m (l + k) (by omega)]
    exact h (l + k) (by omega)
  · intro h j hj
    by_cases hm : j < m
    · have heq : l + (j - l) = j := by omega
      have hk : j - l < m - l := by omega
      rw [coeff_modByMonic_X_pow_of_lt _ m j hm, ← heq,
        coeff_product_eq_shift m l (j - l) a B hB (by omega)]
      exact h (j - l) hk
    · have hdeg := degree_modByMonic_lt (B * truncatedMoments m a) (monic_X_pow m)
      rw [degree_X_pow] at hdeg
      exact (degree_lt_iff_coeff_zero _ m).mp hdeg j (le_of_not_gt hm)

/-- Reflecting through length l turns constant coefficient one into leading
    coefficient one at degree exactly l. -/
theorem monic_natDegree_reflect (B : K[X]) (l : ℕ)
    (hB : B.natDegree ≤ l) (hB0 : B.coeff 0 = 1) :
    (B.reflect l).Monic ∧ (B.reflect l).natDegree = l := by
  have hc : (B.reflect l).coeff l = 1 := by simp [hB0]
  have hd : (B.reflect l).natDegree = l :=
    (natDegree_reflect_le.trans (max_le le_rfl hB)).antisymm
      (le_natDegree_of_ne_zero (by simpa only [hc] using (one_ne_zero : (1 : K) ≠ 0)))
  exact ⟨by rw [Monic, ← coeff_natDegree, hd, hc], hd⟩

/-- The reflected coefficients are the usual reciprocal at every nonzero value. -/
theorem eval_reflect_eq_reciprocal (B : K[X]) (l : ℕ) (hB : B.natDegree ≤ l)
    (t : K) (ht : t ≠ 0) :
    (B.reflect l).eval t = t ^ l * B.eval t⁻¹ := by
  let _ : Invertible t := invertibleOfNonzero ht
  have hd : (B.reflect l).natDegree ≤ l := natDegree_reflect_le.trans (max_le le_rfl hB)
  simpa [invOf_eq_inv, mul_comm] using
    (eval₂_reflect_mul_pow (RingHom.id K) t l (B.reflect l) hd).symm

/-- The Padé product condition gives a monic recurrence from the first 2n moments. -/
theorem recurrence_of_pade (n l : ℕ) (a : ℕ → K) (B R : K[X])
    (hB : B.natDegree ≤ l) (hB0 : B.coeff 0 = 1)
    (hR : R = (B * truncatedMoments (2 * n) a) %ₘ (X ^ (2 * n)))
    (hRdeg : R.degree < l) :
    (B.reflect l).Monic ∧ (B.reflect l).natDegree = l ∧
      FitsTruncatedRecurrence (2 * n) l a (B.reflect l) := by
  obtain ⟨hm, hd⟩ := monic_natDegree_reflect B l hB hB0
  exact ⟨hm, hd, (remainder_degree_lt_iff_fits (2 * n) l a B hB).mp (hR ▸ hRdeg)⟩

/-- The divisibility output of a Padé solver is enough to recover the recurrence. -/
theorem recurrence_of_pade_congruence (n l : ℕ) (a : ℕ → K) (B R : K[X])
    (hl : l ≤ n) (hB : B.natDegree ≤ l) (hB0 : B.coeff 0 = 1)
    (hcong : X ^ (2 * n) ∣ B * truncatedMoments (2 * n) a - R)
    (hRdeg : R.degree < l) :
    (B.reflect l).Monic ∧ (B.reflect l).natDegree = l ∧
      FitsTruncatedRecurrence (2 * n) l a (B.reflect l) := by
  have hdegree : R.degree < (X ^ (2 * n) : K[X]).degree := by
    rw [degree_X_pow]
    have hl2 : l ≤ 2 * n := by omega
    exact hRdeg.trans_le (WithBot.coe_le_coe.mpr hl2)
  have hR : (B * truncatedMoments (2 * n) a) %ₘ (X ^ (2 * n)) = R :=
    (modByMonic_eq_of_dvd_sub (monic_X_pow _) hcong).trans
      ((modByMonic_eq_self_iff (monic_X_pow _)).mpr hdegree)
  exact recurrence_of_pade n l a B R hB hB0 hR.symm hRdeg

/-- Conversely, a monic recurrence yields a connection polynomial and a
    low-degree remainder with the exact Padé congruence. -/
theorem exists_pade_of_recurrence (n l : ℕ) (a : ℕ → K) (p : K[X])
    (hp : p.Monic) (hd : p.natDegree = l)
    (hfit : FitsTruncatedRecurrence (2 * n) l a p) :
    ∃ B R : K[X], B.coeff 0 = 1 ∧ B.natDegree ≤ l ∧ B.reflect l = p ∧
      R = (B * truncatedMoments (2 * n) a) %ₘ (X ^ (2 * n)) ∧
      R.degree < l ∧ X ^ (2 * n) ∣ B * truncatedMoments (2 * n) a - R := by
  let B := p.reflect l
  let A := B * truncatedMoments (2 * n) a
  have hB : B.natDegree ≤ l := natDegree_reflect_le.trans (max_le le_rfl hd.le)
  have hBr : B.reflect l = p := reflect_reflect
  refine ⟨B, A %ₘ (X ^ (2 * n)), ?_, hB, hBr, rfl, ?_, ?_⟩
  · simp [B, ← hd, hp.coeff_natDegree]
  · apply (remainder_degree_lt_iff_fits (2 * n) l a B hB).mpr
    simpa only [hBr] using hfit
  · change X ^ (2 * n) ∣ A - A %ₘ (X ^ (2 * n))
    rw [modByMonic_eq_sub_mul_div, sub_sub_cancel]
    exact dvd_mul_right _ _

/-- When the recurrence length is at most n, every one of the first n
    shifted equations is available from 2n moments. -/
theorem fits_first_n_of_truncated (n l : ℕ) (a : ℕ → K) (p : K[X])
    (hl : l ≤ n) (hd : p.natDegree = l) (hfit : FitsTruncatedRecurrence (2 * n) l a p) :
    ∀ k < n, ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * a (k + i) = 0 := by
  intro k hk
  rw [hd]
  exact hfit k (by omega)

#print axioms coeff_product_eq_shift
#print axioms remainder_degree_lt_iff_fits
#print axioms eval_reflect_eq_reciprocal
#print axioms recurrence_of_pade
#print axioms recurrence_of_pade_congruence
#print axioms exists_pade_of_recurrence
#print axioms fits_first_n_of_truncated

end Cogentic.RandomizedPadeRecurrence
