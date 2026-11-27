import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! The sharp common divisor for roots planted consecutively on one progression. -/

namespace Cogentic.RandomizedPlantedRoots

open scoped BigOperators Nat

/-- The product of the differences from the first k nodes on a progression
of step p, evaluated at the nth node. -/
def progressionProduct (p : ℤ) (k : ℕ) (n : ℤ) : ℤ :=
  ∏ i ∈ Finset.range k, (p * n - p * i)

theorem progressionProduct_eq (p : ℤ) (k : ℕ) (n : ℤ) :
    progressionProduct p k n = p ^ k * ∏ i ∈ Finset.range k, (n - i) := by
  simp only [progressionProduct, ← mul_sub, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range]

/-- The factorial divides every descending product, including at negative indices. -/
theorem factorial_dvd_descending_product (k : ℕ) (n : ℤ) :
    (k ! : ℤ) ∣ ∏ i ∈ Finset.range k, (n - i) := by
  have h := Nat.factorial_coe_dvd_prod k (-n)
  have hprod : (∏ i ∈ Finset.range k, (n - (i : ℤ))) =
      (∏ i ∈ Finset.range k, (-n + (i : ℤ))) * (-1) ^ k := by
    have hs : (∏ _i ∈ Finset.range k, (-1 : ℤ)) = (-1 : ℤ) ^ k := by simp
    rw [← hs, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [hprod]
  exact dvd_mul_of_dvd_left h _

theorem progressionProduct_dvd (p : ℤ) (k : ℕ) (n : ℤ) :
    p ^ k * (k ! : ℤ) ∣ progressionProduct p k n := by
  rw [progressionProduct_eq]
  exact mul_dvd_mul_left _ (factorial_dvd_descending_product k n)

/-- The first unplanted node realizes the claimed common divisor. -/
theorem progressionProduct_next (p : ℤ) (k : ℕ) :
    progressionProduct p k k = p ^ k * (k ! : ℤ) := by
  rw [progressionProduct_eq]
  congr 1
  rw [Nat.factorial_eq_prod_range_add_one k]
  -- Reverse the order of the factors in the factorial.
  rw [← Finset.prod_range_reflect]
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  omega

theorem dvd_all_progressionProduct_iff (p : ℤ) (k : ℕ) (d : ℤ) :
    (∀ n : ℤ, d ∣ progressionProduct p k n) ↔ d ∣ p ^ k * (k ! : ℤ) := by
  constructor
  · intro h
    simpa only [progressionProduct_next] using h k
  · intro h n
    exact h.trans (progressionProduct_dvd p k n)

/-- The exact exponent valid at every node is k plus the p-adic exponent of k factorial. -/
theorem pow_dvd_all_progressionProduct_iff {p : ℕ} (hp : 1 < p) (k e : ℕ) :
    (∀ n : ℤ, (p : ℤ) ^ e ∣ progressionProduct p k n) ↔
      e ≤ k + padicValNat p (k !) := by
  rw [dvd_all_progressionProduct_iff]
  have hne : p ^ k * k ! ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (Nat.factorial_ne_zero _)
  have hg : padicValNat p (p ^ k * k !) = k + padicValNat p (k !) := by
    rw [padicValNat_base_pow_mul hp (Nat.factorial_ne_zero _), Nat.add_comm]
  have hcast : (p : ℤ) ^ e ∣ (p : ℤ) ^ k * (k ! : ℤ) ↔ p ^ e ∣ p ^ k * k ! := by
    exact_mod_cast Iff.rfl
  rw [hcast, Nat.pow_dvd_iff_le_padicValNat (by omega) hne, hg]


section Interpolation

open Polynomial

private theorem sum_eq_zero_or_le_valuation {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) (e : ℤ)
    (hf : ∀ i ∈ s, f i = 0 ∨ e ≤ padicValRat p (f i)) :
    (∑ i ∈ s, f i) = 0 ∨ e ≤ padicValRat p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      rcases hf i (Finset.mem_insert_self i s) with hz | hval
      · simpa [hz] using ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
      rcases ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) with hz | hs
      · simp [hz, hval]
      by_cases hz : f i + ∑ j ∈ s, f j = 0
      · exact Or.inl hz
      · exact Or.inr ((le_min hval hs).trans (padicValRat.min_le_padicValRat_add hz))

/-- The valuation loss when interpolating the top coefficient is at most the
largest valuation of a Lagrange denominator. The top coefficient is the value
at (1,0) of the corresponding homogenized polynomial. -/
theorem coeff_eq_zero_or_le_valuation_of_eval {p : ℕ} [Fact p.Prime]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℚ)
    (hvs : Set.InjOn v s) (P : ℚ[X]) (hP : P.degree < s.card)
    (e D : ℤ)
    (hval : ∀ i ∈ s, P.eval (v i) = 0 ∨ e + D ≤ padicValRat p (P.eval (v i)))
    (hden : ∀ i ∈ s, padicValRat p (∏ j ∈ s.erase i, (v i - v j)) ≤ D) :
    P.coeff (s.card - 1) = 0 ∨ e ≤ padicValRat p (P.coeff (s.card - 1)) := by
  rw [Lagrange.coeff_eq_sum hvs hP]
  apply sum_eq_zero_or_le_valuation
  intro i hi
  rcases eq_or_ne (P.eval (v i)) 0 with hzero | hnonzero
  · simp [hzero]
  have hd : (∏ j ∈ s.erase i, (v i - v j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr fun heq =>
      (Finset.mem_erase.mp hj).1 (hvs hi (Finset.mem_erase.mp hj).2 heq).symm
  refine Or.inr ?_
  rw [padicValRat.div hnonzero hd]
  have hv := (hval i hi).resolve_left hnonzero
  have hD := hden i hi
  omega


/-- Evaluation of the homogeneous degree-d form associated with a polynomial,
on the chart where the second coordinate is nonzero. -/
def homogeneousEval (P : ℚ[X]) (d : ℕ) (x y : ℚ) : ℚ :=
  y ^ d * P.eval (x / y)

private theorem prod_affine_differences {ι : Type*} (s : Finset ι)
    (x y : ι → ℚ) (a b : ℚ) (hb : b ≠ 0) (hy : ∀ j ∈ s, y j ≠ 0) :
    (∏ j ∈ s, (a / b - x j / y j)) =
      (∏ j ∈ s, (a * y j - b * x j)) / (b ^ s.card * ∏ j ∈ s, y j) := by
  calc
    _ = ∏ j ∈ s, ((a * y j - b * x j) / (b * y j)) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [div_sub_div _ _ hb (hy j hj)]
    _ = _ := by rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const]

/-- Homogeneous Lagrange interpolation on a common rational affine chart. -/
theorem homogeneousEval_eq_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x y : ι → ℚ) (hy : ∀ j ∈ s, y j ≠ 0)
    (hinj : Set.InjOn (fun j => x j / y j) s)
    (P : ℚ[X]) (hP : P.degree < s.card) (a b : ℚ) (hb : b ≠ 0) :
    homogeneousEval P (s.card - 1) a b =
      ∑ i ∈ s, homogeneousEval P (s.card - 1) (x i) (y i) *
        (∏ j ∈ s.erase i, (a * y j - b * x j)) /
        (∏ j ∈ s.erase i, (x i * y j - y i * x j)) := by
  let v (i : ι) := x i / y i
  have heval : P.eval (a / b) =
      ∑ i ∈ s, P.eval (v i) / (∏ j ∈ s.erase i, (v i - v j)) *
        ∏ j ∈ s.erase i, (a / b - v j) := by
    nth_rewrite 1 [Lagrange.eq_interpolate hinj hP, Lagrange.interpolate_eq_sum]
    simp [v, Polynomial.eval_finsetSum, Polynomial.eval_prod]
  rw [homogeneousEval, heval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hy' (j : ι) (hj : j ∈ s.erase i) : y j ≠ 0 :=
    hy j (Finset.mem_of_mem_erase hj)
  have hcard : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
  simp only [v, homogeneousEval]
  rw [prod_affine_differences (s.erase i) x y (x i) (y i) (hy i hi) hy',
    prod_affine_differences (s.erase i) x y a b hb hy', hcard]
  have hprod := Finset.prod_ne_zero_iff.mpr hy'
  field_simp

/-- For homogeneous interpolation with nonzero determinant denominators,
a bound on their valuations controls the divisibility loss at the target. -/
theorem homogeneousEval_eq_zero_or_le_valuation {p : ℕ} [Fact p.Prime]
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x y : ι → ℚ) (hy : ∀ j ∈ s, y j ≠ 0)
    (hinj : Set.InjOn (fun j => x j / y j) s)
    (P : ℚ[X]) (hP : P.degree < s.card) (a b : ℚ) (hb : b ≠ 0) (e D : ℤ)
    (hval : ∀ i ∈ s, let w := homogeneousEval P (s.card - 1) (x i) (y i)
      w = 0 ∨ e + D ≤ padicValRat p w)
    (hnum : ∀ i ∈ s, 0 ≤ padicValRat p (∏ j ∈ s.erase i, (a * y j - b * x j)))
    (hden : ∀ i ∈ s, padicValRat p (∏ j ∈ s.erase i, (x i * y j - y i * x j)) ≤ D) :
    homogeneousEval P (s.card - 1) a b = 0 ∨
      e ≤ padicValRat p (homogeneousEval P (s.card - 1) a b) := by
  rw [homogeneousEval_eq_sum s x y hy hinj P hP a b hb]
  apply sum_eq_zero_or_le_valuation
  intro i hi
  by_cases hw : homogeneousEval P (s.card - 1) (x i) (y i) = 0
  · simp [hw]
  by_cases hn : (∏ j ∈ s.erase i, (a * y j - b * x j)) = 0
  · simp [hn]
  by_cases hd : (∏ j ∈ s.erase i, (x i * y j - y i * x j)) = 0
  · simp [hd]
  refine Or.inr ?_
  rw [padicValRat.div (mul_ne_zero hw hn) hd, padicValRat.mul hw hn]
  have hv := (hval i hi).resolve_left hw
  have hn' := hnum i hi
  have hd' := hden i hi
  omega


/-- A unit-valued target forces at least one node to miss any valuation
threshold above the denominator bound. -/
theorem exists_low_valuation_of_homogeneousEval_unit {p : ℕ} [Fact p.Prime]
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x y : ι → ℚ) (hy : ∀ j ∈ s, y j ≠ 0)
    (hinj : Set.InjOn (fun j => x j / y j) s)
    (P : ℚ[X]) (hP : P.degree < s.card) (a b : ℚ) (hb : b ≠ 0) (D : ℤ)
    (hne : homogeneousEval P (s.card - 1) a b ≠ 0)
    (hunit : padicValRat p (homogeneousEval P (s.card - 1) a b) = 0)
    (hnum : ∀ i ∈ s, 0 ≤ padicValRat p (∏ j ∈ s.erase i, (a * y j - b * x j)))
    (hden : ∀ i ∈ s, padicValRat p (∏ j ∈ s.erase i, (x i * y j - y i * x j)) ≤ D) :
    ∃ i ∈ s, let w := homogeneousEval P (s.card - 1) (x i) (y i)
      w ≠ 0 ∧ padicValRat p w ≤ D := by
  classical
  by_contra! h
  have hval (i : ι) (hi : i ∈ s) : let w := homogeneousEval P (s.card - 1) (x i) (y i)
      w = 0 ∨ 1 + D ≤ padicValRat p w := by
    dsimp
    by_cases hz : homogeneousEval P (s.card - 1) (x i) (y i) = 0
    · exact Or.inl hz
    · have hlt : D < padicValRat p (homogeneousEval P (s.card - 1) (x i) (y i)) := by
        by_contra! hv
        exact h i hi ⟨hz, hv⟩
      exact Or.inr (by omega)
  have hc := (homogeneousEval_eq_zero_or_le_valuation s x y hy hinj P hP a b hb 1 D
    hval hnum hden).resolve_left hne
  rw [hunit] at hc
  omega

end Interpolation

end Cogentic.RandomizedPlantedRoots
