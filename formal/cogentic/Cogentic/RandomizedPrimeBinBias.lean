import Cogentic.CharacterEstimate
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

/-- Primes in the sharp interval `(A, B]`. -/
def primeBin (A B : ℕ) : Finset ℕ := (Ioc A B).filter Nat.Prime

private theorem primeBin_sum_eq {q A B : ℕ} (χ : DirichletCharacter ℂ q) (hAB : A ≤ B) :
    (∑ p ∈ primeBin A B, χ p) = Window.primeCount χ B - Window.primeCount χ A := by
  have hdisj : Disjoint (Icc 0 A) (Ioc A B) := Finset.disjoint_left.mpr (by
    intro p hp hq
    exact (not_lt_of_ge (mem_Icc.mp hp).2) (mem_Ioc.mp hq).1)
  have hunion : Icc 0 A ∪ Ioc A B = Icc 0 B := by
    ext p
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  unfold primeBin Window.primeCount
  simp only [Nat.floor_natCast, sum_filter]
  rw [← hunion, sum_union hdisj, add_sub_cancel_left]

/-- Uniform character bound for independent choices of primes from sharp bins. -/
def PrimeBinProductBound : Prop :=
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ),
        (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
        ‖∑ p ∈ Fintype.piFinset (fun i ↦ primeBin (A i) (B i)),
            χ (∏ i, (p i : ZMod q))‖ ≤
          ∏ i, 2 * K * (1 + Real.log (3 * q * B i))^2 * Real.sqrt (B i)

/-- The sharp-bin bound follows by subtraction at the two interval endpoints. -/
theorem primeBin_product_from_critical_line (line : DirichletLZerosOnLine) :
    PrimeBinProductBound := by
  obtain ⟨K, hK, bound⟩ := Window.nonprincipal_prime_count_from_critical_line line
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ ι _ _ A B hA hAB
  have hbin (i : ι) :
      ‖∑ p ∈ primeBin (A i) (B i), χ p‖ ≤
        2 * K * (1 + Real.log (3 * q * B i))^2 * Real.sqrt (B i) := by
    have hAr : (2 : ℝ) ≤ A i := by exact_mod_cast hA i
    have hABr : (A i : ℝ) ≤ B i := by exact_mod_cast hAB i
    have hBr := hAr.trans hABr
    have ha := bound q χ hχ (B i) (A i) hAr hABr
    have hb := bound q χ hχ (B i) (B i) hBr le_rfl
    rw [← Real.sqrt_eq_rpow] at ha hb
    have hscale : 0 ≤ K * (1 + Real.log (3 * q * B i))^2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hABr) hscale
    rw [primeBin_sum_eq χ (hAB i)]
    calc
      _ ≤ ‖Window.primeCount χ (B i)‖ + ‖Window.primeCount χ (A i)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hb ha
      _ ≤ _ := add_le_add le_rfl hscaled
      _ = _ := by ring
  simp_rw [map_prod]
  rw [← Finset.prod_univ_sum (fun i : ι ↦ primeBin (A i) (B i))
    (fun _ (p : ℕ) ↦ χ p)]
  calc
    _ = ∏ i, ‖∑ p ∈ primeBin (A i) (B i), χ p‖ := norm_prod _ _
    _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hbin i)

/-- The corresponding normalized bound uses the actual cardinalities of the bins. -/
theorem primeBin_average_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ),
        (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
        ‖∑ p ∈ Fintype.piFinset (fun i ↦ primeBin (A i) (B i)),
            χ (∏ i, (p i : ZMod q))‖ /
            (Fintype.piFinset (fun i ↦ primeBin (A i) (B i))).card ≤
          ∏ i, (2 * K * (1 + Real.log (3 * q * B i))^2 * Real.sqrt (B i)) /
            (primeBin (A i) (B i)).card := by
  obtain ⟨K, hK, bound⟩ := primeBin_product_from_critical_line line
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ ι _ _ A B hA hAB
  rw [Fintype.card_piFinset, Nat.cast_prod, Finset.prod_div_distrib]
  exact div_le_div_of_nonneg_right (bound q χ hχ A B hA hAB) (by positivity)

/-- The distinct integer products obtained by choosing one prime from every bin. -/
def primeBinProducts {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ) : Finset ℕ :=
  (Fintype.piFinset (fun i ↦ primeBin (A i) (B i))).image (fun p ↦ ∏ i, p i)

/-- Disjoint bins identify the slot of each prime divisor of a tuple product. -/
theorem primeBin_product_injOn {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) :
    Set.InjOn (fun p : ι → ℕ ↦ ∏ i, p i)
      ↑(Fintype.piFinset (fun i ↦ primeBin (A i) (B i))) := by
  intro p hp p' hp' heq
  change (∏ i, p i) = (∏ i, p' i) at heq
  funext i
  have hi := Fintype.mem_piFinset.mp hp i
  have hprime := (mem_filter.mp hi).2
  have hdvd : p i ∣ ∏ j, p' j := by
    rw [← heq]
    exact dvd_prod_of_mem p (mem_univ i)
  obtain ⟨j, _, hj⟩ := ((Nat.prime_iff.mp hprime).dvd_finsetProd_iff p').mp hdvd
  have hj' := Fintype.mem_piFinset.mp hp' j
  have hpp := (Nat.prime_dvd_prime_iff_eq hprime (mem_filter.mp hj').2).mp hj
  have hij : i = j := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hdisj hne)) hi (hpp.symm ▸ hj')
  exact hij ▸ hpp

theorem primeBinProducts_card {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) :
    (primeBinProducts A B).card = ∏ i, (primeBin (A i) (B i)).card := by
  rw [primeBinProducts, Finset.card_image_of_injOn (primeBin_product_injOn A B hdisj),
    Fintype.card_piFinset]

theorem primeBinProducts_character_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) :
    (∑ m ∈ primeBinProducts A B, χ m) =
      ∑ p ∈ Fintype.piFinset (fun i ↦ primeBin (A i) (B i)), χ (∏ i, (p i : ZMod q)) := by
  rw [primeBinProducts, Finset.sum_image (primeBin_product_injOn A B hdisj)]
  simp only [Nat.cast_prod]

private theorem primeBin_pattern_subset {ι : Type} [DecidableEq ι] (A B : ι → ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    {s t : Finset ι} {n : ℕ}
    (hs : n ∈ primeBinProducts (fun i : s ↦ A i) (fun i : s ↦ B i))
    (ht : n ∈ primeBinProducts (fun i : t ↦ A i) (fun i : t ↦ B i)) :
    s ⊆ t := by
  obtain ⟨p, hp, hprod⟩ := mem_image.mp hs
  obtain ⟨p', hp', hprod'⟩ := mem_image.mp ht
  change (∏ i, p i) = n at hprod
  change (∏ j, p' j) = n at hprod'
  intro i hi
  let is : s := ⟨i, hi⟩
  have hpi := Fintype.mem_piFinset.mp hp is
  have hprime := (mem_filter.mp hpi).2
  have hdvd : p is ∣ ∏ j, p' j := by
    rw [hprod', ← hprod]
    exact dvd_prod_of_mem p (mem_univ is)
  obtain ⟨j, _, hj⟩ := ((Nat.prime_iff.mp hprime).dvd_finsetProd_iff p').mp hdvd
  have hpj := Fintype.mem_piFinset.mp hp' j
  have hpp := (Nat.prime_dvd_prime_iff_eq hprime (mem_filter.mp hpj).2).mp hj
  have hij : i = (j : ι) := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hdisj hne)) hpi (hpp.symm ▸ hpj)
  exact hij.symm ▸ j.property

/-- Two different subsets of the same disjoint bins give disjoint integer products. -/
theorem primeBinProducts_disjoint_patterns {ι : Type} [DecidableEq ι] (A B : ι → ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    {s t : Finset ι} (hst : s ≠ t) :
    Disjoint (primeBinProducts (fun i : s ↦ A i) (fun i : s ↦ B i))
      (primeBinProducts (fun i : t ↦ A i) (fun i : t ↦ B i)) :=
  Finset.disjoint_left.mpr fun _ hs ht ↦
    hst (Finset.Subset.antisymm (primeBin_pattern_subset A B hdisj hs ht)
      (primeBin_pattern_subset A B hdisj ht hs))

end Cogentic.Randomized
