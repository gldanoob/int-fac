import Cogentic.RandomizedPrimeBinPatterns
import Cogentic.RandomizedPrimeBinSupply

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

/-- The lower real endpoint at bin index `j` after centering on a pattern sum. -/
noncomputable def centeredBinEndpoint (P δ : ℝ) (a k j : ℕ) : ℝ :=
  P * Real.exp (δ * ((j : ℝ) - (a : ℝ) / (k : ℝ)))

/-- Consecutive floors give half-open integer bins with a common boundary. -/
noncomputable def centeredBinFloor (P δ : ℝ) (a k j : ℕ) : ℕ :=
  Nat.floor (centeredBinEndpoint P δ a k j)

/-- The patterns of size `k` with common index sum `a`. -/
def centeredBinPatterns (J k a : ℕ) : Finset (Finset ℕ) :=
  ((range J).powersetCard k).filter fun s => (∑ j ∈ s, j) = a

/-- The distinct integer products which have a prime in every occupied bin. -/
noncomputable def centeredBinProducts (P δ : ℝ) (J k a : ℕ) : Finset ℕ :=
  primeBinPatternProducts (centeredBinFloor P δ a k)
    (fun j => centeredBinFloor P δ a k (j + 1)) (centeredBinPatterns J k a)

private theorem centeredBinEndpoint_succ (P δ : ℝ) (a k j : ℕ) :
    centeredBinEndpoint P δ a k (j + 1) =
      centeredBinEndpoint P δ a k j * Real.exp δ := by
  unfold centeredBinEndpoint
  rw [Nat.cast_add, Nat.cast_one, show δ * ((j : ℝ) + 1 - (a : ℝ) / (k : ℝ)) =
    δ * ((j : ℝ) - (a : ℝ) / (k : ℝ)) + δ by ring, Real.exp_add, mul_assoc]

theorem centeredBinEndpoint_product (P δ : ℝ) {a k : ℕ} (hk : 0 < k) (s : Finset ℕ)
    (hsize : s.card = k) (hsum : (∑ j ∈ s, j) = a) :
    (∏ j ∈ s, centeredBinEndpoint P δ a k j) = P ^ k := by
  have hkr : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hsumr : (∑ j ∈ s, (j : ℝ)) = (a : ℝ) := by rw [← Nat.cast_sum, hsum]
  have hmean : (k : ℝ) * ((a : ℝ) / (k : ℝ)) = (a : ℝ) := by field_simp
  unfold centeredBinEndpoint
  rw [prod_mul_distrib, prod_const, hsize, ← Real.exp_sum, ← mul_sum, sum_sub_distrib, sum_const,
    nsmul_eq_mul, hsize, hsumr, hmean, sub_self, mul_zero, Real.exp_zero, mul_one]

private theorem centeredBinFloor_mono {P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 ≤ δ) (a k : ℕ) :
    Monotone (centeredBinFloor P δ a k) := by
  intro i j hij
  apply Nat.floor_mono
  unfold centeredBinEndpoint
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (sub_le_sub_right (Nat.cast_le.mpr hij) _) hδ)) hP

theorem centeredBin_disjoint {P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 ≤ δ) (a k : ℕ) :
    Pairwise fun i j => Disjoint
      (primeBin (centeredBinFloor P δ a k i) (centeredBinFloor P δ a k (i + 1)))
      (primeBin (centeredBinFloor P δ a k j) (centeredBinFloor P δ a k (j + 1))) := by
  have ordered : ∀ {i j : ℕ}, i < j → Disjoint
      (primeBin (centeredBinFloor P δ a k i) (centeredBinFloor P δ a k (i + 1)))
      (primeBin (centeredBinFloor P δ a k j) (centeredBinFloor P δ a k (j + 1))) := by
    intro i j hij
    apply disjoint_left.mpr
    intro p hpi hpj
    have hi := (mem_Ioc.mp (mem_filter.mp hpi).1).2
    have hj := (mem_Ioc.mp (mem_filter.mp hpj).1).1
    exact (not_lt_of_ge (hi.trans (centeredBinFloor_mono hP hδ a k hij))) hj
  intro i j hne
  obtain hij | hji := lt_or_gt_of_ne hne
  · exact ordered hij
  · exact (ordered hji).symm

private theorem centeredBin_width {P δ : ℝ} (hP : 0 ≤ P) (a k j : ℕ) :
    δ * centeredBinEndpoint P δ a k j - 1 ≤
      (centeredBinFloor P δ a k (j + 1) : ℝ) - centeredBinFloor P δ a k j := by
  have hlo : 0 ≤ centeredBinEndpoint P δ a k j := mul_nonneg hP (Real.exp_pos _).le
  have hgap := mul_le_mul_of_nonneg_left (Real.add_one_le_exp δ) hlo
  have hl := Nat.floor_le hlo
  have hu := Nat.lt_floor_add_one (centeredBinEndpoint P δ a k (j + 1))
  unfold centeredBinFloor
  nlinarith only [hgap, hl, hu, centeredBinEndpoint_succ P δ a k j]

/-- The square-root supply bound and explicit rounding guards give the full
weighted population. The rounding loss is charged by the `+ 1` in each guard. -/
theorem centeredBinProducts_population (supply : PrimeBinSupplyBound) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P δ c y : ℝ) (J k a : ℕ),
      0 ≤ P → 0 ≤ δ → 0 ≤ c → 1 < y → 0 < k →
      (∀ j < J,
        2 ≤ centeredBinFloor P δ a k j ∧
        (centeredBinFloor P δ a k (j + 1) : ℝ) ≤ y ∧
        K * (1 + Real.log (3 * (centeredBinFloor P δ a k (j + 1) : ℝ))) ^ 2 *
          Real.sqrt (centeredBinFloor P δ a k (j + 1)) + 1 ≤
          (1 - c) * δ * centeredBinEndpoint P δ a k j) →
      ((centeredBinPatterns J k a).card : ℝ) * P ^ k * (c * δ / Real.log y) ^ k ≤
        (centeredBinProducts P δ J k a).card := by
  obtain ⟨K, hK, supply⟩ := supply
  refine ⟨K, hK, ?_⟩
  intro P δ c y J k a hP hδ hc hy hk guard
  let W := c * δ / Real.log y
  have hlog := Real.log_pos hy
  have hW : 0 ≤ W := div_nonneg (mul_nonneg hc hδ) hlog.le
  have hpop (j : ℕ) (hj : j < J) :
      centeredBinEndpoint P δ a k j * W ≤
        ((primeBin (centeredBinFloor P δ a k j) (centeredBinFloor P δ a k (j + 1))).card : ℝ) := by
    obtain ⟨hA, hBy, hguard⟩ := guard j hj
    let A := centeredBinFloor P δ a k j
    let B := centeredBinFloor P δ a k (j + 1)
    let L := centeredBinEndpoint P δ a k j
    let E := K * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt B
    have hAB : A ≤ B := centeredBinFloor_mono hP hδ a k (by omega)
    have hpositive : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hwidth : δ * L - 1 ≤ (B : ℝ) - A := centeredBin_width hP a k j
    have herror : E + 1 ≤ (1 - c) * δ * L := hguard
    have hsupply : (B : ℝ) - A - E ≤ ((primeBin A B).card : ℝ) * Real.log B :=
      supply A B hA hAB
    have hlogB := Real.log_le_log hpositive hBy
    have htarget : c * δ * L ≤ ((primeBin A B).card : ℝ) * Real.log y := calc
      c * δ * L = δ * L - (1 - c) * δ * L := by ring
      _ ≤ (B : ℝ) - A - E := by linarith only [hwidth, herror]
      _ ≤ _ * Real.log B := hsupply
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg _)
    calc
      L * W = c * δ * L / Real.log y := by unfold W; ring
      _ ≤ _ := (div_le_iff₀ hlog).mpr htarget
  let patterns := centeredBinPatterns J k a
  unfold centeredBinProducts
  rw [primeBinPatternProducts_card _ _ (centeredBin_disjoint hP hδ a k), Nat.cast_sum]
  change (patterns.card : ℝ) * P ^ k * W ^ k ≤ ∑ s ∈ patterns, _
  rw [mul_assoc, ← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro s hs
  obtain ⟨hset, hsum⟩ := mem_filter.mp hs
  obtain ⟨hsub, hsize⟩ := mem_powersetCard.mp hset
  rw [primeBinProducts_card _ _ (fun i j hij =>
    centeredBin_disjoint hP hδ a k (Subtype.val_injective.ne hij)), Nat.cast_prod]
  calc
    P ^ k * W ^ k = ∏ j : s, (centeredBinEndpoint P δ a k j * W) := by
      rw [prod_mul_distrib, prod_coe_sort s (centeredBinEndpoint P δ a k),
        centeredBinEndpoint_product P δ hk s hsize hsum, prod_const, card_univ, Fintype.card_coe, hsize]
    _ ≤ _ := prod_le_prod (fun j _ =>
      mul_nonneg (mul_nonneg hP (Real.exp_pos _).le) hW)
      (fun j _ => hpop j (mem_range.mp (hsub j.property)))

/-- Every counted integer is in the common multiplicative strip. -/
theorem centeredBinProducts_mem_strip {P δ : ℝ} (hP : 0 ≤ P) {J k a n : ℕ} (hk : 0 < k)
    (hn : n ∈ centeredBinProducts P δ J k a) :
    P ^ k ≤ (n : ℝ) ∧ (n : ℝ) ≤ P ^ k * Real.exp ((k : ℝ) * δ) := by
  unfold centeredBinProducts primeBinPatternProducts at hn
  obtain ⟨s, hs, hprod⟩ := mem_biUnion.mp hn
  obtain ⟨hset, hsum⟩ := mem_filter.mp hs
  have hsize := (mem_powersetCard.mp hset).2
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hprod
  have hmem (i : s) := (mem_filter.mp (Fintype.mem_piFinset.mp hp i)).1
  rw [Nat.cast_prod]
  have hlow : (∏ i : s, centeredBinEndpoint P δ a k i) = P ^ k := by
    rw [prod_coe_sort, centeredBinEndpoint_product P δ hk s hsize hsum]
  have hup : (∏ i : s, centeredBinEndpoint P δ a k (i + 1)) =
      P ^ k * Real.exp ((k : ℝ) * δ) := by
    simp_rw [centeredBinEndpoint_succ P δ a k]
    rw [prod_mul_distrib, hlow, prod_const, card_univ, Fintype.card_coe, hsize, Real.exp_nat_mul]
  constructor
  · rw [← hlow]
    apply prod_le_prod (fun i _ => mul_nonneg hP (Real.exp_pos _).le)
    intro i _
    have hi := (mem_Ioc.mp (hmem i)).1
    have hcast : (centeredBinFloor P δ a k i : ℝ) + 1 ≤ (p i : ℝ) := by exact_mod_cast hi
    exact (Nat.lt_floor_add_one (centeredBinEndpoint P δ a k i)).le.trans hcast
  · rw [← hup]
    apply prod_le_prod (fun _ _ => Nat.cast_nonneg _)
    intro i _
    have hi := (mem_Ioc.mp (hmem i)).2
    exact (Nat.cast_le.mpr hi).trans (Nat.floor_le (mul_nonneg hP (Real.exp_pos _).le))

#print axioms centeredBinEndpoint_product
#print axioms centeredBinProducts_population
#print axioms centeredBinProducts_mem_strip

end Cogentic.Randomized
