import Cogentic.RandomizedBalancedStrip
import Cogentic.RandomizedPrescribedPrimeCompletion
import Cogentic.RandomizedPrimeGridPrefixEnergy
import Cogentic.RandomizedMarginalModes
import Cogentic.RandomizedRectangularAbel
import Cogentic.RandomizedRelativePrefix
import Cogentic.RandomizedPrimeBinProgression
import Cogentic.RandomizedPrimePatternProgression

namespace Cogentic.Randomized

open Finset
open scoped BigOperators Classical

/-! ## Section 1: Divided strip density ratio -/

/-- The divided strip `S_q = {n / q : n ∈ S, q ∣ n}`. -/
def dividedStrip (S : Finset ℕ) (q : ℕ) : Finset ℕ :=
  (S.filter (q ∣ ·)).image (· / q)

/-- The density `|S| / X` of a finite strip at scale `X`. -/
noncomputable def stripDensity (S : Finset ℕ) (X : ℝ) : ℝ :=
  (S.card : ℝ) / X

theorem dividedStrip_card (S : Finset ℕ) (q : ℕ) :
    (dividedStrip S q).card = (S.filter (q ∣ ·)).card := by
  unfold dividedStrip
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have ha' : q ∣ a := (Finset.mem_filter.mp ha).2
  have hb' : q ∣ b := (Finset.mem_filter.mp hb).2
  have hmul : q * (a / q) = q * (b / q) := congrArg (q * ·) hab
  rwa [Nat.mul_div_cancel' ha', Nat.mul_div_cancel' hb'] at hmul

theorem stripDensity_divided_ratio (S : Finset ℕ) {X : ℝ} (hX : X ≠ 0)
    {q : ℕ} (hq : q ≠ 0) :
    stripDensity (dividedStrip S q) (X / (q : ℝ)) / stripDensity S X =
      (q : ℝ) * ((dividedStrip S q).card : ℝ) / (S.card : ℝ) := by
  unfold stripDensity
  have hqr : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  by_cases hS : (S.card : ℝ) = 0
  · simp [hS]
  · field_simp

/-- Prescribing a prime `q` in bin `j` cuts the cardinality of a disjoint
prime-bin pattern union by at least the population of bin `j`. -/
theorem primeBinPatternProducts_dividedStrip_card_mul_le
    {ι : Type} [DecidableEq ι] (A B : ι → ℕ) (patterns : Finset (Finset ι)) (j : ι) {q : ℕ}
    (hq : q ∈ primeBin (A j) (B j))
    (hdisj : Pairwise fun i k ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A k) (B k))) :
    (primeBin (A j) (B j)).card *
      (dividedStrip (primeBinPatternProducts A B patterns) q).card ≤
        (primeBinPatternProducts A B patterns).card := by
  rw [dividedStrip_card, primeBinPatternProducts_prescribed_card A B patterns j hq hdisj]
  exact Finset.card_le_card
    (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _))

/-- Divided strip cardinality and density ratio bound for any disjoint
prime-bin pattern union when the prescribed bin has population at least
`c * q / (d * log y)`. -/
theorem primeBinPatternProducts_dividedStrip_ratio_le
    {ι : Type} [DecidableEq ι] (A B : ι → ℕ) (patterns : Finset (Finset ι)) (j : ι) {q : ℕ}
    {c d y X : ℝ} (hc : 0 < c) (hd : 0 < d) (hy : 1 < y) (hX : 0 < X)
    (hq : q ∈ primeBin (A j) (B j))
    (hdisj : Pairwise fun i k ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A k) (B k)))
    (hpop : c * (q : ℝ) / (d * Real.log y) ≤ ((primeBin (A j) (B j)).card : ℝ)) :
    let S := primeBinPatternProducts A B patterns
    (q : ℝ) * ((dividedStrip S q).card : ℝ) / (S.card : ℝ) ≤ (d * Real.log y) / c ∧
    stripDensity (dividedStrip S q) (X / (q : ℝ)) / stripDensity S X ≤ (d * Real.log y) / c := by
  intro S
  have hq0 : q ≠ 0 := (Finset.mem_filter.mp hq).2.ne_zero
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hcard_ratio : (q : ℝ) * ((dividedStrip S q).card : ℝ) / (S.card : ℝ) ≤
      (d * Real.log y) / c := by
    by_cases hS : S.card = 0
    · simp only [hS, Nat.cast_zero, div_zero]
      positivity
    · have hSpos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS)
      have hmul : ((primeBin (A j) (B j)).card : ℝ) * ((dividedStrip S q).card : ℝ) ≤
          (S.card : ℝ) := by
        exact_mod_cast primeBinPatternProducts_dividedStrip_card_mul_le A B patterns j hq hdisj
      have h1 : (c * (q : ℝ) / (d * Real.log y)) * ((dividedStrip S q).card : ℝ) ≤ (S.card : ℝ) :=
        (mul_le_mul_of_nonneg_right hpop (Nat.cast_nonneg _)).trans hmul
      have h2 : c * ((q : ℝ) * ((dividedStrip S q).card : ℝ)) ≤ (d * Real.log y) * (S.card : ℝ) := by
        have hdlog : 0 < d * Real.log y := mul_pos hd hlog
        have h1' : (c * (q : ℝ) * ((dividedStrip S q).card : ℝ)) / (d * Real.log y) ≤ (S.card : ℝ) := by
          simpa only [div_mul_eq_mul_div] using h1
        have h1'' := (div_le_iff₀ hdlog).mp h1'
        linarith only [h1'']
      rw [div_le_div_iff₀ hSpos hc]
      linarith only [h2]
  exact ⟨hcard_ratio, by rw [stripDensity_divided_ratio S hX.ne' hq0]; exact hcard_ratio⟩

/-- Divided strip density ratio bound specialized to the balanced centered-bin
strip `centeredBinProducts`. -/
theorem centeredBinProducts_dividedStrip_ratio_le
    {P δ c d y X : ℝ} {J k a j q : ℕ}
    (hP : 0 ≤ P) (hδ : 0 ≤ δ) (hc : 0 < c) (hd : 0 < d) (hy : 1 < y) (hX : 0 < X)
    (hq : q ∈ primeBin (centeredBinFloor P δ a k j) (centeredBinFloor P δ a k (j + 1)))
    (hpop : c * (q : ℝ) / (d * Real.log y) ≤
      ((primeBin (centeredBinFloor P δ a k j) (centeredBinFloor P δ a k (j + 1))).card : ℝ)) :
    let S := centeredBinProducts P δ J k a
    (q : ℝ) * ((dividedStrip S q).card : ℝ) / (S.card : ℝ) ≤ (d * Real.log y) / c ∧
    stripDensity (dividedStrip S q) (X / (q : ℝ)) / stripDensity S X ≤ (d * Real.log y) / c :=
  primeBinPatternProducts_dividedStrip_ratio_le
    (centeredBinFloor P δ a k) (fun i => centeredBinFloor P δ a k (i + 1))
    (centeredBinPatterns J k a) j hc hd hy hX hq (centeredBin_disjoint hP hδ a k) hpop

private theorem centeredBinEndpoint_succ_eq (P δ : ℝ) (a k j : ℕ) :
    centeredBinEndpoint P δ a k (j + 1) =
      centeredBinEndpoint P δ a k j * Real.exp δ := by
  unfold centeredBinEndpoint
  rw [Nat.cast_add, Nat.cast_one,
    show δ * ((j : ℝ) + 1 - (a : ℝ) / (k : ℝ)) = δ * ((j : ℝ) - (a : ℝ) / (k : ℝ)) + δ by ring,
    Real.exp_add, mul_assoc]

private theorem centeredBin_width_le {P δ : ℝ} (hP : 0 ≤ P) (a k j : ℕ) :
    δ * centeredBinEndpoint P δ a k j - 1 ≤
      (centeredBinFloor P δ a k (j + 1) : ℝ) - centeredBinFloor P δ a k j := by
  have hlo : 0 ≤ centeredBinEndpoint P δ a k j := mul_nonneg hP (Real.exp_pos _).le
  have hgap := mul_le_mul_of_nonneg_left (Real.add_one_le_exp δ) hlo
  have hl := Nat.floor_le hlo
  have hu := Nat.lt_floor_add_one (centeredBinEndpoint P δ a k (j + 1))
  unfold centeredBinFloor
  nlinarith only [hgap, hl, hu, centeredBinEndpoint_succ_eq P δ a k j]

private theorem centeredBinFloor_le_succ {P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 ≤ δ) (a k j : ℕ) :
    centeredBinFloor P δ a k j ≤ centeredBinFloor P δ a k (j + 1) := by
  apply Nat.floor_mono
  unfold centeredBinEndpoint
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hP
  have hle : (j : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.le_succ j
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hle _) hδ

/-- Combining `PrimeBinSupplyBound` with `centeredBinProducts_dividedStrip_ratio_le`
yields `μ_q / μ ≤ exp δ * log y / (c * δ)` directly from the prime-bin guard. -/
theorem centeredBinProducts_dividedStrip_ratio_from_supply (supply : PrimeBinSupplyBound) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P δ c y X : ℝ) (J k a j q : ℕ),
      0 ≤ P → 0 < δ → 0 < c → 1 < y → 0 < X →
      q ∈ primeBin (centeredBinFloor P δ a k j) (centeredBinFloor P δ a k (j + 1)) →
      2 ≤ centeredBinFloor P δ a k j →
      (centeredBinFloor P δ a k (j + 1) : ℝ) ≤ y →
      K * (1 + Real.log (3 * (centeredBinFloor P δ a k (j + 1) : ℝ))) ^ 2 *
        Real.sqrt (centeredBinFloor P δ a k (j + 1)) + 1 ≤
          (1 - c) * δ * centeredBinEndpoint P δ a k j →
      let S := centeredBinProducts P δ J k a
      (q : ℝ) * ((dividedStrip S q).card : ℝ) / (S.card : ℝ) ≤
        Real.exp δ * Real.log y / (c * δ) ∧
      stripDensity (dividedStrip S q) (X / (q : ℝ)) / stripDensity S X ≤
        Real.exp δ * Real.log y / (c * δ) := by
  obtain ⟨K, hK, hsup⟩ := supply
  refine ⟨K, hK, ?_⟩
  intro P δ c y X J k a j q hP hδ hc hy hX hq hA hBy hguard
  let A := centeredBinFloor P δ a k j
  let B := centeredBinFloor P δ a k (j + 1)
  let L := centeredBinEndpoint P δ a k j
  have hAB : A ≤ B := centeredBinFloor_le_succ hP hδ.le a k j
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hwidth : δ * L - 1 ≤ (B : ℝ) - A := centeredBin_width_le hP a k j
  have hsupply := hsup A B hA hAB
  have hlogB := Real.log_le_log hBpos hBy
  have hbin : c * δ * L / Real.log y ≤ ((primeBin A B).card : ℝ) := by
    rw [div_le_iff₀ hlog]
    calc
      c * δ * L = δ * L - (1 - c) * δ * L := by ring
      _ ≤ (B : ℝ) - A - K * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt B := by
        linarith only [hwidth, hguard]
      _ ≤ ((primeBin A B).card : ℝ) * Real.log B := hsupply
      _ ≤ ((primeBin A B).card : ℝ) * Real.log y :=
        mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg _)
  have hqB : (q : ℝ) ≤ L * Real.exp δ := by
    have hqle : q ≤ B := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2
    have hBfloor : (B : ℝ) ≤ centeredBinEndpoint P δ a k (j + 1) :=
      Nat.floor_le (mul_nonneg hP (Real.exp_pos _).le)
    rw [centeredBinEndpoint_succ_eq] at hBfloor
    exact (Nat.cast_le.mpr hqle).trans hBfloor
  have hLge : (q : ℝ) / Real.exp δ ≤ L := (div_le_iff₀ (Real.exp_pos δ)).mpr hqB
  have hpop : (c / Real.exp δ) * (q : ℝ) / ((1 / δ) * Real.log y) ≤ ((primeBin A B).card : ℝ) := by
    calc
      (c / Real.exp δ) * (q : ℝ) / ((1 / δ) * Real.log y)
          = c * δ * ((q : ℝ) / Real.exp δ) / Real.log y := by
            have hδne : δ ≠ 0 := hδ.ne'
            have hexpne : Real.exp δ ≠ 0 := (Real.exp_pos δ).ne'
            field_simp
      _ ≤ c * δ * L / Real.log y := by
            gcongr
      _ ≤ ((primeBin A B).card : ℝ) := hbin
  have hres := centeredBinProducts_dividedStrip_ratio_le (J := J) hP hδ.le
    (div_pos hc (Real.exp_pos δ)) (one_div_pos.mpr hδ) hy hX hq hpop
  have hrhs : (1 / δ) * Real.log y / (c / Real.exp δ) = Real.exp δ * Real.log y / (c * δ) := by
    have hδne : δ ≠ 0 := hδ.ne'
    have hcne : c ≠ 0 := hc.ne'
    have hexpne : Real.exp δ ≠ 0 := (Real.exp_pos δ).ne'
    field_simp
  simpa only [hrhs] using hres

/-! ## Section 2: One-point progression strip lower and upper bounds from GRH -/

theorem primeBinProducts_filter_coprime_card
    {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ) (m : ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) :
    ((primeBinProducts A B).filter (·.Coprime m)).card =
      ∏ i, ((primeBin (A i) (B i)).filter (·.Coprime m)).card := by
  have heq : (primeBinProducts A B).filter (·.Coprime m) =
      (Fintype.piFinset (fun i ↦ (primeBin (A i) (B i)).filter (·.Coprime m))).image
        (fun p ↦ ∏ i, p i) := by
    ext n
    simp only [primeBinProducts, Finset.mem_filter, Finset.mem_image, Fintype.mem_piFinset]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hcop⟩
      refine ⟨p, ?_, rfl⟩
      intro i
      exact ⟨hp i, (Nat.coprime_prod_left_iff.mp hcop) i (Finset.mem_univ i)⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, fun i => (hp i).1, rfl⟩, Nat.coprime_prod_left_iff.mpr fun i _ => (hp i).2⟩
  have hsub : (Fintype.piFinset (fun i ↦ (primeBin (A i) (B i)).filter (·.Coprime m)) : Set (ι → ℕ)) ⊆
      ↑(Fintype.piFinset (fun i ↦ primeBin (A i) (B i))) := by
    intro p hp
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_filter] at hp ⊢
    exact fun i => (hp i).1
  rw [heq, Finset.card_image_of_injOn ((primeBin_product_injOn A B hdisj).mono hsub),
    Fintype.card_piFinset]

theorem primeBinPatternProducts_filter_coprime_card
    {ι : Type} [DecidableEq ι] (A B : ι → ℕ) (patterns : Finset (Finset ι)) (m : ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) :
    ((primeBinPatternProducts A B patterns).filter (·.Coprime m)).card =
      ∑ s ∈ patterns, ∏ i ∈ s, ((primeBin (A i) (B i)).filter (·.Coprime m)).card := by
  unfold primeBinPatternProducts
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro s _
    rw [primeBinProducts_filter_coprime_card _ _ m
      (fun _ _ hij ↦ hdisj (Subtype.val_injective.ne hij)),
      Finset.prod_coe_sort s (fun i ↦ ((primeBin (A i) (B i)).filter (·.Coprime m)).card)]
  · intro s _ t _ hst
    exact (primeBinProducts_disjoint_patterns A B hdisj hst).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem filter_unit_eq_filter_coprime_unit {m : ℕ} [NeZero m] (S : Finset ℕ) (r : (ZMod m)ˣ) :
    S.filter (fun n : ℕ ↦ (r : ZMod m) = (n : ZMod m)) =
      (S.filter (·.Coprime m)).filter (fun n : ℕ ↦ (r : ZMod m) = (n : ZMod m)) := by
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hn, hr⟩
    have hunit : IsUnit (n : ZMod m) := hr ▸ r.isUnit
    exact ⟨⟨hn, (ZMod.isUnit_iff_coprime n m).mp hunit⟩, hr⟩
  · rintro ⟨⟨hn, _⟩, hr⟩
    exact ⟨hn, hr⟩

theorem primeBin_card_le_filter_coprime_add_primeFactors (A B : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (primeBin A B).card ≤ ((primeBin A B).filter (·.Coprime m)).card + m.primeFactors.card := by
  have hsub : primeBin A B ⊆ (primeBin A B).filter (·.Coprime m) ∪ m.primeFactors := by
    intro p hp
    by_cases hcop : p.Coprime m
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hcop⟩)
    · have hprime : p.Prime := (Finset.mem_filter.mp hp).2
      have hdvd : p ∣ m := by
        by_contra hndvd
        exact hcop (hprime.coprime_iff_not_dvd.mpr hndvd)
      exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hm⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- General one-point progression error, lower, and upper bounds for a pruned
disjoint prime-bin pattern strip from `DirichletLZerosOnLine`. -/
theorem primePattern_pruned_progression_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) [NeZero m] (r : (ZMod m)ˣ)
      {ι : Type} [DecidableEq ι] (A B : ι → ℕ) (patterns : Finset (Finset ι))
      (k : ℕ) (X U : ℝ),
      0 < X → 0 ≤ U →
      Pairwise (fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
      (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
      (∀ s ∈ patterns, s.card = k) →
      (∀ s ∈ patterns, X ≤ ∏ i ∈ s, (B i : ℝ)) →
      (∀ s ∈ patterns, ∀ i ∈ s,
        2 * K * (1 + Real.log (3 * m * B i)) ^ 2 * (B i : ℝ) ≤
          U * ((primeBin (A i) (B i)).filter (·.Coprime m)).card) →
      let S := primeBinPatternProducts A B patterns
      let S' := S.filter (·.Coprime m)
      let S_r := (S'.filter (fun n : ℕ ↦ (r : ZMod m) = (n : ZMod m))).card
      |(S_r : ℝ) - (S'.card : ℝ) / m.totient| ≤ (U ^ k / Real.sqrt X) * (S'.card : ℝ) ∧
      (1 / (m.totient : ℝ) - U ^ k / Real.sqrt X) * (S'.card : ℝ) ≤ (S_r : ℝ) ∧
      (S_r : ℝ) ≤ (1 / (m.totient : ℝ) + U ^ k / Real.sqrt X) * (S'.card : ℝ) := by
  obtain ⟨K, hK, hprog⟩ := primePattern_progression_of_bin_progression
    (primeBin_progression_of_product_bound (primeBin_product_from_critical_line line))
  refine ⟨K, hK, ?_⟩
  intro m _ r ι _ A B patterns k X U hX hU hdisj hA hAB hsize hscale hslot S S' S_r
  have hprog_r := hprog m r A B patterns hdisj hA hAB
  dsimp only at hprog_r
  rw [filter_unit_eq_filter_coprime_unit] at hprog_r
  have hpat (s : Finset ι) (hs : s ∈ patterns) :
      (∏ i ∈ s, 2 * K * (1 + Real.log (3 * m * B i)) ^ 2 * Real.sqrt (B i)) ≤
        (U ^ k / Real.sqrt X) *
          (∏ i ∈ s, (((primeBin (A i) (B i)).filter (·.Coprime m)).card : ℝ)) := by
    let H (i : ι) := 2 * K * (1 + Real.log (3 * m * B i)) ^ 2 * Real.sqrt (B i)
    have hH (i : ι) : 0 ≤ H i := by dsimp [H]; positivity
    have hmul : (∏ i ∈ s, H i) * Real.sqrt X ≤
        U ^ k * ∏ i ∈ s, (((primeBin (A i) (B i)).filter (·.Coprime m)).card : ℝ) := by
      calc
        (∏ i ∈ s, H i) * Real.sqrt X
            ≤ (∏ i ∈ s, H i) * Real.sqrt (∏ i ∈ s, (B i : ℝ)) :=
              mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hscale s hs))
                (Finset.prod_nonneg fun i _ => hH i)
        _ = (∏ i ∈ s, H i) * ∏ i ∈ s, Real.sqrt (B i) := by
              rw [Real.sqrt_prod s (fun _ _ => Nat.cast_nonneg _)]
        _ = ∏ i ∈ s, (H i * Real.sqrt (B i)) := (Finset.prod_mul_distrib).symm
        _ = ∏ i ∈ s, (2 * K * (1 + Real.log (3 * m * B i)) ^ 2 * (B i : ℝ)) := by
              apply Finset.prod_congr rfl
              intro i _
              dsimp only [H]
              rw [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
        _ ≤ ∏ i ∈ s, (U * (((primeBin (A i) (B i)).filter (·.Coprime m)).card : ℝ)) :=
              Finset.prod_le_prod (fun i _ => by positivity) (fun i hi => hslot s hs i hi)
        _ = U ^ k * ∏ i ∈ s, (((primeBin (A i) (B i)).filter (·.Coprime m)).card : ℝ) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, hsize s hs]
    rw [div_mul_eq_mul_div, le_div_iff₀ (Real.sqrt_pos.mpr hX)]
    exact hmul
  have habs : |(S_r : ℝ) - (S'.card : ℝ) / m.totient| ≤ (U ^ k / Real.sqrt X) * (S'.card : ℝ) := by
    refine hprog_r.trans ?_
    calc
      ∑ s ∈ patterns, ∏ i ∈ s, 2 * K * (1 + Real.log (3 * m * B i)) ^ 2 * Real.sqrt (B i)
          ≤ ∑ s ∈ patterns, (U ^ k / Real.sqrt X) *
              ∏ i ∈ s, (((primeBin (A i) (B i)).filter (·.Coprime m)).card : ℝ) :=
            Finset.sum_le_sum hpat
      _ = (U ^ k / Real.sqrt X) *
            ∑ s ∈ patterns, ∏ i ∈ s, (((primeBin (A i) (B i)).filter (·.Coprime m)).card : ℝ) := by
            rw [Finset.mul_sum]
      _ = (U ^ k / Real.sqrt X) * (S'.card : ℝ) := by
            congr 1
            dsimp only [S', S]
            rw [primeBinPatternProducts_filter_coprime_card A B patterns m hdisj, Nat.cast_sum]
            exact Finset.sum_congr rfl fun s _ => by rw [Nat.cast_prod]
  have ⟨hlo, hhi⟩ := abs_le.mp habs
  refine ⟨habs, ?_, ?_⟩
  · have : (S'.card : ℝ) / (m.totient : ℝ) - (U ^ k / Real.sqrt X) * (S'.card : ℝ) ≤ (S_r : ℝ) := by
      linarith only [hlo]
    linarith only [this, show (1 / (m.totient : ℝ) - U ^ k / Real.sqrt X) * (S'.card : ℝ) =
      (S'.card : ℝ) / (m.totient : ℝ) - (U ^ k / Real.sqrt X) * (S'.card : ℝ) by ring]
  · have : (S_r : ℝ) ≤ (S'.card : ℝ) / (m.totient : ℝ) + (U ^ k / Real.sqrt X) * (S'.card : ℝ) := by
      linarith only [hhi]
    linarith only [this, show (1 / (m.totient : ℝ) + U ^ k / Real.sqrt X) * (S'.card : ℝ) =
      (S'.card : ℝ) / (m.totient : ℝ) + (U ^ k / Real.sqrt X) * (S'.card : ℝ) by ring]

/-- One-point progression bounds on the balanced centered-bin strip in `[X_*, 2X_*]`
(after pruning primes dividing `m`), directly from `DirichletLZerosOnLine`. -/
theorem centeredBinProducts_pruned_progression_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
      ∀ (m : ℕ) [NeZero m] (r : (ZMod m)ˣ)
        (P δ c y U : ℝ) (J k a : ℕ),
        0 < P → 0 < δ → 0 < c → 1 < y → 0 < k → 0 ≤ U →
        (k : ℝ) * δ ≤ Real.log 2 →
        (∀ j < J,
          2 ≤ centeredBinFloor P δ a k j ∧
          (centeredBinFloor P δ a k (j + 1) : ℝ) ≤ y ∧
          1 ≤ δ * centeredBinEndpoint P δ a k j ∧
          K₁ * (1 + Real.log (3 * (centeredBinFloor P δ a k (j + 1) : ℝ))) ^ 2 *
            Real.sqrt (centeredBinFloor P δ a k (j + 1)) + 1 +
            (m.primeFactors.card : ℝ) * Real.log y ≤
              (1 - c) * δ * centeredBinEndpoint P δ a k j ∧
          2 * K₂ * (1 + Real.log (3 * m * centeredBinFloor P δ a k (j + 1))) ^ 2 *
            (centeredBinFloor P δ a k (j + 1) : ℝ) ≤
              U * (c * δ * centeredBinEndpoint P δ a k j / Real.log y)) →
        let Xstar := P ^ k
        let S := centeredBinProducts P δ J k a
        let S' := S.filter (·.Coprime m)
        let S_r := (S'.filter (fun n : ℕ ↦ (r : ZMod m) = (n : ZMod m))).card
        (∀ n ∈ S', Xstar ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Xstar) ∧
        |(S_r : ℝ) - (S'.card : ℝ) / m.totient| ≤ (U ^ k / Real.sqrt Xstar) * (S'.card : ℝ) ∧
        (1 / (m.totient : ℝ) - U ^ k / Real.sqrt Xstar) * (S'.card : ℝ) ≤ (S_r : ℝ) ∧
        (S_r : ℝ) ≤ (1 / (m.totient : ℝ) + U ^ k / Real.sqrt Xstar) * (S'.card : ℝ) := by
  obtain ⟨K₁, hK₁, hsup⟩ := primeBin_supply_from_critical_line line
  obtain ⟨K₂, hK₂, hprog⟩ := primePattern_pruned_progression_from_critical_line line
  refine ⟨K₁, K₂, hK₁, hK₂, ?_⟩
  intro m _ r P δ c y U J k a hP hδ hc hy hk hU hkδ hguard Xstar S S' S_r
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hstrip : ∀ n ∈ S', Xstar ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Xstar := by
    intro n hn
    have hmem := centeredBinProducts_mem_strip hP.le hk (Finset.mem_filter.mp hn).1
    have hexp : Real.exp ((k : ℝ) * δ) ≤ 2 := by
      calc
        Real.exp ((k : ℝ) * δ) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hkδ
        _ = 2 := Real.exp_log (by norm_num)
    exact ⟨hmem.1, hmem.2.trans (by
      have hPk : 0 ≤ P ^ k := pow_nonneg hP.le k
      nlinarith only [hexp, hPk])⟩
  let emb : Fin J ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let A_f (i : Fin J) : ℕ := centeredBinFloor P δ a k i.1
  let B_f (i : Fin J) : ℕ := centeredBinFloor P δ a k (i.1 + 1)
  let pat_f : Finset (Finset (Fin J)) :=
    ((Finset.univ : Finset (Fin J)).powersetCard k).filter fun s => (∑ i ∈ s, (i : ℕ)) = a
  have hdisj_f : Pairwise fun i j : Fin J ↦
      Disjoint (primeBin (A_f i) (B_f i)) (primeBin (A_f j) (B_f j)) :=
    fun i j hij => centeredBin_disjoint hP.le hδ.le a k (Fin.val_injective.ne hij)
  have hS_eq : S = primeBinPatternProducts A_f B_f pat_f := by
    ext n
    unfold S centeredBinProducts primeBinPatternProducts
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨s, hs, hn⟩
      obtain ⟨hset, hsum⟩ := Finset.mem_filter.mp hs
      obtain ⟨hsub, hsize⟩ := Finset.mem_powersetCard.mp hset
      let sf : Finset (Fin J) := Finset.univ.filter fun i : Fin J => (i : ℕ) ∈ s
      have hsf_map : sf.map emb = s := by
        ext x
        simp only [sf, emb, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact hi
        · intro hx
          exact ⟨⟨x, Finset.mem_range.mp (hsub hx)⟩, hx, rfl⟩
      have hsf_mem : sf ∈ pat_f := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
        · rw [← Finset.card_map emb, hsf_map, hsize]
        · rw [← hsf_map, Finset.sum_map] at hsum
          exact hsum
      refine ⟨sf, hsf_mem, ?_⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
      refine Finset.mem_image.mpr ⟨fun i : sf => p ⟨i.1.1, (Finset.mem_filter.mp i.2).2⟩, ?_, ?_⟩
      · apply Fintype.mem_piFinset.mpr
        intro i
        exact Fintype.mem_piFinset.mp hp ⟨i.1.1, (Finset.mem_filter.mp i.2).2⟩
      · let e : ↥sf ≃ ↥s :=
          { toFun := fun i => ⟨i.1.1, (Finset.mem_filter.mp i.2).2⟩
            invFun := fun x => ⟨⟨x.1, Finset.mem_range.mp (hsub x.2)⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
            left_inv := fun i => Subtype.ext (Fin.ext rfl)
            right_inv := fun x => Subtype.ext rfl }
        exact Fintype.prod_equiv e _ _ (fun _ => rfl)
    · rintro ⟨sf, hsf, hn⟩
      obtain ⟨hset, hsum⟩ := Finset.mem_filter.mp hsf
      have hsize : sf.card = k := (Finset.mem_powersetCard.mp hset).2
      let s : Finset ℕ := sf.map emb
      have hs_mem : s ∈ centeredBinPatterns J k a := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
        · intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
          exact Finset.mem_range.mpr i.2
        · rw [Finset.card_map, hsize]
        · simpa only [s, emb, Finset.sum_map, Function.Embedding.coeFn_mk] using hsum
      refine ⟨s, hs_mem, ?_⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
      let e : ↥sf ≃ ↥s :=
        { toFun := fun i => ⟨i.1.1, Finset.mem_map.mpr ⟨i.1, i.2, rfl⟩⟩
          invFun := fun x =>
            ⟨⟨x.1, by obtain ⟨i, _, hi⟩ := Finset.mem_map.mp x.2; exact hi ▸ i.2⟩,
              by
                obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp x.2
                have hfin : (⟨x.1, by obtain ⟨j, _, hj⟩ := Finset.mem_map.mp x.2; exact hj ▸ j.2⟩ : Fin J) = i :=
                  Fin.ext hix.symm
                rw [hfin]
                exact hi⟩
          left_inv := fun i => Subtype.ext (Fin.ext rfl)
          right_inv := fun x => Subtype.ext rfl }
      refine Finset.mem_image.mpr ⟨fun x : s => p (e.symm x), ?_, ?_⟩
      · apply Fintype.mem_piFinset.mpr
        intro x
        have hx := Fintype.mem_piFinset.mp hp (e.symm x)
        have hval : ((e.symm x).1 : ℕ) = (x : ℕ) := rfl
        simpa only [A_f, B_f, hval] using hx
      · exact Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
  have hpop_f (i : Fin J) :
      c * δ * centeredBinEndpoint P δ a k i.1 / Real.log y ≤
        (((primeBin (A_f i) (B_f i)).filter (·.Coprime m)).card : ℝ) := by
    obtain ⟨hA, hBy, _, hsup_g, _⟩ := hguard i.1 i.2
    have hAB : A_f i ≤ B_f i := centeredBinFloor_le_succ hP.le hδ.le a k i.1
    have hApos : 0 < A_f i := lt_of_lt_of_le (by decide) hA
    have hBpos : (0 : ℝ) < B_f i := Nat.cast_pos.mpr (lt_of_lt_of_le hApos hAB)
    have hwidth : δ * centeredBinEndpoint P δ a k i.1 - 1 ≤ (B_f i : ℝ) - A_f i :=
      centeredBin_width_le hP.le a k i.1
    have hsupply := hsup (A_f i) (B_f i) hA hAB
    have hlogB := Real.log_le_log hBpos hBy
    have hprune_card : ((primeBin (A_f i) (B_f i)).card : ℝ) ≤
        (((primeBin (A_f i) (B_f i)).filter (·.Coprime m)).card : ℝ) +
          (m.primeFactors.card : ℝ) := by
      exact_mod_cast primeBin_card_le_filter_coprime_add_primeFactors (A_f i) (B_f i) (NeZero.ne m)
    rw [div_le_iff₀ hlog]
    have hmul_prune : ((primeBin (A_f i) (B_f i)).card : ℝ) * Real.log y ≤
        (((primeBin (A_f i) (B_f i)).filter (·.Coprime m)).card : ℝ) * Real.log y +
          (m.primeFactors.card : ℝ) * Real.log y := by
      nlinarith only [hprune_card, hlog]
    have hmul_log : ((primeBin (A_f i) (B_f i)).card : ℝ) * Real.log (B_f i) ≤
        ((primeBin (A_f i) (B_f i)).card : ℝ) * Real.log y :=
      mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg _)
    linarith only [hwidth, hsup_g, hsupply, hmul_log, hmul_prune]
  have hscale_f (s : Finset (Fin J)) (hs : s ∈ pat_f) :
      Xstar ≤ ∏ i ∈ s, (B_f i : ℝ) := by
    obtain ⟨hset, hsum⟩ := Finset.mem_filter.mp hs
    have hsize : s.card = k := (Finset.mem_powersetCard.mp hset).2
    have hprod_end : (∏ i ∈ s, centeredBinEndpoint P δ a k i.1) = P ^ k := by
      have h1 := centeredBinEndpoint_product P δ hk (s.map emb) (by rw [Finset.card_map, hsize])
        (by simpa only [emb, Finset.sum_map, Function.Embedding.coeFn_mk] using hsum)
      simpa only [emb, Finset.prod_map, Function.Embedding.coeFn_mk] using h1
    rw [show Xstar = P ^ k from rfl, ← hprod_end]
    apply Finset.prod_le_prod (fun i _ => mul_nonneg hP.le (Real.exp_pos _).le)
    intro i _
    have h1 : 1 ≤ δ * centeredBinEndpoint P δ a k i.1 := (hguard i.1 i.2).2.2.1
    have hlo : 0 ≤ centeredBinEndpoint P δ a k i.1 := mul_nonneg hP.le (Real.exp_pos _).le
    have hgap := mul_le_mul_of_nonneg_left (Real.add_one_le_exp δ) hlo
    have hu := Nat.lt_floor_add_one (centeredBinEndpoint P δ a k (i.1 + 1))
    change centeredBinEndpoint P δ a k i.1 ≤ (Nat.floor (centeredBinEndpoint P δ a k (i.1 + 1)) : ℝ)
    nlinarith only [h1, hgap, hu, centeredBinEndpoint_succ_eq P δ a k i.1]
  have hprog_f := hprog m r A_f B_f pat_f k Xstar U (pow_pos hP k) hU hdisj_f
    (fun i => (hguard i.1 i.2).1)
    (fun i => centeredBinFloor_le_succ hP.le hδ.le a k i.1)
    (fun s hs => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).2)
    hscale_f
    (fun s _ i _ => (hguard i.1 i.2).2.2.2.2.trans (mul_le_mul_of_nonneg_left (hpop_f i) hU))
  refine ⟨hstrip, ?_⟩
  simpa only [S_r, S', hS_eq] using hprog_f

/-- Sharp-prefix one-point progression bound on `[X, 2X]` combining
`primeBin_relative_prefix_from_critical_line`, `primePattern_relative_prefix`,
and `Window.uniform_progression_bound`. -/
theorem primePattern_relative_prefix_progression_from_critical_line
    (line : DirichletLZerosOnLine) :
    ∃ C K E : ℝ, 0 < C ∧ 0 < K ∧ 0 ≤ E ∧
      ∀ (X : ℝ) (M m : ℕ) [NeZero m] (r : (ZMod m)ˣ)
        {ι : Type} [DecidableEq ι] (A B : ι → ℕ) (patterns : Finset (Finset ι))
        (k : ℕ) (U : ℝ),
        2 ≤ X → Real.exp 1 ≤ X →
        X ≤ (M : ℝ) + 1 / 2 → (M : ℝ) + 1 / 2 ≤ 2 * X →
        Pairwise (fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (∀ i, 2 ≤ A i) → (∀ i, A i < B i) →
        (∀ i, 2 * E * (1 + Real.log (3 * (B i : ℝ))) ^ 2 * Real.sqrt (B i) ≤
          (B i : ℝ) - A i) →
        0 ≤ U →
        (∀ i, 2 * C * (B i : ℝ) * (1 + Real.log (m * ((B i : ℝ) + X ^ 3 + 2))) ^ 3 *
          Real.log (B i) ≤ U * ((B i : ℝ) - A i)) →
        (∀ s ∈ patterns, s.card = k) →
        (∀ s ∈ patterns, X ≤ ∏ i ∈ s, (B i : ℝ)) →
        (∀ n ∈ primeBinPatternProducts A B patterns, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X) →
        let S := primeBinPatternProducts A B patterns
        let S_M := S.filter (· ≤ M)
        let err := ((4 * Real.exp 2 / Real.pi) * Real.log X * (U ^ k / Real.sqrt X) +
          K / X ^ 2) * (S.card : ℝ)
        |((S_M.filter (fun n : ℕ ↦ (r : ZMod m) = (n : ZMod m))).card : ℝ) -
          ((S_M.filter (·.Coprime m)).card : ℝ) / m.totient| ≤ err := by
  obtain ⟨C, K, E, hC, hK, hE, hrel⟩ := primeBin_relative_prefix_from_critical_line line
  refine ⟨C, K, E, hC, hK, hE, ?_⟩
  intro X M m _ r ι _ A B patterns k U hX heX hM1 hM2 hdisj hA hAB hwidth hU hslot hsize hscale
    hstrip S S_M err
  let R := (4 * Real.exp 2 / Real.pi) * Real.log X * (U ^ k / Real.sqrt X) + K / X ^ 2
  have hR : 0 ≤ R := by
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    dsimp only [R]
    positivity
  have herr_nonneg : 0 ≤ err := mul_nonneg hR (Nat.cast_nonneg _)
  have hχ (χ : DirichletCharacter ℂ m) (hne : χ ≠ 1) :
      ‖Window.twist S_M (fun _ ↦ 1) χ‖ ≤ err := by
    have htw : Window.twist S_M (fun _ ↦ 1) χ = ∑ n ∈ S_M, χ n := by
      simp [Window.twist]
    rw [htw]
    apply primePattern_relative_prefix A B patterns M (fun n => χ n) R hdisj
    intro s hs
    have hPsub : ∀ n ∈ primeBinProducts (fun i : s ↦ A i) (fun i ↦ B i),
        X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X :=
      fun n hn => hstrip n (Finset.mem_biUnion.mpr ⟨s, hs, hn⟩)
    have hcard_s : Fintype.card s = k := by rw [Fintype.card_coe, hsize s hs]
    have hscale_s : X ≤ ∏ i : s, (B i : ℝ) := by
      rw [Finset.prod_coe_sort s (fun i => (B i : ℝ))]
      exact hscale s hs
    have hb := hrel X M m χ hne (fun i : s ↦ A i) (fun i ↦ B i) U hX heX hM1 hM2 hPsub
      (fun _ _ hij => hdisj (Subtype.val_injective.ne hij))
      (fun i => hA i) (fun i => hAB i) (fun i => hwidth i) hscale_s hU (fun i => hslot i)
    simpa only [hcard_s, R] using hb
  have hmass : Window.classMass S_M (fun _ ↦ 1) r =
      ((S_M.filter (fun n : ℕ ↦ (r : ZMod m) = (n : ZMod m))).card : ℂ) := by
    simp [Window.classMass]
  have hprincipal : Window.twist S_M (fun _ ↦ 1) (1 : DirichletCharacter ℂ m) =
      ((S_M.filter (·.Coprime m)).card : ℂ) := by
    simp only [Window.twist, mul_one]
    have hunit (n : ℕ) : (1 : DirichletCharacter ℂ m) (n : ZMod m) =
        if n.Coprime m then 1 else 0 := by
      by_cases hn : n.Coprime m
      · rw [if_pos hn]
        exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n m).mpr hn)
      · rw [if_neg hn]
        exact MulChar.map_nonunit _ (fun h ↦ hn ((ZMod.isUnit_iff_coprime n m).mp h))
    simp_rw [hunit]
    simp
  have h := Window.uniform_progression_bound S_M (fun _ ↦ 1) err herr_nonneg hχ r
  rw [hmass, hprincipal, div_mul_eq_mul_div, mul_div_assoc, ← mul_sub, norm_mul] at h
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hreal : (m : ℝ) *
      |((S_M.filter (fun n : ℕ ↦ (r : ZMod m) = (n : ZMod m))).card : ℝ) -
        ((S_M.filter (·.Coprime m)).card : ℝ) / m.totient| ≤ (m : ℝ) * err := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm_pos] using h
  exact le_of_mul_le_mul_left hreal hm_pos

/-! ## Section 3: Multiplier-averaged coupled-mode Cauchy–Schwarz bound -/

/-- Multiplicative Cauchy–Schwarz form of `RandomizedMarginalModes.coupled_mode_sum`
obtained by optimal AM–GM rescaling. -/
theorem coupled_mode_cauchy_schwarz {Ω S A B : Type*} [Fintype S] [Fintype A] [Fintype B]
    (phases : Finset Ω) (w : Ω → ℝ) (hw : ∀ o ∈ phases, 0 ≤ w o)
    (i : S ↪ A) (j : S ↪ B) (f : Ω → A → ℝ) (g : Ω → B → ℝ)
    {E₁ E₂ : ℝ} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hf : ∑ o ∈ phases, w o * ∑ a, f o a ^ 2 ≤ E₁ ^ 2)
    (hg : ∑ o ∈ phases, w o * ∑ b, g o b ^ 2 ≤ E₂ ^ 2) :
    ∑ o ∈ phases, w o * ∑ s, f o (i s) * g o (j s) ≤ E₁ * E₂ := by
  rcases eq_or_lt_of_le hE₁ with rfl | hE₁pos
  · have hzero : ∑ o ∈ phases, w o * ∑ a, f o a ^ 2 = 0 :=
      le_antisymm (by simpa using hf)
        (Finset.sum_nonneg fun o ho =>
          mul_nonneg (hw o ho) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg fun o ho =>
      mul_nonneg (hw o ho) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp hzero
    have hsum0 : ∑ o ∈ phases, w o * ∑ s, f o (i s) * g o (j s) = 0 := by
      apply Finset.sum_eq_zero
      intro o ho
      rcases mul_eq_zero.mp (hterms o ho) with hwo | hfo
      · rw [hwo, zero_mul]
      · have hfa := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp hfo
        have hs0 : ∑ s, f o (i s) * g o (j s) = 0 :=
          Finset.sum_eq_zero fun s _ => by
            have : f o (i s) = 0 := sq_eq_zero_iff.mp (hfa (i s) (Finset.mem_univ _))
            rw [this, zero_mul]
        rw [hs0, mul_zero]
    linarith only [hsum0]
  · rcases eq_or_lt_of_le hE₂ with rfl | hE₂pos
    · have hzero : ∑ o ∈ phases, w o * ∑ b, g o b ^ 2 = 0 :=
        le_antisymm (by simpa using hg)
          (Finset.sum_nonneg fun o ho =>
            mul_nonneg (hw o ho) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      have hterms := (Finset.sum_eq_zero_iff_of_nonneg fun o ho =>
        mul_nonneg (hw o ho) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp hzero
      have hsum0 : ∑ o ∈ phases, w o * ∑ s, f o (i s) * g o (j s) = 0 := by
        apply Finset.sum_eq_zero
        intro o ho
        rcases mul_eq_zero.mp (hterms o ho) with hwo | hgo
        · rw [hwo, zero_mul]
        · have hgb := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp hgo
          have hs0 : ∑ s, f o (i s) * g o (j s) = 0 :=
            Finset.sum_eq_zero fun s _ => by
              have : g o (j s) = 0 := sq_eq_zero_iff.mp (hgb (j s) (Finset.mem_univ _))
              rw [this, mul_zero]
          rw [hs0, mul_zero]
      linarith only [hsum0]
    · have hcm := RandomizedMarginalModes.coupled_mode_sum phases w hw i j
        (fun o a => f o a / E₁) (fun o b => g o b / E₂)
      have hlhs : (∑ o ∈ phases, w o * ∑ s, (f o (i s) / E₁) * (g o (j s) / E₂)) =
          (∑ o ∈ phases, w o * ∑ s, f o (i s) * g o (j s)) / (E₁ * E₂) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro o _
        rw [mul_div_assoc, Finset.sum_div]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        ring
      have hrhs₁ : (∑ o ∈ phases, w o * ∑ a, (f o a / E₁) ^ 2) ≤ 1 := by
        have h1 : (∑ o ∈ phases, w o * ∑ a, (f o a / E₁) ^ 2) =
            (∑ o ∈ phases, w o * ∑ a, f o a ^ 2) / E₁ ^ 2 := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro o _
          rw [mul_div_assoc, Finset.sum_div]
          congr 1
          apply Finset.sum_congr rfl
          intro a _
          ring
        rw [h1, div_le_one (pow_pos hE₁pos 2)]
        exact hf
      have hrhs₂ : (∑ o ∈ phases, w o * ∑ b, (g o b / E₂) ^ 2) ≤ 1 := by
        have h2 : (∑ o ∈ phases, w o * ∑ b, (g o b / E₂) ^ 2) =
            (∑ o ∈ phases, w o * ∑ b, g o b ^ 2) / E₂ ^ 2 := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro o _
          rw [mul_div_assoc, Finset.sum_div]
          congr 1
          apply Finset.sum_congr rfl
          intro b _
          ring
        rw [h2, div_le_one (pow_pos hE₂pos 2)]
        exact hg
      rw [hlhs] at hcm
      have hdiv : (∑ o ∈ phases, w o * ∑ s, f o (i s) * g o (j s)) / (E₁ * E₂) ≤ 1 := by
        linarith only [hcm, hrhs₁, hrhs₂]
      exact (div_le_one (mul_pos hE₁pos hE₂pos)).mp hdiv

/-- The `k`-th prefix increment of `gridPrefixFourier` along a cutoff sequence `cut`. -/
noncomputable def gridPrefixIncrement {m B : ℕ} [NeZero B]
    (cop : m.Coprime B) (P : Finset ℕ) (cut : ℕ → ℕ)
    (k : ℕ) (x : GridCoordinate m B) : ℂ :=
  match k with
  | 0 => gridPrefixFourier cop P (cut 0) x
  | k + 1 => gridPrefixFourier cop P (cut (k + 1)) x - gridPrefixFourier cop P (cut k) x

theorem sum_gridPrefixIncrement {m B : ℕ} [NeZero B]
    (cop : m.Coprime B) (P : Finset ℕ) (cut : ℕ → ℕ)
    (i : ℕ) (x : GridCoordinate m B) :
    (∑ k ∈ Finset.range (i + 1), gridPrefixIncrement cop P cut k x) =
      gridPrefixFourier cop P (cut i) x := by
  induction i with
  | zero => simp [gridPrefixIncrement]
  | succ i ih =>
    rw [Finset.sum_range_succ, ih, gridPrefixIncrement]
    ring

/-- Rectangular Abel bound for a two-coordinate product array with bounded
1D prefix sums. -/
theorem norm_sum_prod_abel_le
    (N₁ N₂ : ℕ) (d₁ d₂ : ℕ → ℂ) (weight : ℕ → ℕ → ℂ) {P₁ P₂ V : ℝ}
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hrow : ∀ j, weight N₁ j = 0) (hcol : ∀ i, weight i N₂ = 0)
    (hd₁ : ∀ i < N₁, ‖∑ k ∈ Finset.range (i + 1), d₁ k‖ ≤ P₁)
    (hd₂ : ∀ j < N₂, ‖∑ l ∈ Finset.range (j + 1), d₂ l‖ ≤ P₂)
    (hV : (∑ i ∈ Finset.range N₁, ∑ j ∈ Finset.range N₂,
      ‖RandomizedRectangularAbel.mixedDifference weight i j‖) ≤ V) :
    ‖∑ i ∈ Finset.range N₁, ∑ j ∈ Finset.range N₂, (d₁ i * d₂ j) * weight i j‖ ≤
      V * (P₁ * P₂) := by
  have hrect : ∀ i < N₁, ∀ j < N₂,
      ‖RandomizedRectangularAbel.rectangularPrefix (fun k l => d₁ k * d₂ l) i j‖ ≤ P₁ * P₂ := by
    intro i hi j hj
    unfold RandomizedRectangularAbel.rectangularPrefix
    rw [← Finset.sum_mul_sum, norm_mul]
    exact mul_le_mul (hd₁ i hi) (hd₂ j hj) (norm_nonneg _) hP₁
  have habel := RandomizedRectangularAbel.norm_sum_le_prefix_bound_mul_variation
    N₁ N₂ (fun k l => d₁ k * d₂ l) weight (P₁ * P₂) hrow hcol hrect
  calc
    _ ≤ (P₁ * P₂) * (∑ i ∈ Finset.range N₁, ∑ j ∈ Finset.range N₂,
          ‖RandomizedRectangularAbel.mixedDifference weight i j‖) := habel
    _ ≤ (P₁ * P₂) * V := mul_le_mul_of_nonneg_left hV (mul_nonneg hP₁ hP₂)
    _ = V * (P₁ * P₂) := mul_comm _ _

private theorem grid_l2_sum_sq_le {m B : ℕ} [NeZero m] [NeZero B]
    (P : GridCoordinate m B → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hnorm : ‖(WithLp.toLp 2 P : EuclideanSpace ℝ (GridCoordinate m B))‖ ≤ L) :
    ∑ r : (ZMod m)ˣ, ∑ χ : AddChar (ZMod B) ℂ, P (r, χ) ^ 2 ≤ L ^ 2 := by
  rw [EuclideanSpace.norm_eq] at hnorm
  have hsq : ∑ x : GridCoordinate m B, ‖P x‖ ^ 2 ≤ L ^ 2 := by
    have hnonneg : 0 ≤ ∑ x : GridCoordinate m B, ‖P x‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h := (Real.sqrt_le_left hL).mp hnorm
    exact h
  simpa only [GridCoordinate, Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs] using hsq

/-- Exact two-coordinate multiplier-averaged off-zero Fourier error bound:
combines `RandomizedRectangularAbel.norm_sum_le_prefix_bound_mul_variation`,
`RandomizedMarginalModes.coupled_mode_sum` (via `coupled_mode_cauchy_schwarz`),
marginal domination `C_i / φ(m_i)`, injective frequency maps into nonzero
additive characters, and L2 prefix-supremum bounds `L_1, L_2`. -/
theorem averaged_coupled_abel_strip_bound
    {m₁ B₁ m₂ B₂ : ℕ} [NeZero m₁] [NeZero B₁] [NeZero m₂] [NeZero B₂]
    (cop₁ : m₁.Coprime B₁) (cop₂ : m₂.Coprime B₂)
    (strip₁ strip₂ : Finset ℕ)
    (cutoffs₁ cutoffs₂ : Finset ℕ) (hne₁ : cutoffs₁.Nonempty) (hne₂ : cutoffs₂.Nonempty)
    (cut₁ cut₂ : ℕ → ℕ) (N₁ N₂ : ℕ)
    (hcut₁ : ∀ i < N₁, cut₁ i ∈ cutoffs₁) (hcut₂ : ∀ j < N₂, cut₂ j ∈ cutoffs₂)
    (w : (ZMod m₁)ˣ × (ZMod m₂)ˣ → ℝ) (hw : ∀ p, 0 ≤ w p)
    {C₁ C₂ V L₁ L₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hV : 0 ≤ V) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hmarg₁ : ∀ r₁ : (ZMod m₁)ˣ, ∑ r₂ : (ZMod m₂)ˣ, w (r₁, r₂) ≤ C₁ / (m₁.totient : ℝ))
    (hmarg₂ : ∀ r₂ : (ZMod m₂)ˣ, ∑ r₁ : (ZMod m₁)ˣ, w (r₁, r₂) ≤ C₂ / (m₂.totient : ℝ))
    {S : Type*} [Fintype S]
    (a₁ : S ↪ {χ : AddChar (ZMod B₁) ℂ // χ ≠ 0})
    (a₂ : S ↪ {χ : AddChar (ZMod B₂) ℂ // χ ≠ 0})
    (weight : (ZMod m₁)ˣ × (ZMod m₂)ˣ → S → ℕ → ℕ → ℂ)
    (hrow : ∀ p s j, weight p s N₁ j = 0)
    (hcol : ∀ p s i, weight p s i N₂ = 0)
    (hvar : ∀ p s,
      (∑ i ∈ Finset.range N₁, ∑ j ∈ Finset.range N₂,
        ‖RandomizedRectangularAbel.mixedDifference (weight p s) i j‖) ≤ V)
    (hL2₁ : ‖(WithLp.toLp 2 (fun x : GridCoordinate m₁ B₁ =>
      cutoffs₁.sup' hne₁ (fun j => ‖gridPrefixFourier cop₁ strip₁ j x‖)) :
        EuclideanSpace ℝ (GridCoordinate m₁ B₁))‖ ≤ L₁)
    (hL2₂ : ‖(WithLp.toLp 2 (fun x : GridCoordinate m₂ B₂ =>
      cutoffs₂.sup' hne₂ (fun j => ‖gridPrefixFourier cop₂ strip₂ j x‖)) :
        EuclideanSpace ℝ (GridCoordinate m₂ B₂))‖ ≤ L₂) :
    ∑ p : (ZMod m₁)ˣ × (ZMod m₂)ˣ, w p *
      ∑ s : S,
        ‖∑ i ∈ Finset.range N₁, ∑ j ∈ Finset.range N₂,
          (gridPrefixIncrement cop₁ strip₁ cut₁ i (p.1, (a₁ s).1) *
           gridPrefixIncrement cop₂ strip₂ cut₂ j (p.2, (a₂ s).1)) *
          weight p s i j‖ ≤
      Real.sqrt (C₁ * C₂) * V * (L₁ * L₂) /
        Real.sqrt ((m₁.totient : ℝ) * (m₂.totient : ℝ)) := by
  let P₁ (x : GridCoordinate m₁ B₁) : ℝ :=
    cutoffs₁.sup' hne₁ (fun j => ‖gridPrefixFourier cop₁ strip₁ j x‖)
  let P₂ (x : GridCoordinate m₂ B₂) : ℝ :=
    cutoffs₂.sup' hne₂ (fun j => ‖gridPrefixFourier cop₂ strip₂ j x‖)
  have hP₁_nonneg (x : GridCoordinate m₁ B₁) : 0 ≤ P₁ x := by
    obtain ⟨j₀, hj₀⟩ := hne₁
    exact (norm_nonneg _).trans (Finset.le_sup' (fun j => ‖gridPrefixFourier cop₁ strip₁ j x‖) hj₀)
  have hP₂_nonneg (x : GridCoordinate m₂ B₂) : 0 ≤ P₂ x := by
    obtain ⟨j₀, hj₀⟩ := hne₂
    exact (norm_nonneg _).trans (Finset.le_sup' (fun j => ‖gridPrefixFourier cop₂ strip₂ j x‖) hj₀)
  have hpoint (p : (ZMod m₁)ˣ × (ZMod m₂)ˣ) (s : S) :
      ‖∑ i ∈ Finset.range N₁, ∑ j ∈ Finset.range N₂,
        (gridPrefixIncrement cop₁ strip₁ cut₁ i (p.1, (a₁ s).1) *
         gridPrefixIncrement cop₂ strip₂ cut₂ j (p.2, (a₂ s).1)) *
        weight p s i j‖ ≤ V * (P₁ (p.1, (a₁ s).1) * P₂ (p.2, (a₂ s).1)) := by
    refine norm_sum_prod_abel_le N₁ N₂
      (fun i => gridPrefixIncrement cop₁ strip₁ cut₁ i (p.1, (a₁ s).1))
      (fun j => gridPrefixIncrement cop₂ strip₂ cut₂ j (p.2, (a₂ s).1))
      (weight p s) (hP₁_nonneg _) (hP₂_nonneg _) (hrow p s) (hcol p s) ?_ ?_ (hvar p s)
    · intro i hi
      rw [sum_gridPrefixIncrement]
      exact Finset.le_sup' (fun j => ‖gridPrefixFourier cop₁ strip₁ j (p.1, (a₁ s).1)‖) (hcut₁ i hi)
    · intro j hj
      rw [sum_gridPrefixIncrement]
      exact Finset.le_sup' (fun k => ‖gridPrefixFourier cop₂ strip₂ k (p.2, (a₂ s).1)‖) (hcut₂ j hj)
  have hstep1 :
      (∑ p : (ZMod m₁)ˣ × (ZMod m₂)ˣ, w p *
        ∑ s : S,
          ‖∑ i ∈ Finset.range N₁, ∑ j ∈ Finset.range N₂,
            (gridPrefixIncrement cop₁ strip₁ cut₁ i (p.1, (a₁ s).1) *
             gridPrefixIncrement cop₂ strip₂ cut₂ j (p.2, (a₂ s).1)) *
            weight p s i j‖) ≤
      V * ∑ p : (ZMod m₁)ˣ × (ZMod m₂)ˣ, w p *
        ∑ s : S, P₁ (p.1, (a₁ s).1) * P₂ (p.2, (a₂ s).1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    rw [mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (hw p)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun s _ => hpoint p s
  have hφ₁ : (0 : ℝ) < (m₁.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos m₁))
  have hφ₂ : (0 : ℝ) < (m₂.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos m₂))
  let E₁ : ℝ := Real.sqrt C₁ * L₁ / Real.sqrt (m₁.totient : ℝ)
  let E₂ : ℝ := Real.sqrt C₂ * L₂ / Real.sqrt (m₂.totient : ℝ)
  have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp [E₂]; positivity
  have hf_bound :
      ∑ p : (ZMod m₁)ˣ × (ZMod m₂)ˣ, w p * ∑ χ : AddChar (ZMod B₁) ℂ, P₁ (p.1, χ) ^ 2 ≤ E₁ ^ 2 := by
    have hE₁sq : E₁ ^ 2 = (C₁ / (m₁.totient : ℝ)) * L₁ ^ 2 := by
      dsimp only [E₁]
      rw [div_pow, mul_pow, Real.sq_sqrt hC₁, Real.sq_sqrt hφ₁.le]
      ring
    rw [hE₁sq]
    calc
      ∑ p : (ZMod m₁)ˣ × (ZMod m₂)ˣ, w p * ∑ χ : AddChar (ZMod B₁) ℂ, P₁ (p.1, χ) ^ 2
          = ∑ r₁ : (ZMod m₁)ˣ, ∑ r₂ : (ZMod m₂)ˣ,
              w (r₁, r₂) * ∑ χ : AddChar (ZMod B₁) ℂ, P₁ (r₁, χ) ^ 2 :=
            Fintype.sum_prod_type _
      _ = ∑ r₁ : (ZMod m₁)ˣ, (∑ r₂ : (ZMod m₂)ˣ, w (r₁, r₂)) *
              ∑ χ : AddChar (ZMod B₁) ℂ, P₁ (r₁, χ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro r₁ _
            rw [← Finset.sum_mul]
      _ ≤ ∑ r₁ : (ZMod m₁)ˣ, (C₁ / (m₁.totient : ℝ)) *
              ∑ χ : AddChar (ZMod B₁) ℂ, P₁ (r₁, χ) ^ 2 :=
            Finset.sum_le_sum fun r₁ _ =>
              mul_le_mul_of_nonneg_right (hmarg₁ r₁) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = (C₁ / (m₁.totient : ℝ)) *
            ∑ r₁ : (ZMod m₁)ˣ, ∑ χ : AddChar (ZMod B₁) ℂ, P₁ (r₁, χ) ^ 2 := by
            rw [← Finset.mul_sum]
      _ ≤ (C₁ / (m₁.totient : ℝ)) * L₁ ^ 2 :=
            mul_le_mul_of_nonneg_left (grid_l2_sum_sq_le P₁ hL₁ hL2₁) (div_nonneg hC₁ hφ₁.le)
  have hg_bound :
      ∑ p : (ZMod m₁)ˣ × (ZMod m₂)ˣ, w p * ∑ χ : AddChar (ZMod B₂) ℂ, P₂ (p.2, χ) ^ 2 ≤ E₂ ^ 2 := by
    have hE₂sq : E₂ ^ 2 = (C₂ / (m₂.totient : ℝ)) * L₂ ^ 2 := by
      dsimp only [E₂]
      rw [div_pow, mul_pow, Real.sq_sqrt hC₂, Real.sq_sqrt hφ₂.le]
      ring
    rw [hE₂sq]
    calc
      ∑ p : (ZMod m₁)ˣ × (ZMod m₂)ˣ, w p * ∑ χ : AddChar (ZMod B₂) ℂ, P₂ (p.2, χ) ^ 2
          = ∑ r₁ : (ZMod m₁)ˣ, ∑ r₂ : (ZMod m₂)ˣ,
              w (r₁, r₂) * ∑ χ : AddChar (ZMod B₂) ℂ, P₂ (r₂, χ) ^ 2 :=
            Fintype.sum_prod_type _
      _ = ∑ r₂ : (ZMod m₂)ˣ, ∑ r₁ : (ZMod m₁)ˣ,
              w (r₁, r₂) * ∑ χ : AddChar (ZMod B₂) ℂ, P₂ (r₂, χ) ^ 2 :=
            Finset.sum_comm
      _ = ∑ r₂ : (ZMod m₂)ˣ, (∑ r₁ : (ZMod m₁)ˣ, w (r₁, r₂)) *
              ∑ χ : AddChar (ZMod B₂) ℂ, P₂ (r₂, χ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro r₂ _
            rw [← Finset.sum_mul]
      _ ≤ ∑ r₂ : (ZMod m₂)ˣ, (C₂ / (m₂.totient : ℝ)) *
              ∑ χ : AddChar (ZMod B₂) ℂ, P₂ (r₂, χ) ^ 2 :=
            Finset.sum_le_sum fun r₂ _ =>
              mul_le_mul_of_nonneg_right (hmarg₂ r₂) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = (C₂ / (m₂.totient : ℝ)) *
            ∑ r₂ : (ZMod m₂)ˣ, ∑ χ : AddChar (ZMod B₂) ℂ, P₂ (r₂, χ) ^ 2 := by
            rw [← Finset.mul_sum]
      _ ≤ (C₂ / (m₂.totient : ℝ)) * L₂ ^ 2 :=
            mul_le_mul_of_nonneg_left (grid_l2_sum_sq_le P₂ hL₂ hL2₂) (div_nonneg hC₂ hφ₂.le)
  let emb₁ : S ↪ AddChar (ZMod B₁) ℂ := a₁.trans (Function.Embedding.subtype _)
  let emb₂ : S ↪ AddChar (ZMod B₂) ℂ := a₂.trans (Function.Embedding.subtype _)
  have hcs := coupled_mode_cauchy_schwarz Finset.univ w (fun p _ => hw p) emb₁ emb₂
    (fun p χ => P₁ (p.1, χ)) (fun p χ => P₂ (p.2, χ)) hE₁ hE₂ hf_bound hg_bound
  have hstep2 : V * (E₁ * E₂) =
      Real.sqrt (C₁ * C₂) * V * (L₁ * L₂) / Real.sqrt ((m₁.totient : ℝ) * (m₂.totient : ℝ)) := by
    dsimp only [E₁, E₂]
    rw [Real.sqrt_mul hC₁ C₂, Real.sqrt_mul hφ₁.le (m₂.totient : ℝ)]
    ring
  exact hstep1.trans ((mul_le_mul_of_nonneg_left hcs hV).trans_eq hstep2)

/-- Full GRH two-coordinate averaged off-zero Fourier error bound combining
`primeBinProducts_gridPrefix_from_critical_line`, `RandomizedMarginalModes.coupled_mode_sum`,
and `RandomizedRectangularAbel.norm_sum_le_prefix_bound_mul_variation`. -/
theorem primeBinProducts_averaged_coupled_abel_from_critical_line
    {m₁ B₁ m₂ B₂ : ℕ} [NeZero m₁] [NeZero B₁] [NeZero (m₁ * B₁)]
    [NeZero m₂] [NeZero B₂] [NeZero (m₂ * B₂)]
    (line : DirichletLZerosOnLine) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (cop₁ : m₁.Coprime B₁) (cop₂ : m₂.Coprime B₂)
        (X₁ X₂ : ℝ)
        (cutoffs₁ cutoffs₂ : Finset ℕ) (cut₁ cut₂ : ℕ → ℕ) (N₁ N₂ : ℕ)
        {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
        (A₁ U₁ : ι₁ → ℕ) (A₂ U₂ : ι₂ → ℕ)
        (w : (ZMod m₁)ˣ × (ZMod m₂)ˣ → ℝ)
        (C₁ C₂ V : ℝ)
        {S : Type*} [Fintype S]
        (a₁ : S ↪ {χ : AddChar (ZMod B₁) ℂ // χ ≠ 0})
        (a₂ : S ↪ {χ : AddChar (ZMod B₂) ℂ // χ ≠ 0})
        (weight : (ZMod m₁)ˣ × (ZMod m₂)ˣ → S → ℕ → ℕ → ℂ),
        cutoffs₁.Nonempty → cutoffs₂.Nonempty →
        2 ≤ X₁ → Real.exp 1 ≤ X₁ → 2 ≤ X₂ → Real.exp 1 ≤ X₂ →
        (∀ j ∈ cutoffs₁, X₁ ≤ (j : ℝ) + 1 / 2 ∧ (j : ℝ) + 1 / 2 ≤ 2 * X₁) →
        (∀ j ∈ cutoffs₂, X₂ ≤ (j : ℝ) + 1 / 2 ∧ (j : ℝ) + 1 / 2 ≤ 2 * X₂) →
        (∀ i < N₁, cut₁ i ∈ cutoffs₁) → (∀ j < N₂, cut₂ j ∈ cutoffs₂) →
        (∀ n ∈ primeBinProducts A₁ U₁, X₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X₁) →
        (∀ n ∈ primeBinProducts A₂ U₂, X₂ ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X₂) →
        (∀ i, 2 ≤ U₁ i) → (∀ i, A₁ i ≤ U₁ i) →
        (Pairwise fun i j ↦ Disjoint (primeBin (A₁ i) (U₁ i)) (primeBin (A₁ j) (U₁ j))) →
        (∀ i, 2 ≤ U₂ i) → (∀ i, A₂ i ≤ U₂ i) →
        (Pairwise fun i j ↦ Disjoint (primeBin (A₂ i) (U₂ i)) (primeBin (A₂ j) (U₂ j))) →
        (∀ p, 0 ≤ w p) → 0 ≤ C₁ → 0 ≤ C₂ → 0 ≤ V →
        (∀ r₁ : (ZMod m₁)ˣ, ∑ r₂ : (ZMod m₂)ˣ, w (r₁, r₂) ≤ C₁ / (m₁.totient : ℝ)) →
        (∀ r₂ : (ZMod m₂)ˣ, ∑ r₁ : (ZMod m₁)ˣ, w (r₁, r₂) ≤ C₂ / (m₂.totient : ℝ)) →
        (∀ p s j, weight p s N₁ j = 0) →
        (∀ p s i, weight p s i N₂ = 0) →
        (∀ p s,
          (∑ i ∈ Finset.range N₁, ∑ j ∈ Finset.range N₂,
            ‖RandomizedRectangularAbel.mixedDifference (weight p s) i j‖) ≤ V) →
        let L₁ := Real.sqrt B₁ * ((4 * Real.exp 2 / Real.pi) *
          ((∏ i, C * Real.sqrt (U₁ i) * (1 + Real.log ((m₁ * B₁ : ℕ) *
            ((U₁ i : ℝ) + X₁ ^ 3 + 2))) ^ 3) * Real.log X₁) +
          (2 * K / X₁ ^ 2) * (primeBinProducts A₁ U₁).card)
        let L₂ := Real.sqrt B₂ * ((4 * Real.exp 2 / Real.pi) *
          ((∏ i, C * Real.sqrt (U₂ i) * (1 + Real.log ((m₂ * B₂ : ℕ) *
            ((U₂ i : ℝ) + X₂ ^ 3 + 2))) ^ 3) * Real.log X₂) +
          (2 * K / X₂ ^ 2) * (primeBinProducts A₂ U₂).card)
        ∑ p : (ZMod m₁)ˣ × (ZMod m₂)ˣ, w p *
          ∑ s : S,
            ‖∑ i ∈ Finset.range N₁, ∑ j ∈ Finset.range N₂,
              (gridPrefixIncrement cop₁ (primeBinProducts A₁ U₁) cut₁ i (p.1, (a₁ s).1) *
               gridPrefixIncrement cop₂ (primeBinProducts A₂ U₂) cut₂ j (p.2, (a₂ s).1)) *
              weight p s i j‖ ≤
          Real.sqrt (C₁ * C₂) * V * (L₁ * L₂) /
            Real.sqrt ((m₁.totient : ℝ) * (m₂.totient : ℝ)) := by
  obtain ⟨c₁, k₁, hc₁, hk₁, hgrid₁⟩ :=
    primeBinProducts_gridPrefix_from_critical_line (m := m₁) (B := B₁) line
  obtain ⟨c₂, k₂, hc₂, hk₂, hgrid₂⟩ :=
    primeBinProducts_gridPrefix_from_critical_line (m := m₂) (B := B₂) line
  let C := max c₁ c₂
  let K := max k₁ k₂
  have hC : 0 < C := lt_of_lt_of_le hc₁ (le_max_left _ _)
  have hK : 0 < K := lt_of_lt_of_le hk₁ (le_max_left _ _)
  refine ⟨C, K, hC, hK, ?_⟩
  intro cop₁ cop₂ X₁ X₂ cutoffs₁ cutoffs₂ cut₁ cut₂ N₁ N₂
    ι₁ ι₂ _ _ _ _ A₁ U₁ A₂ U₂ w C₁ C₂ V S _ a₁ a₂ weight
    hne₁ hne₂ hX₁ heX₁ hX₂ heX₂ hcutoffs₁ hcutoffs₂ hcut₁ hcut₂ hP₁ hP₂
    hU₁ hAU₁ hdisj₁ hU₂ hAU₂ hdisj₂ hw hC₁ hC₂ hV hmarg₁ hmarg₂ hrow hcol hvar L₁ L₂
  have hlog_nonneg {m B : ℕ} [NeZero (m * B)] {X : ℝ} (hX : 2 ≤ X) (u : ℕ) :
      0 ≤ Real.log ((m * B : ℕ) * ((u : ℝ) + X ^ 3 + 2)) := by
    apply Real.log_nonneg
    apply one_le_mul_of_one_le_of_one_le (by exact_mod_cast (NeZero.one_le : 1 ≤ m * B))
    have hX3 : 0 ≤ X ^ 3 := by positivity
    linarith [Nat.cast_nonneg (α := ℝ) u]
  have hL₁_nonneg : 0 ≤ L₁ := by
    have hlogX₁ : 0 ≤ Real.log X₁ := Real.log_nonneg (by linarith)
    have hprod₁ : 0 ≤ ∏ i, C * Real.sqrt (U₁ i) *
        (1 + Real.log ((m₁ * B₁ : ℕ) * ((U₁ i : ℝ) + X₁ ^ 3 + 2))) ^ 3 :=
      Finset.prod_nonneg fun i _ => by have := hlog_nonneg (m := m₁) (B := B₁) hX₁ (U₁ i); positivity
    dsimp only [L₁]
    positivity
  have hL₂_nonneg : 0 ≤ L₂ := by
    have hlogX₂ : 0 ≤ Real.log X₂ := Real.log_nonneg (by linarith)
    have hprod₂ : 0 ≤ ∏ i, C * Real.sqrt (U₂ i) *
        (1 + Real.log ((m₂ * B₂ : ℕ) * ((U₂ i : ℝ) + X₂ ^ 3 + 2))) ^ 3 :=
      Finset.prod_nonneg fun i _ => by have := hlog_nonneg (m := m₂) (B := B₂) hX₂ (U₂ i); positivity
    dsimp only [L₂]
    positivity
  have hb₁ : ‖(WithLp.toLp 2 (fun x : GridCoordinate m₁ B₁ =>
      cutoffs₁.sup' hne₁ (fun j => ‖gridPrefixFourier cop₁ (primeBinProducts A₁ U₁) j x‖)) :
        EuclideanSpace ℝ (GridCoordinate m₁ B₁))‖ ≤ L₁ := by
    refine (hgrid₁ cop₁ X₁ cutoffs₁ hne₁ A₁ U₁ hX₁ heX₁ hcutoffs₁ hP₁ hU₁ hAU₁ hdisj₁).trans ?_
    have hlogX₁ : 0 ≤ Real.log X₁ := Real.log_nonneg (by linarith)
    have hprod_le :
        (∏ i, c₁ * Real.sqrt (U₁ i) *
          (1 + Real.log ((m₁ * B₁ : ℕ) * ((U₁ i : ℝ) + X₁ ^ 3 + 2))) ^ 3) ≤
        ∏ i, C * Real.sqrt (U₁ i) *
          (1 + Real.log ((m₁ * B₁ : ℕ) * ((U₁ i : ℝ) + X₁ ^ 3 + 2))) ^ 3 := by
      apply Finset.prod_le_prod
      · intro i _
        have := hlog_nonneg (m := m₁) (B := B₁) hX₁ (U₁ i)
        positivity
      · intro i _
        have := hlog_nonneg (m := m₁) (B := B₁) hX₁ (U₁ i)
        have hcle : c₁ ≤ C := le_max_left _ _
        gcongr
    have hkle : k₁ ≤ K := le_max_left _ _
    dsimp only [L₁]
    gcongr
  have hb₂ : ‖(WithLp.toLp 2 (fun x : GridCoordinate m₂ B₂ =>
      cutoffs₂.sup' hne₂ (fun j => ‖gridPrefixFourier cop₂ (primeBinProducts A₂ U₂) j x‖)) :
        EuclideanSpace ℝ (GridCoordinate m₂ B₂))‖ ≤ L₂ := by
    refine (hgrid₂ cop₂ X₂ cutoffs₂ hne₂ A₂ U₂ hX₂ heX₂ hcutoffs₂ hP₂ hU₂ hAU₂ hdisj₂).trans ?_
    have hlogX₂ : 0 ≤ Real.log X₂ := Real.log_nonneg (by linarith)
    have hprod_le :
        (∏ i, c₂ * Real.sqrt (U₂ i) *
          (1 + Real.log ((m₂ * B₂ : ℕ) * ((U₂ i : ℝ) + X₂ ^ 3 + 2))) ^ 3) ≤
        ∏ i, C * Real.sqrt (U₂ i) *
          (1 + Real.log ((m₂ * B₂ : ℕ) * ((U₂ i : ℝ) + X₂ ^ 3 + 2))) ^ 3 := by
      apply Finset.prod_le_prod
      · intro i _
        have := hlog_nonneg (m := m₂) (B := B₂) hX₂ (U₂ i)
        positivity
      · intro i _
        have := hlog_nonneg (m := m₂) (B := B₂) hX₂ (U₂ i)
        have hcle : c₂ ≤ C := le_max_right _ _
        gcongr
    have hkle : k₂ ≤ K := le_max_right _ _
    dsimp only [L₂]
    gcongr
  exact averaged_coupled_abel_strip_bound cop₁ cop₂
    (primeBinProducts A₁ U₁) (primeBinProducts A₂ U₂)
    cutoffs₁ cutoffs₂ hne₁ hne₂ cut₁ cut₂ N₁ N₂ hcut₁ hcut₂
    w hw hC₁ hC₂ hV hL₁_nonneg hL₂_nonneg hmarg₁ hmarg₂
    a₁ a₂ weight hrow hcol hvar hb₁ hb₂

/-! ## Section 4: Ratio-expectation and pruned-prime restoration inequalities -/

/-- Expectation of a Poisson quotient `(Z_k + E_k) / (1 + A_k)` when `Z_k ≥ 0`
and `|A_k| ≤ δ < 1` uniformly across multipliers `k`. -/
theorem ratio_expectation_le {ι : Type*} (K : Finset ι) (w Z E A : ι → ℝ) {δ : ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (hZ : ∀ k ∈ K, 0 ≤ Z k)
    (hA : ∀ k ∈ K, |A k| ≤ δ) (hδ : δ < 1) :
    ∑ k ∈ K, w k * ((Z k + E k) / (1 + A k)) ≤
      (1 / (1 - δ)) * ((∑ k ∈ K, w k * Z k) + ∑ k ∈ K, w k * |E k|) := by
  have h1δ : 0 < 1 - δ := sub_pos.mpr hδ
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hAk : 1 - δ ≤ 1 + A k := by
    have := (abs_le.mp (hA k hk)).1
    linarith only [this]
  have h1A : 0 < 1 + A k := lt_of_lt_of_le h1δ hAk
  have hnum_le : Z k + E k ≤ Z k + |E k| := add_le_add le_rfl (le_abs_self (E k))
  have hnum_nonneg : 0 ≤ Z k + |E k| := add_nonneg (hZ k hk) (abs_nonneg (E k))
  have hfrac : (Z k + E k) / (1 + A k) ≤ (1 / (1 - δ)) * (Z k + |E k|) := by
    calc
      (Z k + E k) / (1 + A k) ≤ (Z k + |E k|) / (1 + A k) :=
        div_le_div_of_nonneg_right hnum_le h1A.le
      _ ≤ (Z k + |E k|) / (1 - δ) :=
        div_le_div_of_nonneg_left hnum_nonneg h1δ hAk
      _ = (1 / (1 - δ)) * (Z k + |E k|) := by ring
  calc
    w k * ((Z k + E k) / (1 + A k))
        ≤ w k * ((1 / (1 - δ)) * (Z k + |E k|)) := mul_le_mul_of_nonneg_left hfrac (hw k hk)
    _ = (1 / (1 - δ)) * (w k * Z k + w k * |E k|) := by ring

/-- Specialized version with probability weights `∑ w k = 1` and a uniform
error bound `|E k| ≤ ε`. -/
theorem ratio_expectation_le_of_prob {ι : Type*} (K : Finset ι) (w Z E A : ι → ℝ) {δ ε : ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (hw_sum : ∑ k ∈ K, w k = 1)
    (hZ : ∀ k ∈ K, 0 ≤ Z k) (hA : ∀ k ∈ K, |A k| ≤ δ) (hδ : δ < 1)
    (hE : ∀ k ∈ K, |E k| ≤ ε) :
    ∑ k ∈ K, w k * ((Z k + E k) / (1 + A k)) ≤
      (1 / (1 - δ)) * ((∑ k ∈ K, w k * Z k) + ε) := by
  have h1δ : 0 < 1 - δ := sub_pos.mpr hδ
  refine (ratio_expectation_le K w Z E A hw hZ hA hδ).trans ?_
  have hEsum : ∑ k ∈ K, w k * |E k| ≤ ε := by
    calc
      ∑ k ∈ K, w k * |E k| ≤ ∑ k ∈ K, w k * ε :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hE k hk) (hw k hk)
      _ = (∑ k ∈ K, w k) * ε := (Finset.sum_mul _ _ _).symm
      _ = ε := by rw [hw_sum, one_mul]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hEsum) (by positivity)

/-- Every integer removed by coprimality pruning modulo `m ≠ 0` is divisible by
some prime factor in `m.primeFactors`. -/
theorem coprime_pruning_witness (S : Finset ℕ) {m : ℕ} (hm : m ≠ 0) :
    ∀ n ∈ S, n ∉ S.filter (·.Coprime m) → ∃ p ∈ m.primeFactors, p ∣ n := by
  intro n hn hnot
  have hncop : ¬ n.Coprime m := fun h => hnot (Finset.mem_filter.mpr ⟨hn, h⟩)
  have hgcd : Nat.gcd n m ≠ 1 := hncop
  refine ⟨Nat.minFac (Nat.gcd n m), ?_, (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left n m)⟩
  exact Nat.mem_primeFactors.mpr
    ⟨Nat.minFac_prime hgcd, (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right n m), hm⟩

/-- Exact pruned-prime restoration lemma for finite weighted joint pair events:
restoring a set `removed` of pruned primes increases the joint pair probability
by at most the sum of one-point divisibility probabilities across `removed`. -/
theorem pruned_prime_pair_restoration_weighted {α : Type*} (Ω : Finset α) (w : α → ℝ)
    (hw : ∀ ω ∈ Ω, 0 ≤ w ω) (X₁ X₂ : α → ℕ)
    (S S' removed : Finset ℕ)
    (hprune : ∀ n ∈ S, n ∉ S' → ∃ p ∈ removed, p ∣ n) :
    (∑ ω ∈ Ω.filter (fun ω => X₁ ω ∈ S ∧ X₂ ω ∈ S), w ω) ≤
      (∑ ω ∈ Ω.filter (fun ω => X₁ ω ∈ S' ∧ X₂ ω ∈ S'), w ω) +
        ∑ p ∈ removed,
          ((∑ ω ∈ Ω.filter (fun ω => p ∣ X₁ ω), w ω) +
           (∑ ω ∈ Ω.filter (fun ω => p ∣ X₂ ω), w ω)) := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_add_distrib, Finset.sum_comm (s := removed), Finset.sum_comm (s := removed),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω hω
  have hwω : 0 ≤ w ω := hw ω hω
  have hsum_nonneg₁ : 0 ≤ ∑ p ∈ removed, if p ∣ X₁ ω then w ω else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> linarith
  have hsum_nonneg₂ : 0 ≤ ∑ p ∈ removed, if p ∣ X₂ ω then w ω else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> linarith
  by_cases hS : X₁ ω ∈ S ∧ X₂ ω ∈ S
  · rw [if_pos hS]
    by_cases hS' : X₁ ω ∈ S' ∧ X₂ ω ∈ S'
    · rw [if_pos hS']
      linarith only [hsum_nonneg₁, hsum_nonneg₂]
    · rw [if_neg hS', zero_add]
      by_cases h1 : X₁ ω ∈ S'
      · have h2 : X₂ ω ∉ S' := fun h => hS' ⟨h1, h⟩
        obtain ⟨p, hp, hpdvd⟩ := hprune (X₂ ω) hS.2 h2
        have hle : w ω ≤ ∑ q ∈ removed, if q ∣ X₂ ω then w ω else 0 := by
          have := Finset.single_le_sum (f := fun q => if q ∣ X₂ ω then w ω else 0)
            (fun q _ => by split_ifs <;> linarith) hp
          simpa only [if_pos hpdvd] using this
        linarith only [hle, hsum_nonneg₁]
      · obtain ⟨p, hp, hpdvd⟩ := hprune (X₁ ω) hS.1 h1
        have hle : w ω ≤ ∑ q ∈ removed, if q ∣ X₁ ω then w ω else 0 := by
          have := Finset.single_le_sum (f := fun q => if q ∣ X₁ ω then w ω else 0)
            (fun q _ => by split_ifs <;> linarith) hp
          simpa only [if_pos hpdvd] using this
        linarith only [hle, hsum_nonneg₂]
  · rw [if_neg hS]
    have hS'_nonneg : 0 ≤ if X₁ ω ∈ S' ∧ X₂ ω ∈ S' then w ω else 0 := by
      split_ifs <;> linarith
    linarith only [hS'_nonneg, hsum_nonneg₁, hsum_nonneg₂]

/-- Exact pruned-prime restoration lemma in measure-theoretic form. -/
theorem pruned_prime_pair_restoration_measure {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (X₁ X₂ : α → ℕ)
    (S S' removed : Finset ℕ)
    (hprune : ∀ n ∈ S, n ∉ S' → ∃ p ∈ removed, p ∣ n) :
    μ {ω | X₁ ω ∈ S ∧ X₂ ω ∈ S} ≤
      μ {ω | X₁ ω ∈ S' ∧ X₂ ω ∈ S'} +
        ∑ p ∈ removed, (μ {ω | p ∣ X₁ ω} + μ {ω | p ∣ X₂ ω}) := by
  have hsub : {ω | X₁ ω ∈ S ∧ X₂ ω ∈ S} ⊆
      {ω | X₁ ω ∈ S' ∧ X₂ ω ∈ S'} ∪
        (⋃ p ∈ removed, ({ω | p ∣ X₁ ω} ∪ {ω | p ∣ X₂ ω})) := by
    intro ω hω
    by_cases hS' : X₁ ω ∈ S' ∧ X₂ ω ∈ S'
    · exact Or.inl hS'
    · refine Or.inr ?_
      simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq]
      by_cases h1 : X₁ ω ∈ S'
      · obtain ⟨p, hp, hpdvd⟩ := hprune (X₂ ω) hω.2 (fun h => hS' ⟨h1, h⟩)
        exact ⟨p, hp, Or.inr hpdvd⟩
      · obtain ⟨p, hp, hpdvd⟩ := hprune (X₁ ω) hω.1 h1
        exact ⟨p, hp, Or.inl hpdvd⟩
  calc
    μ {ω | X₁ ω ∈ S ∧ X₂ ω ∈ S}
        ≤ μ ({ω | X₁ ω ∈ S' ∧ X₂ ω ∈ S'} ∪
            (⋃ p ∈ removed, ({ω | p ∣ X₁ ω} ∪ {ω | p ∣ X₂ ω}))) :=
          MeasureTheory.measure_mono hsub
    _ ≤ μ {ω | X₁ ω ∈ S' ∧ X₂ ω ∈ S'} +
          μ (⋃ p ∈ removed, ({ω | p ∣ X₁ ω} ∪ {ω | p ∣ X₂ ω})) :=
          MeasureTheory.measure_union_le _ _
    _ ≤ μ {ω | X₁ ω ∈ S' ∧ X₂ ω ∈ S'} +
          ∑ p ∈ removed, μ ({ω | p ∣ X₁ ω} ∪ {ω | p ∣ X₂ ω}) :=
          add_le_add le_rfl (MeasureTheory.measure_biUnion_finset_le removed _)
    _ ≤ μ {ω | X₁ ω ∈ S' ∧ X₂ ω ∈ S'} +
          ∑ p ∈ removed, (μ {ω | p ∣ X₁ ω} + μ {ω | p ∣ X₂ ω}) :=
          add_le_add le_rfl (Finset.sum_le_sum fun p _ => MeasureTheory.measure_union_le _ _)

/-- Specialization of `pruned_prime_pair_restoration_weighted` to pruning all
primes dividing `m ≠ 0`. -/
theorem pruned_prime_pair_restoration_coprime {α : Type*} (Ω : Finset α) (w : α → ℝ)
    (hw : ∀ ω ∈ Ω, 0 ≤ w ω) (X₁ X₂ : α → ℕ) (S : Finset ℕ) {m : ℕ} (hm : m ≠ 0) :
    (∑ ω ∈ Ω.filter (fun ω => X₁ ω ∈ S ∧ X₂ ω ∈ S), w ω) ≤
      (∑ ω ∈ Ω.filter (fun ω => X₁ ω ∈ S.filter (·.Coprime m) ∧ X₂ ω ∈ S.filter (·.Coprime m)),
        w ω) +
      ∑ p ∈ m.primeFactors,
        ((∑ ω ∈ Ω.filter (fun ω => p ∣ X₁ ω), w ω) +
         (∑ ω ∈ Ω.filter (fun ω => p ∣ X₂ ω), w ω)) :=
  pruned_prime_pair_restoration_weighted Ω w hw X₁ X₂ S (S.filter (·.Coprime m)) m.primeFactors
    (coprime_pruning_witness S hm)

#print axioms primeBinPatternProducts_dividedStrip_ratio_le
#print axioms centeredBinProducts_dividedStrip_ratio_le
#print axioms centeredBinProducts_dividedStrip_ratio_from_supply
#print axioms primePattern_pruned_progression_from_critical_line
#print axioms centeredBinProducts_pruned_progression_from_critical_line
#print axioms primePattern_relative_prefix_progression_from_critical_line
#print axioms coupled_mode_cauchy_schwarz
#print axioms averaged_coupled_abel_strip_bound
#print axioms primeBinProducts_averaged_coupled_abel_from_critical_line
#print axioms ratio_expectation_le
#print axioms ratio_expectation_le_of_prob
#print axioms pruned_prime_pair_restoration_weighted
#print axioms pruned_prime_pair_restoration_measure
#print axioms pruned_prime_pair_restoration_coprime

end Cogentic.Randomized
