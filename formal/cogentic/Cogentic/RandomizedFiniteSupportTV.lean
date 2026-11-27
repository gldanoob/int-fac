import Cogentic.RandomizedSamplerTransfer
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open Finset
open scoped BigOperators

namespace Cogentic.RandomizedFiniteSupportTV

open RandomizedSamplerTransfer (totalVariation mean_difference_le_totalVariation)

section FiniteTarget

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]

theorem uniform_mass_outside_eq (S : Finset Ω) :
    (∑ _z ∈ univ \ S, (1 : ℝ) / (Fintype.card Ω : ℝ)) =
      1 - (S.card : ℝ) / (Fintype.card Ω : ℝ) := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← sum_div, sum_const, nsmul_eq_mul, mul_one,
    card_sdiff_of_subset (subset_univ S), card_univ,
    Nat.cast_sub (by simpa using card_le_card (subset_univ S)), sub_div, div_self hn]

/-- A probability mass supported on `S` misses at least the uniform mass
outside `S` in total variation. -/
theorem uniform_mass_outside_le_totalVariation (S : Finset Ω) (p : Ω → ℝ)
    (hp : ∑ z, p z = 1) (hS : ∀ z ∉ S, p z = 0) :
    (∑ _z ∈ univ \ S, (1 : ℝ) / (Fintype.card Ω : ℝ)) ≤
      totalVariation p (fun _ => 1 / (Fintype.card Ω : ℝ)) := by
  let q : ℝ := 1 / (Fintype.card Ω : ℝ)
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hq : (∑ _z : Ω, q) = 1 := by
    simp [q, nsmul_eq_mul, hn]
  let test (z : Ω) : ℝ := if z ∉ S then 1 else 0
  have htest₀ (z : Ω) : 0 ≤ test z := by unfold test; split <;> norm_num
  have htest₁ (z : Ω) : test z ≤ 1 := by unfold test; split <;> norm_num
  have h := mean_difference_le_totalVariation (hp.trans hq.symm) test htest₀ htest₁
  have hp₀ : ∑ z, p z * test z = 0 := by
    apply sum_eq_zero
    intro z _
    by_cases hz : z ∈ S
    · simp [test, hz]
    · simp [hS z hz]
  have hqsum : ∑ z, q * test z = ∑ _z ∈ univ \ S, q := by
    have hcomplement : univ \ S = univ.filter (fun z => z ∉ S) := by ext z; simp
    rw [hcomplement, sum_filter]
    simp only [test, mul_ite, mul_one, mul_zero]
  rw [hp₀, hqsum, zero_sub, abs_neg,
    abs_of_nonneg (sum_nonneg fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))] at h
  exact h

theorem uniform_mass_off_image_ge {A : Type*} (S : Finset A) (f : A → Ω) :
    1 - (S.card : ℝ) / (Fintype.card Ω : ℝ) ≤
      ∑ _z ∈ univ \ S.image f, (1 : ℝ) / (Fintype.card Ω : ℝ) := by
  rw [uniform_mass_outside_eq]
  apply sub_le_sub_left
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_image_le) (Nat.cast_nonneg _)

/-- Mass of the fiber of `f` at an output point. -/
def fiberMass {A : Type*} (S : Finset A) (f : A → Ω) (w : A → ℝ) (z : Ω) : ℝ :=
  ∑ x ∈ S.filter (fun x => f x = z), w x

/-- Every finite weighted image law has total variation from uniform at least
one minus the ratio of the number of input points to the number of outputs. -/
theorem one_sub_card_div_le_totalVariation_fiberMass {A : Type*}
    (S : Finset A) (f : A → Ω) (w : A → ℝ) (hw : ∑ x ∈ S, w x = 1) :
    1 - (S.card : ℝ) / (Fintype.card Ω : ℝ) ≤
      totalVariation (fiberMass S f w) (fun _ => 1 / (Fintype.card Ω : ℝ)) := by
  apply (uniform_mass_off_image_ge S f).trans
  apply uniform_mass_outside_le_totalVariation
  · unfold fiberMass
    rw [sum_fiberwise_of_maps_to (fun x _ => mem_univ (f x)), hw]
  · intro z hz
    unfold fiberMass
    apply sum_eq_zero
    intro x hx
    obtain ⟨hxS, hfx⟩ := mem_filter.mp hx
    exact (hz (mem_image.mpr ⟨x, hxS, hfx⟩)).elim

#print axioms uniform_mass_outside_eq
#print axioms uniform_mass_outside_le_totalVariation
#print axioms uniform_mass_off_image_ge
#print axioms one_sub_card_div_le_totalVariation_fiberMass

end FiniteTarget

section PMFLaws

variable {A B : Type*}

/-- Half the sum of absolute atom differences between two discrete probability laws. -/
noncomputable def pmfTotalVariation (p q : PMF B) : ℝ :=
  (∑' z, |(p z).toReal - (q z).toReal|) / 2

theorem pmfTotalVariation_eq_totalVariation [Fintype B] (p q : PMF B) :
    pmfTotalVariation p q = totalVariation (fun z => (p z).toReal) (fun z => (q z).toReal) := by
  rw [pmfTotalVariation, totalVariation, tsum_fintype]

private theorem pmf_tsum_toReal (p : PMF B) : (∑' z, (p z).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe, ENNReal.toReal_one]

private theorem summable_pmf_min (p q : PMF B) :
    Summable (fun z => min (p z).toReal (q z).toReal) :=
  Summable.of_nonneg_of_le
    (fun _ => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun _ => min_le_left _ _) (ENNReal.summable_toReal p.tsum_coe_ne_top)

/-- The complement of total variation is the common mass of the two laws. -/
theorem one_sub_pmfTotalVariation_eq_tsum_min (p q : PMF B) :
    1 - pmfTotalVariation p q = ∑' z, min (p z).toReal (q z).toReal := by
  have hp := ENNReal.summable_toReal p.tsum_coe_ne_top
  have hq := ENNReal.summable_toReal q.tsum_coe_ne_top
  have hmin := summable_pmf_min p q
  have habs := (hp.sub hq).abs
  have hpoint (z : B) : (p z).toReal + (q z).toReal =
      2 * min (p z).toReal (q z).toReal + |(p z).toReal - (q z).toReal| := by
    rcases le_total (p z).toReal (q z).toReal with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  have h : (∑' z, ((p z).toReal + (q z).toReal)) =
      ∑' z, (2 * min (p z).toReal (q z).toReal + |(p z).toReal - (q z).toReal|) :=
    tsum_congr hpoint
  rw [hp.tsum_add hq, (hmin.mul_left 2).tsum_add habs, tsum_mul_left,
    pmf_tsum_toReal p, pmf_tsum_toReal q] at h
  unfold pmfTotalVariation
  linarith only [h]

/-- Separation of the two centers bounds the common mass by their two
centered second moments. Charging both deviations gives the constant two. -/
theorem one_sub_pmfTotalVariation_le_centered_second_moments (p q : PMF B)
    (T : B → ℝ) {a b : ℝ} (hab : a < b)
    (hp : Summable (fun z => (p z).toReal * (T z - a) ^ 2))
    (hq : Summable (fun z => (q z).toReal * (T z - b) ^ 2)) :
    1 - pmfTotalVariation p q ≤
      2 * ((∑' z, (p z).toReal * (T z - a) ^ 2) +
        (∑' z, (q z).toReal * (T z - b) ^ 2)) / (b - a) ^ 2 := by
  let overlap (z : B) := min (p z).toReal (q z).toReal
  have hpoint (z : B) : (b - a) ^ 2 * overlap z ≤
      2 * ((p z).toReal * (T z - a) ^ 2 + (q z).toReal * (T z - b) ^ 2) := by
    have hgap : (b - a) ^ 2 ≤ 2 * ((T z - a) ^ 2 + (T z - b) ^ 2) := by
      nlinarith only [sq_nonneg (2 * T z - a - b)]
    calc
      _ ≤ (2 * ((T z - a) ^ 2 + (T z - b) ^ 2)) * overlap z :=
        mul_le_mul_of_nonneg_right hgap (le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      _ = 2 * (overlap z * (T z - a) ^ 2 + overlap z * (T z - b) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))) (by norm_num)
  have h := ((summable_pmf_min p q).mul_left ((b - a) ^ 2)).tsum_le_tsum hpoint
    ((hp.add hq).mul_left 2)
  rw [tsum_mul_left, tsum_mul_left, hp.tsum_add hq] at h
  apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hab))).2
  rw [one_sub_pmfTotalVariation_eq_tsum_min, mul_comm]
  exact h

/-- The constant-four separation bound stated with upper bounds on the
two centered second moments. -/
theorem one_sub_pmfTotalVariation_le_four_mul_moment_bounds (p q : PMF B)
    (T : B → ℝ) {a b Vp Vq : ℝ} (hab : a < b)
    (hp : Summable (fun z => (p z).toReal * (T z - a) ^ 2))
    (hq : Summable (fun z => (q z).toReal * (T z - b) ^ 2))
    (hVp : (∑' z, (p z).toReal * (T z - a) ^ 2) ≤ Vp)
    (hVq : (∑' z, (q z).toReal * (T z - b) ^ 2) ≤ Vq) :
    1 - pmfTotalVariation p q ≤ 4 * (Vp + Vq) / (b - a) ^ 2 := by
  have hVp₀ : 0 ≤ Vp :=
    (tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)).trans hVp
  have hVq₀ : 0 ≤ Vq :=
    (tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)).trans hVq
  apply (one_sub_pmfTotalVariation_le_centered_second_moments p q T hab hp hq).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  linarith only [hVp, hVq, hVp₀, hVq₀]

/-- The difference between the masses of a finite event is bounded by total variation. -/
theorem pmf_finset_mass_sub_le_totalVariation (p q : PMF B) (T : Finset B) :
    (∑ z ∈ T, (p z).toReal) - (∑ z ∈ T, (q z).toReal) ≤ pmfTotalVariation p q := by
  let d (z : B) := (p z).toReal - (q z).toReal
  have hp := ENNReal.summable_toReal p.tsum_coe_ne_top
  have hq := ENNReal.summable_toReal q.tsum_coe_ne_top
  have hd : Summable d := hp.sub hq
  have hzero : (∑' z, d z) = 0 := by
    unfold d
    rw [hp.tsum_sub hq, pmf_tsum_toReal p, pmf_tsum_toReal q, sub_self]
  have hsplit := hd.sum_add_tsum_subtype_compl T
  rw [hzero] at hsplit
  have hfinite : ∑ z ∈ T, d z ≤ ∑ z ∈ T, |d z| := sum_le_sum fun _ _ => le_abs_self _
  have hcompl : -(∑' z : {z // z ∉ T}, d z) ≤ ∑' z : {z // z ∉ T}, |d z| := by
    rw [← tsum_neg]
    have hc : Summable (fun z : {z // z ∉ T} => d z) := hd.subtype (· ∉ T)
    exact hc.neg.tsum_le_tsum (fun _ => neg_le_abs _) hc.abs
  rw [← sum_sub_distrib]
  change (∑ z ∈ T, d z) ≤ (∑' z, |d z|) / 2
  rw [← hd.abs.sum_add_tsum_subtype_compl T]
  linarith only [hsplit, hfinite, hcompl]

private theorem pmf_atom_cap_nonneg (q : PMF B) {m : ℝ} (hatom : ∀ z, (q z).toReal ≤ m) :
    0 ≤ m := by
  obtain ⟨z, _⟩ := q.support_nonempty
  exact (ENNReal.toReal_nonneg (a := q z)).trans (hatom z)

/-- An atom cap times the size of a finite set bounds its probability mass. -/
theorem pmf_finset_mass_le_card_mul (q : PMF B) (S : Finset B) {m : ℝ}
    (hatom : ∀ z, (q z).toReal ≤ m) :
    (∑ z ∈ S, (q z).toReal) ≤ (S.card : ℝ) * m := calc
  _ ≤ ∑ _z ∈ S, m := sum_le_sum fun z _ => hatom z
  _ = _ := by simp [nsmul_eq_mul]

/-- A high-mass finite input set limits the image law's proximity to any target
law whose atoms are uniformly bounded. -/
theorem pmf_map_totalVariation_ge (p : PMF A) (q : PMF B)
    (f : A → B) (S : Finset A) (ε m : ℝ)
    (hmass : 1 - ε ≤ ∑ x ∈ S, (p x).toReal)
    (hatom : ∀ z, (q z).toReal ≤ m) :
    1 - ε - (S.card : ℝ) * m ≤ pmfTotalVariation (p.map f) q := by
  classical
  have himage : (∑ x ∈ S, (p x).toReal) ≤ ∑ z ∈ S.image f, ((p.map f) z).toReal := by
    have h := p.toOuterMeasure_mono
      (s := (S : Set A)) (t := f ⁻¹' ((S.image f : Finset B) : Set B))
      (fun x hx => mem_image_of_mem f hx.1)
    rw [← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_finset,
      PMF.toOuterMeasure_apply_finset] at h
    have hre := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun z _ => (p.map f).apply_ne_top z) h
    rw [ENNReal.toReal_sum (fun x _ => p.apply_ne_top x),
      ENNReal.toReal_sum (fun z _ => (p.map f).apply_ne_top z)] at hre
    exact hre
  have htarget : (∑ z ∈ S.image f, (q z).toReal) ≤ (S.card : ℝ) * m :=
    (pmf_finset_mass_le_card_mul q (S.image f) hatom).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast card_image_le) (pmf_atom_cap_nonneg q hatom))
  calc
    _ ≤ (∑ z ∈ S.image f, ((p.map f) z).toReal) - ∑ z ∈ S.image f, (q z).toReal :=
      sub_le_sub (hmass.trans himage) htarget
    _ ≤ _ := pmf_finset_mass_sub_le_totalVariation (p.map f) q (S.image f)

/-- A finite mixture preserves at least the weighted component masses on
the union of their respective sets. An atom cap bounds the target mass there. -/
theorem pmf_finite_mixture_totalVariation_ge {ι : Type*} (w : PMF ι) (I : Finset ι)
    (hw : ∀ i ∉ I, w i = 0) (p : ι → PMF B) (q : PMF B)
    (S : ι → Finset B) (δ : ι → ℝ) (K : ι → ℕ) (m : ℝ)
    (hmass : ∀ i ∈ I, δ i ≤ ∑ z ∈ S i, (p i z).toReal)
    (hsize : ∀ i ∈ I, (S i).card ≤ K i) (hatom : ∀ z, (q z).toReal ≤ m) :
    (∑ i ∈ I, (w i).toReal * δ i) - m * (∑ i ∈ I, (K i : ℝ)) ≤
      pmfTotalVariation (w.bind p) q := by
  classical
  let U := I.biUnion S
  have hbind (z : B) : ((w.bind p) z).toReal =
      ∑ i ∈ I, (w i).toReal * (p i z).toReal := by
    rw [PMF.bind_apply, tsum_eq_sum (s := I) (fun i hi => by rw [hw i hi, zero_mul]),
      ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (w.apply_ne_top i) ((p i).apply_ne_top z))]
    simp only [ENNReal.toReal_mul]
  have hmix : (∑ i ∈ I, (w i).toReal * δ i) ≤ ∑ z ∈ U, ((w.bind p) z).toReal := calc
    _ ≤ ∑ i ∈ I, (w i).toReal * (∑ z ∈ U, (p i z).toReal) := by
      apply sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact (hmass i hi).trans (sum_le_sum_of_subset_of_nonneg
        (fun z hz => mem_biUnion.mpr ⟨i, hi, hz⟩) (fun _ _ _ => ENNReal.toReal_nonneg))
    _ = _ := by simp only [mul_sum, hbind]; exact sum_comm
  have hcard : U.card ≤ ∑ i ∈ I, K i := card_biUnion_le.trans (sum_le_sum hsize)
  have htarget : (∑ z ∈ U, (q z).toReal) ≤ m * ∑ i ∈ I, (K i : ℝ) := calc
    _ ≤ (U.card : ℝ) * m := pmf_finset_mass_le_card_mul q U hatom
    _ ≤ (∑ i ∈ I, (K i : ℝ)) * m :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pmf_atom_cap_nonneg q hatom)
    _ = _ := mul_comm _ _
  exact (sub_le_sub hmix htarget).trans (pmf_finset_mass_sub_le_totalVariation (w.bind p) q U)

#print axioms pmfTotalVariation_eq_totalVariation
#print axioms one_sub_pmfTotalVariation_eq_tsum_min
#print axioms one_sub_pmfTotalVariation_le_centered_second_moments
#print axioms one_sub_pmfTotalVariation_le_four_mul_moment_bounds
#print axioms pmf_finset_mass_sub_le_totalVariation
#print axioms pmf_map_totalVariation_ge
#print axioms pmf_finite_mixture_totalVariation_ge

end PMFLaws

end Cogentic.RandomizedFiniteSupportTV
