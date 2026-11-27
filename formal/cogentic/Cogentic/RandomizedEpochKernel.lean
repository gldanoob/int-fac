import Cogentic.RandomizedCostedFactorLaw
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Normed

namespace Cogentic.RandomizedEpochKernel

open RandomizedCostedFactorLaw
open scoped BigOperators Classical ENNReal

variable {α : Type*} [Fintype α]

abbrev Factors (n : ℕ) := {p : ℕ × ℕ // 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 * p.2 = n}

noncomputable def successMass (epoch : PMF α) (success : α → Prop) : ℝ≥0∞ :=
  ∑' a : Subtype success, epoch a

private theorem successMass_add_failureMass (epoch : PMF α) (success : α → Prop) :
    successMass epoch success + successMass epoch (fun a => ¬ success a) = 1 := by
  calc
    _ = (∑ a : Subtype success, epoch a) + ∑ a : {a : α // ¬ success a}, epoch a :=
      congrArg₂ (· + ·) (tsum_fintype (fun a : Subtype success => epoch a))
        (tsum_fintype (fun a : {a : α // ¬ success a} => epoch a))
    _ = ∑ a, epoch a := Fintype.sum_subtype_add_sum_subtype success (fun a => epoch a)
    _ = 1 := (tsum_fintype (fun a : α => epoch a)).symm.trans epoch.tsum_coe

private theorem successMass_ne_top (epoch : PMF α) (success : α → Prop) :
    successMass epoch success ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    ((le_add_right le_rfl).trans_eq (successMass_add_failureMass epoch success))

private theorem one_sub_failureMass (epoch : PMF α) (success : α → Prop) :
    1 - successMass epoch (fun a => ¬ success a) = successMass epoch success := by
  have h := successMass_add_failureMass epoch success
  have hq : successMass epoch (fun a => ¬ success a) ≤ 1 := (le_add_left le_rfl).trans_eq h
  exact ENNReal.sub_eq_of_eq_add (ne_top_of_le_ne_top ENNReal.one_ne_top hq) h.symm

private theorem failureMass_lt_one (epoch : PMF α) (success : α → Prop)
    (hp : 0 < successMass epoch success) :
    successMass epoch (fun a => ¬ success a) < 1 := by
  rw [← one_sub_failureMass epoch success, tsub_pos_iff_lt] at hp
  exact hp

/-- A stopping transcript records each failed draw in order and the first
successful draw, with the results of both kinds of draw retained. -/
abbrev Transcript (success : α → Prop) :=
  Σ k : ℕ, (Fin k → {a : α // ¬ success a}) × Subtype success

private noncomputable def transcriptMass (epoch : PMF α) {success : α → Prop}
    (t : Transcript success) : ℝ≥0∞ :=
  (∏ i, epoch (t.2.1 i)) * epoch t.2.2

private theorem failed_draws_sum (epoch : PMF α) (success : α → Prop) (k : ℕ) :
    (∑ f : Fin k → {a : α // ¬ success a}, ∏ i, epoch (f i)) =
      successMass epoch (fun a => ¬ success a) ^ k := by
  calc
    _ = (∑ a : {a : α // ¬ success a}, epoch a) ^ k := by
      simpa only [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] using
        (Finset.sum_prod_piFinset (Finset.univ : Finset {a : α // ¬ success a})
          (fun (_ : Fin k) a => epoch a))
    _ = _ := congrArg (· ^ k) (tsum_fintype (fun a : {a : α // ¬ success a} => epoch a)).symm

private theorem transcript_mass_sum (epoch : PMF α) (success : α → Prop) (k : ℕ) :
    (∑ t : (Fin k → {a : α // ¬ success a}) × Subtype success,
      transcriptMass epoch ⟨k, t⟩) =
    successMass epoch (fun a => ¬ success a) ^ k * successMass epoch success := by
  simp only [Fintype.sum_prod_type, transcriptMass]
  calc
    _ = ∑ f : Fin k → {a : α // ¬ success a}, (∏ i, epoch (f i)) * successMass epoch success := by
      apply Finset.sum_congr rfl
      intro f _
      rw [successMass, tsum_fintype]
      exact (Finset.mul_sum Finset.univ (fun a : Subtype success => epoch a)
        (∏ i, epoch (f i))).symm
    _ = _ := by rw [← Finset.sum_mul, failed_draws_sum]

/-- Independent calls to the epoch kernel give each particular stopping path
the product of the masses of its draws. Positive success mass normalizes
these finite stopping paths to probability one. -/
noncomputable def transcriptLaw (epoch : PMF α) (success : α → Prop)
    (hp : 0 < successMass epoch success) : PMF (Transcript success) := by
  refine ⟨transcriptMass epoch, ?_⟩
  have hsum : (∑' t : Transcript success, transcriptMass epoch t) = 1 := by
    rw [ENNReal.tsum_sigma (fun k t => transcriptMass epoch ⟨k, t⟩)]
    simp only [tsum_fintype, transcript_mass_sum]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_sub_failureMass,
      ENNReal.inv_mul_cancel hp.ne' (successMass_ne_top epoch success)]
  exact hsum ▸ ENNReal.summable.hasSum

theorem transcriptLaw_apply (epoch : PMF α) (success : α → Prop)
    (hp : 0 < successMass epoch success) (t : Transcript success) :
    transcriptLaw epoch success hp t = (∏ i, epoch (t.2.1 i)) * epoch t.2.2 := rfl

/-- The successful draw has the original epoch law conditioned on success.
Its factor and work records remain jointly distributed. -/
theorem transcriptLaw_terminal_apply (epoch : PMF α) (success : α → Prop)
    (hp : 0 < successMass epoch success) (a : Subtype success) :
    ((transcriptLaw epoch success hp).map fun t => t.2.2) a = epoch a / successMass epoch success := by
  rw [PMF.map_apply]
  calc
    _ = ∑' (k : ℕ) (t : (Fin k → {a : α // ¬ success a}) × Subtype success),
          if a = t.2 then transcriptLaw epoch success hp ⟨k, t⟩ else 0 := by
      refine (tsum_congr fun t => ?_).trans (ENNReal.tsum_sigma _)
      by_cases h : a = t.2.2 <;> simp [h]
    _ = ∑' k : ℕ, successMass epoch (fun a => ¬ success a) ^ k * epoch a := by
      apply tsum_congr
      intro k
      simp only [tsum_fintype, Fintype.sum_prod_type, transcriptLaw_apply]
      have hterm (failed : Fin k → {a : α // ¬ success a}) :
          (∑ last : Subtype success, if a = last then (∏ i, epoch (failed i)) * epoch last else 0) =
            (∏ i, epoch (failed i)) * epoch a := by simp
      simp only [hterm]
      rw [← Finset.sum_mul, failed_draws_sum]
    _ = _ := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_sub_failureMass, div_eq_mul_inv, mul_comm]

private theorem geometric_attempt_mean {p q : ℝ≥0∞}
    (hp : 0 < p) (hqt : q < 1) (h : 1 - q = p) :
    (∑' k : ℕ, q ^ k * p * (↑(k + 1) : ℝ≥0∞)) = p⁻¹ := by
  have hqtop := ne_top_of_lt (hqt.trans ENNReal.one_lt_top)
  have hptop : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (h ▸ tsub_le_self)
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp.ne' hptop
  have hqR : q.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hqtop ENNReal.one_ne_top).mpr hqt
  have hpq : p.toReal = 1 - q.toReal := by
    rw [← h, ENNReal.toReal_sub_of_le hqt.le ENNReal.one_ne_top, ENNReal.toReal_one]
  have hn : ‖q.toReal‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hqR
  let f (k : ℕ) : ℝ := q.toReal ^ k * p.toReal * (k + 1)
  have hf (k : ℕ) : 0 ≤ f k := by positivity
  have hsplit (k : ℕ) : f k = (k * q.toReal ^ k + q.toReal ^ k) * p.toReal := by
    dsimp [f]
    ring
  have hgeom := hasSum_geometric_of_lt_one ENNReal.toReal_nonneg hqR
  have hweighted := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have hsum := (hweighted.add hgeom).mul_right p.toReal
  have hf' : HasSum f p.toReal⁻¹ := by
    rw [funext hsplit]
    have hvalue : (q.toReal / (1 - q.toReal) ^ 2 + (1 - q.toReal)⁻¹) * p.toReal =
        p.toReal⁻¹ := by
      rw [← hpq]
      field_simp [hpR.ne']
      linarith only [hpq]
    exact hvalue ▸ hsum
  have hcast (k : ℕ) : ENNReal.ofReal (f k) = q ^ k * p * (↑(k + 1) : ℝ≥0∞) := by
    dsimp only [f]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hqtop,
      ENNReal.ofReal_toReal hptop, ← Nat.cast_succ, ENNReal.ofReal_natCast]
  calc
    _ = ∑' k, ENNReal.ofReal (f k) := tsum_congr fun k => (hcast k).symm
    _ = ENNReal.ofReal p.toReal⁻¹ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hf hf'.summable, hf'.tsum_eq]
    _ = _ := by rw [ENNReal.ofReal_inv_of_pos hpR, ENNReal.ofReal_toReal hptop]

/-- The exact raw work charged to all epochs, including failed attempts. -/
def transcriptWork {success : α → Prop} (work : α → ℕ) (t : Transcript success) : ℕ :=
  (∑ i, work (t.2.1 i)) + work t.2.2

omit [Fintype α] in
theorem transcriptWork_le {success : α → Prop} (work : α → ℕ) {W : ℕ}
    (hwork : ∀ a, work a ≤ W) (t : Transcript success) :
    transcriptWork work t ≤ (t.1 + 1) * W := by
  unfold transcriptWork
  rw [Nat.add_mul, one_mul]
  refine Nat.add_le_add ?_ (hwork _)
  simpa using (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hwork (t.2.1 i)))

private theorem transcript_mean_le (epoch : PMF α) (success : α → Prop)
    (hp : 0 < successMass epoch success) (work : α → ℕ) {W : ℕ} (hwork : ∀ a, work a ≤ W) :
    mean (transcriptLaw epoch success hp) (fun t => transcriptWork work t) ≤
      (W : ℝ≥0∞) / successMass epoch success := by
  calc
    _ ≤ ∑' t : Transcript success, transcriptMass epoch t * (↑(t.1 + 1) * (W : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro t
      apply mul_le_mul_right
      rw [← Nat.cast_mul]
      exact Nat.cast_le.mpr (transcriptWork_le work hwork t)
    _ = _ := by
      simp only [← mul_assoc]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_sigma
        (fun k t => transcriptMass epoch ⟨k, t⟩ * (↑(k + 1) : ℝ≥0∞))]
      simp only [tsum_fintype, ← Finset.sum_mul, transcript_mass_sum]
      rw [geometric_attempt_mean hp (failureMass_lt_one epoch success hp)
        (one_sub_failureMass epoch success), div_eq_mul_inv, mul_comm]

private def successfulFactors {n : ℕ} (outcome : α → Option (Factors n))
    (a : {a : α // outcome a ≠ none}) : Factors n :=
  (outcome a).get (Option.isSome_iff_ne_none.mpr a.property)

/-- Verified factors from the final draw, paired with the work of the whole
stopping transcript. The verifier is part of the supplied epoch computation. -/
noncomputable def repeatedKernel {n : ℕ} (epoch : PMF α) (outcome : α → Option (Factors n))
    (work : α → ℕ) (hp : 0 < successMass epoch (fun a => outcome a ≠ none)) :
    PMF (SplitOutcome n) :=
  (transcriptLaw epoch _ hp).map fun t =>
    let f := successfulFactors outcome t.2.2
    ⟨f.val.1, f.val.2, transcriptWork work t, f.property.1, f.property.2.1, f.property.2.2⟩

/-- The factor-pair marginal is exactly the mass of the epoch outcomes
returning those factors, normalized by the probability of success. -/
theorem repeatedKernel_factors_apply {n : ℕ} (epoch : PMF α)
    (outcome : α → Option (Factors n)) (work : α → ℕ)
    (hp : 0 < successMass epoch (fun a => outcome a ≠ none)) (factors : Factors n) :
    ((repeatedKernel epoch outcome work hp).map
      (fun s => (⟨(s.left, s.right), s.left_ge, s.right_ge, s.product⟩ : Factors n))) factors =
    ∑ a : {a : α // outcome a ≠ none},
      if outcome a = some factors then epoch a / successMass epoch (fun a => outcome a ≠ none)
      else 0 := by
  let law := transcriptLaw epoch (fun a => outcome a ≠ none) hp
  have hmap :
      (repeatedKernel epoch outcome work hp).map
        (fun s => (⟨(s.left, s.right), s.left_ge, s.right_ge, s.product⟩ : Factors n)) =
      (law.map (fun t => t.2.2)).map (successfulFactors outcome) := by
    rw [repeatedKernel, PMF.map_comp, PMF.map_comp]
    rfl
  rw [hmap, PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  have heq : factors = successfulFactors outcome a ↔ outcome a = some factors := by
    have hs : some (successfulFactors outcome a) = outcome a := Option.some_get _
    rw [← hs, Option.some.injEq, eq_comm]
  dsimp only [law]
  rw [heq, transcriptLaw_terminal_apply]
  by_cases h : outcome a = some factors <;> simp [h]

theorem repeatedKernel_mean_le {n : ℕ} (epoch : PMF α) (outcome : α → Option (Factors n))
    (work : α → ℕ) (hp : 0 < successMass epoch (fun a => outcome a ≠ none))
    {W : ℕ} (hwork : ∀ a, work a ≤ W) :
    mean (repeatedKernel epoch outcome work hp) (fun s => s.work) ≤
      (W : ℝ≥0∞) / successMass epoch (fun a => outcome a ≠ none) := by
  rw [repeatedKernel, mean_map]
  exact transcript_mean_le epoch _ hp work hwork

#print axioms transcriptLaw_terminal_apply
#print axioms repeatedKernel_factors_apply
#print axioms repeatedKernel_mean_le

end Cogentic.RandomizedEpochKernel
