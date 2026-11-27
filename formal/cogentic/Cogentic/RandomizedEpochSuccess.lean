import Cogentic.RandomizedVerifiedHiddenSplit
import Cogentic.RandomizedFiniteSupportTV

namespace Cogentic.RandomizedEpochSuccess

open RandomizedHiddenLabels RandomizedHiddenOutputLaw RandomizedVerifiedHiddenSplit
open RandomizedFiniteSupportTV
open scoped ENNReal

/-- All data used by the charged verifier are fixed by the public transcript. -/
structure TranscriptData (Label : Type*) (N : ℕ) where
  labels : Finset Label
  multiplicity : Label → ℕ
  publicRoot : (ZMod N)ˣ
  privateIndex : Label
  mem_labels : privateIndex ∈ labels
  odd_multiplicity : Odd (multiplicity privateIndex)

variable {Coins Label Public : Type*} [DecidableEq Public] {N : ℕ}

/-- Verify good transcripts, with a rejection and zero post-ratio charge elsewhere. -/
noncomputable def epochTrial (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public) (data : good → TranscriptData Label N)
    (x : Coins × (Label → (ZMod N)ˣ)) : Option (ℕ × ℕ) × ℕ :=
  if h : observe trace x ∈ good then
    let d := data ⟨observe trace x, h⟩
    verifiedTrial (comparisonRatio d.labels d.multiplicity d.publicRoot x.2)
  else (none, 0)

theorem epochTrial_budget_sound (hN : 3 ≤ N)
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public) (data : good → TranscriptData Label N) (x) :
    (epochTrial trace good data x).2 ≤ trialBudget N ∧
      ∀ pair, (epochTrial trace good data x).1 = some pair →
        2 ≤ pair.1 ∧ 2 ≤ pair.2 ∧ pair.1 * pair.2 = N := by
  unfold epochTrial
  split
  · exact verifiedTrial_budget_sound hN _
  · simp

/-- The same trial with a certified factor pair on success, suitable for the epoch
kernel. The proper-pair type is definitionally the epoch kernel's factors type. -/
noncomputable def certifiedEpochTrial (hN : 3 ≤ N)
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public) (data : good → TranscriptData Label N)
    (x : Coins × (Label → (ZMod N)ˣ)) : Option (RandomizedHiddenSplitLaw.ProperPair N) × ℕ :=
  (match h : (epochTrial trace good data x).1 with
    | none => none
    | some pair => some ⟨pair, (epochTrial_budget_sound hN trace good data x).2 pair h⟩,
    (epochTrial trace good data x).2)

theorem certifiedEpochTrial_erasure (hN : 3 ≤ N)
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public) (data : good → TranscriptData Label N) (x) :
    ((certifiedEpochTrial hN trace good data x).1.map Subtype.val,
      (certifiedEpochTrial hN trace good data x).2) = epochTrial trace good data x := by
  apply Prod.ext
  · unfold certifiedEpochTrial
    split <;> simp_all
  · rfl

theorem certifiedEpochTrial_accepts (hN : 3 ≤ N)
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public) (data : good → TranscriptData Label N) (x) :
    (certifiedEpochTrial hN trace good data x).1 ≠ none ↔
      (epochTrial trace good data x).1 ≠ none := by
  have h := congrArg Prod.fst (certifiedEpochTrial_erasure hN trace good data x)
  rw [← h]
  cases (certifiedEpochTrial hN trace good data x).1 <;> simp

private theorem filtered_mass_mul {X : Type*} (p : PMF X) (S T : Set X)
    (hS : ∃ x ∈ S, x ∈ p.support) :
    ((p.filter S hS).toOuterMeasure T).toReal * (p.toOuterMeasure S).toReal =
      (p.toOuterMeasure (T ∩ S)).toReal := by
  classical
  have hn : p.toOuterMeasure S ≠ 0 := by
    intro h
    obtain ⟨x, hx, hs⟩ := hS
    exact Set.disjoint_left.mp ((PMF.toOuterMeasure_apply_eq_zero_iff p S).mp h) hs hx
  have ht : p.toOuterMeasure S ≠ ⊤ := by
    rw [PMF.toOuterMeasure_apply]
    exact p.tsum_coe_indicator_ne_top S
  have hfiltered : (p.filter S hS).toOuterMeasure T =
      p.toOuterMeasure (T ∩ S) * (p.toOuterMeasure S)⁻¹ := by
    rw [PMF.toOuterMeasure_apply _ T, PMF.toOuterMeasure_apply p (T ∩ S),
      ← ENNReal.tsum_mul_right, PMF.toOuterMeasure_apply p S]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ T <;> by_cases hy : x ∈ S <;>
      simp [PMF.filter_apply, Set.indicator_apply, hx, hy]
  rw [← ENNReal.toReal_mul, hfiltered, ENNReal.inv_mul_cancel_right hn ht]

private theorem event_mass_finset {X : Type*} [Fintype X] (p : PMF X) (S : Set X)
    [DecidablePred (· ∈ S)] :
    (p.toOuterMeasure S).toReal = ∑ x ∈ Finset.univ.filter (· ∈ S), (p x).toReal := by
  classical
  have hs : (↑(Finset.univ.filter (· ∈ S)) : Set X) = S := by ext x; simp
  calc
    _ = (p.toOuterMeasure (↑(Finset.univ.filter (· ∈ S)) : Set X)).toReal :=
      congrArg (fun T ↦ (p.toOuterMeasure T).toReal) hs.symm
    _ = _ := by
      rw [PMF.toOuterMeasure_apply_finset, ENNReal.toReal_sum]
      exact fun x _ ↦ p.apply_ne_top x

/-- On good transcripts in the ideal law, the existing conditional split theorem
applies. Joint total variation transfers the probability of the same checked
success event to the actual finite sampler. -/
theorem epoch_verified_split_probability [Fintype Coins] [Fintype Label] [DecidableEq Label]
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (ideal actual : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public) (data : good → TranscriptData Label N)
    (hseen : ∀ t : good, ∃ x ∈ {x | observe trace x = t.val}, x ∈ ideal.support)
    (hcheck : ∀ (t : good) x, observe trace x = t.val →
      (labelProduct (data t).labels (data t).multiplicity x.2)^2 = (data t).publicRoot^2)
    (huniform : ∀ (t : good) x y, observe trace x = t.val → x.1 = y.1 →
      (x.2 (data t).privateIndex)^2 = (y.2 (data t).privateIndex)^2 →
      (∀ j, j ≠ (data t).privateIndex → x.2 j = y.2 j) → ideal x = ideal y)
    (γ ε : ℝ)
    (hγ : γ ≤ (ideal.toOuterMeasure {x | observe trace x ∈ good}).toReal)
    (hTV : pmfTotalVariation ideal actual ≤ ε) :
    γ * (1 - 2 / (2 : ℝ)^N.primeFactors.card) - ε ≤
      ((actual.map (epochTrial trace good data)).toOuterMeasure {o | o.1 ≠ none}).toReal := by
  classical
  let : NeZero N := ⟨by omega⟩
  let X := Coins × (Label → (ZMod N)ˣ)
  let success : Set X := {x | (epochTrial trace good data x).1 ≠ none}
  let valid : Set X := {x | observe trace x ∈ good}
  let fiber (t : Public) : Set X := {x | observe trace x = t}
  let s : ℝ := 1 - 2 / (2 : ℝ)^N.primeFactors.card
  have hs : 0 ≤ s := by
    have hpow : (2 : ℝ)^1 ≤ (2 : ℝ)^N.primeFactors.card :=
      pow_le_pow_right₀ (by norm_num) (by have := RandomizedOddSplit.two_le_factor_count hN hnot; omega)
    dsimp [s]
    exact sub_nonneg.mpr ((div_le_iff₀ (by positivity)).mpr (by simpa using hpow))
  have hsuccess : success ⊆ valid := by
    intro x hx
    by_contra hbad
    have hr : epochTrial trace good data x = (none, 0) := dif_neg hbad
    exact hx (congrArg Prod.fst hr)
  have hfiber (t : good) :
      (ideal.toOuterMeasure (success ∩ fiber t)).toReal =
        s * (ideal.toOuterMeasure (fiber t)).toReal := by
    have hc := (conditional_verified_split hN ho hnot ideal trace t.val
      (data t).labels (data t).multiplicity (data t).publicRoot
      (data t).mem_labels (data t).odd_multiplicity (hseen t) (hcheck t) (huniform t)).1
    rw [PMF.toOuterMeasure_map_apply] at hc
    have hcap : success ∩ fiber t =
        ((fun x : X ↦ verifiedTrial
          (comparisonRatio (data t).labels (data t).multiplicity (data t).publicRoot x.2)) ⁻¹'
          {o | o.1 ≠ none}) ∩ fiber t := by
      ext x
      constructor <;> intro hx
      all_goals
        refine ⟨?_, hx.2⟩
        have heq : observe trace x = t.val := hx.2
        have hgood : observe trace x ∈ good := by simpa only [heq] using t.property
        have hdata : (⟨observe trace x, hgood⟩ : good) = t := Subtype.ext heq
        simpa [success, epochTrial, hgood, hdata] using hx.1
    rw [hcap, ← filtered_mass_mul ideal (fiber t) _ (hseen t)]
    exact congrArg (· * (ideal.toOuterMeasure (fiber t)).toReal) hc
  have hsum (S : Set X) (hS : S ⊆ valid) :
      (ideal.toOuterMeasure S).toReal =
        ∑ t ∈ good, (ideal.toOuterMeasure (S ∩ fiber t)).toReal := by
    rw [event_mass_finset]
    rw [← Finset.sum_fiberwise_of_maps_to (t := good) (g := observe trace)
      (fun x hx ↦ hS (Finset.mem_filter.mp hx).2) (fun x ↦ (ideal x).toReal)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [event_mass_finset]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hmass : (ideal.toOuterMeasure success).toReal = s * (ideal.toOuterMeasure valid).toReal := by
    rw [hsum success hsuccess, hsum valid (fun _ h ↦ h), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hf : valid ∩ fiber t = fiber t := by
      apply Set.inter_eq_right.mpr
      intro x hx
      show observe trace x ∈ good
      simpa only [show observe trace x = t from hx] using ht
    simpa only [hf] using hfiber ⟨t, ht⟩
  have htransfer :
      (ideal.toOuterMeasure success).toReal - (actual.toOuterMeasure success).toReal ≤ ε := by
    rw [event_mass_finset ideal, event_mass_finset actual]
    exact (pmf_finset_mass_sub_le_totalVariation ideal actual _).trans hTV
  rw [PMF.toOuterMeasure_map_apply]
  change γ*s - ε ≤ (actual.toOuterMeasure success).toReal
  linarith only [hmass, htransfer, mul_le_mul_of_nonneg_left hγ hs]

/-- An odd non-prime-power modulus has at least the half-mass success bound. -/
theorem epoch_verified_split_probability_half [Fintype Coins] [Fintype Label] [DecidableEq Label]
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (ideal actual : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public) (data : good → TranscriptData Label N)
    (hseen : ∀ t : good, ∃ x ∈ {x | observe trace x = t.val}, x ∈ ideal.support)
    (hcheck : ∀ (t : good) x, observe trace x = t.val →
      (labelProduct (data t).labels (data t).multiplicity x.2)^2 = (data t).publicRoot^2)
    (huniform : ∀ (t : good) x y, observe trace x = t.val → x.1 = y.1 →
      (x.2 (data t).privateIndex)^2 = (y.2 (data t).privateIndex)^2 →
      (∀ j, j ≠ (data t).privateIndex → x.2 j = y.2 j) → ideal x = ideal y)
    (γ ε : ℝ) (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ (ideal.toOuterMeasure {x | observe trace x ∈ good}).toReal)
    (hTV : pmfTotalVariation ideal actual ≤ ε) :
    γ / 2 - ε ≤
      ((actual.map (epochTrial trace good data)).toOuterMeasure {o | o.1 ≠ none}).toReal := by
  have hpow : (4 : ℝ) ≤ (2 : ℝ)^N.primeFactors.card := by
    calc
      4 = (2 : ℝ)^2 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (RandomizedOddSplit.two_le_factor_count hN hnot)
  have hs : (1/2 : ℝ) ≤ 1 - 2 / (2 : ℝ)^N.primeFactors.card := by
    have hdiv := (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^N.primeFactors.card)).mpr
      (show (2 : ℝ) ≤ (1/2) * (2 : ℝ)^N.primeFactors.card by linarith only [hpow])
    linarith only [hdiv]
  exact (show γ / 2 - ε ≤ γ * (1 - 2 / (2 : ℝ)^N.primeFactors.card) - ε by
    linarith only [mul_le_mul_of_nonneg_left hs hγ₀]).trans
      (epoch_verified_split_probability hN ho hnot ideal actual trace good data hseen hcheck
        huniform γ ε hγ hTV)

end Cogentic.RandomizedEpochSuccess
