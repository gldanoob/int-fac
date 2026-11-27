import Cogentic.RandomizedOddSplit
import Mathlib.Probability.Distributions.Uniform

namespace Cogentic.RandomizedHiddenSplitLaw

open RandomizedHiddenLabels RandomizedSignCount RandomizedOddSplit
open scoped ENNReal

/-- An ordered pair certified to be a proper split of the modulus. -/
abbrev ProperPair (N : ℕ) := {p : ℕ × ℕ // 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 * p.2 = N}

private def checkedPair (N d : ℕ) (hdvd : d ∣ N) : Option (ProperPair N) :=
  if h : 1 < d ∧ d < N then
    some ⟨(d, N / d), by
      have hprod : d * (N / d) = N := Nat.mul_div_cancel' hdvd
      have hquot : 2 ≤ N / d := by
        by_contra hsmall
        have hle := Nat.mul_le_mul_left d (by omega : N / d ≤ 1)
        rw [hprod, Nat.mul_one] at hle
        omega
      exact ⟨h.1, hquot, hprod⟩⟩
  else none

variable {Label : Type*} [DecidableEq Label] {N : ℕ}
variable (labels : Finset Label) (multiplicity : Label → ℕ) (roots : Label → (ZMod N)ˣ)
variable {i : Label} (hi : i ∈ labels)
variable (publicRoot : SquareFiber (labelProduct labels multiplicity roots))

/-- Map a supplied hidden root to its proper gcd and quotient, rejecting trivial gcds. -/
def hiddenSplitTrial (x : SquareFiber (roots i)) : Option (ProperPair N) :=
  let r := compareRoot publicRoot (replacementOutput labels multiplicity roots i hi x)
  checkedPair N (splitGcd r) (Nat.gcd_dvd_right _ _)

theorem hiddenSplitTrial_accepts (x : SquareFiber (roots i)) :
    hiddenSplitTrial labels multiplicity roots hi publicRoot x ≠ none ↔
      let d := splitGcd (compareRoot publicRoot (replacementOutput labels multiplicity roots i hi x))
      1 < d ∧ d < N := by
  unfold hiddenSplitTrial checkedPair
  dsimp only
  split <;> simp_all

theorem hiddenSplitTrial_pair (x : SquareFiber (roots i)) (outcome : ProperPair N)
    (h : hiddenSplitTrial labels multiplicity roots hi publicRoot x = some outcome) :
    let d := splitGcd (compareRoot publicRoot (replacementOutput labels multiplicity roots i hi x))
    outcome.val = (d, N / d) := by
  unfold hiddenSplitTrial checkedPair at h
  dsimp only at h
  split at h
  · exact congrArg Subtype.val (Option.some.inj h).symm
  · contradiction

/-- The uniform law on the supplied square fiber, expressed by its CRT enumeration.
This is an input law for the following theorem. -/
noncomputable def uniformHiddenRoot (hn : 3 ≤ N) (ho : Odd N) (hodd : Odd (multiplicity i)) :
    PMF (SquareFiber (roots i)) :=
  let signs := comparisonSigns labels multiplicity roots hi hodd publicRoot (oddSigns hn ho)
  PMF.uniformOfFinset (Finset.univ.map signs.symm.toEmbedding) (by simp)

/-- Pushing forward the uniform hidden-root input gives a finite rejection/split law.
Each non-rejection result has type `ProperPair N`, and its probability of occurrence
as a class of results is the mixed-sign fraction. -/
theorem hiddenSplitLaw_acceptance (hn : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (hodd : Odd (multiplicity i)) (input : PMF (SquareFiber (roots i)))
    (hinput : input = uniformHiddenRoot labels multiplicity roots hi publicRoot hn ho hodd) :
    ((input.map (hiddenSplitTrial labels multiplicity roots hi publicRoot)).toOuterMeasure
      {outcome | outcome ≠ none}).toReal = 1 - 2 / (2 : ℝ)^N.primeFactors.card := by
  classical
  obtain ⟨hmem, _, _, hratio, _⟩ :=
    hidden_split_fraction hn ho hnot labels multiplicity roots hi hodd publicRoot
  rw [PMF.toOuterMeasure_map_apply, hinput, uniformHiddenRoot,
    PMF.toOuterMeasure_uniformOfFinset_apply]
  let signs := comparisonSigns labels multiplicity roots hi hodd publicRoot (oddSigns hn ho)
  let favorable := (usefulSigns N.primeFactors.card).map signs.symm.toEmbedding
  let all := Finset.univ.map signs.symm.toEmbedding
  have hfilt :
      (all.filter fun x ↦ x ∈ (hiddenSplitTrial labels multiplicity roots hi publicRoot) ⁻¹'
        {outcome | outcome ≠ none}) =
        favorable := by
    ext x
    rw [Finset.mem_filter]
    change (x ∈ all ∧ hiddenSplitTrial labels multiplicity roots hi publicRoot x ≠ none) ↔ _
    rw [hiddenSplitTrial_accepts, ← hmem x]
    simp [all, favorable, signs]
  rw [hfilt, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have hreal := congrArg (fun x : ℚ ↦ (x : ℝ)) hratio
  push_cast at hreal
  simpa only [favorable, signs] using hreal

/-- The accepted law exists and can be represented as a PMF on proper pairs. -/
theorem hiddenSplitLaw_conditioned (hn : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (hodd : Odd (multiplicity i)) (input : PMF (SquareFiber (roots i)))
    (hinput : input = uniformHiddenRoot labels multiplicity roots hi publicRoot hn ho hodd) :
    let trial := input.map (hiddenSplitTrial labels multiplicity roots hi publicRoot)
    let accepted : Set (Option (ProperPair N)) := {outcome | outcome ≠ none}
    ∃ (h : ∃ o ∈ accepted, o ∈ trial.support) (law : PMF (ProperPair N)),
      law.map some = trial.filter accepted h := by
  classical
  dsimp only
  let trial := input.map (hiddenSplitTrial labels multiplicity roots hi publicRoot)
  let accepted : Set (Option (ProperPair N)) := {outcome | outcome ≠ none}
  have hmass := hiddenSplitLaw_acceptance labels multiplicity roots hi publicRoot hn ho hnot
    hodd input hinput
  have hfour : (4 : ℝ) ≤ (2 : ℝ)^N.primeFactors.card := by
    calc
      4 = (2 : ℝ)^2 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (two_le_factor_count hn hnot)
  have hnonzero : trial.toOuterMeasure accepted ≠ 0 := by
    intro hz
    change (trial.toOuterMeasure accepted).toReal = _ at hmass
    rw [hz, ENNReal.toReal_zero] at hmass
    have hp : 0 < (2 : ℝ)^N.primeFactors.card := by positivity
    have hlt : (2 : ℝ) / (2 : ℝ)^N.primeFactors.card < 1 :=
      (div_lt_iff₀ hp).mpr (by linarith only [hfour])
    linarith only [hmass, hlt]
  have h : ∃ o ∈ accepted, o ∈ trial.support := by
    obtain ⟨o, hs, ha⟩ :=
      Set.not_disjoint_iff.mp (mt (PMF.toOuterMeasure_apply_eq_zero_iff trial accepted).mpr hnonzero)
    exact ⟨o, ha, hs⟩
  have hwitness := h
  obtain ⟨o, ho', _⟩ := hwitness
  cases o with
  | none => exact (ho' rfl).elim
  | some fallback =>
    let filtered := trial.filter accepted h
    refine ⟨h, filtered.map (fun o ↦ o.getD fallback), ?_⟩
    rw [PMF.map_comp]
    change filtered.map (some ∘ fun o ↦ o.getD fallback) = filtered
    calc
      _ = filtered.map id := by
        ext result
        rw [PMF.map_apply, PMF.map_apply]
        apply tsum_congr
        intro o
        cases o with
        | none =>
          have hz : filtered none = 0 :=
            PMF.filter_apply_eq_zero_of_notMem h (by simp [accepted])
          simp [hz]
        | some outcome => rfl
      _ = _ := PMF.map_id filtered

end Cogentic.RandomizedHiddenSplitLaw
