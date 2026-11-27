import Cogentic.RandomizedEpochFactorization
import Cogentic.RandomizedPreprocessingCost
import Cogentic.RandomizedSerializedDriver

namespace Cogentic.RandomizedInputDriver

open RandomizedCostedFactorLaw RandomizedOneThirdAsymptotic RandomizedEpochKernel
open RandomizedSerializedDriver RandomizedFactorSerialization Filter Real
open scoped ENNReal

/-- A fixed generator cutoff works for every input. The remaining premise
bounds the actual charge and observed success probability of one hard epoch. -/
theorem serialized_epoch_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ {α : ℕ → Type} [∀ n, Fintype (α n)] (epoch : ∀ n, PMF (α n))
      (attempt : ∀ n, α n → Option (Factors n) × ℕ) {C : ℝ}, 0 ≤ C →
      (∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Odd n → ¬n.Prime → ¬IsPrimePow n →
        ∃ W S : ℝ, 0 < S ∧
          mean (epoch n) (fun a => ((attempt n a).2+1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
          S ≤ (((epoch n).map (attempt n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
          W / S ≤ exp ((C+δ)*scale n)) →
      (∀ n (hn : 2 ≤ n) bits, bits ∈ (outputBits k sound (epochHard epoch attempt) n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound (epochHard epoch attempt) n hn) (fun out => out.2) ≤
          ENNReal.ofReal (exp ((C+ε)*scale n)) := by
  obtain ⟨k, prep⟩ := RandomizedPreprocessing.of_critical_line line
  let sound := fun m hm => (prep m hm).1
  refine ⟨k, sound, ?_⟩
  intro α _ epoch attempt C hC hEpoch
  exact ⟨fun _ hn _ => outputBits_support_correct k sound (epochHard epoch attempt) hn,
    serializedFactor_expected_eventually k sound (epochHard epoch attempt) hC
      (factor_expected_from_epoch k prep epoch attempt hC hEpoch)⟩

#print axioms serialized_epoch_from_critical_line

end Cogentic.RandomizedInputDriver
