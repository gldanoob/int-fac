import Cogentic.RandomizedEpochEventCost
import Cogentic.RandomizedInputAsymptotic
import Cogentic.RandomizedTotalEpochSplit

namespace Cogentic.RandomizedInputDriver

open RandomizedCostedFactorLaw RandomizedOneThirdAsymptotic RandomizedCappedEpoch
open RandomizedEpochKernel RandomizedTotalEpochSplit Filter Real
open scoped ENNReal

/-- Use the finite tape splitter and its deterministic fallback on each hard
input. The counted precheck handles the remaining recursive nodes. -/
noncomputable def epochHard {α : ℕ → Type} (epoch : ∀ n, PMF (α n))
    (attempt : ∀ n, α n → Option (Factors n) × ℕ) : HardKernel :=
  fun n hn _ hp _ => splitLaw hn hp (epoch n) (attempt n)

/-- The epoch cost/success ratio is required only eventually. A zero success
probability on any finite set of inputs is covered by deterministic trial division. -/
theorem factor_expected_from_epoch {α : ℕ → Type} [∀ n, Fintype (α n)]
    (k : ℕ) (prep : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n ∧
        (RandomizedPreprocessing.run k n).2 ≤ (10000*(k+1))^32*(n.log2+2)^32)
    (epoch : ∀ n, PMF (α n)) (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hEpoch : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
      ∃ W S : ℝ, 0 < S ∧
        mean (epoch n) (fun a => ((attempt n a).2+1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
        S ≤ (((epoch n).map (attempt n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
        W / S ≤ exp ((C+δ)*scale n)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
      mean (factor k (fun m hm => (prep m hm).1) (epochHard epoch attempt) n hn)
        (fun out => out.2) ≤ ENNReal.ofReal (exp ((C+ε)*scale n)) := by
  classical
  let B (n : ℕ) : ℝ := if h : 2 ≤ n ∧ Odd n ∧ ¬n.Prime ∧ ¬IsPrimePow n then
      (mean (splitLaw h.1 h.2.2.1 (epoch n) (attempt n)) (fun s => s.work)).toReal else 0
  refine factor_expected_from_hard k prep (epochHard epoch attempt) B ?_ ?_ hC ?_
  · intro n
    dsimp only [B]
    split <;> positivity
  · intro n hn ho hp hpow
    have hd : 2 ≤ n ∧ Odd n ∧ ¬n.Prime ∧ ¬IsPrimePow n := ⟨hn, ho, hp, hpow⟩
    simp [epochHard, B, hd, ENNReal.ofReal_toReal (splitLaw_mean_ne_top hn hp (epoch n) (attempt n))]
  · intro δ hδ
    filter_upwards [hEpoch δ hδ] with n h
    dsimp only [B]
    split
    · rename_i hn
      obtain ⟨W, S, hS, work, hit, ratio⟩ := h hn.2.1 hn.2.2.1 hn.2.2.2
      have hb := (splitLaw_mean_le hn.1 hn.2.2.1 (epoch n) (attempt n)).trans
        ((epoch_ratio_le_of_real_bounds (epoch n) (attempt n) hS work hit).trans
          (ENNReal.ofReal_le_ofReal ratio))
      simpa [ENNReal.toReal_ofReal (exp_pos _).le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    · exact (exp_pos _).le

end Cogentic.RandomizedInputDriver
