import Cogentic.RandomizedCostedFactorLaw
import Cogentic.RandomizedOneThirdAsymptotic

namespace Cogentic.RandomizedCostedFactorLaw

open Filter Real RandomizedOneThirdAsymptotic
open scoped ENNReal

/-- Lift a finite local budget to the expected cost of the joint factor-output
and work law. The conclusion bounds the extended expectation itself. -/
theorem expectedCost_eventually_le_exp (split : SplitKernel) (leaf : ℕ → ℕ)
    (T : ℕ → ℝ) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (hleaf : ∀ n, n.Prime → (leaf n : ℝ≥0∞) ≤ ENNReal.ofReal (T n))
    (hsplit : ∀ n (hn : 2 ≤ n) (hp : ¬ n.Prime),
      mean (split n hn hp) (fun s => s.work) ≤ ENNReal.ofReal (T n))
    (hlocal : ∀ᶠ n : ℕ in atTop, T n ≤ exp (c * scale n)) :
    ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
      expectedCost split leaf n hn ≤ ENNReal.ofReal (exp ((c + ε) * scale n)) := by
  have hδ : 0 < ε / 2 := by positivity
  obtain ⟨M, hmono, hM, hbound⟩ := exists_monotone_majorant hc hδ hlocal
  have bound {n : ℕ} (hn : 2 ≤ n) := expectedCost_le_log2 split leaf (fun n => ENNReal.ofReal (M n))
    (ENNReal.ofReal_mono.comp hmono)
    (fun n hp => (hleaf n hp).trans (ENNReal.ofReal_le_ofReal (hM n)))
    (fun n hn hp => (hsplit n hn hp).trans (ENNReal.ofReal_le_ofReal (hM n))) hn
  filter_upwards [hbound, eventually_bitPoly_le_exp (A := 2) hδ 1] with n hMn hpoly
  intro hn
  let a := 2 * n.log2 - 1
  have ha : (a : ℝ) ≤ exp ((ε/2) * scale n) := by
    have hnat : a ≤ 2 * n.log2 := Nat.sub_le ..
    have hreal : (a : ℝ) ≤ 2 * (n.log2 : ℝ) := by exact_mod_cast hnat
    simp only [pow_one] at hpoly
    linarith
  calc
    _ ≤ (a : ℝ≥0∞) * ENNReal.ofReal (M n) := bound hn
    _ ≤ ENNReal.ofReal (exp ((ε/2) * scale n)) *
          ENNReal.ofReal (exp ((c + ε/2) * scale n)) := by
        exact mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal ha)
          (ENNReal.ofReal_le_ofReal hMn)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
      congr 2
      ring

#print axioms expectedCost_eventually_le_exp

end Cogentic.RandomizedCostedFactorLaw
