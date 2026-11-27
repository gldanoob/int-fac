import Cogentic.RandomizedFactorLawAsymptotic
import Cogentic.RandomizedInputDriver

namespace Cogentic.RandomizedInputDriver

open RandomizedCostedFactorLaw RandomizedOneThirdAsymptotic Filter Real
open scoped ENNReal

private theorem precheck_verify_cost {k n : ℕ} (hn : 2 ≤ n)
    (h : (RandomizedPreprocessing.run k n).2 ≤ (10000*(k+1))^32*(n.log2+2)^32) :
    (RandomizedPreprocessing.run k n).2 + RandomizedSplitVerification.verifierBudget n ≤
      ((10000*(k+1))^32 * 2^32 + 53) * (n.log2 + 1)^32 := by
  let b := n.log2 + 1
  have h1 : 1 ≤ b := by dsimp [b]; omega
  have hsize : n.size ≤ b := Nat.size_le.mpr Nat.lt_log2_self
  have hprep : n.log2+2 ≤ 2*b := by dsimp [b]; omega
  have hv := RandomizedSplitVerification.verifierBudget_le_quadratic (show 0 < n by omega)
  calc
    _ ≤ (10000*(k+1))^32 * (2*b)^32 + 53 * b^2 :=
      Nat.add_le_add (h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hprep 32)))
        (hv.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 2)))
    _ ≤ (10000*(k+1))^32 * (2^32*b^32) + 53 * b^32 := by
      rw [mul_pow 2 b 32]
      exact Nat.add_le_add le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right h1 (by decide : 2 ≤ 32)))
    _ = _ := by rw [add_mul, mul_assoc]

/-- A finite real budget for the actual hard sampler suffices. Preprocessing
and divisor verification are charged here at every node. -/
theorem factor_expected_from_hard (k : ℕ)
    (prep : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n ∧
      (RandomizedPreprocessing.run k n).2 ≤ (10000*(k+1))^32*(n.log2+2)^32)
    (hard : HardKernel) (B : ℕ → ℝ) (hB₀ : ∀ n, 0 ≤ B n)
    (hmean : ∀ n (hn : 2 ≤ n) (ho : Odd n) (hp : ¬n.Prime) (hpow : ¬IsPrimePow n),
      mean (hard n hn ho hp hpow) (fun s => s.work) ≤ ENNReal.ofReal (B n))
    {C : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, B n ≤ exp ((C+δ) * scale n)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
      mean (factor k (fun m hm => (prep m hm).1) hard n hn) (fun out => out.2) ≤
        ENNReal.ofReal (exp ((C+ε) * scale n)) := by
  let A : ℕ := (10000*(k+1))^32 * 2^32 + 53
  let P (n : ℕ) : ℝ := (A : ℝ) * ((n.log2 : ℝ) + 1)^32
  let T (n : ℕ) : ℝ := P n + B n
  have hP n : 0 ≤ P n := by dsimp [P]; positivity
  have front {n : ℕ} (hn : 2 ≤ n) :
      ((RandomizedPreprocessing.run k n).2 : ℝ≥0∞) + RandomizedSplitVerification.verifierBudget n ≤
        ENNReal.ofReal (P n) := by
    have h := precheck_verify_cost hn (prep n hn).2
    have hr : (((RandomizedPreprocessing.run k n).2 + RandomizedSplitVerification.verifierBudget n : ℕ) : ℝ) ≤ P n := by
      dsimp [P, A]
      exact_mod_cast h
    rw [← Nat.cast_add, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hr
  let sound := fun m hm => (prep m hm).1
  have hs n hn hp := (splitter_mean_le k sound hard (fun m => ENNReal.ofReal (B m)) hmean n hn hp).trans
    (add_le_add (front hn) le_rfl)
  intro ε hε
  have hδ : 0 < ε/3 := by positivity
  have hlocalT : ∀ᶠ n : ℕ in atTop, T n ≤ exp ((C + 2*(ε/3)) * scale n) := by
    filter_upwards [hlocal (ε/3) hδ, eventually_bitPoly_le_exp (A := (A : ℝ)) hδ 32,
      eventually_bitPoly_le_exp (A := 2) hδ 0, scale_grows.eventually_ge_atTop 0] with n hb hp htwo hscale
    simp only [pow_zero, mul_one] at htwo
    have hp' : P n ≤ exp ((C + ε/3) * scale n) :=
      hp.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hscale))
    calc
      T n ≤ 2 * exp ((C + ε/3) * scale n) := by dsimp [T]; linarith
      _ ≤ exp ((ε/3) * scale n) * exp ((C + ε/3) * scale n) :=
        mul_le_mul_of_nonneg_right htwo (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  have result := expectedCost_eventually_le_exp (splitter k sound hard)
    (fun n => (RandomizedPreprocessing.run k n).2) T (by linarith : 0 ≤ C + 2*(ε/3)) hδ
    (fun n hp => calc
      _ ≤ ENNReal.ofReal (P n) := (le_add_right le_rfl).trans (front hp.two_le)
      _ ≤ ENNReal.ofReal (T n) := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (hB₀ n)))
    (fun n hn hp => by simpa [T, ENNReal.ofReal_add (hP n) (hB₀ n)] using hs n hn hp) hlocalT
  filter_upwards [result] with n h hn
  rw [factor_eq]
  have he : C + 2 * (ε / 3) + ε / 3 = C + ε := by ring
  rw [he] at h
  exact h hn

end Cogentic.RandomizedInputDriver
