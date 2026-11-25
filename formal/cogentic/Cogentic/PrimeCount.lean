import Cogentic.WindowPrime
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

namespace Cogentic.Window
open Finset ArithmeticFunction Real

noncomputable def twistedPsi {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, (vonMangoldt n : ℂ) * χ n

private noncomputable def primeLog {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n.Prime then (Real.log n : ℂ) * χ n else 0

noncomputable def twistedTheta {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, primeLog χ n

@[simp] theorem twistedTheta_one {q : ℕ} (χ : DirichletCharacter ℂ q) : twistedTheta χ 1 = 0 := by
  simp [twistedTheta, primeLog]

@[simp] theorem twistedTheta_zero {q : ℕ} (χ : DirichletCharacter ℂ q) : twistedTheta χ 0 = 0 := by
  simp [twistedTheta]

/-- The error from discarding prime powers is bounded uniformly over all characters. -/
theorem prime_power_tail {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 1 ≤ x) : ‖twistedPsi χ x - twistedTheta χ x‖ ≤ 2 * √x * Real.log x := by
  unfold twistedPsi twistedTheta
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (le_trans ?_ (Chebyshev.psi_sub_theta_le hx))
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, sum_filter]
  apply sum_le_sum
  intro n hn
  by_cases hp : n.Prime
  · simp [primeLog, hp, vonMangoldt_apply_prime hp]
  · simp only [primeLog, hp, ↓reduceIte, sub_zero, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    simpa using mul_le_mul_of_nonneg_left (χ.norm_le_one n) (vonMangoldt_nonneg (n := n))

/-- Discrete partial summation for a decreasing real weight and complex coefficients. -/
private theorem decreasing_weight (a : ℕ → ℂ) (w : ℕ → ℝ) (wpos : ∀ j, 0 ≤ w j)
    (dec : Antitone w) {m : ℕ} {K : ℝ}
    (partialBound : ∀ j ≤ m, ‖∑ i ∈ range j, a i‖ ≤ K) :
    ‖∑ i ∈ range m, (w i : ℂ)*a i‖ ≤ w 0*K := by
  let A (j : ℕ) := ∑ i ∈ range j, a i
  let W (j : ℕ) := ∑ i ∈ range j, (w i : ℂ)*a i
  have residual (j : ℕ) (hj : j ≤ m) : ‖W j - w j * A j‖ ≤ (w 0-w j)*K := by
    induction j with
    | zero => simp [W, A]
    | succ j ih =>
      have eq : W (j+1) - w (j+1)*A (j+1) =
          (W j-w j*A j) + ((w j-w (j+1) : ℝ) : ℂ)*A (j+1) := by
        simp only [W, A, sum_range_succ, Complex.ofReal_sub]
        ring
      rw [eq]
      apply (norm_add_le ..).trans
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (dec (by omega)))]
      calc
        _ ≤ (w 0-w j)*K + (w j-w (j+1))*K := add_le_add (ih (by omega))
          (mul_le_mul_of_nonneg_left (partialBound _ hj) (sub_nonneg.mpr (dec (by omega))))
        _ = _ := by ring
  change ‖W m‖ ≤ _
  calc
    _ = ‖(W m - w m*A m) + w m*A m‖ := by rw [sub_add_cancel]
    _ ≤ ‖W m - w m*A m‖ + ‖w m*A m‖ := norm_add_le ..
    _ ≤ (w 0-w m)*K + w m*K := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wpos _)]
      exact add_le_add (residual m le_rfl) (mul_le_mul_of_nonneg_left (partialBound m le_rfl) (wpos _))
    _ = _ := by ring

/-- An upper envelope for twisted theta on integer prefixes is enough to remove log p. -/
theorem prime_count_from_theta {q : ℕ} (χ : DirichletCharacter ℂ q) {x K : ℝ} (hK : 0 ≤ K)
    (bounded : ∀ n : ℕ, n ≤ ⌊x⌋₊ → ‖twistedTheta χ n‖ ≤ K) :
    ‖primeCount χ x‖ ≤ (Real.log 2)⁻¹*K := by
  let w (n : ℕ) : ℝ := (Real.log (max 2 (n : ℝ)))⁻¹
  have pos (j : ℕ) : 0 < Real.log (max 2 (j : ℝ)) := Real.log_pos (by linarith [le_max_left (2:ℝ) j])
  have dec : Antitone w := by
    intro a b hab
    exact inv_anti₀ (pos a) (Real.log_le_log (by linarith [le_max_left (2:ℝ) a])
      (max_le_max_left _ (by exact_mod_cast hab)))
  have pref (j : ℕ) (hj : j ≤ ⌊x⌋₊+1) : ‖∑ i ∈ range j, primeLog χ i‖ ≤ K := by
    cases j with
    | zero => simpa using hK
    | succ n =>
      rw [Nat.range_succ_eq_Icc_zero, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
      simpa [twistedTheta, primeLog] using bounded n (by omega)
  have bound := decreasing_weight (primeLog χ) w (fun j => inv_nonneg.mpr (pos j).le) dec pref
  rw [Nat.range_succ_eq_Icc_zero] at bound
  have term (n : ℕ) : (w n : ℂ)*primeLog χ n = if n.Prime then χ n else 0 := by
    by_cases hp : n.Prime
    · have hn : (2:ℝ) ≤ n := by exact_mod_cast hp.two_le
      have hlog : ((Real.log n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
        (Real.log_pos (by linarith : (1:ℝ) < n)).ne'
      simp only [w, max_eq_right hn, primeLog, hp, if_true, Complex.ofReal_inv, ← mul_assoc,
        inv_mul_cancel₀ hlog, one_mul]
    · simp [primeLog, hp]
  simpa only [term, w, Nat.cast_zero, max_eq_left (by norm_num : (0:ℝ) ≤ 2), primeCount] using bound

end Cogentic.Window
