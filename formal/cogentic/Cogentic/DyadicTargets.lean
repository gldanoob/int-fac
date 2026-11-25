import Cogentic.CharacterEstimate
import Mathlib.Analysis.SpecificLimits.Normed

namespace Cogentic

open Finset Filter Real Formalism.MainNotions.GlobalTheoryTheory

/-- The target primes in the dyadic interval (B/2,B]. -/
def dyadicTargets (β : ℕ) : Finset ℕ := Nat.primesLE (2^β) \ Nat.primesLE (2^(β-1))

theorem mem_dyadicTargets {p β : ℕ} : p ∈ dyadicTargets β ↔
    p.Prime ∧ 2^(β-1) < p ∧ p ≤ 2^β := by
  rw [dyadicTargets, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hi,hp⟩,absent⟩
    exact ⟨hp,lt_of_not_ge (fun low => absent ⟨low,hp⟩),hi⟩
  · rintro ⟨hp,lo,hi⟩
    exact ⟨⟨hi,hp⟩, fun h => lo.not_ge h.1⟩

theorem principal_psi (x : ℝ) :
    psi0 (1 : DirichletCharacter ℂ 1) x = ((Chebyshev.psi x - x : ℝ) : ℂ) := by
  have trivial (j : ℕ) : (1 : DirichletCharacter ℂ 1) (j : ZMod 1) = 1 :=
    MulChar.one_apply ((ZMod.isUnit_iff_coprime j 1).mpr (Nat.coprime_one_right j))
  simp only [psi0, if_true, trivial, mul_one, Chebyshev.psi, Complex.ofReal_sub, Complex.ofReal_sum]
  rfl

private theorem dyadic_theta_accurate (line : DirichletLZerosOnLine) :
    ∀ᶠ β : ℕ in atTop,
      |Chebyshev.theta ((2:ℝ)^β) - (2:ℝ)^β| ≤ (2:ℝ)^β / 10 := by
  obtain ⟨C,hc,all⟩ := Window.uniform_psi_from_critical_line line
  let K := 10*(16*C+2)
  have kpos : 0 < K := by dsimp [K]; linarith
  have root : 1 < √2 := Real.one_lt_sqrt_two
  have small := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 2 root).bound (inv_pos.mpr kpos)
  filter_upwards [small, eventually_ge_atTop 1] with β hβ bpos
  let x : ℝ := 2^β
  have xb : 2 ≤ x := by simpa [x] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) bpos
  have b1 : (1:ℝ) ≤ β := by exact_mod_cast bpos
  have logtwo : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have logx : log x ≤ β := by
    dsimp [x]
    rw [Real.log_pow]
    exact (mul_le_mul_of_nonneg_left logtwo (Nat.cast_nonneg β)).trans_eq (mul_one _)
  have lx : 0 ≤ log x := log_nonneg (by linarith)
  have log3 : log 3 ≤ 2 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)]
  have D : 1+log (3*x) ≤ 4*β := by rw [log_mul (by norm_num) (by linarith : x ≠ 0)]; linarith
  have dpos : 0 ≤ 1+log (3*x) := by linarith [log_nonneg (show 1 ≤ 3*x by linarith)]
  have psi := all 1 (1 : DirichletCharacter ℂ 1) x xb
  rw [principal_psi, Complex.norm_real, Real.norm_eq_abs] at psi
  simp only [Nat.cast_one, mul_one] at psi
  have tail := Chebyshev.psi_sub_theta_le (show 1 ≤ x by linarith)
  have pos := Chebyshev.theta_le_psi x
  have approx : |Chebyshev.theta x - x| ≤ (16*C+2)*√x*(β:ℝ)^2 := by
    have ps := psi.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dpos D 2) (by positivity))
    have ta := tail.trans (mul_le_mul_of_nonneg_left logx (by positivity))
    have sq : (β:ℝ) ≤ (β:ℝ)^2 := by nlinarith
    have ta' := ta.trans (mul_le_mul_of_nonneg_left sq (by positivity : 0 ≤ 2*√x))
    obtain ⟨lo,hi⟩ := abs_le.mp ps
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg (β:ℝ))]
  refine approx.trans ?_
  have rs : √x = (√2)^β := by
    have eq : ((√2)^β)^2 = x := by rw [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
    rw [← eq, Real.sqrt_sq (by positivity)]
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (β:ℝ)), abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg 2) β)] at hβ
  have bbound : K*(β:ℝ)^2 ≤ √x := by
    rw [rs]
    calc
      _ ≤ K*(K⁻¹*(√2)^β) := mul_le_mul_of_nonneg_left hβ kpos.le
      _ = (√2)^β := by rw [← mul_assoc, mul_inv_cancel₀ kpos.ne', one_mul]
  have full := mul_le_mul_of_nonneg_right bbound (Real.sqrt_nonneg x)
  rw [← sq, Real.sq_sqrt (by linarith)] at full
  dsimp [K] at full
  linarith

/-- The original integer count test holds throughout the sufficiently large
    dyadic intervals, with the exact same constant as the saturation code. -/
theorem dyadic_count_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ cutoff : ℕ, ∀ β ≥ cutoff, 2^β ≤ 3*β*(dyadicTargets β).card := by
  obtain ⟨b,hb⟩ := eventually_atTop.mp (dyadic_theta_accurate line)
  refine ⟨b+1, fun β hβ => ?_⟩
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : β ≠ 0)
  have upper := (abs_le.mp (hb t (by omega))).2
  have lower := (abs_le.mp (hb (t+1) (by omega))).1
  have sub : Nat.primesLE (2^t) ⊆ Nat.primesLE (2^(t+1)) := by
    intro p hp
    obtain ⟨hle,prime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hle.trans (Nat.pow_le_pow_right (by decide) (by omega)),prime⟩
  have logsum : (∑ p ∈ dyadicTargets (t+1), log p) =
      Chebyshev.theta ((2:ℝ)^(t+1)) - Chebyshev.theta ((2:ℝ)^t) := by
    simp only [dyadicTargets, Nat.add_sub_cancel, sum_sdiff_eq_sub sub]
    rw [← Chebyshev.theta_eq_sum_primesLE_log, ← Chebyshev.theta_eq_sum_primesLE_log]
    norm_cast
  have each (p : ℕ) (hp : p ∈ dyadicTargets (t+1)) : log p ≤ t+1 := by
    obtain ⟨prime,_,le⟩ := mem_dyadicTargets.mp hp
    have l := log_le_log (by exact_mod_cast prime.pos : (0:ℝ) < p)
      (show (p:ℝ) ≤ (2:ℝ)^(t+1) by exact_mod_cast le)
    rw [Real.log_pow] at l
    have lt : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    push_cast at l
    nlinarith [mul_le_mul_of_nonneg_left lt (by positivity : (0:ℝ) ≤ t+1)]
  have count := sum_le_sum each
  rw [logsum, sum_const, nsmul_eq_mul] at count
  have good : (2:ℝ)^(t+1) ≤ 3*((t:ℝ)+1)*(dyadicTargets (t+1)).card := by
    rw [pow_succ] at lower count ⊢
    nlinarith
  exact_mod_cast good

end Cogentic

#print axioms Cogentic.dyadic_count_from_critical_line
