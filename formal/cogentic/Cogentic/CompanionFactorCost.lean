import Cogentic.CompanionSplitCost
import TwoThirdsFactor
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Cogentic.CompanionFactorCost
open Real Filter CompanionSplitCost TwoThirdsFactor

/-- Eventual single-call charges on the two-thirds scale give complete prime
factorization with all multiplicities at the same leading constant. The finitely
many smaller cofactors may carry arbitrary charges. -/
theorem recursive_factorization_cost (charge : ℕ → ℕ) {A : ℝ} (ha : 0 ≤ A)
    (perCall : ∀ᶠ m : ℕ in atTop, (charge m : ℝ) ≤ exp (A * scale m)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t : Run n,
      t.factors.prod = n ∧ (∀ p ∈ t.factors, p.Prime) ∧
      (∀ p, p.Prime → ∀ k, p^k ∣ n ↔ k ≤ t.factors.count p) ∧
      (t.work charge : ℝ) ≤ exp ((A + ε) * scale n) := by
  intro ε he
  have logs : Tendsto (fun n : ℕ => log n) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨m₀,localBound⟩ := eventually_atTop.mp (perCall.and (logs.eventually_ge_atTop (exp 1)))
  let K := (Finset.range m₀).sup charge + 1
  have kp : 1 ≤ K := Nat.le_add_left 1 _
  have kp' : (0:ℝ) < K := by exact_mod_cast (by omega : 0<K)
  have two : 0 < log 2 := log_pos (by norm_num)
  have little := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<2/3)).bound (by linarith : 0<ε/2)
  filter_upwards [eventually_ge_atTop m₀, logs.eventually_ge_atTop (2*(K:ℝ)/log 2), logs.eventually little]
    with n large capLog pen t
  have hL : exp 1 ≤ log n := (localBound n large).2
  have Lpos := (exp_pos 1).trans_le hL
  have z1 := (le_log_iff_exp_le Lpos).mpr hL
  have sv : (log n)^(2/3:ℝ) ≤ scale n :=
    le_mul_of_one_le_right (rpow_nonneg Lpos.le _) (one_le_rpow z1 (by norm_num))
  have spos := (rpow_pos_of_pos Lpos (2/3:ℝ)).trans_le sv
  let cap := ⌊exp (A * scale n)⌋₊
  have capPos : 1 ≤ cap := Nat.le_floor (by simpa using one_le_exp (mul_nonneg ha spos.le))
  have bound (a : ℕ) (_ : 2 ≤ a) (an : a ≤ n) : charge a ≤ K*cap := by
    by_cases big : m₀ ≤ a
    · obtain ⟨value,hloga⟩ := localBound a big
      have alp := (exp_pos 1).trans_le hloga
      have ala : 0<(a:ℝ) := by exact_mod_cast (by omega : 0<a)
      have mono := log_le_log ala (Nat.cast_le.mpr an)
      have gz := (le_log_iff_exp_le alp).mpr hloga
      have mscale : scale a ≤ scale n := by
        unfold scale; gcongr
      exact (Nat.le_floor (value.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_left mscale ha)))).trans
        (Nat.le_mul_of_pos_left _ (by omega : 0<K))
    · have hk := Finset.le_sup (f:=charge) (Finset.mem_range.mpr (by omega : a < m₀))
      exact (hk.trans (Nat.le_succ _)).trans (Nat.le_mul_of_pos_right _ capPos)
  have calls : ((2*n.log2-1 : ℕ):ℝ)*(K:ℝ) ≤ (log n)^2 := by
    have coeff := log2_le_logb n
    rw [logb] at coeff
    calc
      _ ≤ (2*(n.log2:ℝ))*(K:ℝ) := by gcongr; exact_mod_cast Nat.sub_le (2*n.log2) 1
      _ ≤ (log n)*(2*(K:ℝ)/log 2) := (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left coeff (by norm_num : (0:ℝ)≤2)) kp'.le).trans_eq (by ring)
      _ ≤ _ := by rw [sq]; gcongr
  have poly : (log n)^2 ≤ exp (ε*scale n) := by
    simp only [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤log (log n)),
      abs_of_nonneg (rpow_nonneg Lpos.le (2/3:ℝ))] at pen
    rw [show (log n)^2 = exp (log (log n)+log (log n)) by rw [exp_add,exp_log Lpos,sq]]
    exact exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left sv he.le])
  refine ⟨t.correct.1,fun p hp=>Nat.prime_def.mpr (t.correct.2 p hp),
    fun p hp k=>t.multiplicity (Nat.prime_def.mp hp) k,?_⟩
  calc
    _ ≤ ((2*n.log2-1:ℕ):ℝ)*((K:ℝ)*(cap:ℝ)) := by exact_mod_cast t.work_bound charge bound
    _ ≤ (log n)^2*exp (A*scale n) := by
      rw [←mul_assoc]; exact mul_le_mul calls (Nat.floor_le (exp_pos _).le) (Nat.cast_nonneg _) (sq_nonneg _)
    _ ≤ exp (ε*scale n)*exp (A*scale n) := by gcongr
    _ = _ := by rw [←exp_add]; congr 1; ring

end Cogentic.CompanionFactorCost

#print axioms Cogentic.CompanionFactorCost.recursive_factorization_cost
