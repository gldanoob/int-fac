import Cogentic.PrincipalMass
import Cogentic.SaddleLocation

open Real Set MeasureTheory
open scoped BigOperators

namespace Cogentic.Window

noncomputable section

/-- Comparison with the integral having the constant denominator H at the
    top of the logarithmic band gains an entire factor exp(λ/2). -/
theorem sharp_tilted_integral (H k : ℝ) (hH : 0 < H) (hl : 2 ≤ k*H) :
    Real.exp (k*H) ≤ 2*(k*H)*(∫ v in H/2..H, Real.exp (k*v)/v) := by
  have kp : 0 < k := by by_contra! z; nlinarith [mul_nonpos_of_nonpos_of_nonneg z hH.le]
  have ord : H/2 ≤ H := by linarith
  have cont : ContinuousOn (fun v : ℝ => Real.exp (k*v)/v) (uIcc (H/2) H) := by
    intro x hx
    rw [uIcc_of_le ord] at hx
    have nz : x ≠ 0 := (by linarith [hx.1] : 0 < x).ne'
    fun_prop (disch := assumption)
  have bound := intervalIntegral.integral_mono_on (μ := volume) ord
    (f := fun v : ℝ => Real.exp (k*v)/H) ((by fun_prop : Continuous (fun v : ℝ => Real.exp (k*v)/H)).intervalIntegrable ..)
    cont.intervalIntegrable (fun x hx => div_le_div_of_nonneg_left (Real.exp_pos _).le
      (by linarith [hx.1]) hx.2)
  have ant (v : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (k*x)/(k*H))
      (Real.exp (k*v)/H) v := by
    convert! (((hasDerivAt_id v).const_mul k).exp.div_const (k*H)) using 1
    field_simp
    rfl
  have ex := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := H/2) (b := H)
    (fun v _ => ant v) ((by fun_prop : Continuous (fun v : ℝ => Real.exp (k*v)/H)).intervalIntegrable ..)
  rw [ex,← sub_div] at bound
  have main := (div_le_iff₀ (mul_pos kp hH)).mp bound
  have two : 2 ≤ Real.exp (k*(H/2)) := by linarith [Real.add_one_le_exp (k*(H/2))]
  have half : 2*Real.exp (k*(H/2)) ≤ Real.exp (k*H) := by
    rw [show k*H=k*(H/2)+k*(H/2) by ring,Real.exp_add]
    exact mul_le_mul_of_nonneg_right two (Real.exp_pos _).le
  nlinarith only [main,half]

/-- The actual Euler mass at the saddle is at least exp(u), an estimate
    that survives each deleted factor at the cost of its weight. -/
theorem saddle_euler_log_lower (J : Finset ℕ) (α H : ℝ) (hH : 0 < H)
    (band : ∀ p ∈ J, Real.log p ≤ H) :
    saddleMean J α/H ≤ Real.log (eulerMass J α) := by
  have den (p : ℕ) : 0 < 1+(p:ℝ)^(-α) := by positivity
  rw [eulerMass,Real.log_prod (fun p _ => (den p).ne'),div_le_iff₀ hH,saddleMean,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  have w : 0 ≤ primeProbability α p := by unfold primeProbability; positivity
  have cap := Real.one_sub_inv_le_log_of_pos (den p)
  have eq : 1-(1+(p:ℝ)^(-α))⁻¹=primeProbability α p := by unfold primeProbability; field_simp; ring
  rw [eq] at cap
  exact (mul_le_mul_of_nonneg_left (band p hp) w).trans (mul_le_mul_of_nonneg_right cap hH.le)

theorem fixed_saddle_euler_margin (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B α u : ℝ) (D : Finset ℕ), 16 ≤ B → 199/200 ≤ α → α ≤ 1 →
      C*(1+Real.log (3*B))^2*B^(-19/400:ℝ) ≤ 1 →
      let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      let H := Real.log B
      let lam := (1-α)*H
      D ⊆ J → saddleMean J α=H*u → 2 ≤ lam →
      Real.exp lam ≤ 2*lam*(4*u+1) ∧ lam ≤ 2*Real.log (16*u+4) ∧
      u-D.card*B^(-199/400:ℝ) ≤ Real.log (eulerMass (J\D) α) := by
  obtain ⟨C,hC,prime⟩ := tilted_prime_mass line
  refine ⟨C,hC,fun B α u D hb a0 a1 small => ?_⟩
  let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
  let H := Real.log B
  let l := (1-α)*H
  dsimp only
  intro om saddle lam
  have bp : 0 < B := by linarith
  have hp : 0 < H := Real.log_pos (by linarith)
  have ord (p : ℕ) (h : p ∈ J) : 1 ≤ p ∧ H/2 ≤ Real.log p ∧ Real.log p ≤ H := by
    obtain ⟨rng,pr⟩ := Finset.mem_filter.mp h
    obtain ⟨lo,hi⟩ := Finset.mem_Ioc.mp rng
    refine ⟨pr.one_le,?_,?_⟩
    · dsimp [H]
      rw [← Real.log_sqrt bp.le]
      exact Real.log_le_log (Real.sqrt_pos.mpr bp) (Nat.lt_of_floor_lt lo).le
    · exact Real.log_le_log (by exact_mod_cast pr.pos) ((Nat.cast_le.mpr hi).trans (Nat.floor_le bp.le))
  have actual := prime B α ∅ hb a0 a1 (Finset.empty_subset J)
  simp only [Finset.sdiff_empty,Finset.card_empty,Nat.cast_zero,zero_mul,add_zero] at actual
  let I := ∫ x in H/2..H, Real.exp ((1-α)*x)/x
  let P := ∑ p ∈ J, (p:ℝ)^(-α)
  change |P-I| ≤ _ at actual
  have cmp := (tilted_mean_bounds J H α hp.le (by linarith) ord).1
  change H/4*P ≤ saddleMean J α at cmp
  change saddleMean J α=H*u at saddle
  rw [saddle] at cmp
  have pu : P ≤ 4*u := by
    apply le_of_mul_le_mul_left (a := H) _ hp
    linarith only [cmp]
  have ij : I ≤ 4*u+1 := by linarith [((abs_le.mp actual).1)]
  have sharp := sharp_tilted_integral H (1-α) hp lam
  change Real.exp l ≤ 2*l*I at sharp
  have lp : 0 < l := by change 2 ≤ l at lam; linarith
  have el := sharp.trans (mul_le_mul_of_nonneg_left ij (show 0 ≤ 2*l by positivity))
  have coarse : l ≤ 2*Real.log (16*u+4) := by
    have ke : l ≤ 2*Real.exp (l/2) := by linarith [Real.add_one_le_exp (l/2)]
    have sc : 0 ≤ 4*u+1 := by
      have nn : 0 ≤ P := Finset.sum_nonneg (fun p _ => by positivity)
      linarith
    have term := mul_le_mul_of_nonneg_right ke sc
    have eh : Real.exp (l/2)*Real.exp (l/2)=Real.exp l := by rw [← Real.exp_add]; congr 1; ring
    have vv : Real.exp (l/2) ≤ 16*u+4 := by
      apply le_of_mul_le_mul_left (a := Real.exp (l/2)) _ (Real.exp_pos _)
      rw [eh]
      nlinarith only [el,term]
    have lg := Real.log_le_log (Real.exp_pos _) vv
    rw [Real.log_exp] at lg
    linarith
  have full := saddle_euler_log_lower J α H hp (fun p h => (ord p h).2.2)
  rw [saddle,mul_div_cancel_left₀ _ hp.ne'] at full
  let f := fun p : ℕ => Real.log (1+(p:ℝ)^(-α))
  have split : (∑ p ∈ J\D, f p)+(∑ p ∈ D, f p) = ∑ p ∈ J, f p := Finset.sum_sdiff om
  have each (p : ℕ) (h : p ∈ D) : f p ≤ B^(-199/400:ℝ) := by
    have low := Nat.lt_of_floor_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp (om h)).1).1
    have upper := Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.mpr bp) low.le (by linarith : -α ≤ 0)
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul bp.le] at upper
    have cap := Real.log_le_sub_one_of_pos (show 0 < 1+(p:ℝ)^(-α) by positivity)
    change Real.log (1+(p:ℝ)^(-α)) ≤ _
    refine (by linarith only [cap] : Real.log (1+(p:ℝ)^(-α)) ≤ (p:ℝ)^(-α)).trans (upper.trans ?_)
    apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ B)
    linarith
  have cost := Finset.sum_le_sum each
  simp only [Finset.sum_const, nsmul_eq_mul] at cost
  rw [eulerMass,Real.log_prod (fun p _ => by positivity)] at full
  rw [eulerMass,Real.log_prod (fun p _ => by positivity)]
  exact ⟨el,coarse,by dsimp only [f] at split cost; linarith⟩

end

end Cogentic.Window
