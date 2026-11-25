import Cogentic.PrincipalBand
import Cogentic.WindowSaddle

namespace Cogentic.Window
open Set Real MeasureTheory

noncomputable def primeWave (α t v : ℝ) : ℂ :=
  Complex.exp ((1-((α:ℂ)-(t:ℂ)*Complex.I))*v)/(v:ℂ)

lemma primeWave_continuousOn {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (α t : ℝ) :
    ContinuousOn (primeWave α t) (uIcc a b) := by
  apply ContinuousOn.div _ Complex.continuous_ofReal.continuousOn
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact Complex.ofReal_ne_zero.mpr (ha.trans_le hx.1).ne'
  · fun_prop

lemma primeWave_re (α t v : ℝ) : (primeWave α t v).re =
    Real.exp ((1-α)*v)/v * Real.cos (t*v) := by
  simp [primeWave,Complex.div_ofReal_re,Complex.exp_re,Complex.mul_re,Complex.mul_im]
  ring

/-- The main continuous prime integral loses mass at every frequency with
    |t log B| ≥ 1, including near multiples of 2π. -/
theorem principal_integral_cosine_loss (α t H : ℝ) (hH : 0 < H)
    (hLam : 2 ≤ (1-α)*H) (ht : 1 ≤ |t*H|) :
    Real.exp ((1-α)*H-1)/(36*((1-α)*H)^3) ≤
      (∫ v in H/2..H, primeWave α 0 v).re - (∫ v in H/2..H, primeWave α t v).re := by
  let lam := (1-α)*H
  let g (u : ℝ) := Real.exp (lam*u)/u*(1-Real.cos ((t*H)*u))
  let f (v : ℝ) := Real.exp ((1-α)*v)/v*(1-Real.cos (t*v))
  have posLam : 0 < lam := by dsimp [lam]; linarith
  have frac : 1/lam ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hLam
  have smaller : (1/2:ℝ) ≤ 1-1/lam := by linarith
  have endpt : 1-1/lam ≤ 1 := by linarith [one_div_pos.mpr posLam]
  have cont : ContinuousOn g (Icc (1/2:ℝ) 1) := by
    intro u hu
    have h : u ≠ 0 := (by linarith [hu.1] : 0 < u).ne'
    dsimp [g]
    fun_prop (disch := assumption)
  have above : (∫ u in (1-1/lam)..1, g u) ≤ ∫ u in (1/2:ℝ)..1, g u := by
    have eq := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (cont.mono (by rw [uIcc_of_le smaller]; exact Icc_subset_Icc_right endpt)).intervalIntegrable
      (cont.mono (by rw [uIcc_of_le endpt]; exact Icc_subset_Icc_left smaller)).intervalIntegrable
    have pos : 0 ≤ ∫ u in (1/2:ℝ)..(1-1/lam), g u := intervalIntegral.integral_nonneg smaller (by
      intro u hu
      exact mul_nonneg (div_nonneg (Real.exp_pos _).le (by linarith [hu.1]))
        (sub_nonneg.mpr (Real.cos_le_one _)))
    linarith
  have sub : (∫ u in (1/2:ℝ)..1, g u) = ∫ v in H/2..H, f v := by
    have e := intervalIntegral.smul_integral_comp_mul_left (a := (1/2:ℝ)) (b := 1) f H
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul, mul_one,
      show H*(1/2) = H/2 by ring] at e
    refine Eq.trans (intervalIntegral.integral_congr (fun u hu => ?_)) e
    rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at hu
    have un : u ≠ 0 := (by linarith [hu.1] : 0 < u).ne'
    dsimp [f,g,lam]
    rw [mul_assoc (1-α), mul_assoc t]
    field_simp [hH.ne',un]
  have cont₀ := primeWave_continuousOn (a := H/2) (b := H) (by linarith) (by linarith) α 0
  have contt := primeWave_continuousOn (a := H/2) (b := H) (by linarith) (by linarith) α t
  have eq (u : ℝ) (h : IntervalIntegrable (primeWave α u) volume (H/2) H) :
      (∫ v in H/2..H, (primeWave α u v).re) = (∫ v in H/2..H, primeWave α u v).re :=
    intervalIntegral.intervalIntegral_re h
  have dif : (∫ v in H/2..H, f v) =
      (∫ v in H/2..H, primeWave α 0 v).re - (∫ v in H/2..H, primeWave α t v).re := by
    rw [← eq 0 cont₀.intervalIntegrable, ← eq t contt.intervalIntegrable,
      ← intervalIntegral.integral_sub (f := fun v => (primeWave α 0 v).re) (g := fun v => (primeWave α t v).re) (μ := volume) (Complex.continuous_re.comp_continuousOn cont₀).intervalIntegrable
        (Complex.continuous_re.comp_continuousOn contt).intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [primeWave_re,zero_mul,Real.cos_zero,mul_one,f]
    ring
  exact (saddle_weighted_cosine_gap lam (t*H) hLam ht).trans (above.trans_eq (sub.trans dif))

theorem prime_phase_re (p : ℕ) (hp : p.Prime) (α t : ℝ) :
    ((p:ℂ)^(-((α:ℂ)-(t:ℂ)*Complex.I))).re = (p:ℝ)^(-α)*Real.cos (t*Real.log p) := by
  have pos : (0:ℝ) < p := by exact_mod_cast hp.pos
  rw [← Complex.ofReal_natCast, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr pos.ne'),
    ← Complex.ofReal_log pos.le, Complex.exp_re, Real.rpow_def_of_pos pos]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im, Complex.sub_re,
    Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im, Complex.I_re,Complex.I_im,
    zero_mul,mul_zero,add_zero,sub_zero,zero_sub,neg_neg,mul_one]
  rw [mul_comm (Real.log p) t]

/-- The oscillatory loss for the actual prime sum survives deletion of the
    individual prime factors excluded by a clean progression. -/
theorem prime_band_cosine_loss (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B α t : ℝ) (D : Finset ℕ), 16 ≤ B → 199/200 ≤ α → α ≤ 1 →
      |t| ≤ B^(1/5:ℝ) → 2 ≤ (1-α)*Real.log B → 1 ≤ |t*Real.log B| →
      let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      D ⊆ J →
        Real.exp ((1-α)*Real.log B-1)/(36*((1-α)*Real.log B)^3) -
          (C*(1+Real.log (3*B))^2*B^(-19/400:ℝ) + 2*D.card*B^(-199/400:ℝ)) ≤
        ∑ p ∈ J \ D, (p:ℝ)^(-α)*(1-Real.cos (t*Real.log p)) := by
  obtain ⟨c,hc,approx⟩ := fixed_principal_prime_band line
  refine ⟨2*c,by positivity,fun B α t D hB hlo hhi ht hLam hω => ?_⟩
  let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
  dsimp only
  intro hD
  let W (p : ℕ) := (p:ℝ)^(-α)
  let H := Real.log B
  let E := c*(1+Real.log (3*B))^2*B^(-19/400:ℝ)
  have pos : 0 < B := by linarith
  have logpos : 0 < H := Real.log_pos (by linarith)
  have estimate (u : ℝ) (hu : |u| ≤ B^(1/5:ℝ)) :
      |(∑ p ∈ J, W p*Real.cos (u*Real.log p)) - (∫ x in H/2..H, primeWave α u x).re| ≤ E := by
    let s : ℂ := (α:ℂ)-(u:ℂ)*Complex.I
    have sr : s.re = α := by simp [s]
    have si : |s.im| = |u| := by simp [s]
    have main := approx B s hB (sr ▸ hlo) (sr ▸ hhi) (si ▸ hu)
    have r := (Complex.abs_re_le_norm _).trans main
    rw [Complex.sub_re,Complex.re_sum] at r
    change |(∑ p ∈ J, _) - _| ≤ E at r
    have sums : (∑ p ∈ J, W p*Real.cos (u*Real.log p)) = ∑ p ∈ J, ((p:ℂ)^(-s)).re := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (prime_phase_re p (Finset.mem_filter.mp hp).2 α u).symm
    rw [sums]
    exact r
  have a := estimate 0 (by simp; positivity)
  have b := estimate t ht
  have outside := principal_integral_cosine_loss α t H logpos hLam hω
  have full : Real.exp ((1-α)*H-1)/(36*((1-α)*H)^3)-2*E ≤
      ∑ p ∈ J, W p*(1-Real.cos (t*Real.log p)) := by
    simp only [zero_mul,Real.cos_zero,mul_one] at a
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
    linarith [(abs_le.mp a).1,(abs_le.mp b).2]
  have lost (p : ℕ) (hp : p ∈ D) : W p*(1-Real.cos (t*Real.log p)) ≤ 2*B^(-199/400:ℝ) := by
    have lp := Nat.lt_of_floor_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hD hp)).1).1
    have sp := Real.sqrt_pos.mpr pos
    have wbound : W p ≤ B^(-199/400:ℝ) := by
      refine (Real.rpow_le_rpow_of_nonpos sp lp.le (by linarith : -α ≤ 0)).trans ?_
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul pos.le]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    calc
      _ ≤ W p*2 := mul_le_mul_of_nonneg_left (by linarith [Real.neg_one_le_cos (t*Real.log p)])
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ _ := by linarith
  have cost : (∑ p ∈ D, W p*(1-Real.cos (t*Real.log p))) ≤ D.card*(2*B^(-199/400:ℝ)) := by
    simpa using Finset.sum_le_sum lost
  change _ ≤ ∑ p ∈ J \ D, W p*(1-Real.cos (t*Real.log p))
  rw [Finset.sum_sdiff_eq_sub hD]
  dsimp [H,E] at full
  linarith

/-- A uniform bound on the actual normalized product, with a quantitative
    loss away from the central arc and with arbitrary specified deletions. -/
theorem principal_product_off_center (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B α t : ℝ) (D : Finset ℕ), 16 ≤ B → 199/200 ≤ α → α ≤ 1 →
      |t| ≤ B^(1/5:ℝ) → 2 ≤ (1-α)*Real.log B → 1 ≤ |t*Real.log B| →
      let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      D ⊆ J →
        ‖saddleCharacteristic (J \ D) (primeProbability α) (fun p => Real.log p) t‖ ≤
        Real.exp ((C*(1+Real.log (3*B))^2*B^(-19/400:ℝ) + 2*D.card*B^(-199/400:ℝ) -
          Real.exp ((1-α)*Real.log B-1)/(36*((1-α)*Real.log B)^3))/4) := by
  obtain ⟨C,hC,loss⟩ := prime_band_cosine_loss line
  refine ⟨C,hC,fun B α t D hB hlo hhi ht hLam hω => ?_⟩
  let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
  dsimp only
  intro hD
  have g := loss B α t D hB hlo hhi ht hLam hω hD
  let W (p : ℕ) := (p:ℝ)^(-α)
  let cost (p : ℕ) := W p*(1-Real.cos (t*Real.log p))
  have indiv (p : ℕ) (hp : p ∈ J \ D) :
      ‖centeredFactor (primeProbability α p) (t*Real.log p)‖ ≤ Real.exp (-cost p/4) := by
    have one : (1:ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.one_le
    have wn : 0 ≤ W p := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have wo : W p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos one (by linarith)
    have den : 0 < 1+W p := by linarith
    have den2 : (1+W p)^2 ≤ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr wo) (show 0 ≤ 3+W p by linarith)]
    have var : W p/4 ≤ primeProbability α p*(1-primeProbability α p) := by
      change W p/4 ≤ W p/(1+W p)*(1-W p/(1+W p))
      rw [show 1-W p/(1+W p) = 1/(1+W p) by field_simp; ring]
      rw [div_mul_div_comm, mul_one, ← sq]
      exact div_le_div_of_nonneg_left wn (sq_pos_of_pos den) den2
    refine (centeredFactor_decay _ _).trans (Real.exp_le_exp.mpr ?_)
    dsimp only [cost]
    linarith [mul_le_mul_of_nonneg_right var (sub_nonneg.mpr (Real.cos_le_one (t*Real.log p)))]
  change ‖saddleCharacteristic (J \ D) _ _ t‖ ≤ _
  rw [saddleCharacteristic, norm_prod]
  refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) indiv).trans ?_
  rw [← Real.exp_sum, ← Finset.sum_div, Finset.sum_neg_distrib]
  apply Real.exp_le_exp.mpr
  change _ ≤ ∑ p ∈ J \ D, cost p at g
  linarith

end Cogentic.Window
