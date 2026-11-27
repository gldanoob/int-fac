import Cogentic.RandomizedScaledSchedule

namespace Cogentic.Randomized

def classScheduleRootPolynomial (u : ℝ) : ℝ :=
  455625*u^18 - 437400*u^15 + 680400*u^12 - 136512*u^9 - 82944*u^6 + 9216*u^3 + 1024

def classScheduleRootLower : ℝ := 0.5562511167685462797656

def classScheduleRootUpper : ℝ := 0.5562511167685462797657

noncomputable abbrev classScheduleCost (u : ℝ) : ℝ := scaledSupportingCost (1/2) u

theorem exists_classScheduleRoot :
    ∃ u, classScheduleRootLower < u ∧ u < classScheduleRootUpper ∧
      classScheduleRootPolynomial u = 0 := by
  have hab : classScheduleRootLower ≤ classScheduleRootUpper := by
    norm_num [classScheduleRootLower, classScheduleRootUpper]
  have hf : Continuous classScheduleRootPolynomial := by unfold classScheduleRootPolynomial; fun_prop
  have hlo : 0 < classScheduleRootPolynomial classScheduleRootLower := by
    norm_num [classScheduleRootLower, classScheduleRootPolynomial]
  have hhi : classScheduleRootPolynomial classScheduleRootUpper < 0 := by
    norm_num [classScheduleRootUpper, classScheduleRootPolynomial]
  obtain ⟨u, hu, hz⟩ := intermediate_value_Icc' hab hf.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (classScheduleRootPolynomial classScheduleRootUpper)
      (classScheduleRootPolynomial classScheduleRootLower) from ⟨hhi.le, hlo.le⟩)
  refine ⟨u, lt_of_le_of_ne hu.1 ?_, lt_of_le_of_ne hu.2 ?_, hz⟩
  · intro h
    rw [← h] at hz
    exact hlo.ne' hz
  · intro h
    rw [h] at hz
    exact hhi.ne hz

private theorem classSchedule_den_neg {u : ℝ} (hu : 0 < u) (hr : u < classScheduleRootUpper) :
    3*u^3-2 < 0 := by
  have h3 := pow_le_pow_left₀ hu.le hr.le 3
  norm_num [classScheduleRootUpper] at h3
  linarith only [h3]

/-- Rational enclosure of the half-width stationary budget. -/
theorem classScheduleCost_bounds {u : ℝ} (hl : classScheduleRootLower < u)
    (hr : u < classScheduleRootUpper) :
    2.03288100822533195 < classScheduleCost u ∧ classScheduleCost u < 2.03288100822533196 := by
  have h₀ : 0 < classScheduleRootLower := by norm_num [classScheduleRootLower]
  have hu := h₀.trans hl
  have lo (k : ℕ) := pow_le_pow_left₀ h₀.le hl.le k
  have hi (k : ℕ) := pow_le_pow_left₀ hu.le hr.le k
  have hd : 36*u^2*(3*u^3-4*(1/2 : ℝ)) < 0 := by
    have h := classSchedule_den_neg hu hr
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith only [h])
  unfold classScheduleCost scaledSupportingCost
  constructor
  · apply (lt_div_iff_of_neg hd).mpr
    have h₁ := lo 3
    have h₂ := hi 6
    have h₃ := hi 2
    have h₄ := lo 5
    norm_num [classScheduleRootLower, classScheduleRootUpper] at h₁ h₂ h₃ h₄
    linarith only [h₁,h₂,h₃,h₄]
  · apply (div_lt_iff_of_neg hd).mpr
    have h₁ := hi 3
    have h₂ := lo 6
    have h₃ := lo 2
    have h₄ := hi 5
    norm_num [classScheduleRootLower, classScheduleRootUpper] at h₁ h₂ h₃ h₄
    linarith only [h₁,h₂,h₃,h₄]

private theorem classSchedule_sqrt_sq {u : ℝ} (hu : u ≠ 0) (hd : 3*u^3-2 ≠ 0)
    (hp : classScheduleRootPolynomial u = 0) :
    scaledSupportingSqrt (1/2) u ^ 2 = classScheduleCost u := by
  have h : scaledSupportingSqrt (1/2) u ^ 2 - classScheduleCost u =
      classScheduleRootPolynomial u / (46656*u^8*(3*u^3-2)^2) := by
    unfold scaledSupportingSqrt classScheduleCost scaledSupportingCost scaledPrivateCost
      classScheduleRootPolynomial
    have ht : 4*(1/2 : ℝ) = 2 := by norm_num
    rw [ht]
    generalize he : 3*u^3-2 = a at hd ⊢
    field_simp [hu, hd]
    subst a
    ring
  rw [hp, zero_div] at h
  exact sub_eq_zero.mp h

/-- The exact half-width lower bound for the two-cost model. -/
theorem classSchedule_stationary_floor {u b δ v : ℝ}
    (hl : classScheduleRootLower < u) (hr : u < classScheduleRootUpper)
    (hp : classScheduleRootPolynomial u = 0) (hd : 0 < δ) (hv : 0 < v)
    (hprivate : b + scaledPrivateCost (1/2) v < classScheduleCost u)
    (hterminal : 3*v^2/2+4/δ+classScheduleCost u*δ ≤ 6*b*(classScheduleCost u-b)) : False := by
  have hu : 0 < u := (by norm_num [classScheduleRootLower] : 0 < classScheduleRootLower).trans hl
  have hden := classSchedule_den_neg hu hr
  let C := classScheduleCost u
  let p := scaledPrivateCost (1/2) u
  have hgap : C-2*(C-p) = -(9*u^4)/(4*(3*u^3-2)) := by
    dsimp [C,p,classScheduleCost,scaledSupportingCost,scaledPrivateCost]
    rw [show 4*(1/2 : ℝ) = 2 by norm_num]
    generalize he : 3*u^3-2 = a at hden ⊢
    field_simp [hu.ne', hden.ne]
    subst a
    ring
  have hg : 0 < C-2*(C-p) := by
    rw [hgap]
    exact div_pos_of_neg_of_neg (neg_neg_of_pos (by positivity))
      (mul_neg_of_pos_of_neg (by norm_num) hden)
  have hslope : 2/3-8*(1/2 : ℝ)/(9*u^3) = 2*(3*u^3-2)/(9*u^3) := by field_simp; ring
  apply scaled_stationary_schedule_floor (1/2) u C (scaledSupportingSqrt (1/2) u) (C-p) b δ v
    (by norm_num) hu hd hv (classSchedule_sqrt_sq hu.ne' hden.ne hp) rfl hg _ _ hprivate hterminal
  · dsimp [C,p,scaledSupportingSqrt]
    ring
  · rw [hgap, hslope]
    generalize he : 3*u^3-2 = a at hden ⊢
    field_simp [hu.ne', hden.ne]
    ring

/-- Every finite positive grid of half-width satisfies the stationary lower
bound, including grids whose endpoint is free. -/
theorem classSchedule_finite_floor {u C : ℝ}
    (hl : classScheduleRootLower < u) (hr : u < classScheduleRootUpper)
    (hp : classScheduleRootPolynomial u = 0) (s : ScaledFinitePrivateSchedule (1/2) C) :
    classScheduleCost u ≤ C := by
  by_contra! hC
  have hg := scaled_finite_private_gate s.z s.w s.hc s.hZ s.hh s.hz0 s.hzn
    s.hstep s.htail s.hmoment
  have hv := mul_pos s.hc s.hZ
  have he : s.δ/(2*(2/(3*(s.curve*s.Z)^2))) = s.δ*s.Z^2/(2*(2/(3*s.curve^2))) := by field_simp
  have ht := terminal_tradeoff_of_search s.b s.δ (2/(3*(s.curve*s.Z)^2)) s.ratio s.v s.height
    (classScheduleCost u) s.hb s.hd (by positivity) s.hratio
    (by simpa only [he] using s.hheight) s.hbox s.hmean (s.hraw.trans hC.le)
  have hi : 1/(2/(3*(s.curve*s.Z)^2)) = 3*(s.curve*s.Z)^2/2 := by field_simp
  rw [hi] at ht
  exact classSchedule_stationary_floor hl hr hp s.hd hv
    (by unfold scaledPrivateCost; linarith only [hg, hC]) ht

theorem classSchedule_numeric_lower {C : ℝ} (s : ScaledFinitePrivateSchedule (1/2) C) :
    2.03288100822533195 < C := by
  obtain ⟨u, hl, hr, hp⟩ := exists_classScheduleRoot
  exact (classScheduleCost_bounds hl hr).1.trans_le (classSchedule_finite_floor hl hr hp s)


/-- Every positive slack above the stationary budget admits a finite
half-width grid with positive weights and endpoint one. -/
theorem classSchedule_finite_with_slack {u ε : ℝ}
    (hl : classScheduleRootLower < u) (hr : u < classScheduleRootUpper)
    (hp : classScheduleRootPolynomial u = 0) (hε : 0 < ε) :
    ∃ s : ScaledFinitePrivateSchedule (1/2) (classScheduleCost u+ε),
      s.Z = 1 ∧ s.h = s.curve := by
  let C := classScheduleCost u
  let p := scaledPrivateCost (1/2) u
  let W := 4*(1/2 : ℝ)/(9*u^2)
  let b := C-p
  let s := scaledSupportingSqrt (1/2) u
  let δ := 2/s
  let x := 2/(3*u^2)
  have hul : (556/1000 : ℝ) < u :=
    (by norm_num [classScheduleRootLower] : (556/1000 : ℝ) ≤ classScheduleRootLower).trans_lt hl
  have huh : u < (557/1000 : ℝ) := hr.trans_le (by norm_num [classScheduleRootUpper])
  have hu : 0 < u := by linarith only [hul]
  have hu2lo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 556/1000) hul.le 2
  have hu2hi := pow_le_pow_left₀ hu.le huh.le 2
  have hC : 2 < C := (by norm_num : (2 : ℝ) < 2.03288100822533195).trans
    (classScheduleCost_bounds hl hr).1
  have hWlo : (7/10 : ℝ) < W := by
    dsimp [W]
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith only [hu2hi]
  have hWhi : W < (4/5 : ℝ) := by
    dsimp [W]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith only [hu2lo]
  have hpdef : p = W+2*u/3 := rfl
  have hp₀ : 1 < p := by linarith only [hpdef, hWlo, hul]
  have hp₁ : p < (6/5 : ℝ) := by linarith only [hpdef, hWhi, huh]
  have hb₀ : (4/5 : ℝ) < b := by dsimp [b]; linarith only [hC, hp₁]
  have hb : 0 < b := by linarith only [hb₀]
  have hprod : (4/5 : ℝ) < b*p := by
    simpa only [mul_one] using mul_lt_mul hb₀ hp₀.le zero_lt_one hb.le
  have hval : 6*b*p = 3*u^2/2+4*s := by dsimp [b,s,C,p,scaledSupportingSqrt]; ring
  have hs : 0 < s := by nlinarith only [hval, hprod, hu2hi]
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hsq : s^2 = C := classSchedule_sqrt_sq hu.ne' (classSchedule_den_neg hu hr).ne hp
  have hinv : 1/x = 3*u^2/2 := by dsimp [x]; field_simp
  have heδ : 4/δ+C*δ = 4*s := by
    dsimp [δ]
    rw [← hsq]
    field_simp
    ring
  have hb' : C-b = p := by dsimp [b]; ring
  have ht : 1/x+4/δ+C*δ = 6*b*(C-b) := by rw [hb']; linarith only [hinv, heδ, hval]
  obtain ⟨ratio, v, height, hratio, _, _, hheight, hbox, hmean, hraw⟩ :=
    terminal_tradeoff_attainment b δ x C hb hd (by dsimp [x]; positivity) (by linarith only [hC]) ht
  have hW : u/3 < W := by linarith only [hWlo, huh]
  have hprivate : b+W+2*u/3 = C := by dsimp [b]; rw [hpdef]; ring
  obtain ⟨k, hk⟩ := exists_nat_gt (u/ε)
  let n : ℝ := (k : ℝ)+1
  let z : ℕ → ℝ := fun i => (i : ℝ)/n
  have hn : 0 < n := by dsimp [n]; positivity
  have hmesh : u/n ≤ ε := by
    have he := (div_lt_iff₀ hε).1 hk
    apply (div_le_iff₀ hn).2
    dsimp [n]
    nlinarith only [he, hε]
  obtain ⟨w, _, hpositive, hmoment, hgate, _, herror⟩ := uniform_private_grid_upper k hu hW
  change (∑ i ∈ Finset.range (k+1), z (i+1)^2*w i) = W at hmoment
  have htail (i : ℕ) (hi : i < k+1) :
      (∑ j ∈ Finset.Ico i (k+1), w j) ≤ C+ε-b-u*z (i+1) := by
    have hg := hgate i hi
    change u*z (i+1)+(∑ j ∈ Finset.Ico i (k+1), w j) =
      W+2*u/3+(u/(2*n)-u/(6*n^2)) at hg
    change u/(2*n)-u/(6*n^2) ≤ u/n at herror
    linarith only [hg, herror, hmesh, hprivate]
  refine ⟨{
    n := k+1
    z := z
    w := w
    b := b
    δ := δ
    curve := u
    h := u
    ratio := ratio
    v := v
    height := height
    Z := 1
    hb := hb
    hd := hd
    hc := hu
    hZ := by norm_num
    hh := le_rfl
    hz0 := by simp [z]
    hzn := by simpa [z, n] using div_self hn.ne'
    hstep := fun i _ => div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ i) hn.le
    hpositive := hpositive
    htail := htail
    hmoment := hmoment.ge
    hratio := hratio.le
    hheight := by simpa only [one_pow, mul_one] using hheight.le
    hbox := hbox.le
    hmean := hmean.le
    hraw := hraw.le.trans (le_add_of_nonneg_right hε.le)
  }, rfl, rfl⟩

/-- The stationary half-width budget is the greatest lower bound of the
finite positive-grid budgets in the scaled relaxation. -/
theorem sharp_classSchedule_infimum {u : ℝ}
    (hl : classScheduleRootLower < u) (hr : u < classScheduleRootUpper)
    (hp : classScheduleRootPolynomial u = 0) :
    IsGLB {C : ℝ | Nonempty (ScaledFinitePrivateSchedule (1/2) C)} (classScheduleCost u) := by
  constructor
  · rintro C ⟨s⟩
    exact classSchedule_finite_floor hl hr hp s
  · intro C hC
    by_contra! h
    let ε := (C-classScheduleCost u)/2
    have hε : 0 < ε := half_pos (sub_pos.mpr h)
    obtain ⟨s, _, _⟩ := classSchedule_finite_with_slack hl hr hp hε
    have hb := hC (show classScheduleCost u+ε ∈
      {C : ℝ | Nonempty (ScaledFinitePrivateSchedule (1/2) C)} from ⟨s⟩)
    change C ≤ classScheduleCost u+ε at hb
    dsimp [ε] at hb
    linarith only [hb, h]

end Cogentic.Randomized
