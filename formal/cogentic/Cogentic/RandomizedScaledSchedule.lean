import Cogentic.RandomizedSharpSchedule

namespace Cogentic.Randomized

/-- The tail-cap argument charges a coordinate of logarithmic width `θ`
through the private moment. The recognition charge is unchanged. -/
theorem scaled_finite_private_gate {n : ℕ} (z w : ℕ → ℝ)
    {θ C b curve h Z : ℝ} (hc : 0 < curve) (hZ : 0 < Z) (hh : curve ≤ h)
    (hz0 : z 0 = 0) (hzn : z n = Z) (hstep : ∀ i < n, z i ≤ z (i+1))
    (htail : ∀ i < n, (∑ j ∈ Finset.Ico i n, w j) ≤ C-b-h*z (i+1))
    (hmoment : 4*θ/(9*curve^2) ≤ ∑ i ∈ Finset.range n, z (i+1)^2*w i) :
    b + 4*θ/(9*(curve*Z)^2) + 2*(curve*Z)/3 ≤ C := by
  let y (i : ℕ) := z i / Z
  have htail' (i : ℕ) (hi : i < n) :
      (∑ j ∈ Finset.Ico i n, w j) ≤ C-b-(h*Z)*y (i+1) := by
    have he : h*Z*y (i+1) = h*z (i+1) := by dsimp [y]; field_simp
    simpa only [he] using htail i hi
  have hgrid := Cogentic.finite_stage_private_floor y w
    (mul_nonneg (hc.le.trans hh) hZ.le) (by simp [y,hz0]) (by simp [y,hzn,hZ.ne'])
    (fun i hi => div_le_div_of_nonneg_right (hstep i hi) hZ.le) htail'
  have hm : 4*θ/(9*(curve*Z)^2) ≤ ∑ i ∈ Finset.range n, y (i+1)^2*w i := by
    have he (i : ℕ) : y (i+1)^2*w i = (z (i+1)^2*w i)/Z^2 := by
      dsimp [y]; rw [div_pow, div_mul_eq_mul_div]
    have he' : 4*θ/(9*(curve*Z)^2) = (4*θ/(9*curve^2))/Z^2 := by field_simp
    simpa only [he, he', div_eq_mul_inv, Finset.sum_mul] using
      (div_le_div_of_nonneg_right hmoment (sq_nonneg Z))
  linarith only [hm, hgrid, mul_le_mul_of_nonneg_right hh hZ.le]

noncomputable def scaledPrivateCost (θ v : ℝ) : ℝ := 4*θ/(9*v^2) + 2*v/3

/-- The same supporting-line argument applies to every nonnegative width
when its stationary value and slope are specified. -/
theorem scaled_stationary_terminal_slack (θ u C s b₀ b δ v : ℝ)
    (hθ : 0 ≤ θ) (hu : 0 < u) (hd : 0 < δ) (hv : 0 < v) (hsq : s^2 = C)
    (hb₀ : b₀ = C - scaledPrivateCost θ u) (hgap : 0 < C - 2*b₀)
    (hvalue : 6*b₀*(C-b₀) = 3*u^2/2 + 4*s)
    (hslope : 6*(C-2*b₀)*(2/3-8*θ/(9*u^3)) = -3*u) :
    6*(C-2*b₀)*(C - (b + scaledPrivateCost θ v)) ≤
      3*v^2/2 + 4/δ + C*δ - 6*b*(C-b) := by
  have hδ : 4*s ≤ 4/δ + C*δ := by
    have he : (4/δ + C*δ)*δ = 4 + C*δ^2 := by field_simp
    apply le_of_mul_le_mul_right (a := δ) _ hd
    rw [he, ← hsq]
    nlinarith only [sq_nonneg (s*δ-2)]
  have hinv : 3/u^2 - 2*v/u^3 ≤ 1/v^2 := by
    field_simp
    nlinarith only [mul_nonneg (sq_nonneg (v-u)) (show 0 ≤ 2*v+u by positivity)]
  have hprivate : scaledPrivateCost θ u + (2/3-8*θ/(9*u^3))*(v-u) ≤
      scaledPrivateCost θ v := by
    have he : scaledPrivateCost θ u + (2/3-8*θ/(9*u^3))*(v-u) =
        (4*θ/9)*(3/u^2 - 2*v/u^3) + 2*v/3 := by
      unfold scaledPrivateCost
      field_simp
      ring
    have hv' : scaledPrivateCost θ v = (4*θ/9)*(1/v^2) + 2*v/3 := by
      unfold scaledPrivateCost
      ring
    rw [he, hv']
    exact add_le_add_left (mul_le_mul_of_nonneg_left hinv (by positivity)) _
  have hweight : 0 < 6*(C-2*b₀) := by positivity
  have hprivate' := mul_le_mul_of_nonneg_left hprivate hweight.le
  have hstationary := congrArg (fun a : ℝ => a*(v-u)) hslope
  have hbudget := congrArg (fun a : ℝ => 6*(C-2*b₀)*a) hb₀
  nlinarith only [hδ, hprivate', hstationary, hbudget, hvalue,
    sq_nonneg (b-b₀), sq_nonneg (v-u)]

theorem scaled_stationary_schedule_floor (θ u C s b₀ b δ v : ℝ)
    (hθ : 0 ≤ θ) (hu : 0 < u) (hd : 0 < δ) (hv : 0 < v) (hsq : s^2 = C)
    (hb₀ : b₀ = C - scaledPrivateCost θ u) (hgap : 0 < C - 2*b₀)
    (hvalue : 6*b₀*(C-b₀) = 3*u^2/2 + 4*s)
    (hslope : 6*(C-2*b₀)*(2/3-8*θ/(9*u^3)) = -3*u)
    (hprivate : b + scaledPrivateCost θ v < C)
    (hterminal : 3*v^2/2 + 4/δ + C*δ ≤ 6*b*(C-b)) : False := by
  have h := scaled_stationary_terminal_slack θ u C s b₀ b δ v hθ hu hd hv hsq hb₀ hgap hvalue hslope
  have hpos : 0 < 6*(C-2*b₀)*(C - (b + scaledPrivateCost θ v)) :=
    mul_pos (by positivity) (sub_pos.mpr hprivate)
  linarith only [h, hpos, hterminal]

/-- Width one recovers the original exact isolated-root certificate. -/
theorem width_one_schedule_floor {u b δ v : ℝ} (hl : rootLower < u) (hr : u < rootUpper)
    (hp : rootPolynomial u = 0) (hd : 0 < δ) (hv : 0 < v)
    (hprivate : b + scaledPrivateCost 1 v < algebraicCost u)
    (hterminal : 3*v^2/2 + 4/δ + algebraicCost u*δ ≤ 6*b*(algebraicCost u-b)) : False := by
  apply isolated_root_schedule_floor hl hr hp hd hv _ hterminal
  simpa [scaledPrivateCost, ← add_assoc] using hprivate


/-- The stationary cost obtained by solving the slope equation. -/
noncomputable def scaledSupportingCost (θ u : ℝ) : ℝ :=
  (225*u^6-96*θ*u^3-128*θ^2)/(36*u^2*(3*u^3-4*θ))

noncomputable def scaledSupportingSqrt (θ u : ℝ) : ℝ :=
  (6*scaledPrivateCost θ u*(scaledSupportingCost θ u-scaledPrivateCost θ u)-3*u^2/2)/4

private theorem scaled_supporting_floor {θ u b δ v : ℝ}
    (hθ : 0 ≤ θ) (hu : 0 < u) (hd : 0 < δ) (hv : 0 < v) (hden : 3*u^3-4*θ < 0)
    (hsq : scaledSupportingSqrt θ u ^ 2 = scaledSupportingCost θ u)
    (hprivate : b + scaledPrivateCost θ v < scaledSupportingCost θ u)
    (hterminal : 3*v^2/2 + 4/δ + scaledSupportingCost θ u*δ ≤
      6*b*(scaledSupportingCost θ u-b)) : False := by
  let C := scaledSupportingCost θ u
  let p := scaledPrivateCost θ u
  have hgap : C-2*(C-p) = -(9*u^4)/(4*(3*u^3-4*θ)) := by
    dsimp [C,p,scaledSupportingCost,scaledPrivateCost]
    generalize he : 3*u^3-4*θ = a at hden ⊢
    field_simp [hu.ne', hden.ne]
    subst a
    ring
  have hg : 0 < C-2*(C-p) := by
    rw [hgap]
    exact div_pos_of_neg_of_neg (neg_neg_of_pos (by positivity))
      (mul_neg_of_pos_of_neg (by norm_num) hden)
  have hslope : 2/3-8*θ/(9*u^3) = 2*(3*u^3-4*θ)/(9*u^3) := by field_simp; ring
  apply scaled_stationary_schedule_floor θ u C (scaledSupportingSqrt θ u) (C-p) b δ v
    hθ hu hd hv hsq rfl hg _ _ hprivate hterminal
  · dsimp [C,p,scaledSupportingSqrt]
    ring
  · rw [hgap, hslope]
    generalize he : 3*u^3-4*θ = a at hden ⊢
    field_simp [hu.ne', hden.ne]
    ring

def twoThirdsRootPolynomial (u : ℝ) : ℝ :=
  164025*u^12 - 23328*u^9 + 311040*u^6 + 36864*u^3 - 32768

def twoThirdsRootLower : ℝ := 0.64530346987224908815

def twoThirdsRootUpper : ℝ := 0.64530346987224908816

theorem exists_twoThirdsRoot :
    ∃ u, twoThirdsRootLower < u ∧ u < twoThirdsRootUpper ∧ twoThirdsRootPolynomial u = 0 := by
  have hab : twoThirdsRootLower ≤ twoThirdsRootUpper := by
    norm_num [twoThirdsRootLower, twoThirdsRootUpper]
  have hf : Continuous twoThirdsRootPolynomial := by unfold twoThirdsRootPolynomial; fun_prop
  have hlo : twoThirdsRootPolynomial twoThirdsRootLower < 0 := by
    norm_num [twoThirdsRootPolynomial, twoThirdsRootLower]
  have hhi : 0 < twoThirdsRootPolynomial twoThirdsRootUpper := by
    norm_num [twoThirdsRootPolynomial, twoThirdsRootUpper]
  obtain ⟨u, hu, hzero⟩ := intermediate_value_Icc hab hf.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (twoThirdsRootPolynomial twoThirdsRootLower)
      (twoThirdsRootPolynomial twoThirdsRootUpper) from ⟨hlo.le, hhi.le⟩)
  refine ⟨u, lt_of_le_of_ne hu.1 ?_, lt_of_le_of_ne hu.2 ?_, hzero⟩
  · intro h
    rw [← h] at hzero
    exact hlo.ne hzero
  · intro h
    rw [h] at hzero
    exact hhi.ne' hzero

private theorem twoThirds_scaled_sqrt_sq {u : ℝ} (hu : u ≠ 0) (hd : 3*u^3-4*(2/3 : ℝ) ≠ 0)
    (hp : twoThirdsRootPolynomial u = 0) :
    scaledSupportingSqrt (2/3) u ^ 2 = scaledSupportingCost (2/3) u := by
  have h : scaledSupportingSqrt (2/3) u ^ 2 - scaledSupportingCost (2/3) u =
      (2025*u^6-1008*u^3-128)*twoThirdsRootPolynomial u /
        (34012224*u^8*(3*u^3-4*(2/3 : ℝ))^2) := by
    unfold scaledSupportingSqrt scaledSupportingCost scaledPrivateCost twoThirdsRootPolynomial
    generalize he : 3*u^3-4*(2/3 : ℝ) = a at hd ⊢
    field_simp [hu, hd]
    subst a
    ring
  rw [hp, mul_zero, zero_div] at h
  exact sub_eq_zero.mp h

private theorem twoThirds_den_neg {u : ℝ} (hu : 0 < u) (hhi : u < twoThirdsRootUpper) :
    3*u^3-4*(2/3 : ℝ) < 0 := by
  have h3 := pow_le_pow_left₀ hu.le hhi.le 3
  norm_num [twoThirdsRootUpper] at h3
  linarith only [h3]

/-- The limiting-width cost lies inside this exact rational enclosure. -/
theorem twoThirdsCost_bounds {u : ℝ} (hl : twoThirdsRootLower < u) (hr : u < twoThirdsRootUpper) :
    2.07377842496623257 < scaledSupportingCost (2/3) u ∧
      scaledSupportingCost (2/3) u < 2.07377842496623258 := by
  have h₀ : 0 < twoThirdsRootLower := by norm_num [twoThirdsRootLower]
  have hu := h₀.trans hl
  have lo (k : ℕ) := pow_le_pow_left₀ h₀.le hl.le k
  have hi (k : ℕ) := pow_le_pow_left₀ hu.le hr.le k
  have hd : 36*u^2*(3*u^3-4*(2/3 : ℝ)) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (twoThirds_den_neg hu hr)
  unfold scaledSupportingCost
  constructor
  · apply (lt_div_iff_of_neg hd).mpr
    have h₁ := lo 3
    have h₂ := hi 6
    have h₃ := hi 2
    have h₄ := lo 5
    norm_num [twoThirdsRootLower, twoThirdsRootUpper] at h₁ h₂ h₃ h₄
    linarith only [h₁,h₂,h₃,h₄]
  · apply (div_lt_iff_of_neg hd).mpr
    have h₁ := hi 3
    have h₂ := lo 6
    have h₃ := lo 2
    have h₄ := hi 5
    norm_num [twoThirdsRootLower, twoThirdsRootUpper] at h₁ h₂ h₃ h₄
    linarith only [h₁,h₂,h₃,h₄]

/-- The two-thirds width limit has its own supporting certificate in the
same two-cost relaxation. -/
theorem twoThirds_width_schedule_floor {u b δ v : ℝ}
    (hl : twoThirdsRootLower < u) (hr : u < twoThirdsRootUpper)
    (hp : twoThirdsRootPolynomial u = 0) (hd : 0 < δ) (hv : 0 < v)
    (hprivate : b + scaledPrivateCost (2/3) v < scaledSupportingCost (2/3) u)
    (hterminal : 3*v^2/2 + 4/δ + scaledSupportingCost (2/3) u*δ ≤
      6*b*(scaledSupportingCost (2/3) u-b)) : False := by
  have hu : 0 < u := (by norm_num [twoThirdsRootLower] : 0 < twoThirdsRootLower).trans hl
  have hden := twoThirds_den_neg hu hr
  exact scaled_supporting_floor (by norm_num) hu hd hv hden
    (twoThirds_scaled_sqrt_sq hu.ne' hden.ne hp) hprivate hterminal


private theorem twoThirds_width_finite_grid_floor_at_root {n : ℕ} (z w : ℕ → ℝ)
    {θ C b δ curve h ratio v height Z u : ℝ} (hθ : 2/3 ≤ θ)
    (hl : twoThirdsRootLower < u) (hr : u < twoThirdsRootUpper)
    (hp : twoThirdsRootPolynomial u = 0)
    (hbudget : C ≤ scaledSupportingCost (2/3) u)
    (hstrict : 2/3 < θ ∨ C < scaledSupportingCost (2/3) u)
    (hb : 0 < b) (hd : 0 < δ) (hc : 0 < curve) (hZ : 0 < Z) (hh : curve ≤ h)
    (hz0 : z 0 = 0) (hzn : z n = Z) (hstep : ∀ i < n, z i ≤ z (i+1))
    (htail : ∀ i < n, (∑ j ∈ Finset.Ico i n, w j) ≤ C-b-h*z (i+1))
    (hmoment : 4*θ/(9*curve^2) ≤ ∑ i ∈ Finset.range n, z (i+1)^2*w i)
    (hratio : 0 ≤ ratio) (hheight : (1 + δ*Z^2/(2*(2/(3*curve^2))))/δ^3 ≤ height)
    (hbox : height+v ≤ ratio*(b/δ))
    (hmean : ratio/3 + 1/(3*δ^2*b) ≤ 2*v-b/δ)
    (hraw : b+δ*ratio/3+1/(3*δ*b) ≤ C) : False := by
  have hgate := scaled_finite_private_gate z w hc hZ hh hz0 hzn hstep htail hmoment
  have hwidth : scaledPrivateCost (2/3) (curve*Z) ≤ scaledPrivateCost θ (curve*Z) := by
    unfold scaledPrivateCost
    gcongr
  have hu : 0 < curve*Z := mul_pos hc hZ
  have he : δ/(2*(2/(3*(curve*Z)^2))) = δ*Z^2/(2*(2/(3*curve^2))) := by field_simp
  have ht := terminal_tradeoff_of_search b δ (2/(3*(curve*Z)^2)) ratio v height
    (scaledSupportingCost (2/3) u) hb hd (by positivity) hratio
    (by simpa only [he] using hheight) hbox hmean (hraw.trans hbudget)
  have hi : 1/(2/(3*(curve*Z)^2)) = 3*(curve*Z)^2/2 := by field_simp
  rw [hi] at ht
  apply twoThirds_width_schedule_floor hl hr hp hd hu _ ht
  unfold scaledPrivateCost at hwidth
  unfold scaledPrivateCost
  rcases hstrict with hstrict | hstrict
  · have hwidth' : 4*(2/3 : ℝ)/(9*(curve*Z)^2) < 4*θ/(9*(curve*Z)^2) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hstrict (by norm_num)) (by positivity)
    linarith only [hwidth', hgate, hbudget]
  · linarith only [hwidth, hgate, hstrict]

/-- Any coordinate width at least two thirds inherits the limiting-width
lower bound for the finite private grid and the physical terminal costs. -/
theorem twoThirds_width_finite_grid_floor {n : ℕ} (z w : ℕ → ℝ)
    {θ C b δ curve h ratio v height Z : ℝ} (hθ : 2/3 ≤ θ)
    (hbudget : C ≤ 2.07377842496623257)
    (hb : 0 < b) (hd : 0 < δ) (hc : 0 < curve) (hZ : 0 < Z) (hh : curve ≤ h)
    (hz0 : z 0 = 0) (hzn : z n = Z) (hstep : ∀ i < n, z i ≤ z (i+1))
    (htail : ∀ i < n, (∑ j ∈ Finset.Ico i n, w j) ≤ C-b-h*z (i+1))
    (hmoment : 4*θ/(9*curve^2) ≤ ∑ i ∈ Finset.range n, z (i+1)^2*w i)
    (hratio : 0 ≤ ratio) (hheight : (1 + δ*Z^2/(2*(2/(3*curve^2))))/δ^3 ≤ height)
    (hbox : height+v ≤ ratio*(b/δ))
    (hmean : ratio/3 + 1/(3*δ^2*b) ≤ 2*v-b/δ)
    (hraw : b+δ*ratio/3+1/(3*δ*b) ≤ C) : False := by
  obtain ⟨u, hl, hr, hp⟩ := exists_twoThirdsRoot
  have hC := hbudget.trans_lt (twoThirdsCost_bounds hl hr).1
  exact twoThirds_width_finite_grid_floor_at_root z w hθ hl hr hp hC.le (Or.inr hC)
    hb hd hc hZ hh hz0 hzn hstep htail hmoment hratio hheight hbox hmean hraw


/-- The finite private grid with a moment scaled by the width of one smooth
coordinate and the original physical terminal constraints. -/
structure ScaledFinitePrivateSchedule (θ C : ℝ) where
  n : ℕ
  z : ℕ → ℝ
  w : ℕ → ℝ
  b : ℝ
  δ : ℝ
  curve : ℝ
  h : ℝ
  ratio : ℝ
  v : ℝ
  height : ℝ
  Z : ℝ
  hb : 0 < b
  hd : 0 < δ
  hc : 0 < curve
  hZ : 0 < Z
  hh : curve ≤ h
  hz0 : z 0 = 0
  hzn : z n = Z
  hstep : ∀ i < n, z i ≤ z (i+1)
  hpositive : ∀ i < n, 0 < w i
  htail : ∀ i < n, (∑ j ∈ Finset.Ico i n, w j) ≤ C-b-h*z (i+1)
  hmoment : 4*θ/(9*curve^2) ≤ ∑ i ∈ Finset.range n, z (i+1)^2*w i
  hratio : 0 ≤ ratio
  hheight : (1+δ*Z^2/(2*(2/(3*curve^2))))/δ^3 ≤ height
  hbox : height+v ≤ ratio*(b/δ)
  hmean : ratio/3+1/(3*δ^2*b) ≤ 2*v-b/δ
  hraw : b+δ*ratio/3+1/(3*δ*b) ≤ C

private theorem twoThirds_terminal_attainment {u : ℝ} (hl : twoThirdsRootLower < u)
    (hr : u < twoThirdsRootUpper) (hp : twoThirdsRootPolynomial u = 0) :
    let θ : ℝ := 2/3
    let C := scaledSupportingCost θ u
    let b := C - scaledPrivateCost θ u
    let δ := 2 / scaledSupportingSqrt θ u
    ∃ ratio v height : ℝ, 0 < b ∧ 0 < δ ∧ 0 < u ∧ 0 < ratio ∧
      u/3 < 4*θ/(9*u^2) ∧ b+scaledPrivateCost θ u = C ∧
      (1+δ/(2*(2/(3*u^2))))/δ^3 = height ∧ height+v = ratio*(b/δ) ∧
      ratio/3+1/(3*δ^2*b) = 2*v-b/δ ∧ b+δ*ratio/3+1/(3*δ*b) = C := by
  let θ : ℝ := 2/3
  let C := scaledSupportingCost θ u
  let p := scaledPrivateCost θ u
  let b := C-p
  let s := scaledSupportingSqrt θ u
  let δ := 2/s
  let x := 2/(3*u^2)
  have hul : (64/100 : ℝ) < u := (by norm_num [twoThirdsRootLower] : (64/100 : ℝ) ≤ twoThirdsRootLower).trans_lt hl
  have huh : u < (65/100 : ℝ) := hr.trans_le (by norm_num [twoThirdsRootUpper])
  have hu : 0 < u := by linarith only [hul]
  have hu2lo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 64/100) hul.le 2
  have hu2hi := pow_le_pow_left₀ hu.le huh.le 2
  have hC : 2 < C := (by norm_num : (2 : ℝ) < 2.07377842496623257).trans
    (twoThirdsCost_bounds hl hr).1
  have hqlo : (7/10 : ℝ) < 4*θ/(9*u^2) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    dsimp [θ]
    nlinarith only [hu2hi]
  have hqhi : 4*θ/(9*u^2) < (4/5 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).mpr
    dsimp [θ]
    nlinarith only [hu2lo]
  have hp₀ : 1 < p := by dsimp [p,scaledPrivateCost]; linarith only [hul, hqlo]
  have hp₁ : p < (13/10 : ℝ) := by dsimp [p,scaledPrivateCost]; linarith only [huh, hqhi]
  have hb₀ : (7/10 : ℝ) < b := by dsimp [b]; linarith only [hC, hp₁]
  have hb : 0 < b := by linarith only [hb₀]
  have hbp : (7/10 : ℝ) < b*p := by
    simpa only [mul_one] using mul_lt_mul hb₀ hp₀.le zero_lt_one hb.le
  have hval : 6*b*p = 3*u^2/2+4*s := by dsimp [b,s,C,p,scaledSupportingSqrt]; ring
  have hs : 0 < s := by nlinarith only [hval, hbp, hu2hi]
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hsq : s^2 = C := twoThirds_scaled_sqrt_sq hu.ne' (twoThirds_den_neg hu hr).ne hp
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
  refine ⟨ratio, v, height, hb, hd, hu, hratio, ?_, ?_, hheight, hbox, hmean, hraw⟩
  · linarith only [hqlo, huh]
  · change b+p = C
    dsimp [b]
    ring


/-- Every strict cost ceiling above the limiting optimum admits a finite
grid with width strictly above two thirds and arbitrarily close to it. -/
theorem scaled_finite_schedule_near_twoThirds {u C ξ : ℝ}
    (hl : twoThirdsRootLower < u) (hr : u < twoThirdsRootUpper)
    (hp : twoThirdsRootPolynomial u = 0) (hC : scaledSupportingCost (2/3) u < C) (hξ : 0 < ξ) :
    ∃ θ : ℝ, 2/3 < θ ∧ θ < 1 ∧ θ < 2/3+ξ ∧
      ∃ s : ScaledFinitePrivateSchedule θ C, s.Z = 1 ∧ s.h = s.curve := by
  let C₀ := scaledSupportingCost (2/3) u
  let b := C₀ - scaledPrivateCost (2/3) u
  let δ := 2 / scaledSupportingSqrt (2/3) u
  let ε := C-C₀
  have hε : 0 < ε := sub_pos.mpr hC
  obtain ⟨ratio, v, height, hb, hd, hu, hratio, hbase, hprivate, hheight, hbox, hmean, hraw⟩ :=
    twoThirds_terminal_attainment hl hr hp
  change 0 < b at hb
  change 0 < δ at hd
  change b + scaledPrivateCost (2/3) u = C₀ at hprivate
  change (1+δ/(2*(2/(3*u^2))))/δ^3 = height at hheight
  change height+v = ratio*(b/δ) at hbox
  change ratio/3+1/(3*δ^2*b) = 2*v-b/δ at hmean
  change b+δ*ratio/3+1/(3*δ*b) = C₀ at hraw
  let r := min (ξ/2) (min (1/6) (ε*(9*u^2)/8))
  let θ : ℝ := 2/3+r
  let W := 4*θ/(9*u^2)
  have hrpos : 0 < r := lt_min (half_pos hξ) (lt_min (by norm_num) (by positivity))
  have hrξ : r ≤ ξ/2 := min_le_left _ _
  have hr₁ : r ≤ 1/6 := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε*(9*u^2)/8 := (min_le_right _ _).trans (min_le_right _ _)
  have hθ₀ : (2/3 : ℝ) < θ := by dsimp [θ]; linarith only [hrpos]
  have hθ₁ : θ < 1 := by dsimp [θ]; linarith only [hr₁]
  have hθξ : θ < 2/3+ξ := by dsimp [θ]; linarith only [hrξ, hξ]
  have hW : u/3 < W := by
    refine hbase.trans_le ?_
    dsimp [W]
    gcongr
  have hwidth : W ≤ 4*(2/3)/(9*u^2)+ε/2 := by
    have hinc : 4*r/(9*u^2) ≤ ε/2 := by
      apply (div_le_iff₀ (by positivity)).2
      linarith only [hrε]
    have he : W = 4*(2/3)/(9*u^2) + 4*r/(9*u^2) := by dsimp [W, θ]; ring
    linarith only [he, hinc]
  obtain ⟨k, hk⟩ := exists_nat_gt (u/(ε/2))
  let n : ℝ := (k : ℝ)+1
  let z : ℕ → ℝ := fun i => (i : ℝ)/n
  have hn : 0 < n := by dsimp [n]; positivity
  have hmesh : u/n ≤ ε/2 := by
    have hc' := (div_lt_iff₀ (half_pos hε)).1 hk
    apply (div_le_iff₀ hn).2
    dsimp [n]
    nlinarith only [hc', hε]
  obtain ⟨w, _, hpositive, hmoment, hgate, _, herror⟩ := uniform_private_grid_upper k hu hW
  change (∑ i ∈ Finset.range (k+1), z (i+1)^2*w i) = W at hmoment
  have htail (i : ℕ) (hi : i < k+1) :
      (∑ j ∈ Finset.Ico i (k+1), w j) ≤ C-b-u*z (i+1) := by
    have hg := hgate i hi
    change u*z (i+1)+(∑ j ∈ Finset.Ico i (k+1), w j) =
      W+2*u/3+(u/(2*n)-u/(6*n^2)) at hg
    change u/(2*n)-u/(6*n^2) ≤ u/n at herror
    unfold scaledPrivateCost at hprivate
    dsimp [ε] at hwidth hmesh
    linarith only [hg, herror, hmesh, hprivate, hwidth]
  refine ⟨θ, hθ₀, hθ₁, hθξ, {
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
    hraw := hraw.le.trans hC.le
  }, rfl, rfl⟩

/-- With strict width above two thirds, precisely the budgets strictly
above the limiting optimum admit a finite scaled schedule. -/
theorem strict_scaled_finite_budget_iff {u C : ℝ}
    (hl : twoThirdsRootLower < u) (hr : u < twoThirdsRootUpper)
    (hp : twoThirdsRootPolynomial u = 0) :
    (∃ θ : ℝ, 2/3 < θ ∧ θ < 1 ∧ Nonempty (ScaledFinitePrivateSchedule θ C)) ↔
      scaledSupportingCost (2/3) u < C := by
  constructor
  · rintro ⟨θ, hθ, _, ⟨s⟩⟩
    by_contra! hC
    exact twoThirds_width_finite_grid_floor_at_root s.z s.w hθ.le hl hr hp hC (Or.inl hθ)
      s.hb s.hd s.hc s.hZ s.hh s.hz0 s.hzn s.hstep s.htail s.hmoment
      s.hratio s.hheight s.hbox s.hmean s.hraw
  · intro hC
    obtain ⟨θ, hθ, hθ₁, _, s, _, _⟩ := scaled_finite_schedule_near_twoThirds hl hr hp hC
      (show (0 : ℝ) < 1 by norm_num)
    exact ⟨θ, hθ, hθ₁, ⟨s⟩⟩

/-- The limiting optimum is the greatest lower bound with width restricted
to the physically admissible open interval. -/
theorem sharp_strict_scaled_finite_schedule_infimum {u : ℝ}
    (hl : twoThirdsRootLower < u) (hr : u < twoThirdsRootUpper)
    (hp : twoThirdsRootPolynomial u = 0) :
    IsGLB {C : ℝ | ∃ θ : ℝ, 2/3 < θ ∧ θ < 1 ∧ Nonempty (ScaledFinitePrivateSchedule θ C)}
      (scaledSupportingCost (2/3) u) := by
  have hset : {C : ℝ | ∃ θ : ℝ, 2/3 < θ ∧ θ < 1 ∧ Nonempty (ScaledFinitePrivateSchedule θ C)} =
      Set.Ioi (scaledSupportingCost (2/3) u) := by
    ext C
    exact strict_scaled_finite_budget_iff hl hr hp
  rw [hset]
  exact isGLB_Ioi

end Cogentic.Randomized
