import Cogentic.RandomizedOptimalCost

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
  have hgate := scaled_finite_private_gate z w hc hZ hh hz0 hzn hstep htail hmoment
  have hwidth : scaledPrivateCost (2/3) (curve*Z) ≤ scaledPrivateCost θ (curve*Z) := by
    unfold scaledPrivateCost
    gcongr
  have hu : 0 < curve*Z := mul_pos hc hZ
  have he : δ/(2*(2/(3*(curve*Z)^2))) = δ*Z^2/(2*(2/(3*curve^2))) := by field_simp
  have ht := terminal_tradeoff_of_search b δ (2/(3*(curve*Z)^2)) ratio v height
    (scaledSupportingCost (2/3) u) hb hd (by positivity) hratio
    (by simpa only [he] using hheight) hbox hmean (hraw.trans hC.le)
  have hi : 1/(2/(3*(curve*Z)^2)) = 3*(curve*Z)^2/2 := by field_simp
  rw [hi] at ht
  apply twoThirds_width_schedule_floor hl hr hp hd hu _ ht
  unfold scaledPrivateCost at hwidth
  unfold scaledPrivateCost
  linarith only [hwidth, hgate, hC]

end Cogentic.Randomized
