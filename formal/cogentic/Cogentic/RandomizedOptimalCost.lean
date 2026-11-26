import Cogentic.RandomizedAlgebraicRoot
import Cogentic.RandomizedStationaryFloor
import Cogentic.RandomizedScheduleFloor

namespace Cogentic.Randomized

/-- Exact enclosure of the cost at the isolated root. -/
theorem algebraicCost_bounds {u : ℝ} (hl : rootLower < u) (hr : u < rootUpper) :
    2.15463021529917670 < algebraicCost u ∧ algebraicCost u < 2.15463021529917672 := by
  have hl₀ : 0 < rootLower := by norm_num [rootLower]
  have hu := hl₀.trans hl
  have lo (k : ℕ) := pow_le_pow_left₀ hl₀.le hl.le k
  have hi (k : ℕ) := pow_le_pow_left₀ hu.le hr.le k
  have hc := hi 3
  norm_num [rootUpper] at hc
  have hd : 36*u^2*(3*u^3-4) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by linarith only [hc])
  unfold algebraicCost
  constructor
  · apply (lt_div_iff_of_neg hd).mpr
    have h₁ := lo 3
    have h₂ := hi 6
    have h₃ := hi 2
    have h₄ := lo 5
    norm_num [rootLower, rootUpper] at h₁ h₂ h₃ h₄
    linarith only [h₁,h₂,h₃,h₄]
  · apply (div_lt_iff_of_neg hd).mpr
    have h₁ := hi 3
    have h₂ := lo 6
    have h₃ := lo 2
    have h₄ := hi 5
    norm_num [rootLower, rootUpper] at h₁ h₂ h₃ h₄
    linarith only [h₁,h₂,h₃,h₄]

/-- The ideal two-cost relaxation has a certified supporting inequality at the
isolated algebraic root, valid at all positive private scales and degrees. -/
theorem isolated_root_schedule_floor {u b δ v : ℝ} (hl : rootLower < u) (hr : u < rootUpper)
    (hp : rootPolynomial u = 0) (hd : 0 < δ) (hv : 0 < v)
    (hprivate : b + 4/(9*v^2) + 2*v/3 < algebraicCost u)
    (hterminal : 3*v^2/2 + 4/δ + algebraicCost u*δ ≤ 6*b*(algebraicCost u-b)) : False := by
  have hu : 0 < u := (by norm_num [rootLower] : 0 < rootLower).trans hl
  have hi := pow_le_pow_left₀ hu.le hr.le 3
  norm_num [rootUpper] at hi
  have hden : 3*u^3-4 < 0 := by linarith only [hi]
  let C := algebraicCost u
  let p := algebraicPrivate u
  have hgap : C-2*(C-p) = -(9*u^4)/(4*(3*u^3-4)) := by
    dsimp [C,p,algebraicCost,algebraicPrivate]
    generalize he : 3*u^3-4 = a at hden ⊢
    field_simp [hu.ne', hden.ne]
    subst a
    ring
  have hg : 0 < C-2*(C-p) := by
    rw [hgap]
    exact div_pos_of_neg_of_neg (neg_neg_of_pos (by positivity)) (mul_neg_of_pos_of_neg (by norm_num) hden)
  have hslope : 2/3-8/(9*u^3) = 2*(3*u^3-4)/(9*u^3) := by field_simp; ring
  apply stationary_schedule_floor u C (algebraicSqrtCost u) (C-p) b δ v hu hd hv
    (algebraicSqrtCost_sq hu.ne' hden.ne hp) rfl hg _ _ hprivate hterminal
  · dsimp [C,p,algebraicSqrtCost]
    ring
  · rw [hgap, hslope]
    generalize he : 3*u^3-4 = a at hden ⊢
    field_simp [hu.ne', hden.ne]
    ring


/-- Every finite private grid, including one with a free endpoint, obeys the
same lower bound once its physical terminal height and raw trials are charged. -/
theorem exact_finite_grid_floor {n : ℕ} (z w : ℕ → ℝ)
    {u C b δ curve h ratio v height Z : ℝ}
    (hl : rootLower < u) (hr : u < rootUpper) (hp : rootPolynomial u = 0)
    (hbudget : C < algebraicCost u)
    (hb : 0 < b) (hd : 0 < δ) (hc : 0 < curve) (hZ : 0 < Z) (hh : curve ≤ h)
    (hz0 : z 0 = 0) (hzn : z n = Z) (hstep : ∀ i < n, z i ≤ z (i+1))
    (htail : ∀ i < n, (∑ j ∈ Finset.Ico i n, w j) ≤ C-b-h*z (i+1))
    (hmoment : 4/(9*curve^2) ≤ ∑ i ∈ Finset.range n, z (i+1)^2*w i)
    (hratio : 0 ≤ ratio)
    (hheight : (1 + δ*Z^2/(2*(2/(3*curve^2))))/δ^3 ≤ height)
    (hbox : height+v ≤ ratio*(b/δ))
    (hmean : ratio/3 + 1/(3*δ^2*b) ≤ 2*v-b/δ)
    (hraw : b+δ*ratio/3+1/(3*δ*b) ≤ C) : False := by
  let y (i : ℕ) := z i / Z
  have htail' (i : ℕ) (hi : i < n) :
      (∑ j ∈ Finset.Ico i n, w j) ≤ C-b-(h*Z)*y (i+1) := by
    have e : h*Z*y (i+1) = h*z (i+1) := by dsimp [y]; field_simp
    simpa only [e] using htail i hi
  have hgrid := Cogentic.finite_stage_private_floor y w
    (mul_nonneg (hc.le.trans hh) hZ.le) (by simp [y,hz0]) (by simp [y,hzn,hZ.ne'])
    (fun i hi ↦ div_le_div_of_nonneg_right (hstep i hi) hZ.le) htail'
  have hm : 4/(9*(curve*Z)^2) ≤ ∑ i ∈ Finset.range n, y (i+1)^2*w i := by
    have e (i : ℕ) : y (i+1)^2*w i = (z (i+1)^2*w i)/Z^2 := by
      dsimp [y]; rw [div_pow,div_mul_eq_mul_div]
    have e' : 4/(9*(curve*Z)^2) = (4/(9*curve^2))/Z^2 := by field_simp
    simpa only [e, e', div_eq_mul_inv, Finset.sum_mul] using
      (div_le_div_of_nonneg_right hmoment (sq_nonneg Z))
  have e : δ/(2*(2/(3*(curve*Z)^2))) = δ*Z^2/(2*(2/(3*curve^2))) := by field_simp
  have term := terminal_tradeoff_of_search b δ (2/(3*(curve*Z)^2)) ratio v height
    (algebraicCost u) hb hd (by positivity) hratio (by simpa only [e] using hheight)
    hbox hmean (hraw.trans hbudget.le)
  have einv : 1/(2/(3*(curve*Z)^2)) = 3*(curve*Z)^2/2 := by field_simp
  rw [einv] at term
  exact isolated_root_schedule_floor hl hr hp hd (mul_pos hc hZ)
    (by linarith only [hm,hgrid,hbudget,mul_le_mul_of_nonneg_right hh hZ.le]) term

end Cogentic.Randomized
