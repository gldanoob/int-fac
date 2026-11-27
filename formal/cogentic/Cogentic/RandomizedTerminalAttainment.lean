import Cogentic.RandomizedOptimalCost

namespace Cogentic.Randomized

/-- Equality in the relaxed terminal tradeoff supplies a positive box scale,
ratio, and height attaining all four terminal constraints. -/
theorem terminal_tradeoff_attainment (b δ x C : ℝ) (hb : 0 < b) (hd : 0 < δ)
    (hx : 0 < x) (hC : 0 ≤ C) (htrade : 1/x + 4/δ + C*δ = 6*b*(C-b)) :
    ∃ ratio v height : ℝ, 0 < ratio ∧ 0 < v ∧ 0 < height ∧
      (1+δ/(2*x))/δ^3 = height ∧ height+v = ratio*(b/δ) ∧
      ratio/3 + 1/(3*δ^2*b) = 2*v-b/δ ∧ b+δ*ratio/3+1/(3*δ*b) = C := by
  let ratio := 3*(C-b)/δ - 1/(δ^2*b)
  let height := (1+δ/(2*x))/δ^3
  let v := ratio*(b/δ)-height
  have he : ratio*(2*b*δ) = 6*b*(C-b)-2/δ := by
    dsimp [ratio]
    field_simp
    ring
  have hp : 0 < 6*b*(C-b)-2/δ := by
    have heq : 6*b*(C-b)-2/δ = 1/x+2/δ+C*δ := by rw [← htrade]; ring
    rw [heq]
    positivity
  have hr : 0 < ratio := by
    by_contra! hneg
    have hm := mul_nonpos_of_nonpos_of_nonneg hneg (show 0 ≤ 2*b*δ by positivity)
    linarith only [he, hp, hm]
  have hbalance : (2*v-b/δ-(ratio/3+1/(3*δ^2*b)))*δ^2 =
      6*b*(C-b)-(1/x+4/δ+C*δ) := by
    dsimp [v, ratio, height]
    field_simp
    ring
  have hz : (2*v-b/δ-(ratio/3+1/(3*δ^2*b)))*δ^2 = 0 := by
    rw [hbalance, htrade, sub_self]
  have hm := (mul_eq_zero.mp hz).resolve_right (pow_ne_zero 2 hd.ne')
  have hv : 0 < v := by
    linarith only [hm, (show 0 < ratio/3+1/(3*δ^2*b)+b/δ by positivity)]
  refine ⟨ratio, v, height, hr, hv, by dsimp [height]; positivity, rfl, ?_, ?_, ?_⟩
  · dsimp [v]
    ring
  · linarith only [hm]
  · dsimp [ratio]
    field_simp
    ring

/-- The isolated stationary root attains the relaxed terminal model with
endpoint one, and its continuous private cost uses the same ceiling. -/
theorem isolated_root_terminal_attainment {u : ℝ} (hl : rootLower < u) (hr : u < rootUpper)
    (hp : rootPolynomial u = 0) :
    let C := algebraicCost u
    let b := C-algebraicPrivate u
    let δ := 2/algebraicSqrtCost u
    let curve := u
    ∃ ratio v height : ℝ, 0 < b ∧ 0 < δ ∧ 0 < curve ∧
      0 < ratio ∧ 0 < v ∧ 0 < height ∧
      b+4/(9*curve^2)+2*curve/3 = C ∧
      (1+δ/(2*(2/(3*curve^2))))/δ^3 = height ∧ height+v = ratio*(b/δ) ∧
      ratio/3 + 1/(3*δ^2*b) = 2*v-b/δ ∧ b+δ*ratio/3+1/(3*δ*b) = C := by
  let C := algebraicCost u
  let p := algebraicPrivate u
  let b := C-p
  let s := algebraicSqrtCost u
  let δ := 2/s
  let x := 2/(3*u^2)
  have hu₀ : (78/100 : ℝ) < u := (by norm_num [rootLower] : 78/100 ≤ rootLower).trans_lt hl
  have hu₁ : u < (79/100 : ℝ) := hr.trans_le (by norm_num [rootUpper])
  have hu : 0 < u := by linarith only [hu₀]
  have hu₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 78/100) hu₀.le 2
  have hu₃ := pow_le_pow_left₀ hu.le hu₁.le 2
  have hden : 3*u^3-4 < 0 := by
    have h := pow_le_pow_left₀ hu.le hu₁.le 3
    nlinarith only [h]
  have hC : (21/10 : ℝ) < C := by
    exact (by norm_num : (21/10 : ℝ) < 2.15463021529917670).trans (algebraicCost_bounds hl hr).1
  have hquot₀ : (7/10 : ℝ) < 4/(9*u^2) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith only [hu₃]
  have hquot₁ : 4/(9*u^2) < (3/4 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith only [hu₂]
  have hp₀ : 1 < p := by dsimp [p, algebraicPrivate]; linarith only [hu₀, hquot₀]
  have hp₁ : p < (13/10 : ℝ) := by dsimp [p, algebraicPrivate]; linarith only [hu₁, hquot₁]
  have hb₀ : (4/5 : ℝ) < b := by dsimp [b]; linarith only [hC, hp₁]
  have hb : 0 < b := by linarith only [hb₀]
  have hvalue : 6*b*(C-b) = 3*u^2/2+4*s := by
    dsimp [b, s, C, p, algebraicSqrtCost]
    ring
  have hprod : (4/5 : ℝ) < b*p := by
    simpa only [mul_one] using mul_lt_mul hb₀ hp₀.le zero_lt_one hb.le
  have hs : 0 < s := by
    have h : C-b = p := by dsimp [b]; ring
    rw [h] at hvalue
    nlinarith only [hvalue, hprod, hu₃]
  have hsq : s^2 = C := algebraicSqrtCost_sq hu.ne' hden.ne hp
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hx : 0 < x := by dsimp [x]; positivity
  have hinv : 1/x = 3*u^2/2 := by dsimp [x]; field_simp
  have heδ : 4/δ+C*δ = 4*s := by
    dsimp [δ]
    rw [← hsq]
    field_simp
    ring
  have htrade : 1/x+4/δ+C*δ = 6*b*(C-b) := by linarith only [hinv, heδ, hvalue]
  obtain ⟨ratio, v, height, hratio, hv, hheight, heheight, hbox, hmean, hraw⟩ :=
    terminal_tradeoff_attainment b δ x C hb hd hx (by linarith only [hC]) htrade
  refine ⟨ratio, v, height, hb, hd, hu, hratio, hv, hheight, ?_, heheight, hbox, hmean, hraw⟩
  change b+4/(9*u^2)+2*u/3 = C
  dsimp [b, p, algebraicPrivate]
  ring

end Cogentic.Randomized
