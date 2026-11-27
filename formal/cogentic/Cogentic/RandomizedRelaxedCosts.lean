import Cogentic.RandomizedScheduleFloor
import Cogentic.RandomizedRadixFloor
import Cogentic.RandomizedFreeRationalFloor

namespace Cogentic.Randomized

/-- θ is the retained fraction of the excess Gaussian height, and ρ the
retained fraction of the work for finding a rationally eligible candidate.
The terminal mean still charges its actual density. -/
theorem terminal_cost_relaxation (b δ curve ratio v height θ ρ C : ℝ)
    (hb : 0 < b) (hd : 0 < δ) (hc : 0 < curve) (ht : 0 ≤ θ) (hratio : 0 ≤ ratio)
    (hheight : (1 + θ*δ*(3*curve^2)/4)/δ^3 ≤ height)
    (hbox : height + v ≤ ratio*(b/δ))
    (hmean : ratio/3 + 1/(3*δ^2*b) ≤ 2*v-b/δ)
    (hraw : b+δ*ratio/3+ρ/(3*δ*b) ≤ C) :
    θ*(3*curve^2/2) + 2*(1+ρ)/δ + (1-ρ)/(3*b) + C*δ ≤ 6*b*(C-b) := by
  have h := terminal_tradeoff_of_height b δ ratio v ((1+θ*δ*(3*curve^2)/4)/δ^3)
    (ρ/(3*δ*b)) C hb hd (by positivity) hratio (by linarith) hmean hraw
  convert h using 1
  field_simp
  ring

/-- With the original rational trials and terminal mean, removing all excess
height still leaves a floor above the ordinary GNFS heuristic coefficient. -/
theorem radix_only_search_floor (b δ curve ratio v height : ℝ)
    (hb : 0 < b) (hd : 0 < δ) (hc : 0 < curve) (hratio : 0 ≤ ratio)
    (hprivate : b+4/(9*curve^2)+2*curve/3 ≤ 1.94548659)
    (hheight : 1/δ^3 ≤ height) (hbox : height + v ≤ ratio*(b/δ))
    (hmean : ratio/3 + 1/(3*δ^2*b) ≤ 2*v-b/δ)
    (hraw : b+δ*ratio/3+1/(3*δ*b) ≤ 1.94548659) : False := by
  have h := terminal_cost_relaxation b δ curve ratio v height 0 1 1.94548659 hb hd hc
    (by norm_num) hratio (by simpa using hheight) hbox hmean hraw
  apply radix_schedule_floor b δ curve hd hc
  · norm_num at hprivate ⊢
    exact hprivate
  · norm_num at h ⊢
    exact h


/-- Granting a free source of rationally eligible trials still requires enough
points in the original box to supply the terminal candidate. -/
theorem free_rational_search_floor (b δ curve ratio v height : ℝ)
    (hb : 0 < b) (hd : 0 < δ) (hc : 0 < curve) (hratio : 0 ≤ ratio)
    (hprivate : b+4/(9*curve^2)+2*curve/3 ≤ 39/20)
    (hheight : (1+δ*(3*curve^2)/4)/δ^3 ≤ height)
    (hbox : height+v ≤ ratio*(b/δ))
    (hmean : ratio/3 + 1/(3*δ^2*b) ≤ 2*v-b/δ)
    (hraw : b+δ*ratio/3 ≤ 39/20) : False := by
  have h := terminal_cost_relaxation b δ curve ratio v height 1 0 (39/20) hb hd hc
    (by norm_num) hratio (by simpa using hheight) hbox hmean (by simpa using hraw)
  apply Cogentic.randomizedFreeRationalFloor hc hd hb hprivate
  simpa only [one_mul, add_zero, sub_zero, mul_one, one_div] using h


/-- The ordinary terminal population and rational proposal law already imply
the classical GNFS constant, even without any private cost or excess height. -/
theorem terminal_gnfs_floor {b δ C : ℝ} (hd : 0 < δ) (hC : 0 ≤ C)
    (hterm : 4/δ + C*δ ≤ 6*b*(C-b)) : 64 ≤ 9*C^3 := by
  have hpar : 6*b*(C-b) ≤ 3*C^2/2 := by nlinarith only [sq_nonneg (2*b-C)]
  have hc := mul_le_mul_of_nonneg_right (hterm.trans hpar) hd.le
  have e : (4/δ + C*δ)*δ = 4 + C*δ^2 := by field_simp
  rw [e] at hc
  nlinarith only [hc, mul_nonneg hC (sq_nonneg (4*δ-3*C))]

/-- Sharpness in this terminal relaxation. Positivity or strict mean margins
in a concrete algorithm may make equality inaccessible. -/
theorem terminal_gnfs_equality {C : ℝ} (hC : 0 < C) (hc : 9*C^3 = 64) :
    4/(3*C/4) + C*(3*C/4) = 6*(C/2)*(C-C/2) := by
  field_simp
  nlinarith only [hc]

theorem terminal_search_gnfs_floor (b δ ratio v height C : ℝ)
    (hb : 0 < b) (hd : 0 < δ) (hC : 0 ≤ C) (hratio : 0 ≤ ratio)
    (hheight : 1/δ^3 ≤ height) (hbox : height+v ≤ ratio*(b/δ))
    (hmean : ratio/3 + 1/(3*δ^2*b) ≤ 2*v-b/δ)
    (hraw : b+δ*ratio/3+1/(3*δ*b) ≤ C) : 64 ≤ 9*C^3 := by
  have h := terminal_cost_relaxation b δ 1 ratio v height 0 1 C hb hd (by norm_num)
    (by norm_num) hratio (by simpa using hheight) hbox hmean hraw
  apply terminal_gnfs_floor hd hC (b := b)
  norm_num at h ⊢
  exact h

end Cogentic.Randomized
