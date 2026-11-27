import Cogentic.RandomizedPrivateFloor
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

/-- Separate the contribution of the field height from the cost of drawing a
rationally eligible point in the two-coordinate terminal box. -/
theorem terminal_tradeoff_of_height (b δ ratio v height charge C : ℝ)
    (hb : 0 < b) (hd : 0 < δ) (hh : 0 ≤ height) (hratio : 0 ≤ ratio)
    (hbox : height + v ≤ ratio*(b/δ))
    (hmean : ratio/3 + 1/(3*δ^2*b) ≤ 2*v-b/δ)
    (hraw : b+δ*ratio/3+charge ≤ C) :
    2*height*δ^2 + 1/(3*b) + C*δ + (6*b-δ)*charge ≤ 6*b*(C-b) := by
  have hlo : b/δ + 2*height + 1/(3*δ^2*b) ≤ (2*(b/δ)-1/3)*ratio := by linarith
  have hslope : 0 ≤ 2*(b/δ)-1/3 := by
    by_contra! hneg
    have hpos : 0 < b/δ + 2*height + 1/(3*δ^2*b) := by positivity
    linarith only [hpos,hlo,mul_nonpos_of_nonpos_of_nonneg hneg.le hratio]
  have hupper : ratio ≤ 3*(C-b-charge)/δ := by
    apply (le_div_iff₀ hd).mpr
    linarith
  have h := mul_le_mul_of_nonneg_left hupper hslope
  have h' := mul_le_mul_of_nonneg_right (hlo.trans h) (sq_nonneg δ)
  apply sub_nonneg.mp
  convert sub_nonneg.mpr h' using 1 <;> first | rfl | (field_simp; ring)

/-- The ordinary field height and rational trial charge give the current
private/terminal schedule tradeoff. -/
theorem terminal_tradeoff_of_search (b δ x ratio v height C : ℝ)
    (hb : 0 < b) (hd : 0 < δ) (hx : 0 < x)
    (hratio : 0 ≤ ratio)
    (hheight : (1 + δ / (2*x)) / δ^3 ≤ height)
    (hbox : height + v ≤ ratio * (b / δ))
    (hmean : ratio / 3 + 1 / (3*δ^2*b) ≤ 2*v - b/δ)
    (hraw : b + δ*ratio/3 + 1/(3*δ*b) ≤ C) :
    1 / x + 4 / δ + C * δ ≤ 6 * b * (C - b) := by
  have h := terminal_tradeoff_of_height b δ ratio v ((1+δ/(2*x))/δ^3) (1/(3*δ*b))
    C hb hd (by positivity) hratio (by linarith) hmean hraw
  convert h using 1
  field_simp
  ring

private theorem reciprocal_square_tangent (y a : ℝ) (hy : 0 < y) (ha : 0 < a) :
    3/a^2 - 2*y/a^3 ≤ 1/y^2 := by
  field_simp
  nlinarith [mul_nonneg (sq_nonneg (y-a)) (show 0 ≤ 2*y+a by linarith)]

/-- A rational separating inequality for the fixed two-cost schedule model.
Here 2/(3v²) is κδ and v is the least elliptic recognition coefficient
in private cutoff units. The conclusion excludes a ceiling of 2.15463. -/
theorem sparse_schedule_floor (b δ v : ℝ) (hd : 0 < δ) (hv : 0 < v)
    (hprivate : b + 4/(9*v^2) + 2*v/3 ≤ 215463/100000)
    (hterminal : 3*v^2/2 + 4/δ + (215463/100000)*δ ≤ 6*b*(215463/100000-b)) :
    False := by
  let a : ℝ := 7848521/10000000
  let k : ℝ := 13394292/10000000
  let s : ℝ := 146786579/100000000
  have ha : 0 < a := by norm_num [a]
  have hk : 0 < k := by norm_num [k]
  have hδ : 4*s ≤ 4/δ + (215463/100000)*δ := by
    have h : 4*s*δ ≤ 4 + (215463/100000)*δ^2 := by
      dsimp [s]
      nlinarith only [sq_nonneg ((146786579/100000000 : ℝ)*δ-2), sq_nonneg δ]
    have he : (4/δ + (215463/100000)*δ)*δ = 4 + (215463/100000)*δ^2 := by
      field_simp
    exact le_of_mul_le_mul_right (a := δ) (by linarith only [h,he]) hd
  have hinv : (2*k/3)*(3/a^2 - 2*v/a^3) ≤ (2*k/3)*(1/v^2) :=
    mul_le_mul_of_nonneg_left (reciprocal_square_tangent v a hv ha) (by positivity)
  have he : 4/(9*v^2) = (4/9)*(1/v^2) := by ring
  rw [he] at hprivate
  dsimp [a,k,s] at *
  have hbq := sq_nonneg (b-90988635/100000000)
  have hvq := sq_nonneg (v + ((13394292/10000000 : ℝ) - 4*(13394292/10000000)/(3*(7848521/10000000 : ℝ)^3))/3)
  generalize 1/v^2 = u at hinv hprivate
  generalize 4/δ = e at hδ hterminal
  norm_num at hinv hvq
  ring_nf at hprivate hterminal hδ hinv hbq hvq
  linarith only [hprivate,hterminal,hδ,hinv,hbq,hvq]


/-- The model floor applies to every finite private grid ending at one.
The moment condition encodes the prescribed private factor mass. -/
theorem finite_grid_schedule_floor {n : ℕ} (z w : ℕ → ℝ)
    (b δ curve h ratio v height : ℝ) (hb : 0 < b) (hd : 0 < δ) (hc : 0 < curve)
    (hh : curve ≤ h) (hz0 : z 0 = 0) (hzn : z n = 1)
    (hstep : ∀ i < n, z i ≤ z (i+1))
    (htail : ∀ i < n, (∑ j ∈ Finset.Ico i n, w j) ≤ 215463/100000 - b - h*z (i+1))
    (hmoment : 4/(9*curve^2) ≤ ∑ i ∈ Finset.range n, z (i+1)^2*w i)
    (hratio : 0 ≤ ratio)
    (hheight : (1 + δ/(2*(2/(3*curve^2))))/δ^3 ≤ height)
    (hbox : height + v ≤ ratio*(b/δ))
    (hmean : ratio/3 + 1/(3*δ^2*b) ≤ 2*v-b/δ)
    (hraw : b + δ*ratio/3 + 1/(3*δ*b) ≤ 215463/100000) : False := by
  have hgrid := Cogentic.finite_stage_private_floor z w (hc.le.trans hh) hz0 hzn hstep htail
  have hterminal := terminal_tradeoff_of_search b δ (2/(3*curve^2)) ratio v height
    (215463/100000) hb hd (by positivity) hratio hheight hbox hmean hraw
  have hinv : 1/(2/(3*curve^2)) = 3*curve^2/2 := by field_simp
  rw [hinv] at hterminal
  exact sparse_schedule_floor b δ curve hd hc (by linarith only [hgrid,hmoment,hh]) hterminal

end Cogentic.Randomized
