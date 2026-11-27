import Cogentic.RandomizedKnotCount
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

noncomputable def classKnotPrivateCost (m u : ℝ) : ℝ :=
  2 / (9 * u ^ 2) + (1 - m) * u

private theorem invSquare_tangent {v u : ℝ} (hv : 0 < v) (hu : 0 < u) :
    3 / v ^ 2 - 2 * u / v ^ 3 ≤ 1 / u ^ 2 := by
  field_simp
  nlinarith only [mul_nonneg (sq_nonneg (u - v)) (show 0 ≤ 2 * u + v by positivity)]

private theorem exclude_with_tangent {C v q s b₀ p' L u b δ : ℝ}
    (hv : 0 < v) (hu : 0 < u) (hδ : 0 < δ) (hs : s ^ 2 ≤ C)
    (hb₀ : b₀ = C - (2 / (9 * v ^ 2) + q * v)) (hp' : p' = q - 4 / (9 * v ^ 3))
    (hL : L = -6 * (C - 2 * b₀) * p' - 3 * v) (hgap : 0 ≤ 6 * (C - 2 * b₀))
    (hnum : 6 * b₀ * (C - b₀) - 3 * v ^ 2 / 2 - 4 * s + L ^ 2 / 6 < 0)
    (hprivate : b + (2 / (9 * u ^ 2) + q * u) ≤ C)
    (hterminal : 3 * u ^ 2 / 2 + 4 / δ + C * δ ≤ 6 * b * (C - b)) : False := by
  have htangent : (2 / (9 * v ^ 2) + q * v) + p' * (u - v) ≤
      2 / (9 * u ^ 2) + q * u := by
    have hleft : (2 / (9 * v ^ 2) + q * v) + p' * (u - v) =
        (2 / 9) * (3 / v ^ 2 - 2 * u / v ^ 3) + q * u := by
      rw [hp']
      field_simp [hv.ne']
      ring
    rw [hleft]
    have hi := mul_le_mul_of_nonneg_left (invSquare_tangent hv hu) (by norm_num : 0 ≤ (2 : ℝ) / 9)
    have hr : (2 / 9) * (1 / u ^ 2) = 2 / (9 * u ^ 2) := by ring
    rw [hr] at hi
    exact add_le_add hi le_rfl
  have hb : b - b₀ ≤ -p' * (u - v) := by
    rw [hb₀]
    linarith only [hprivate, htangent]
  have hsurplus : 6 * b * (C - b) - 3 * u ^ 2 / 2 - 4 * s ≤
      6 * b₀ * (C - b₀) - 3 * v ^ 2 / 2 - 4 * s + L * (u - v) - 3 * (u - v) ^ 2 / 2 := by
    have hc := mul_le_mul_of_nonneg_left hb hgap
    rw [hL]
    nlinarith only [hc, sq_nonneg (b - b₀)]
  have hcomplete : L * (u - v) - 3 * (u - v) ^ 2 / 2 ≤ L ^ 2 / 6 := by
    nlinarith only [sq_nonneg (3 * (u - v) - L)]
  have hterm : 4 * s ≤ 4 / δ + C * δ := by
    apply le_of_mul_le_mul_right (a := δ) _ hδ
    have he : (4 / δ + C * δ) * δ = 4 + C * δ ^ 2 := by field_simp
    rw [he]
    nlinarith only [sq_nonneg (s * δ - 2), mul_le_mul_of_nonneg_right hs (sq_nonneg δ)]
  linarith only [hterminal, hterm, hsurplus, hcomplete, hnum]

/-- At budget `2.033`, a finite left-square maximum at most `1/3 - 4/3178`
precludes meeting the half-width private budget and terminal budget together. -/
theorem class_knot_threshold_exclusion {m u b δ : ℝ}
    (hm : m ≤ 1 / 3 - 4 / 3178) (hu : 0 < u) (hδ : 0 < δ)
    (hprivate : b + classKnotPrivateCost m u ≤ 2033 / 1000)
    (hterminal : 3 * u ^ 2 / 2 + 4 / δ + (2033 / 1000) * δ ≤
      6 * b * ((2033 / 1000) - b)) : False := by
  let C : ℝ := 2033 / 1000
  let v : ℝ := 0.55648169
  let q : ℝ := 2 / 3 + 4 / 3178
  let s : ℝ := 1425833089811 / 1000000000000
  let b₀ := C - (2 / (9 * v ^ 2) + q * v)
  let p' := q - 4 / (9 * v ^ 3)
  let L := -6 * (C - 2 * b₀) * p' - 3 * v
  have hv : 0 < v := by norm_num [v]
  have hs : s ^ 2 ≤ C := by norm_num [s, C]
  have hgap : 0 ≤ 6 * (C - 2 * b₀) := by norm_num [C, b₀, v, q]
  have hnum : 6 * b₀ * (C - b₀) - 3 * v ^ 2 / 2 - 4 * s + L ^ 2 / 6 < 0 := by
    norm_num [L, p', C, b₀, v, q, s]
  have hcoef : q ≤ 1 - m := by dsimp [q]; linarith only [hm]
  have hprivate' : b + (2 / (9 * u ^ 2) + q * u) ≤ C :=
    (add_le_add le_rfl (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hu.le))).trans hprivate
  exact exclude_with_tangent hv hu hδ hs rfl rfl rfl hgap hnum hprivate' hterminal

/-- Every normalized half-width grid with budget at most 2.033 and the ordinary
terminal constraints has at least 353 screening stages. -/
theorem half_width_at_least_353_stages {k : ℕ} (z w : ℕ → ℝ) {C b u δ : ℝ}
    (hC : 0 < C) (hcap : C ≤ 2033 / 1000) (hu : 0 < u) (hδ : 0 < δ)
    (hz0 : z 0 = 0) (hz1 : z (k + 1) = 1)
    (hstep : ∀ i < k + 1, z i ≤ z (i + 1))
    (htail : ∀ i < k + 1, (∑ j ∈ Finset.Ico i (k + 1), w j) ≤ C - b - u * z (i + 1))
    (hmoment : 2 / (9 * u ^ 2) ≤ ∑ i ∈ Finset.range (k + 1), z (i + 1) ^ 2 * w i)
    (hterminal : 3 * u ^ 2 / 2 + 4 / δ + C * δ ≤ 6 * b * (C - b)) :
    353 ≤ k + 1 := by
  by_contra hfew
  have hk : k ≤ 351 := by omega
  have hgate := finite_knot_private_floor k z w hu.le hz0 hz1 hstep htail
  have hprivate : b + classKnotPrivateCost (finiteKnotMaximum k) u ≤ 2033 / 1000 := by
    unfold classKnotPrivateCost
    rw [mul_comm (1 - finiteKnotMaximum k) u]
    linarith only [hmoment, hgate, hcap]
  have hpos : 0 < C * (6 * b - δ) := by
    nlinarith only [hterminal, sq_nonneg u, sq_nonneg b, div_pos (by norm_num : (0:ℝ)<4) hδ]
  have hgrowth : 0 ≤ 6 * b - δ := (pos_of_mul_pos_right hpos hC.le).le
  have hterminal' : 3 * u ^ 2 / 2 + 4 / δ + (2033 / 1000) * δ ≤
      6 * b * ((2033 / 1000) - b) := by
    nlinarith only [hterminal, mul_nonneg (sub_nonneg.mpr hcap) hgrowth]
  exact class_knot_threshold_exclusion (finiteKnotMaximum_atMost352_bound hk)
    hu hδ hprivate hterminal'

end Cogentic.Randomized
