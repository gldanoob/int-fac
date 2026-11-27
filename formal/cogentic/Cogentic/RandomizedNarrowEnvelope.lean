import Cogentic.RandomizedScaledSchedule

namespace Cogentic.Randomized

/-- The slope of the same scaled private cost used by the finite schedule. -/
noncomputable def scaledPrivateSlope (θ v : ℝ) : ℝ := 2 / 3 - 8 * θ / (9 * v ^ 3)

private theorem private_tangent {θ v u : ℝ} (hθ : 0 ≤ θ)
    (hv : 0 < v) (hu : 0 < u) :
    scaledPrivateCost θ v + scaledPrivateSlope θ v * (u - v) ≤ scaledPrivateCost θ u := by
  have hinv : 3 / v ^ 2 - 2 * u / v ^ 3 ≤ 1 / u ^ 2 := by
    field_simp
    nlinarith only [mul_nonneg (sq_nonneg (u - v)) (show 0 ≤ 2 * u + v by positivity)]
  have hv' : scaledPrivateCost θ v + scaledPrivateSlope θ v * (u - v) =
      (4 * θ / 9) * (3 / v ^ 2 - 2 * u / v ^ 3) + 2 * u / 3 := by
    unfold scaledPrivateCost scaledPrivateSlope
    field_simp
    ring
  have hu' : scaledPrivateCost θ u = (4 * θ / 9) * (1 / u ^ 2) + 2 * u / 3 := by
    unfold scaledPrivateCost
    ring
  rw [hv', hu']
  exact add_le_add_left (mul_le_mul_of_nonneg_left hinv (show 0 ≤ 4 * θ / 9 by positivity)) _

/-- A tangent at a rational test point bounds the entire two-variable
envelope. A nonzero slope residual is handled by completing the square. -/
theorem narrow_envelope_tangent {θ U C s v u b : ℝ}
    (hθ : 0 ≤ θ) (hU : 0 < U) (hv : 0 < v) (hu : 0 < u)
    (hs : s ≤ Real.sqrt C) (hgap : 0 ≤ C - 2 * (C - scaledPrivateCost θ v))
    (hprivate : b + scaledPrivateCost θ u ≤ C) :
    let b₀ := C - scaledPrivateCost θ v
    let residue := -(6 * (C - 2 * b₀)) * scaledPrivateSlope θ v - 2 * U * v
    6 * b * (C - b) - U * u ^ 2 - 4 * Real.sqrt C ≤
      6 * b₀ * (C - b₀) - U * v ^ 2 - 4 * s + residue ^ 2 / (4 * U) := by
  dsimp only
  let b₀ := C - scaledPrivateCost θ v
  let w := 6 * (C - 2 * b₀)
  let residue := -w * scaledPrivateSlope θ v - 2 * U * v
  have hh : b - b₀ ≤ -scaledPrivateSlope θ v * (u - v) := by
    dsimp [b₀]
    linarith only [private_tangent hθ hv hu, hprivate]
  have hw : 0 ≤ w := by dsimp [w, b₀]; positivity
  have hlinear := mul_le_mul_of_nonneg_left hh hw
  have hcomplete :
      residue * (u - v) - U * (u - v) ^ 2 ≤ residue ^ 2 / (4 * U) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith only [sq_nonneg (2 * U * (u - v) - residue)]
  change 6 * b * (C - b) - U * u ^ 2 - 4 * Real.sqrt C ≤
    6 * b₀ * (C - b₀) - U * v ^ 2 - 4 * s + residue ^ 2 / (4 * U)
  calc
    _ = 6 * b₀ * (C - b₀) - U * v ^ 2 - 4 * Real.sqrt C +
        (w * (b - b₀) - 2 * U * v * (u - v) - 6 * (b - b₀) ^ 2 - U * (u - v) ^ 2) := by
      dsimp [w]
      ring
    _ ≤ _ := by
      dsimp only [residue] at hcomplete ⊢
      nlinarith only [hlinear, hcomplete, sq_nonneg (b - b₀), hs]

private theorem terminal_at_larger_ceiling {U C C₀ u b : ℝ} (hU : 0 ≤ U)
    (hC : 0 < C) (hb : 0 < b) (hC₀ : C ≤ C₀)
    (hterminal : U * u ^ 2 + 4 * Real.sqrt C ≤ 6 * b * (C - b)) :
    U * u ^ 2 + 4 * Real.sqrt C₀ ≤ 6 * b * (C₀ - b) := by
  have hs : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  have hs₀ : 0 ≤ Real.sqrt C₀ := Real.sqrt_nonneg _
  have hcs := Real.sq_sqrt hC.le
  have hcs₀ := Real.sq_sqrt (hC.le.trans hC₀)
  have hbase : 4 * Real.sqrt C ≤ 6 * b * C := by
    nlinarith only [hterminal, mul_nonneg hU (sq_nonneg u), sq_nonneg b]
  have hcoef : 4 ≤ 6 * b * Real.sqrt C := by
    apply le_of_mul_le_mul_right _ hs
    nlinarith only [hbase, congrArg (fun x : ℝ => 6 * b * x) hcs]
  have hcoef' : 4 ≤ 6 * b * (Real.sqrt C₀ + Real.sqrt C) := by
    nlinarith only [hcoef, mul_nonneg hb.le hs₀]
  have hdiff : 0 ≤ Real.sqrt C₀ - Real.sqrt C := sub_nonneg.mpr (Real.sqrt_le_sqrt hC₀)
  have hmove : 4 * (Real.sqrt C₀ - Real.sqrt C) ≤ 6 * b * (C₀ - C) := by
    calc
      _ ≤ (6 * b * (Real.sqrt C₀ + Real.sqrt C)) * (Real.sqrt C₀ - Real.sqrt C) :=
        mul_le_mul_of_nonneg_right hcoef' hdiff
      _ = 6 * b * (Real.sqrt C₀ ^ 2 - Real.sqrt C ^ 2) := by ring
      _ = _ := by rw [hcs₀, hcs]
  nlinarith only [hterminal, hmove]

/-- A negative rational tangent certificate at C₀ forces every feasible
budget to exceed C₀. -/
theorem narrow_envelope_exclusion {θ U C₀ s v u b C : ℝ}
    (hθ : 0 ≤ θ) (hU : 0 < U) (hv : 0 < v) (hu : 0 < u) (hC : 0 < C) (hb : 0 < b)
    (hs : s ≤ Real.sqrt C₀) (hgap : 0 ≤ C₀ - 2 * (C₀ - scaledPrivateCost θ v))
    (hcert :
      let b₀ := C₀ - scaledPrivateCost θ v
      let residue := -(6 * (C₀ - 2 * b₀)) * scaledPrivateSlope θ v - 2 * U * v
      6 * b₀ * (C₀ - b₀) - U * v ^ 2 - 4 * s + residue ^ 2 / (4 * U) < 0)
    (hprivate : b + scaledPrivateCost θ u ≤ C)
    (hterminal : U * u ^ 2 + 4 * Real.sqrt C ≤ 6 * b * (C - b)) :
    C₀ < C := by
  by_contra! hle
  have ht := terminal_at_larger_ceiling hU.le hC hb hle hterminal
  have h := narrow_envelope_tangent hθ hU hv hu hs hgap (hprivate.trans hle)
  exact (not_lt_of_ge (sub_nonneg.mpr (by linarith only [ht]))) (h.trans_lt hcert)

/-- The abstract half-width envelope with coefficient 111/80 excludes all
budgets up to 2.02602644. The tangent witness consists only of rationals. -/
theorem narrow_envelope_37_20_lower {u b C : ℝ} (hu : 0 < u) (hb : 0 < b) (hC : 0 < C)
    (hprivate : b + scaledPrivateCost (1 / 2) u ≤ C)
    (hterminal : (111 / 80) * u ^ 2 + 4 * Real.sqrt C ≤ 6 * b * (C - b)) :
    (2.02602644 : ℝ) < C := by
  have hs : (711692777819 / 500000000000 : ℝ) ≤ Real.sqrt 2.02602644 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  apply narrow_envelope_exclusion (v := (0.55978617 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hu hC hb hs _ _ hprivate hterminal
  · norm_num [scaledPrivateCost]
  · norm_num [scaledPrivateCost, scaledPrivateSlope]

end Cogentic.Randomized
