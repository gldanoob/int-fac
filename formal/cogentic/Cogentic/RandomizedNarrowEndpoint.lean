import Cogentic.RandomizedNarrowEnvelope

namespace Cogentic.Randomized

/-- Every admissible multiplier above three halves obeys the same rational
lower certificate, including the endpoint multiplier. -/
theorem narrow_envelope_endpoint_lower {χ u b C : ℝ} (hχ : 3 / 2 ≤ χ)
    (hu : 0 < u) (hb : 0 < b) (hC : 0 < C)
    (hp : b + scaledPrivateCost (1 / 2) u ≤ C)
    (ht : (3 * χ / 4) * u ^ 2 + 4 * Real.sqrt C ≤ 6 * b * (C - b)) :
    2.00943303641033 < C := by
  have hs : (1.41754472113239870087 : ℝ) ≤ Real.sqrt 2.00943303641033 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  have ht' : 9 / 8 * u ^ 2 + 4 * Real.sqrt C ≤ 6 * b * (C - b) := by
    have hc : (9 / 8 : ℝ) ≤ 3 * χ / 4 := by linarith
    linarith only [mul_le_mul_of_nonneg_right hc (sq_nonneg u), ht]
  apply narrow_envelope_exclusion (v := (0.568950838804681 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hu hC hb hs _ _ hp ht'
  · norm_num [scaledPrivateCost]
  · norm_num [scaledPrivateCost, scaledPrivateSlope]

/-- A strictly larger width already attains the upper rational enclosure
in the two-inequality model. -/
theorem narrow_envelope_endpoint_upper :
    ∃ χ u b : ℝ, 3 / 2 < χ ∧ 0 < u ∧ 0 < b ∧
      b + scaledPrivateCost (1 / 2) u ≤ 2.00943303641034 ∧
      (3 * χ / 4) * u ^ 2 + 4 * Real.sqrt 2.00943303641034 ≤
        6 * b * (2.00943303641034 - b) := by
  let u : ℝ := 0.568950838804681
  let b : ℝ := 2.00943303641034 - scaledPrivateCost (1 / 2) u
  refine ⟨1.500000000000001, u, b, by norm_num, by norm_num [u], ?_, ?_, ?_⟩
  · norm_num [b, u, scaledPrivateCost]
  · simp [b]
  · have hs : Real.sqrt 2.00943303641034 ≤ (1.41754472113240222810 : ℝ) := by
      apply (Real.sqrt_le_iff).2
      norm_num
    calc
      _ ≤ (3 * 1.500000000000001 / 4) * u ^ 2 + 4 * 1.41754472113240222810 := by
        linarith only [hs]
      _ ≤ _ := by norm_num [b, u, scaledPrivateCost]


/-- The two inequalities for the balanced top construction have an absolute
floor at every width at least one. -/
theorem balanced_envelope_endpoint_lower {χ u b C : ℝ} (hχ : 1 ≤ χ)
    (hu : 0 < u) (hb : 0 < b) (hC : 0 < C)
    (hp : b + scaledPrivateCost (1 / 2) u ≤ C)
    (ht : (3 * χ / 4) * u ^ 2 + 4 * Real.sqrt C ≤ 6 * b * (C - b)) :
    1.9839824118071388228 < C := by
  have hs : (1.408539105529959655440003 : ℝ) ≤ Real.sqrt 1.9839824118071388228 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  have ht' : 3 / 4 * u ^ 2 + 4 * Real.sqrt C ≤ 6 * b * (C - b) := by
    have hc : (3 / 4 : ℝ) ≤ 3 * χ / 4 := by linarith
    linarith only [mul_le_mul_of_nonneg_right hc (sq_nonneg u), ht]
  apply narrow_envelope_exclusion (v := (0.58514027906279831 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hu hC hb hs _ _ hp ht'
  · norm_num [scaledPrivateCost]
  · norm_num [scaledPrivateCost, scaledPrivateSlope]

/-- A width strictly above one fits the upper rational endpoint. -/
theorem balanced_envelope_endpoint_upper :
    ∃ χ u b : ℝ, 1 < χ ∧ 0 < u ∧ 0 < b ∧
      b + scaledPrivateCost (1 / 2) u ≤ 1.9839824118071388230 ∧
      (3 * χ / 4) * u ^ 2 + 4 * Real.sqrt 1.9839824118071388230 ≤
        6 * b * (1.9839824118071388230 - b) := by
  let u : ℝ := 0.58514027906279831
  let b : ℝ := 1.9839824118071388230 - scaledPrivateCost (1 / 2) u
  refine ⟨1.00000000000000000001, u, b, by norm_num, by norm_num [u], ?_, ?_, ?_⟩
  · norm_num [b, u, scaledPrivateCost]
  · simp [b]
  · have hs : Real.sqrt 1.9839824118071388230 ≤ (1.408539105529959655511000 : ℝ) := by
      apply (Real.sqrt_le_iff).2
      norm_num
    calc
      _ ≤ (3 * 1.00000000000000000001 / 4) * u ^ 2 + 4 * 1.408539105529959655511000 := by
        linarith only [hs]
      _ ≤ _ := by norm_num [b, u, scaledPrivateCost]

end Cogentic.Randomized
