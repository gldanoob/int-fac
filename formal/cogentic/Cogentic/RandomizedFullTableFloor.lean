import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic

/-- The rational population bound implies a lower bound on the top-field height. -/
theorem randomizedFullTableHeight {u C : ℝ} (hu : 0 < u) (hC : 0 < C)
    (population : 4 / (9 * u ^ 2) + 2 * u / 3 ≤ C) :
    2 / (3 * C) ≤ 3 * u ^ 2 / 2 := by
  have reciprocal : 4 / (9 * u ^ 2) ≤ C := by
    linarith only [population, hu]
  have bound := (div_le_iff₀ (show 0 < 9 * u ^ 2 by positivity)).mp reciprocal
  apply (div_le_iff₀ (show 0 < 3 * C by positivity)).mpr
  nlinarith only [bound]

/-- At coefficient 1.97 the reduced full terminal-table inequality is impossible
even when the cost model charges just one private anchor. -/
theorem randomizedFullTableFloor {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (sweep : 3 * (197 / 100 : ℝ) ^ 2 * t * (1 - t / 2) ≥
      2 / (3 * (197 / 100 : ℝ)) + 2 * Real.sqrt (2 * (197 / 100 : ℝ) * (1 + t))) :
    False := by
  let a : ℝ := 19849 / 5000
  let b : ℝ := 28071 / 5000
  let chord : ℝ := a * (1 - t) + b * t
  let radical : ℝ := 2 * Real.sqrt (2 * (197 / 100 : ℝ) * (1 + t))
  have hgap : 0 ≤ 1 - t := sub_nonneg.mpr ht'
  have hgap' : 0 ≤ t * (1 - t) := mul_nonneg ht hgap
  have chord_sq : chord ^ 2 ≤ (1 - t) * a ^ 2 + t * b ^ 2 := by
    dsimp [chord, a, b]
    nlinarith only [hgap']
  have endpoints : (1 - t) * a ^ 2 + t * b ^ 2 ≤ 8 * (197 / 100 : ℝ) * (1 + t) := by
    have ha : a ^ 2 ≤ 8 * (197 / 100 : ℝ) := by norm_num [a]
    have hb : b ^ 2 ≤ 16 * (197 / 100 : ℝ) := by norm_num [b]
    calc
      _ ≤ (1 - t) * (8 * (197 / 100 : ℝ)) + t * (16 * (197 / 100 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left ha hgap) (mul_le_mul_of_nonneg_left hb ht)
      _ = _ := by ring
  have radical_sq : radical ^ 2 = 8 * (197 / 100 : ℝ) * (1 + t) := by
    have h : 0 ≤ 2 * (197 / 100 : ℝ) * (1 + t) := by positivity
    dsimp [radical]
    nlinarith only [Real.sq_sqrt h]
  have chord_le : chord ≤ radical := by
    by_contra! hn
    have hr : 0 ≤ radical := by
      dsimp [radical]
      positivity
    have h := mul_pos (sub_pos.mpr hn) (add_pos_of_pos_of_nonneg (lt_of_le_of_lt hr hn) hr)
    have hs : chord ^ 2 ≤ radical ^ 2 := chord_sq.trans (endpoints.trans radical_sq.ge)
    apply (not_lt_of_ge hs)
    calc
      radical ^ 2 < radical ^ 2 + (chord - radical) * (chord + radical) :=
        lt_add_of_pos_right _ h
      _ = chord ^ 2 := by ring
  change 2 / (3 * (197 / 100 : ℝ)) + radical ≤
    3 * (197 / 100 : ℝ) ^ 2 * t * (1 - t / 2) at sweep
  dsimp [chord, a, b] at chord_le
  nlinarith only [sweep, chord_le, sq_nonneg (t - 99983 / 116427)]

end Cogentic
