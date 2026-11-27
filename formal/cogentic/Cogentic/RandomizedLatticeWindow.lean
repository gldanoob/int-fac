import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Cogentic.Randomized

/-- The open interval for the denominator exponent is feasible precisely
above the two-thirds threshold. -/
theorem lattice_sigma_interval_iff (a : ℝ) :
    (∃ σ : ℝ, 1 - a < σ ∧ σ < a/2) ↔ 2/3 < a := by
  constructor
  · rintro ⟨σ, hlo, hhi⟩
    linarith
  · intro ha
    exact ⟨1/2 - a/4, by linarith, by linarith⟩

/-- The strict exponent comparisons used with a short-vector window. -/
def LatticeWindow (a σ η : ℝ) : Prop :=
  0 < η ∧
    1 - a + η < σ ∧
    σ + η < a/2 ∧
    1 - σ + 2*η < a ∧
    1 - a/2 + 2*η < a ∧
    1 - a + η < a/2 ∧
    a + η < 1

/-- Positive slack below each of the three gaps suffices for all the
exponent comparisons. The first exceptional-set cost dominates the second
because the chosen denominator exponent is below half the main exponent. -/
theorem latticeWindow_of_margins {a σ η : ℝ} (hη : 0 < η)
    (hlo : 2*η < a + σ - 1) (hhi : η < a/2 - σ) (ha : η < 1 - a) :
    LatticeWindow a σ η := by
  unfold LatticeWindow
  exact ⟨hη, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- A quarter of the smallest available gap gives explicit positive slack
for every denominator exponent strictly inside the feasible interval. -/
theorem latticeWindow_explicit {a σ : ℝ} (ha : a < 1)
    (hlo : 1 - a < σ) (hhi : σ < a/2) :
    LatticeWindow a σ (min (a + σ - 1) (min (a/2 - σ) (1 - a)) / 4) := by
  let g := min (a + σ - 1) (min (a/2 - σ) (1 - a))
  have hg : 0 < g := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have h₁ : g ≤ a + σ - 1 := min_le_left _ _
  have h₂ : g ≤ a/2 - σ := (min_le_right _ _).trans (min_le_left _ _)
  have h₃ : g ≤ 1 - a := (min_le_right _ _).trans (min_le_right _ _)
  change LatticeWindow a σ (g/4)
  exact latticeWindow_of_margins (by linarith) (by linarith) (by linarith) (by linarith)

/-- The slack conditions admit a solution precisely between the
two-thirds threshold and one. -/
theorem latticeWindow_exists_iff (a : ℝ) :
    (∃ σ η : ℝ, LatticeWindow a σ η) ↔ 2/3 < a ∧ a < 1 := by
  constructor
  · rintro ⟨σ, η, hη, hlo, hhi, _, _, _, ha⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, ha'⟩
    obtain ⟨σ, hlo, hhi⟩ := (lattice_sigma_interval_iff a).mpr ha
    exact ⟨σ, _, latticeWindow_explicit ha' hlo hhi⟩

/-- An exact witness just above the threshold. -/
theorem latticeWindow_667 : LatticeWindow (667/1000) (1333/4000) (1/16000) := by
  norm_num [LatticeWindow]

/-- An exact witness with more slack. -/
theorem latticeWindow_750 : LatticeWindow (3/4) (5/16) (1/64) := by
  norm_num [LatticeWindow]

end Cogentic.Randomized
