import Cogentic.RandomizedUniformGrid
import Cogentic.RandomizedPrivateGates
import Mathlib.Tactic.NormNum

namespace Cogentic.RandomizedSparseSchedule

local notation "δ" => (1.36252214 : ℝ)
local notation "κ" => (0.79430825 : ℝ)
local notation "β" => (0.66779525506 : ℝ)
local notation "b" => (δ * β)
local notation "α" => (0.500000001 : ℝ)
local notation "γ" => (0.68401159399 : ℝ)
local notation "height" => (0.6441958804 : ℝ)
local notation "h" => (0.7848525113 : ℝ)
local notation "slack" => (0.000000002 : ℝ)
local notation "ceiling" => (2.154631 : ℝ)
local notation "lowRatio" => (2.14867235968 : ℝ)
local notation "start" => (0.002 : ℝ)
local notation "step" => ((1 - start) / 262143)
local notation "mass" => (2 * κ * δ / 3)

noncomputable def knot (i : ℕ) : ℝ := start + (i : ℝ) * step

/-- The last band absorbs the moment left by the 262143 equally spaced gaps. -/
noncomputable def lastWeight : ℝ := mass - h * step * ∑ j ∈ Finset.range 262143, (knot j)^2

theorem private_gate_bound {i : ℕ} (hi : i ≤ 262143) :
    b + (h * knot i +
      (∑ j ∈ Finset.Ico i 262143, h * (knot (j+1) - knot j)) + lastWeight) + slack < ceiling := by
  rw [RandomizedPrivateGates.gate_equalization knot h lastWeight hi]
  unfold lastWeight knot
  rw [RandomizedUniformGrid.sum_uniform_grid_sq]
  norm_num

theorem private_allocation :
    0 < lastWeight ∧ h * (1-start) + lastWeight < 2 * mass := by
  unfold lastWeight knot
  rw [RandomizedUniformGrid.sum_uniform_grid_sq]
  norm_num

/-- Strict room for the field height, terminal box, mean, and rational trials. -/
theorem terminal_costs :
    (1 + α/κ)/δ^3 < height ∧ height + (α+γ)*β < lowRatio*β ∧
    lowRatio/3 + 1/(3*δ^3*β) + 0.000000003 < (2*(α+γ)-1)*β ∧
    b + δ*lowRatio/3 + 1/(3*δ*b) + 2*slack < ceiling := by
  norm_num

/-- The rational curve allowances exceed the ideal coefficients. The top and
high algebraic tests use squared comparisons to avoid numerical square roots. -/
theorem other_costs :
    (2 : ℝ) < 1.41421357^2 ∧ 1.41421357^2 < h^2*(3*δ*κ) ∧
    0 < ceiling-(b+δ*1.78/3+2*slack) ∧
    h^2*α/1.78 < (ceiling-(b+δ*1.78/3+2*slack))^2 ∧
    0 < ceiling-(b+δ*1.97/3+2*slack) ∧
    h^2*α^2/(1.78*1.97) < (ceiling-(b+δ*1.97/3+2*slack))^2 ∧
    b+δ*1.78/3+2*slack+1/(3*δ*b) < ceiling ∧
    b+δ*1.97/3+2*slack+(1+α^2/(2*κ*1.78))/(3*δ*b) < ceiling ∧
    b+2*δ/3 < ceiling ∧ 2*b < ceiling := by
  norm_num

end Cogentic.RandomizedSparseSchedule
