import Cogentic.RandomizedPrimeBinBias
import Cogentic.Window

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

/-- Deviation of the actual integer count in a unit residue from the mean count
among all unit residues. Products containing a divisor of the modulus are excluded
from the principal mass. -/
def PrimeBinProgressionBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (r : (ZMod q)ˣ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ),
    Pairwise (fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
    (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
    let S := primeBinProducts A B
    |((S.filter (fun n : ℕ ↦ (r : ZMod q) = (n : ZMod q))).card : ℝ) -
      ((S.filter (fun n ↦ n.Coprime q)).card : ℝ) / q.totient| ≤
        ∏ i, 2 * K * (1 + Real.log (3 * q * B i))^2 * Real.sqrt (B i)

theorem primeBin_progression_of_product_bound (hbias : PrimeBinProductBound) :
    PrimeBinProgressionBound := by
  classical
  obtain ⟨K, hK, bound⟩ := hbias
  refine ⟨K, hK, ?_⟩
  intro q _ r ι _ _ A B hdisj hA hAB
  let S := primeBinProducts A B
  let e := ∏ i, 2 * K * (1 + Real.log (3 * q * B i))^2 * Real.sqrt (B i)
  have he : 0 ≤ e := Finset.prod_nonneg fun i _ ↦ by positivity
  have hχ (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
      ‖Window.twist S (fun _ ↦ 1) χ‖ ≤ e := by
    simpa [Window.twist, S, primeBinProducts_character_sum χ A B hdisj, e]
      using bound q χ hne A B hA hAB
  have hmass : Window.classMass S (fun _ ↦ 1) r =
      ((S.filter (fun n : ℕ ↦ (r : ZMod q) = (n : ZMod q))).card : ℂ) := by
    simp [Window.classMass]
  have hprincipal : Window.twist S (fun _ ↦ 1) (1 : DirichletCharacter ℂ q) =
      ((S.filter (fun n ↦ n.Coprime q)).card : ℂ) := by
    simp only [Window.twist, mul_one]
    have hunit (n : ℕ) : (1 : DirichletCharacter ℂ q) (n : ZMod q) =
        if n.Coprime q then 1 else 0 := by
      by_cases hn : n.Coprime q
      · rw [if_pos hn]
        exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn)
      · rw [if_neg hn]
        exact MulChar.map_nonunit _ (fun h ↦ hn ((ZMod.isUnit_iff_coprime n q).mp h))
    simp_rw [hunit]
    simp
  have h := Window.uniform_progression_bound S (fun _ ↦ 1) e he hχ r
  rw [hmass, hprincipal, div_mul_eq_mul_div, mul_div_assoc, ← mul_sub, norm_mul] at h
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hreal : (q : ℝ) *
      |((S.filter (fun n : ℕ ↦ (r : ZMod q) = (n : ZMod q))).card : ℝ) -
        ((S.filter (fun n ↦ n.Coprime q)).card : ℝ) / q.totient| ≤ q * e := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] using h
  exact le_of_mul_le_mul_left hreal hq

end Cogentic.Randomized

#print axioms Cogentic.Randomized.primeBin_progression_of_product_bound
