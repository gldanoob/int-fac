import Cogentic.RandomizedSignCount
import Mathlib.Probability.Distributions.Uniform

/-! A finite hidden-root law for public selection. An instantiation must show
that its sampling has the stipulated mass symmetry, that its selection,
rejection decisions and comparison root are determined by the public view,
and that each accepted transcript certifies both parity and the square check. -/

namespace Cogentic.RandomizedHiddenOutputLaw

open RandomizedHiddenLabels RandomizedSignCount

variable {Coins Label G Public : Type*} [CommGroup G]

/-- The public transcript can use the coins and the entire vector of squares. -/
def observe (trace : Coins → (Label → G) → Public) (x : Coins × (Label → G)) : Public :=
  trace x.1 (fun j => x.2 j ^ 2)

/-- Compare the hidden product against the public root. The fallback is outside
any transcript on which the square check has passed. -/
noncomputable def comparisonRatio (labels : Finset Label) (multiplicity : Label → ℕ)
    (publicRoot : G) (roots : Label → G) : SquareFiber (1 : G) := by
  classical
  exact if h : (labelProduct labels multiplicity roots) ^ 2 = publicRoot ^ 2 then
    ⟨labelProduct labels multiplicity roots * publicRoot⁻¹,
      by rw [mul_pow, inv_pow, h, mul_inv_cancel, one_pow]⟩
  else ⟨1, rfl⟩

private theorem comparisonRatio_val (labels : Finset Label) (multiplicity : Label → ℕ)
    (publicRoot : G) (roots : Label → G)
    (h : (labelProduct labels multiplicity roots) ^ 2 = publicRoot ^ 2) :
    (comparisonRatio labels multiplicity publicRoot roots).val =
      labelProduct labels multiplicity roots * publicRoot⁻¹ := by
  simp [comparisonRatio, h]

variable [DecidableEq Label]

private def flip (i : Label) (t : SquareFiber (1 : G)) :
    (Coins × (Label → G)) ≃ (Coins × (Label → G)) :=
  Function.Involutive.toPerm (fun x => (x.1, Function.update x.2 i (t.val * x.2 i))) (by
    intro x
    refine Prod.ext rfl (funext fun j => ?_)
    by_cases h : j = i
    · subst j
      have ht : t.val * t.val = 1 := by simpa only [pow_two, one_mul] using t.property
      simp [← mul_assoc, ht]
    · simp [Function.update_of_ne h])

private theorem flip_square (i : Label) (t : SquareFiber (1 : G))
    (x : Coins × (Label → G)) (j : Label) : ((flip i t x).2 j) ^ 2 = (x.2 j) ^ 2 := by
  change (Function.update x.2 i (t.val * x.2 i) j) ^ 2 = (x.2 j) ^ 2
  by_cases h : j = i
  · subst j
    simp [mul_pow, t.property]
  · rw [Function.update_of_ne h]

private theorem uniform_of_constant {A : Type*} [Fintype A] [Nonempty A] (p : PMF A)
    (h : ∀ a b, p a = p b) : p = PMF.uniformOfFintype A := by
  apply PMF.ext
  intro a
  have hsum : ∑ _ : A, p a = 1 := calc
    ∑ _ : A, p a = ∑ b : A, p b := Finset.sum_congr rfl fun b _ => h a b
    _ = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] at hsum
  rw [PMF.uniformOfFintype_apply]
  exact ENNReal.eq_inv_of_mul_eq_one_left hsum

/-- Condition on a realized public transcript. The labels, their multiplicities,
the odd coordinate, and the comparison root can all be chosen from this transcript.
The mass equality expresses conditional uniformity of the odd coordinate when the
coins, its square, and the other coordinates are held fixed. -/
theorem comparisonRatio_uniform [Fintype G]
    (input : PMF (Coins × (Label → G))) (trace : Coins → (Label → G) → Public)
    (transcript : Public) (labels : Finset Label) (multiplicity : Label → ℕ) (publicRoot : G)
    {i : Label} (hi : i ∈ labels) (hodd : Odd (multiplicity i))
    (hseen : ∃ x ∈ {x | observe trace x = transcript}, x ∈ input.support)
    (hcheck : ∀ x, observe trace x = transcript →
      (labelProduct labels multiplicity x.2) ^ 2 = publicRoot ^ 2)
    (huniform : ∀ x y, observe trace x = transcript → x.1 = y.1 →
      (x.2 i) ^ 2 = (y.2 i) ^ 2 → (∀ j, j ≠ i → x.2 j = y.2 j) → input x = input y) :
    letI : DecidablePred (fun x : G => x ^ 2 = (1 : G) ^ 2) := Classical.decPred _
    letI : Nonempty (SquareFiber (1 : G)) := ⟨⟨1, rfl⟩⟩
    (input.filter {x | observe trace x = transcript} hseen).map
      (fun x => comparisonRatio labels multiplicity publicRoot x.2) =
      PMF.uniformOfFintype (SquareFiber (1 : G)) := by
  classical
  have : Nonempty (SquareFiber (1 : G)) := ⟨⟨1, rfl⟩⟩
  apply uniform_of_constant
  intro a b
  let t : SquareFiber (1 : G) := ⟨b.val * a.val⁻¹, by rw [mul_pow, inv_pow, b.property,
    a.property, mul_inv_cancel, one_pow]⟩
  let e := flip (Coins := Coins) i t
  have hview (x : Coins × (Label → G)) : observe trace (e x) = observe trace x := by
    unfold observe
    exact congrArg (trace x.1) (funext (flip_square i t x))
  have ht : t.val ^ 2 = 1 := by simpa using t.property
  rw [PMF.map_apply, PMF.map_apply]
  conv_rhs => rw [← e.tsum_eq]
  apply tsum_congr
  intro x
  by_cases hx : observe trace x = transcript
  · have hxe : observe trace (e x) = transcript := (hview x).trans hx
    have hmass : input x = input (e x) := by
      apply huniform x (e x) hx rfl (flip_square i t x i).symm
      intro j hj
      exact (Function.update_of_ne hj _ _).symm
    have hr : (comparisonRatio labels multiplicity publicRoot (e x).2).val =
        t.val * (comparisonRatio labels multiplicity publicRoot x.2).val := by
      rw [comparisonRatio_val _ _ _ _ (hcheck _ hxe), comparisonRatio_val _ _ _ _ (hcheck _ hx)]
      change labelProduct labels multiplicity (Function.update x.2 i (t.val * x.2 i)) *
          publicRoot⁻¹ = _
      rw [labelProduct_update_odd labels multiplicity x.2 hi hodd ht, mul_assoc]
    have heq : b = comparisonRatio labels multiplicity publicRoot (e x).2 ↔
        a = comparisonRatio labels multiplicity publicRoot x.2 := by
      rw [← Subtype.val_inj, ← Subtype.val_inj, hr]
      have hb : b.val = t.val * a.val := by simp [t, mul_assoc]
      rw [hb, mul_left_cancel_iff]
    rw [heq]
    congr 1
    simp only [PMF.filter_apply, Set.indicator_apply, Set.mem_ofPred_eq, hx, hxe, if_true, hmass]
  · have hxe : observe trace (e x) ≠ transcript := fun h => hx ((hview x).symm.trans h)
    rw [PMF.filter_apply_eq_zero_of_notMem hseen hx, PMF.filter_apply_eq_zero_of_notMem hseen hxe]
    simp

#print axioms comparisonRatio_uniform

end Cogentic.RandomizedHiddenOutputLaw
