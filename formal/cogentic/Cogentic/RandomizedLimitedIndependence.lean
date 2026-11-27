import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

/-- The multiplicity of `i` in a tuple. -/
def tupleMultiplicity {J : Type*} [Fintype J] (f : J → I) (i : I) : ℕ :=
  (univ.filter (fun j ↦ f j = i)).card

private def singletonFreeTuples (I : Type*) [Fintype I] [DecidableEq I] (t : ℕ) :
    Finset (Fin (2*t) → I) :=
  univ.filter (fun f ↦ ∀ i, tupleMultiplicity f i ≠ 1)

omit [Fintype I] in
private theorem support_card_le_of_singletonFree (t : ℕ) (f : Fin (2*t) → I)
    (hf : ∀ i, tupleMultiplicity f i ≠ 1) : (univ.image f).card ≤ t := by
  have htwo (i : I) (hi : i ∈ univ.image f) : 2 ≤ tupleMultiplicity f i := by
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    have hp : 0 < tupleMultiplicity f (f j) := card_pos.mpr ⟨j, by simp⟩
    have hne := hf (f j)
    omega
  have hcount : (∑ i ∈ univ.image f, tupleMultiplicity f i) = 2*t := by
    unfold tupleMultiplicity
    rw [← card_eq_sum_card_image, card_univ, Fintype.card_fin]
  have hl : (∑ _i ∈ univ.image f, 2) = 2*(univ.image f).card := by
    simp [Nat.mul_comm]
  have hbound := sum_le_sum htwo
  rw [hl, hcount] at hbound
  omega

private theorem singletonFreeTuples_card_le [Nonempty I] (t : ℕ) :
    (singletonFreeTuples I t).card ≤ Fintype.card I ^ t * t^(2*t) := by
  classical
  let encode (pair : (Fin t → I) × (Fin (2*t) → Fin t)) : Fin (2*t) → I := pair.1 ∘ pair.2
  have hsubset : singletonFreeTuples I t ⊆ univ.image encode := by
    intro f hf
    have hfree : ∀ i, tupleMultiplicity f i ≠ 1 := (mem_filter.mp hf).2
    let S := univ.image f
    have hcard : Fintype.card ↥S ≤ Fintype.card (Fin t) := by
      simpa only [Fintype.card_coe, Fintype.card_fin] using support_card_le_of_singletonFree t f hfree
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
    let lift (j : Fin (2*t)) : ↥S := ⟨f j, mem_image_of_mem f (mem_univ j)⟩
    let labels := Function.extend e (Subtype.val : ↥S → I) (fun _ ↦ Classical.choice ‹Nonempty I›)
    refine mem_image.mpr ⟨⟨labels, fun j ↦ e (lift j)⟩, mem_univ _, ?_⟩
    funext j
    change labels (e (lift j)) = (lift j).val
    exact e.injective.extend_apply Subtype.val _ (lift j)
  have h := (card_le_card hsubset).trans (card_image_le (s := univ) (f := encode))
  simpa [Fintype.card_fun] using h

/-- Finite weighted expectation over the sample space. -/
def finiteExpectation (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, μ ω*f ω

/-- If every tuple with a singleton coordinate has zero mixed moment, the
centered even moment is controlled by the number of tuples with no singleton. -/
theorem even_moment_le_of_singletons [Nonempty I] (t : ℕ) (μ : Ω → ℝ)
    (X : Ω → I → ℝ) (M : ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (hnorm : ∑ ω, μ ω = 1)
    (hM : 0 ≤ M) (hbound : ∀ ω i, |X ω i| ≤ M)
    (hvanish : ∀ f : Fin (2*t) → I, (∃ i, tupleMultiplicity f i = 1) →
      finiteExpectation μ (fun ω ↦ ∏ j, X ω (f j)) = 0) :
    finiteExpectation μ (fun ω ↦ (∑ i, X ω i)^(2*t)) ≤
      (Fintype.card I : ℝ)^t * (t : ℝ)^(2*t) * M^(2*t) := by
  classical
  let term (f : Fin (2*t) → I) := finiteExpectation μ (fun ω ↦ ∏ j, X ω (f j))
  have hexpand : finiteExpectation μ (fun ω ↦ (∑ i, X ω i)^(2*t)) = ∑ f, term f := by
    unfold term finiteExpectation
    simp_rw [Fintype.sum_pow, mul_sum]
    rw [sum_comm]
  have hrestrict : (∑ f, term f) = ∑ f ∈ singletonFreeTuples I t, term f := by
    symm
    apply sum_subset (filter_subset _ _)
    intro f _ hf
    exact hvanish f (by simpa [singletonFreeTuples] using hf)
  have hterm (f : Fin (2*t) → I) : term f ≤ M^(2*t) := by
    unfold term finiteExpectation
    calc
      _ ≤ ∑ ω, μ ω * M^(2*t) := by
        apply sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hμ ω)
        calc
          _ ≤ |∏ j, X ω (f j)| := le_abs_self _
          _ = ∏ j, |X ω (f j)| := abs_prod _ _
          _ ≤ ∏ _j : Fin (2*t), M := prod_le_prod (fun _ _ ↦ abs_nonneg _) (fun j _ ↦ hbound ω (f j))
          _ = _ := by simp
      _ = _ := by rw [← sum_mul, hnorm, one_mul]
  have hcount : ((singletonFreeTuples I t).card : ℝ) ≤ (Fintype.card I : ℝ)^t*(t : ℝ)^(2*t) := by
    exact_mod_cast singletonFreeTuples_card_le (I := I) t
  rw [hexpand, hrestrict]
  calc
    _ ≤ ∑ _f ∈ singletonFreeTuples I t, M^(2*t) := sum_le_sum fun f _ ↦ hterm f
    _ = ((singletonFreeTuples I t).card : ℝ)*M^(2*t) := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (pow_nonneg hM _)

/-- The finite product-moment factorization supplied by `k`-wise independence.
Powers may vary by coordinate, and only the support size is restricted. -/
def FactorsMomentsUpTo (k : ℕ) (μ : Ω → ℝ) (X : Ω → I → ℝ) : Prop :=
  ∀ S : Finset I, S.card ≤ k → ∀ e : I → ℕ,
    finiteExpectation μ (fun ω ↦ ∏ i ∈ S, X ω i ^ e i) =
      ∏ i ∈ S, finiteExpectation μ (fun ω ↦ X ω i ^ e i)

omit [Fintype I] in
/-- A product containing exactly one occurrence of a centered coordinate
has expectation zero under the finite factorization hypothesis. -/
theorem singleton_moment_eq_zero (t : ℕ) (μ : Ω → ℝ) (X : Ω → I → ℝ)
    (hcenter : ∀ i, finiteExpectation μ (fun ω ↦ X ω i) = 0)
    (hind : FactorsMomentsUpTo (2*t) μ X) (f : Fin (2*t) → I)
    (hsingle : ∃ i, tupleMultiplicity f i = 1) :
    finiteExpectation μ (fun ω ↦ ∏ j, X ω (f j)) = 0 := by
  obtain ⟨i, hi⟩ := hsingle
  have hpos : 0 < tupleMultiplicity f i := by rw [hi]; decide
  obtain ⟨j, hj⟩ := card_pos.mp hpos
  have hmem : i ∈ univ.image f :=
    mem_image.mpr ⟨j, mem_univ _, (mem_filter.mp hj).2⟩
  have hsize : (univ.image f).card ≤ 2*t := by
    exact card_image_le.trans_eq (by simp)
  calc
    _ = finiteExpectation μ (fun ω ↦ ∏ i ∈ univ.image f, X ω i ^ tupleMultiplicity f i) := by
      congr 1
      funext ω
      exact prod_comp (X ω) f
    _ = ∏ i ∈ univ.image f, finiteExpectation μ (fun ω ↦ X ω i ^ tupleMultiplicity f i) :=
      hind _ hsize (tupleMultiplicity f)
    _ = 0 := prod_eq_zero hmem (by simpa only [hi, pow_one] using hcenter i)

/-- The `2*t` centered moment bound needs only factorization on sets of size
at most `2*t`. -/
theorem even_moment_le_of_limited_independence [Nonempty I] (t : ℕ) (μ : Ω → ℝ)
    (X : Ω → I → ℝ) (M : ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (hnorm : ∑ ω, μ ω = 1)
    (hM : 0 ≤ M) (hbound : ∀ ω i, |X ω i| ≤ M)
    (hcenter : ∀ i, finiteExpectation μ (fun ω ↦ X ω i) = 0)
    (hind : FactorsMomentsUpTo (2*t) μ X) :
    finiteExpectation μ (fun ω ↦ (∑ i, X ω i)^(2*t)) ≤
      (Fintype.card I : ℝ)^t * (t : ℝ)^(2*t) * M^(2*t) :=
  even_moment_le_of_singletons t μ X M hμ hnorm hM hbound
    (singleton_moment_eq_zero t μ X hcenter hind)

/-- Finite two-sided Markov inequality for an even moment. -/
theorem finite_even_moment_tail_le (t : ℕ) (μ : Ω → ℝ) (f : Ω → ℝ) (r : ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hr : 0 < r) :
    (∑ ω ∈ univ.filter (fun ω ↦ r ≤ |f ω|), μ ω) ≤
      finiteExpectation μ (fun ω ↦ (f ω)^(2*t)) / r^(2*t) := by
  apply (le_div_iff₀ (pow_pos hr _)).mpr
  rw [sum_mul]
  calc
    _ ≤ ∑ ω ∈ univ.filter (fun ω ↦ r ≤ |f ω|), μ ω*(f ω)^(2*t) := by
      apply sum_le_sum
      intro ω hω
      apply mul_le_mul_of_nonneg_left _ (hμ ω)
      rw [← pow_abs_two_mul (f ω)]
      exact pow_le_pow_left₀ hr.le (mem_filter.mp hω).2 _
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun ω _ _ ↦ by
      rw [← pow_abs_two_mul (f ω)]
      exact mul_nonneg (hμ ω) (pow_nonneg (abs_nonneg _) _))

/-- The two-sided tail under a normalized finite law and limited independence. -/
theorem tail_le_of_limited_independence [Nonempty I] (t : ℕ) (μ : Ω → ℝ)
    (X : Ω → I → ℝ) (M r : ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (hnorm : ∑ ω, μ ω = 1)
    (hM : 0 ≤ M) (hr : 0 < r) (hbound : ∀ ω i, |X ω i| ≤ M)
    (hcenter : ∀ i, finiteExpectation μ (fun ω ↦ X ω i) = 0)
    (hind : FactorsMomentsUpTo (2*t) μ X) :
    (∑ ω ∈ univ.filter (fun ω ↦ r ≤ |∑ i, X ω i|), μ ω) ≤
      ((Fintype.card I : ℝ)^t * (t : ℝ)^(2*t) * M^(2*t)) / r^(2*t) :=
  (finite_even_moment_tail_le t μ (fun ω ↦ ∑ i, X ω i) r hμ hr).trans
    (div_le_div_of_nonneg_right
      (even_moment_le_of_limited_independence t μ X M hμ hnorm hM hbound hcenter hind) (pow_nonneg hr.le _))

end Cogentic.Randomized
