import Cogentic.RandomizedLimitedIndependence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

/-- The sum of products over ordered tuples of distinct coordinates. -/
noncomputable def orderedDistinctProductSum (t : ℕ) (X : I → ℝ) : ℝ :=
  ∑ e : Fin t ↪ I, ∏ j, X (e j)

private theorem orderedDistinctProductSum_succ (t : ℕ) (X : I → ℝ) :
    orderedDistinctProductSum (t+1) X =
      ∑ e : Fin t ↪ I, (∑ i : {i // i ∉ Set.range e}, X i.val) * (∏ j, X (e j)) := by
  unfold orderedDistinctProductSum
  rw [← (Equiv.embeddingFinSucc t I).symm.sum_comp]
  simp only [Equiv.coe_embeddingFinSucc_symm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, sum_mul]
  exact Fintype.sum_sigma' (fun (e : Fin t ↪ I) (i : {i // i ∉ Set.range e}) ↦
    X i.val * ∏ j, X (e j))

/-- Each ordered `t`-tuple can be extended by every coordinate outside its
range. The excluded weight is at most `t*d`. -/
theorem orderedDistinctProductSum_step (t : ℕ) (X : I → ℝ) (d : ℝ)
    (h₀ : ∀ i, 0 ≤ X i) (hd : ∀ i, X i ≤ d) :
    ((∑ i, X i)-(t : ℝ)*d)*orderedDistinctProductSum t X ≤
      orderedDistinctProductSum (t+1) X := by
  rw [orderedDistinctProductSum_succ, orderedDistinctProductSum, mul_sum]
  apply sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun j _ ↦ h₀ (e j)))
  have hpart := Fintype.sum_subtype_add_sum_subtype (fun i : I ↦ i ∈ Set.range e) X
  have hused : (∑ i : Set.range e, X i.val) ≤ (t : ℝ)*d := by
    rw [← (Equiv.ofInjective e e.injective).sum_comp]
    simp only [Equiv.ofInjective_apply]
    calc
      _ ≤ ∑ _j : Fin t, d := sum_le_sum fun j _ ↦ hd (e j)
      _ = _ := by simp [nsmul_eq_mul]
  linarith only [hpart, hused]

/-- A bounded nonnegative array with enough total weight has a large
ordered distinct-product sum. -/
theorem pow_sub_le_orderedDistinctProductSum (t : ℕ) (X : I → ℝ) (d : ℝ)
    (h₀ : ∀ i, 0 ≤ X i) (hd : ∀ i, X i ≤ d) (hd₀ : 0 ≤ d)
    (hmass : (t : ℝ)*d ≤ ∑ i, X i) :
    ((∑ i, X i)-(t : ℝ)*d)^t ≤ orderedDistinctProductSum t X := by
  induction t with
  | zero => simp [orderedDistinctProductSum]
  | succ t ih =>
    have ht : (t : ℝ)*d ≤ ((t+1 : ℕ) : ℝ)*d := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ t) hd₀
    let l := (∑ i, X i)-((t+1 : ℕ) : ℝ)*d
    let u := (∑ i, X i)-(t : ℝ)*d
    have hl : 0 ≤ l := sub_nonneg.mpr hmass
    have hlu : l ≤ u := sub_le_sub_left ht _
    have hu : 0 ≤ u := hl.trans hlu
    have hpower := pow_le_pow_left₀ hl hlu t
    change l^(t+1) ≤ orderedDistinctProductSum (t+1) X
    calc
      l^(t+1) = l*l^t := by rw [pow_succ']
      _ ≤ u*u^t := mul_le_mul hlu hpower (pow_nonneg hl _) hu
      _ ≤ u*orderedDistinctProductSum t X := mul_le_mul_of_nonneg_left (ih (ht.trans hmass)) hu
      _ ≤ _ := orderedDistinctProductSum_step t X d h₀ hd

private theorem orderedDistinctProductSum_le_pow (t : ℕ) (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) :
    orderedDistinctProductSum t p ≤ (∑ i, p i)^t := by
  classical
  let embed (e : Fin t ↪ I) : Fin t → I := e
  rw [Fintype.sum_pow]
  calc
    _ = ∑ f ∈ univ.image embed, ∏ j, p (f j) :=
      (sum_image Function.Embedding.coe_injective.injOn).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun f _ _ ↦
      prod_nonneg (fun j _ ↦ hp (f j)))

/-- The expectation of the ordered distinct-product sum is bounded by a
power of the aggregate coordinate bounds. Only distinct mixed products are needed. -/
theorem expected_distinctProductSum_le (t : ℕ) (μ : Ω → ℝ) (X : Ω → I → ℝ) (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hprod : ∀ e : Fin t ↪ I, finiteExpectation μ (fun ω ↦ ∏ j, X ω (e j)) ≤
      ∏ j, p (e j)) :
    finiteExpectation μ (fun ω ↦ orderedDistinctProductSum t (X ω)) ≤ (∑ i, p i)^t := by
  unfold finiteExpectation orderedDistinctProductSum
  simp_rw [mul_sum]
  rw [sum_comm]
  exact (sum_le_sum (fun e _ ↦ hprod e)).trans (orderedDistinctProductSum_le_pow t p hp)

/-- The finite upper tail from bounded coordinate weights and distinct
mixed-product bounds. The threshold must exceed the worst `t` omitted weights. -/
theorem tail_le_of_distinct_product_bound (t : ℕ) (μ : Ω → ℝ) (X : Ω → I → ℝ)
    (p : I → ℝ) (d a : ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (hp : ∀ i, 0 ≤ p i)
    (h₀ : ∀ ω i, 0 ≤ X ω i) (hd : ∀ ω i, X ω i ≤ d) (hd₀ : 0 ≤ d)
    (ha : (t : ℝ)*d < a)
    (hprod : ∀ e : Fin t ↪ I, finiteExpectation μ (fun ω ↦ ∏ j, X ω (e j)) ≤
      ∏ j, p (e j)) :
    (∑ ω ∈ univ.filter (fun ω ↦ a ≤ ∑ i, X ω i), μ ω) ≤
      ((∑ i, p i)/(a-(t : ℝ)*d))^t := by
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos (sub_pos.mpr ha) _)).mpr
  rw [sum_mul]
  calc
    _ ≤ ∑ ω ∈ univ.filter (fun ω ↦ a ≤ ∑ i, X ω i), μ ω*orderedDistinctProductSum t (X ω) := by
      apply sum_le_sum
      intro ω hω
      have htotal := (mem_filter.mp hω).2
      apply mul_le_mul_of_nonneg_left _ (hμ ω)
      exact (pow_le_pow_left₀ (sub_nonneg.mpr ha.le) (sub_le_sub_right htotal _) _).trans
        (pow_sub_le_orderedDistinctProductSum t (X ω) d (h₀ ω) (hd ω) hd₀ (ha.le.trans htotal))
    _ ≤ finiteExpectation μ (fun ω ↦ orderedDistinctProductSum t (X ω)) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro ω _ _
      exact mul_nonneg (hμ ω) (sum_nonneg (fun e _ ↦ prod_nonneg (fun j _ ↦ h₀ ω (e j))))
    _ ≤ _ := expected_distinctProductSum_le t μ X p hp hprod

omit [Fintype I] in
/-- Limited independence factorizes the product at any ordered tuple of
distinct coordinates. -/
theorem distinct_product_factorization (t : ℕ) (μ : Ω → ℝ) (X : Ω → I → ℝ)
    (hind : FactorsMomentsUpTo t μ X) (e : Fin t ↪ I) :
    finiteExpectation μ (fun ω ↦ ∏ j, X ω (e j)) =
      ∏ j, finiteExpectation μ (fun ω ↦ X ω (e j)) := by
  have hcard : (univ.image e).card ≤ t := card_image_le.trans_eq (by simp)
  have h := hind (univ.image e) hcard (fun _ ↦ 1)
  simpa only [pow_one, prod_image e.injective.injOn] using h

/-- A coordinatewise marginal upper bound under limited independence is
sufficient for the distinct-product tail inequality. -/
theorem tail_le_of_distinct_limited_independence (t : ℕ) (μ : Ω → ℝ) (X : Ω → I → ℝ)
    (p : I → ℝ) (d a : ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (hp : ∀ i, 0 ≤ p i)
    (h₀ : ∀ ω i, 0 ≤ X ω i) (hd : ∀ ω i, X ω i ≤ d) (hd₀ : 0 ≤ d)
    (ha : (t : ℝ)*d < a) (hmean : ∀ i, finiteExpectation μ (fun ω ↦ X ω i) ≤ p i)
    (hind : FactorsMomentsUpTo t μ X) :
    (∑ ω ∈ univ.filter (fun ω ↦ a ≤ ∑ i, X ω i), μ ω) ≤
      ((∑ i, p i)/(a-(t : ℝ)*d))^t := by
  apply tail_le_of_distinct_product_bound t μ X p d a hμ hp h₀ hd hd₀ ha
  intro e
  rw [distinct_product_factorization t μ X hind e]
  apply prod_le_prod _ (fun j _ ↦ hmean (e j))
  exact fun j _ ↦ sum_nonneg (fun ω _ ↦ mul_nonneg (hμ ω) (h₀ ω (e j)))

/-- The same tail bound at a multiple `T` of an aggregate marginal cap `m`. -/
theorem multiple_tail_le_of_distinct_product_bound (t : ℕ) (μ : Ω → ℝ) (X : Ω → I → ℝ)
    (p : I → ℝ) (d m T : ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (hp : ∀ i, 0 ≤ p i)
    (h₀ : ∀ ω i, 0 ≤ X ω i) (hd : ∀ ω i, X ω i ≤ d) (hd₀ : 0 ≤ d)
    (ha : (t : ℝ)*d < T*m) (hmean : ∑ i, p i ≤ m)
    (hprod : ∀ e : Fin t ↪ I, finiteExpectation μ (fun ω ↦ ∏ j, X ω (e j)) ≤
      ∏ j, p (e j)) :
    (∑ ω ∈ univ.filter (fun ω ↦ T*m ≤ ∑ i, X ω i), μ ω) ≤
      (m/(T*m-(t : ℝ)*d))^t := by
  apply (tail_le_of_distinct_product_bound t μ X p d (T*m) hμ hp h₀ hd hd₀ ha hprod).trans
  have hden := (sub_pos.mpr ha).le
  exact pow_le_pow_left₀ (div_nonneg (sum_nonneg (fun i _ ↦ hp i)) hden)
    (div_le_div_of_nonneg_right hmean hden) _

end Cogentic.Randomized
