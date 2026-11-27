import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Hom.Basic

open Finset
open scoped BigOperators

namespace Cogentic.RandomizedRationalChildRouting

variable {I Lane G : Type*} [DecidableEq Lane] [CommGroup G]

/-- Route repeated occurrences of a common group element by summing their
signed multiplicities in each fiber. -/
theorem prod_routed_zpow (children : Finset I) (lanes : Finset Lane) (lane : I → Lane)
    (hroute : ∀ i ∈ children, lane i ∈ lanes) (value : Lane → G) (multiplicity : I → ℤ) :
    (∏ i ∈ children, value (lane i) ^ multiplicity i) =
      ∏ j ∈ lanes, value j ^ (∑ i ∈ children.filter (fun i => lane i = j), multiplicity i) := by
  have collapse (s : Finset I) (x : G) :
      (∏ i ∈ s, x ^ multiplicity i) = x ^ (∑ i ∈ s, multiplicity i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => simp only [prod_insert hi, sum_insert hi, zpow_add, ih]
  rw [← prod_fiberwise_of_maps_to hroute (fun i => value (lane i) ^ multiplicity i)]
  apply prod_congr rfl
  intro j _
  rw [← collapse]
  apply prod_congr rfl
  intro i hi
  rw [(mem_filter.mp hi).2]

variable {F : Lane → Type*} [∀ j, CommGroup (F j)]

/-- The evaluations of all child components agree with the evaluation of
one product per lane. Each listed signed multiplicity stays in its fiber. -/
theorem prod_routed_evaluations (children : Finset I) (lanes : Finset Lane) (lane : I → Lane)
    (hroute : ∀ i ∈ children, lane i ∈ lanes) (evaluate : ∀ j, F j →* G)
    (component : ∀ j, I → F j) (multiplicity : I → ℤ) :
    (∏ i ∈ children, evaluate (lane i) (component (lane i) i ^ multiplicity i)) =
      ∏ j ∈ lanes, evaluate j (∏ i ∈ children.filter (fun i => lane i = j),
        component j i ^ multiplicity i) := by
  rw [← prod_fiberwise_of_maps_to hroute
    (fun i => evaluate (lane i) (component (lane i) i ^ multiplicity i))]
  apply prod_congr rfl
  intro j _
  rw [map_prod]
  apply prod_congr rfl
  intro i hi
  rw [(mem_filter.mp hi).2]

/-- Substitute the checked child equalities and collect their factors into
one rational correction and a product for each lane. -/
theorem discharge_signed_children (children : Finset I) (lanes : Finset Lane) (lane : I → Lane)
    (hroute : ∀ i ∈ children, lane i ∈ lanes) (evaluate : ∀ j, F j →* G)
    (component : ∀ j, I → F j) (multiplicity : I → ℤ) (child correction : I → G)
    {P base : G} (hP : P = base * ∏ i ∈ children, child i ^ multiplicity i)
    (hchild : ∀ i ∈ children, child i = correction i * evaluate (lane i) (component (lane i) i)) :
    P = (base * ∏ i ∈ children, correction i ^ multiplicity i) *
      ∏ j ∈ lanes, evaluate j (∏ i ∈ children.filter (fun i => lane i = j),
        component j i ^ multiplicity i) := by
  calc
    P = base * ∏ i ∈ children, child i ^ multiplicity i := hP
    _ = base * ∏ i ∈ children, correction i ^ multiplicity i *
          evaluate (lane i) (component (lane i) i ^ multiplicity i) := by
      congr 1
      apply prod_congr rfl
      intro i hi
      rw [hchild i hi, mul_zpow, map_zpow]
    _ = _ := by
      rw [prod_mul_distrib, ← mul_assoc, prod_routed_evaluations children lanes lane hroute]

#print axioms prod_routed_zpow
#print axioms prod_routed_evaluations
#print axioms discharge_signed_children

end Cogentic.RandomizedRationalChildRouting
