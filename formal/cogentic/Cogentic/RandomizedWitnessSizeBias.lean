import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open Finset
open scoped BigOperators

namespace Cogentic.RandomizedWitnessSizeBias

variable {Anchor Witness Mark : Type*} [DecidableEq Anchor]

def witnessFiber (witnesses : Finset Witness) (anchor : Witness → Anchor) (a : Anchor) :
    Finset Witness :=
  witnesses.filter (fun h => anchor h = a)

/-- Summing a weighted witness test by anchor leaves the anchor weight
outside the sum over each fiber. -/
theorem sum_weighted_witness_test {R : Type*} [Semiring R]
    (anchors : Finset Anchor) (witnesses : Finset Witness) (anchor : Witness → Anchor)
    (hmaps : ∀ h ∈ witnesses, anchor h ∈ anchors)
    (weight : Anchor → R) (test : Anchor → Witness → R) :
    (∑ h ∈ witnesses, weight (anchor h) * test (anchor h) h) =
      ∑ a ∈ anchors, weight a * ∑ h ∈ witnessFiber witnesses anchor a, test a h := by
  rw [← sum_fiberwise_of_maps_to hmaps (fun h => weight (anchor h) * test (anchor h) h)]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro h hh
  rw [(mem_filter.mp hh).2]

/-- An anchor-only test receives a factor equal to its witness count. -/
theorem sum_anchor_size_bias {R : Type*} [Semiring R]
    (anchors : Finset Anchor) (witnesses : Finset Witness) (anchor : Witness → Anchor)
    (hmaps : ∀ h ∈ witnesses, anchor h ∈ anchors)
    (weight test : Anchor → R) :
    (∑ h ∈ witnesses, weight (anchor h) * test (anchor h)) =
      ∑ a ∈ anchors, weight a * ((witnessFiber witnesses anchor a).card : R) * test a := by
  simpa only [sum_const, nsmul_eq_mul, mul_assoc] using
    sum_weighted_witness_test anchors witnesses anchor hmaps weight (fun a _ => test a)

/-- The total weight of the witness law is the size-biased anchor mass. -/
theorem sum_witness_mass {R : Type*} [Semiring R]
    (anchors : Finset Anchor) (witnesses : Finset Witness) (anchor : Witness → Anchor)
    (hmaps : ∀ h ∈ witnesses, anchor h ∈ anchors) (weight : Anchor → R) :
    (∑ h ∈ witnesses, weight (anchor h)) =
      ∑ a ∈ anchors, weight a * ((witnessFiber witnesses anchor a).card : R) := by
  simpa only [mul_one] using
    sum_anchor_size_bias anchors witnesses anchor hmaps weight (fun _ => (1 : R))

theorem weighted_mean_anchor_size_bias
    (anchors : Finset Anchor) (witnesses : Finset Witness) (anchor : Witness → Anchor)
    (hmaps : ∀ h ∈ witnesses, anchor h ∈ anchors)
    (weight test : Anchor → ℝ) :
    (∑ h ∈ witnesses, weight (anchor h) * test (anchor h)) /
        (∑ h ∈ witnesses, weight (anchor h)) =
      (∑ a ∈ anchors, weight a * ((witnessFiber witnesses anchor a).card : ℝ) * test a) /
        (∑ a ∈ anchors, weight a * ((witnessFiber witnesses anchor a).card : ℝ)) := by
  rw [sum_anchor_size_bias anchors witnesses anchor hmaps,
    sum_witness_mass anchors witnesses anchor hmaps]

/-- A second mark may be chosen from any anchor-local finite set, and the
test may depend jointly on the witness and that mark. -/
theorem sum_weighted_mixed_mark_test {R : Type*} [Semiring R]
    (anchors : Finset Anchor) (witnesses : Finset Witness) (anchor : Witness → Anchor)
    (hmaps : ∀ h ∈ witnesses, anchor h ∈ anchors)
    (weight : Anchor → R) (marks : Anchor → Finset Mark)
    (test : Anchor → Witness → Mark → R) :
    (∑ h ∈ witnesses, weight (anchor h) * ∑ m ∈ marks (anchor h), test (anchor h) h m) =
      ∑ a ∈ anchors, weight a * ∑ h ∈ witnessFiber witnesses anchor a,
        ∑ m ∈ marks a, test a h m :=
  sum_weighted_witness_test anchors witnesses anchor hmaps weight
    (fun a h => ∑ m ∈ marks a, test a h m)

#print axioms sum_weighted_witness_test
#print axioms sum_anchor_size_bias
#print axioms weighted_mean_anchor_size_bias
#print axioms sum_weighted_mixed_mark_test

end Cogentic.RandomizedWitnessSizeBias
