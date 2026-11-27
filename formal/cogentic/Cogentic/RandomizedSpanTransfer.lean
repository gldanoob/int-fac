import Cogentic.RandomizedProbeCount
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

variable {I Ω Ξ : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Fintype Ξ]

private noncomputable def eventIndicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

/-- The probability of a predicate under the uniform law on a finite type. -/
noncomputable def uniformEventProbability {Ω : Type*} [Fintype Ω] (p : Ω → Prop) : ℝ :=
  (∑ x, eventIndicator (p x)) / Fintype.card Ω

/-- The uniform event probability is the fraction of samples satisfying the predicate. -/
theorem uniformEventProbability_eq_card_filter {Ω : Type*} [Fintype Ω] (p : Ω → Prop) :
    uniformEventProbability p =
      ((by classical exact (univ.filter p).card : ℕ) : ℝ) / Fintype.card Ω := by
  unfold uniformEventProbability eventIndicator
  rw [@sum_boole Ω ℝ _ p (Classical.decPred p) univ]

private theorem sum_binary_probe_indicator (w : I → ZMod 2) :
    (∑ u : I → ZMod 2, eventIndicator (w ⬝ᵥ u = 1)) =
      (Fintype.card (I → ZMod 2) : ℝ) / 2 * eventIndicator (w ≠ 0) := by
  classical
  unfold eventIndicator
  by_cases hw : w = 0
  · simp [hw]
  · obtain ⟨i, _⟩ := Function.ne_iff.mp hw
    let _ : Nonempty I := ⟨i⟩
    have hpos : 0 < Fintype.card I := Fintype.card_pos
    have hfiber := RandomizedProbeCount.card_probe_fiber_of_nonzero w hw 1
    rw [ZMod.card] at hfiber
    rw [@sum_boole (I → ZMod 2) ℝ _ (fun u ↦ w ⬝ᵥ u = 1) (Classical.decPred _) univ,
      ← Fintype.card_subtype, hfiber, if_pos hw, mul_one]
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    have hfull : 2 ^ (Fintype.card I - 1) * 2 = Fintype.card (I → ZMod 2) := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, Fintype.card_fun, ZMod.card]
    exact_mod_cast hfull

/-- Summing over the binary probes detects each nonzero vector on exactly
half the probes and detects the zero vector on none. -/
theorem sum_uniform_binary_probe_probability (row : Ω → I → ZMod 2) :
    (∑ u : I → ZMod 2, uniformEventProbability (fun x ↦ row x ⬝ᵥ u = 1)) =
      (Fintype.card (I → ZMod 2) : ℝ) / 2 *
        uniformEventProbability (fun x ↦ row x ≠ 0) := by
  classical
  unfold uniformEventProbability
  rw [← sum_div, sum_comm]
  simp_rw [sum_binary_probe_indicator, ← mul_sum]
  rw [mul_div_assoc]

/-- A one-sided bound on every parity event transfers the nonzero event
with twice the additive slack. -/
theorem parity_probe_transfer (anchored : Ω → I → ZMod 2) (publicRow : Ξ → I → ZMod 2)
    (L ε : ℝ)
    (h : ∀ u : I → ZMod 2, uniformEventProbability (fun x ↦ anchored x ⬝ᵥ u = 1) ≤
      L * uniformEventProbability (fun y ↦ publicRow y ⬝ᵥ u = 1) + ε) :
    uniformEventProbability (fun x ↦ anchored x ≠ 0) ≤
      L * uniformEventProbability (fun y ↦ publicRow y ≠ 0) + 2*ε := by
  have hsum := sum_le_sum (s := univ) (fun u _ ↦ h u)
  rw [sum_uniform_binary_probe_probability, sum_add_distrib, ← mul_sum,
    sum_uniform_binary_probe_probability, sum_const, card_univ, nsmul_eq_mul] at hsum
  have hpositive : 0 < (Fintype.card (I → ZMod 2) : ℝ) / 2 := by positivity
  apply le_of_mul_le_mul_left (a := (Fintype.card (I → ZMod 2) : ℝ) / 2) _ hpositive
  nlinarith only [hsum]

/-- Applying the probe hypothesis after an injective choice of quotient
coordinates transfers the probability of falling outside the subspace. -/
theorem parity_probe_span_transfer {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (S : Submodule (ZMod 2) V) (coord : (V ⧸ S) →ₗ[ZMod 2] (I → ZMod 2))
    (hinj : Function.Injective coord) (anchored : Ω → V) (publicRow : Ξ → V) (L ε : ℝ)
    (h : ∀ u : I → ZMod 2,
      uniformEventProbability (fun x ↦ coord (S.mkQ (anchored x)) ⬝ᵥ u = 1) ≤
        L * uniformEventProbability (fun y ↦ coord (S.mkQ (publicRow y)) ⬝ᵥ u = 1) + ε) :
    uniformEventProbability (fun x ↦ anchored x ∉ S) ≤
      L * uniformEventProbability (fun y ↦ publicRow y ∉ S) + 2*ε := by
  have hmem (w : V) : coord (S.mkQ w) ≠ 0 ↔ w ∉ S := by
    rw [ne_eq, coord.map_eq_zero_iff hinj, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  simpa only [hmem] using parity_probe_transfer (fun x ↦ coord (S.mkQ (anchored x)))
    (fun y ↦ coord (S.mkQ (publicRow y))) L ε h

end Cogentic.Randomized
