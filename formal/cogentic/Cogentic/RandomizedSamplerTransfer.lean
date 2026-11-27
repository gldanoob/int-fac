import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Cogentic.RandomizedSamplerTransfer

variable {Ω T : Type*} [Fintype Ω]

/-- The probability of a transcript under independent coordinate laws. -/
noncomputable def trialMass {m : ℕ} (p : Fin m → Ω → ℝ) (x : Fin m → Ω) : ℝ :=
  ∏ i, p i (x i)

theorem sum_trialMass {m : ℕ} (p : Fin m → Ω → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1) : ∑ x, trialMass p x = 1 := by
  unfold trialMass
  rw [← Fintype.prod_sum]
  simp [hp]

/-- One half of the L1 gap of finite probability masses. -/
noncomputable def totalVariation (p q : Ω → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

private theorem abs_mul_sub_mul_le {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |a*b-c*d| ≤ |a-c| * b + c*|b-d| := by
  calc
    _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg hc]

/-- The L1 gap between independent transcript laws is at most the sum of
the coordinate L1 gaps. The coordinate distributions may differ by index. -/
theorem trialMass_l1_le {m : ℕ} (p q : Fin m → Ω → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hq : ∀ i a, 0 ≤ q i a)
    (hps : ∀ i, ∑ a, p i a = 1) (hqs : ∀ i, ∑ a, q i a = 1) :
    (∑ x, |trialMass p x - trialMass q x|) ≤ ∑ i, ∑ a, |p i a - q i a| := by
  classical
  induction m with
  | zero => simp [trialMass]
  | succ m ih =>
    let p' := fun i : Fin m => p i.succ
    let q' := fun i : Fin m => q i.succ
    let e := Fin.consEquiv (fun _ : Fin (m+1) => Ω)
    have hp' : ∑ x, trialMass p' x = 1 := sum_trialMass p' (fun i => hps i.succ)
    have haux := ih p' q' (fun i => hp i.succ) (fun i => hq i.succ)
      (fun i => hps i.succ) (fun i => hqs i.succ)
    have hcons (a : Ω) (x : Fin m → Ω) (r : Fin (m+1) → Ω → ℝ) :
        trialMass r (e (a,x)) = r 0 a * trialMass (fun i => r i.succ) x := by
      simp [trialMass, e, Fin.prod_univ_succ]
    have hsum :
        (∑ x, |trialMass p x - trialMass q x|) =
          ∑ y : Ω × (Fin m → Ω), |p 0 y.1 * trialMass p' y.2 - q 0 y.1 * trialMass q' y.2| := by
      symm
      apply Fintype.sum_equiv e
      rintro ⟨a,x⟩
      rw [hcons, hcons]
    rw [hsum, Fintype.sum_prod_type, Fin.sum_univ_succ]
    calc
      _ ≤ ∑ a, ∑ x, (|p 0 a-q 0 a| * trialMass p' x +
          q 0 a * |trialMass p' x-trialMass q' x|) := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro x _
        apply abs_mul_sub_mul_le _ (hq 0 a)
        exact Finset.prod_nonneg fun i _ => hp i.succ (x i)
      _ = (∑ a, |p 0 a-q 0 a|) + ∑ x, |trialMass p' x-trialMass q' x| := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp', mul_one, ← Finset.sum_mul,
          hqs, one_mul]
      _ ≤ _ := add_le_add le_rfl haux

theorem trialMass_totalVariation_le {m : ℕ} (p q : Fin m → Ω → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hq : ∀ i a, 0 ≤ q i a)
    (hps : ∀ i, ∑ a, p i a = 1) (hqs : ∀ i, ∑ a, q i a = 1) :
    totalVariation (trialMass p) (trialMass q) ≤ ∑ i, totalVariation (p i) (q i) := by
  unfold totalVariation
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (trialMass_l1_le p q hp hq hps hqs) (by norm_num)

/-- The difference in expected values of a test taking values in `[0,1]`
is at most the total variation. Equal mass suffices for this inequality. -/
theorem mean_difference_le_totalVariation {p q : Ω → ℝ}
    (h : ∑ a, p a = ∑ a, q a) (test : Ω → ℝ)
    (ht₀ : ∀ a, 0 ≤ test a) (ht₁ : ∀ a, test a ≤ 1) :
    |(∑ a, p a * test a) - ∑ a, q a * test a| ≤ totalVariation p q := by
  have hz : ∑ a, (p a - q a) = 0 := by rw [Finset.sum_sub_distrib, h, sub_self]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  have he : (∑ a, (p a-q a)*(2*test a-1)) = 2 * ∑ a, (p a-q a)*test a := by
    simp_rw [mul_sub, mul_one, ← mul_assoc, mul_comm (p _ - q _) (2 : ℝ), mul_assoc]
    rw [Finset.sum_sub_distrib, hz, sub_zero, Finset.mul_sum]
  have hle : |∑ a, (p a-q a)*(2*test a-1)| ≤ ∑ a, |p a-q a| := by
    refine (Finset.abs_sum_le_sum_abs ..).trans ?_
    apply Finset.sum_le_sum
    intro a _
    rw [abs_mul]
    have ht : |2*test a-1| ≤ 1 := abs_le.mpr ⟨by linarith [ht₀ a], by linarith [ht₁ a]⟩
    exact mul_le_of_le_one_right (abs_nonneg _) ht
  rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hle
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by linarith)

/-- An arbitrary deterministic transcript map and a bounded test of its
output change in expectation by at most the sum of the coordinate errors. -/
theorem mapped_transcript_transfer {m : ℕ} (p q : Fin m → Ω → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hq : ∀ i a, 0 ≤ q i a)
    (hps : ∀ i, ∑ a, p i a = 1) (hqs : ∀ i, ∑ a, q i a = 1)
    (observe : (Fin m → Ω) → T) (test : T → ℝ)
    (ht₀ : ∀ a, 0 ≤ test a) (ht₁ : ∀ a, test a ≤ 1) :
    |(∑ x, trialMass p x * test (observe x)) - ∑ x, trialMass q x * test (observe x)| ≤
      ∑ i, totalVariation (p i) (q i) := by
  have hmass := (sum_trialMass p hps).trans (sum_trialMass q hqs).symm
  exact (mean_difference_le_totalVariation hmass (test ∘ observe)
    (fun x => ht₀ (observe x)) (fun x => ht₁ (observe x))).trans
      (trialMass_totalVariation_le p q hp hq hps hqs)

/-- With at most `ε` total variation per coordinate, any event after
processing the transcript has probability change at most `m*ε`. -/
theorem mapped_transcript_indicator_transfer {m : ℕ} (p q : Fin m → Ω → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hq : ∀ i a, 0 ≤ q i a)
    (hps : ∀ i, ∑ a, p i a = 1) (hqs : ∀ i, ∑ a, q i a = 1)
    (ε : ℝ) (hε : ∀ i, totalVariation (p i) (q i) ≤ ε)
    (observe : (Fin m → Ω) → T) (succeeds : T → Prop) [DecidablePred succeeds] :
    |(∑ x, if succeeds (observe x) then trialMass p x else 0) -
        ∑ x, if succeeds (observe x) then trialMass q x else 0| ≤ (m : ℝ)*ε := by
  let f := fun a => if succeeds a then (1 : ℝ) else 0
  have h0 : ∀ a, 0 ≤ f a := by intro a; dsimp [f]; split <;> norm_num
  have h1 : ∀ a, f a ≤ 1 := by intro a; dsimp [f]; split <;> norm_num
  have h := mapped_transcript_transfer p q hp hq hps hqs observe f h0 h1
  simp only [f, mul_ite, mul_one, mul_zero] at h
  exact h.trans (by simpa using (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hε i))

end Cogentic.RandomizedSamplerTransfer
