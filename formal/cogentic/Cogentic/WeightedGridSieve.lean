import Cogentic.FixedGridSieve
import Mathlib.Algebra.BigOperators.Module

namespace Cogentic.Construction
open Finset Real

/-- Summation by parts charges the variation of a signed weight once
when every initial segment has the same discrepancy bound. -/
theorem weighted_prefix_discrepancy (M : ℕ) (f g : ℕ → ℝ) (E : ℝ)
    (initial : ∀ i ≤ M, |∑ j ∈ range i, g j| ≤ E) :
    |∑ i ∈ range M, f i*g i| ≤
    (|f (M-1)|+∑ i ∈ range (M-1), |f (i+1)-f i|)*E := by
  have parts := sum_range_by_parts (R:=ℝ) f g M
  simp only [smul_eq_mul] at parts
  rw [parts]
  have last : |f (M-1)*(∑ j ∈ range M, g j)| ≤ |f (M-1)| * E := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (initial _ le_rfl) (abs_nonneg _)
  have tail : |∑ i ∈ range (M-1), (f (i+1)-f i)*(∑ j ∈ range (i+1), g j)| ≤
      (∑ i ∈ range (M-1), |f (i+1)-f i|)*E := by
    rw [sum_mul]
    apply (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun i h => ?_))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (initial (i+1) (by have := mem_range.mp h; omega)) (abs_nonneg _)
  exact (abs_sub _ _).trans ((add_le_add last tail).trans_eq (by ring))

/-- The mesh weight can have either sign. Its discrepancy over the
actual eligible marks is uniform over all residue classes, subintervals
and tuples and is proportional to its endpoint size plus variation. -/
theorem weighted_constructed_marks (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ ell ∈ dyadicTargets (Fixed.beta (n.log2+1)),
    ¬n.Prime → presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = none →
    ∀ (lo M q r u₀ u₁ v₀ v₁ : ℕ) (f : ℕ → ℝ),
    let b := n.log2+1
    let k := markModulus n ell
    let P := k.primeFactors.filter (fun p => ¬p ∣ q)
    let ρ := ∏ p ∈ P, (1-(p:ℝ)⁻¹)
    let marks := (construct n ell u₀ u₁ v₀ v₁).marks
    0 < q → (∀ p ∈ k.primeFactors, p ∣ q → ¬r ≡ Fixed.rootBase n [MOD p]) →
    (∀ x ∈ Ico lo (lo+M), x ≡ r [MOD q] →
      1 ≤ x ∧ x ≤ Fixed.A b ∧ onGrid (Fixed.d b) (Fixed.A b) (Fixed.invWidth b) x) →
    |∑ i ∈ range M, f i*((if lo+i ≡ r [MOD q] ∧ lo+i ∈ marks then 1 else 0)-ρ/q)| ≤
      (|f (M-1)|+∑ i ∈ range (M-1), |f (i+1)-f i|) *
      (((Fixed.B b:ℝ)+2*((M:ℝ)/q)*exp 6)*exp (-K*(Fixed.z b:ℝ)^2)) := by
  classical
  obtain ⟨n₀,counts⟩ := constructed_interval_marks line K hK
  refine ⟨n₀,?_⟩
  intro n hn ell target comp absent lo M q r u₀ u₁ v₀ v₁ f b k P ρ marks qp eligible grid
  apply weighted_prefix_discrepancy
  intro i hi
  let X := (Ico lo (lo+i)).filter (fun x => x ≡ r [MOD q])
  have ok (x : ℕ) (mem : x ∈ X) := grid x
    (Finset.mem_Ico.mpr ⟨(mem_Ico.mp (mem_filter.mp mem).1).1,
      (mem_Ico.mp (mem_filter.mp mem).1).2.trans_le (Nat.add_le_add_left hi _)⟩)
    (mem_filter.mp mem).2
  have e := (counts n hn ell target comp absent lo (lo+i) q r u₀ u₁ v₀ v₁
    (Nat.le_add_right ..) qp eligible ok).2
  have eq : (∑ j ∈ range i, if lo+j ≡ r [MOD q] ∧ lo+j ∈ marks then (1:ℝ) else 0) =
      ((X.filter (fun x => x ∈ marks)).card:ℝ) := by
    have changeBase := sum_Ico_eq_sum_range (fun x => if x ≡ r [MOD q] ∧ x∈marks then (1:ℝ) else 0) lo (lo+i)
    simp only [Nat.add_sub_cancel_left] at changeBase
    rw [←changeBase,←sum_filter,sum_const,nsmul_eq_mul,mul_one]
    congr 2
    ext x
    simp [X,and_assoc]
  have subL := div_le_div_of_nonneg_right (show (i:ℝ) ≤ M by exact_mod_cast hi) (Nat.cast_nonneg (α:=ℝ) q)
  change |((X.filter (fun x => x ∈ marks)).card:ℝ)-(((lo+i:ℕ):ℝ)-lo)/q*ρ| ≤ _ at e
  simp only [Nat.cast_add,add_sub_cancel_left] at e
  rw [sum_sub_distrib,eq,sum_const,card_range,nsmul_eq_mul]
  rw [show (i:ℝ)*(ρ/q)=(i/q:ℝ)*ρ by ring]
  refine e.trans (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left subL (by norm_num : (0:ℝ)≤2)) (exp_pos 6).le)

end Cogentic.Construction
