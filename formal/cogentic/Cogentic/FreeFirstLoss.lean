import Cogentic.CleanObservationMass
import Cogentic.FreePrimeCongruence

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical

/-- The first quotient can admit a second value divisible by a fixed free
prime on at most this proportion of the true first smooth mass. -/
theorem PrescribedRows.free_bad_first_loss (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a y : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → y∈(construct n ell 0 0 0 0).marks →
    ∀ (side : Bool) (p : ℕ), p∈R.miss a \ R.hit y →
    let z := fun k : ℤ×ℤ => R.intercept a side k.1 k.2
    let smooth := fun k => supportedValue (sieveBand n ell (R.prefactor a side)) (z k)
    prescribedProbability R side (fun k => smooth k ∧ R.badFirstQuotient a y side p (z k)) ≤
      (36*(Fixed.B b:ℝ)^(-199/400:ℝ))*prescribedProbability R side smooth := by
  classical
  obtain ⟨b₀,filter⟩ := PrescribedRows.free_prime_exception_filter line
  refine ⟨b₀,?_⟩
  intro n ell a y R b large hn comp target absent am ym side p free z smooth
  obtain ⟨F,detect,bound⟩ := filter R large hn comp target absent am ym side p free
  let A := fun k : ℤ×ℤ => smooth k ∧ R.badFirstQuotient a y side p (z k)
  let B := fun k : ℤ×ℤ => smooth k ∧ F (z k)
  have sub (k : ℤ×ℤ) (h : A k) : B k := by
    obtain ⟨u,v,ok,eq,dvd⟩ := h.2
    exact ⟨h.1,eq ▸ detect u v ok dvd⟩
  have main := R.point_event side target A
  have cover := @PrescribedRows.point_event n ell R side target B (Classical.decPred B)
  apply (show prescribedProbability R side A ≤ @prescribedProbability n ell R side B (Classical.decPred B) by
    rw [←main.tsum_eq,←cover.tsum_eq]
    apply main.summable.tsum_le_tsum _ cover.summable
    intro k
    by_cases h : A k.val
    · rw [if_pos h,if_pos (sub k.val h)]
    · rw [if_neg h]; split <;> first | rfl | exact R.pointMass_nonneg side k).trans
  apply bound.trans
  have vp : 0<Fixed.v b := Nat.mul_pos (Fixed.degree_pos (Nat.succ_pos _))
    (Nat.mul_pos (Fixed.degree_pos (Nat.succ_pos _)) (Nat.succ_pos _))
  have up : 270≤(Fixed.U b:ℝ) := by
    exact_mod_cast (by decide : 270≤2^10).trans (Nat.pow_le_pow_right (by decide : 0<2) (by omega))
  have norm : 1+270*exp (-(Fixed.U b:ℝ))≤2 := by
    rw [exp_neg,←div_eq_mul_inv,←le_sub_iff_add_le',div_le_iff₀ (exp_pos _)]
    linarith only [up,add_one_le_exp (Fixed.U b:ℝ)]
  have nn : 0≤prescribedProbability R side smooth := by
    apply div_nonneg
    · apply tsum_nonneg; intro k; split <;> first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | rfl
    · exact tsum_nonneg (fun _ => mul_nonneg (exp_pos _).le (exp_pos _).le)
  apply mul_le_mul_of_nonneg_right _ nn
  calc _ ≤ 2*(18*(Fixed.B b:ℝ)^(-199/400:ℝ)) := mul_le_mul_of_nonneg_right norm (by positivity)
       _ = _ := by ring

end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.free_bad_first_loss
