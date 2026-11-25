import Cogentic.RetainedDenominatorPeeling
import Cogentic.TargetClassSupply

namespace Cogentic.Construction
open Finset Real
open scoped Classical
noncomputable section

/-- Every residue at the target prime has physical prior mass at most
sixteen times its uniform mass, for any fixed convex mixture of cells. -/
theorem constructor_mixture_target_prior_density (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ mix : Option (Bool×Fin (Fixed.d (n.log2+1)))→ℝ, (∀ c, 0 ≤ mix c) → (∑ c,mix c)=1 →
    ∀ r : ℕ, (∑ a∈(univ.biUnion (constructorCellMarks n ell)).filter (fun a=>a%ell=r),constructorMixturePrior n ell mix a)≤16/(ell:ℝ) := by
  classical
  obtain ⟨n₀,marks⟩ := grid_cells_have_marks line
  refine ⟨n₀,?_⟩
  intro n old ell target comp absent mix pos norm r
  let b := n.log2+1; let M : ℝ := cellMarkCount b
  let X := constructorCellMarks n ell
  have ep : (0:ℝ)<ell := Nat.cast_pos.mpr (mem_dyadicTargets.mp target).1.pos
  have mp : 0<M := by dsimp [M,cellMarkCount];positivity
  have bound (c) : ((X c).filter (fun a=>a%ell=r)).card/((X c).card:ℝ)≤16/(ell:ℝ) := by
    have c4 : 1≤(Fixed.B b)^4 := Nat.succ_le_of_lt (pow_pos (Nat.pow_pos (by decide)) _)
    have den := marks n old ell target comp absent 1 0 0 0 0 0 c (by decide) c4
      (fun p hp dvd=>((Nat.prime_of_mem_primeFactors hp).ne_one (Nat.eq_one_of_dvd_one dvd)).elim)
    simp only [Nat.modEq_one,filter_true,Nat.cast_one,div_one] at den
    change M/8≤((X c).card:ℝ) at den
    have num := target_class_card target c r
    have sub : (X c).filter (fun a=>a%ell=r) ⊆ (X c).filter (fun a=>a ≡ r [MOD ell]) := by
      intro a ha
      obtain ⟨ax,ar⟩ := mem_filter.mp ha
      exact mem_filter.mpr ⟨ax,ar ▸ (Nat.mod_modEq a ell).symm⟩
    have total := (Nat.cast_le.mpr (card_le_card sub) : (↑(_):ℝ)≤_).trans num
    change _ ≤ 2*M/(ell:ℝ) at total
    have dp : (0:ℝ)<(X c).card := (by positivity : 0<M/8).trans_le den
    rw [div_le_div_iff₀ dp ep]
    exact ((le_div_iff₀ ep).mp total).trans (by linarith only [den])
  let indicator (a : ℕ) : ℝ := if a%ell=r then 1 else 0
  have sums := constructor_mixture_prior_sum n ell mix indicator
  simp only [indicator,mul_ite,mul_one,mul_zero,←sum_filter,sum_const,nsmul_one] at sums
  rw [sums]
  have all := sum_le_sum (s:=univ) (fun c _=>mul_le_mul_of_nonneg_left (bound c) (pos c))
  rwa [←sum_mul,norm,one_mul] at all

end
end Cogentic.Construction

#print axioms Cogentic.Construction.constructor_mixture_target_prior_density
