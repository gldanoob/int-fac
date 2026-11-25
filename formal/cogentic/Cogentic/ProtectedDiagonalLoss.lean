import Cogentic.ConstructorPriorDensity

namespace Cogentic.Construction
open Finset Real
noncomputable section
open scoped Classical

/-- Expected sum of all normalized stage-one diagonal losses on the protected
target rows. The target is fixed, so this estimate uses no row-admission
probability: its residue-class density pays for the full squared row scale. -/
theorem protected_diagonal_rejection (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ mix : Option (Bool×Fin (Fixed.d b))→ℝ, (∀ c,0 ≤ mix c) → (∑ c,mix c)=1 →
    ∀ α : ℝ, α≤1 →
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    let X := univ.biUnion (constructorCellMarks n ell)
    let rows := (wanted (Fixed.d b) ell (Fixed.rootBase n)).toFinset
    let wt := fun a=>(ell:ℝ)^α*constructorMixturePrior n ell mix a/smoothMarkProbability O O a
    let lost := fun (k : Ω) (r : ℕ)=>∑ a∈X with a%ell=r, if rejectedSmoothMark O O a k.1.val k.2.val then wt a else 0
    ∃ μ : ℝ, HasSum (fun k : Ω=>twoFieldWeight O O k*(∑ r∈rows,lost k r)) μ ∧
      μ≤16*(Fixed.d b:ℝ)*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨n₁,density⟩ := constructor_mixture_target_prior_density line
  obtain ⟨b₁,lossLaw⟩ := rejected_score_loss line K hK
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 3
  refine ⟨max n₁ (max 2 (2^(max b₁ b₂))),?_⟩
  intro n big ell target comp absent b mix nonn norm α ha O Ω X rows wt lost
  obtain ⟨old,more⟩ := max_le_iff.mp big
  obtain ⟨hn,lim⟩ := max_le_iff.mp more
  obtain ⟨bl,bd⟩ := max_le_iff.mp (((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _))
  let prior := constructorMixturePrior n ell mix
  let e := exp (-K*(Fixed.z b:ℝ)^2)
  have ep : 0≤e := (exp_pos _).le
  have ellPos : (0:ℝ)<ell := by exact_mod_cast (mem_dyadicTargets.mp target).1.pos
  have tilt : (ell:ℝ)^α≤ell := (rpow_le_rpow_of_exponent_le (by exact_mod_cast (mem_dyadicTargets.mp target).1.one_le : (1:ℝ)≤ell) ha).trans_eq (rpow_one _)
  have pp (a) : 0≤(ell:ℝ)^α*prior a :=
    mul_nonneg (rpow_nonneg ellPos.le _) (constructor_mixture_prior_nonneg n ell mix nonn a)
  have sep (a) : (O.prefactor a false).Coprime (O.prefactor a true) :=
    (O.prefactors_coprime_iff O (degree b bd) target a).mpr (by simp [O,PrescribedRows.unrestricted,PrescribedRows.hit])
  have one (r : ℕ) : ∃ c : ℝ, HasSum (fun k : Ω=>twoFieldWeight O O k*lost k r) c ∧ c≤16*e := by
    let Y := X.filter (fun a=>a%ell=r)
    have marks (a) (hy : a∈Y) : a∈(construct n ell 0 0 0 0).marks := by
      obtain ⟨_,_,hm⟩ := mem_biUnion.mp (mem_filter.mp hy).1
      exact (mem_filter.mp hm).2
    obtain ⟨μ,law,upper⟩ := lossLaw O O bl hn comp target absent Y (fun a=>(ell:ℝ)^α*prior a) marks (fun a _=>sep a)
    simp only [abs_of_nonneg (pp _)] at upper law
    refine ⟨μ,law,upper.trans ?_⟩
    have count : (∑ a∈Y,prior a)≤16/(ell:ℝ) := density n old ell target comp absent mix nonn norm r
    rw [←mul_sum]
    have lim := mul_le_mul tilt count (sum_nonneg (fun a _=>constructor_mixture_prior_nonneg n ell mix nonn a)) ellPos.le
    have eq : (ell:ℝ)*(16/(ell:ℝ))=16 := by field_simp
    exact (mul_le_mul_of_nonneg_left (lim.trans_eq eq) ep).trans_eq (mul_comm ..)
  choose c laws bounds using one
  have agg := hasSum_sum (s:=rows) (fun r _=>laws r)
  refine ⟨∑ r∈rows,c r,?_,?_⟩
  · simpa only [mul_sum] using agg
  · have size : rows.card≤Fixed.d b := (List.toFinset_card_le _).trans_eq (wanted_spec (target_gt_degree target) (Fixed.rootBase n)).1
    have sum := sum_le_sum (s:=rows) (fun r _=>bounds r)
    rw [sum_const,nsmul_eq_mul] at sum
    exact sum.trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast size : (rows.card:ℝ)≤(Fixed.d b:ℝ)) (by positivity : 0≤16*e)).trans_eq (by ring))

end
end Cogentic.Construction

#print axioms Cogentic.Construction.protected_diagonal_rejection
