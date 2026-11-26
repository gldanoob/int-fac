import Cogentic.ConstructorPriorDensity

namespace Cogentic.Construction
open Finset Real
open scoped Classical
noncomputable section

/-- Smooth marks before the executable rejects singular or shared roots. -/
def smoothMesh (n ell : ℕ) (x y : ℤ×ℤ) : Finset ℕ :=
  let O := PrescribedRows.unrestricted n ell
  (univ.biUnion (constructorCellMarks n ell)).filter
    (fun a=>smoothMarkEvent O false a x ∧ smoothMarkEvent O true a y)

def meshWeight (n ell a : ℕ) : ℝ :=
  let O := PrescribedRows.unrestricted n ell
  constructorMixturePrior n ell (meshMix n ell) a/smoothMarkProbability O O a

/-- On one retained draw, dividing every smooth mark by its common total
turns pooled, centered scores into actual entry errors on a probability
distribution. The denominator is at least one sixteenth of the raw grid size. -/
theorem normalized_mesh_score (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ x y : ℤ×ℤ, retainedDenominatorGood n ell (meshMix n ell) x y →
    let b := n.log2+1; let O := PrescribedRows.unrestricted n ell
    let X := constructorCellMarks n ell; let S := smoothMesh n ell x y
    let Q := ∑ a∈S,meshWeight n ell a
    let w := fun a=>meshWeight n ell a/Q
    let total := ∑ c,((X c).card:ℝ)
    let raw := (2*(Fixed.d b:ℝ)+1)*(cellMarkCount b:ℝ)
    1/2≤Q ∧ raw/16≤total*Q ∧ (∀ a,0≤w a) ∧ (∑ a∈S,w a)=1 ∧
      ∀ (f : ℕ→ℝ) (θ : ℝ),
        twoFieldScore (univ.biUnion X)
          (fun a=>pooledMarkWeight univ X (fun _ i=>f i-θ) a/smoothMarkProbability O O a)
          (smoothMarkEvent O false) (smoothMarkEvent O true) x y =
          total*Q*((∑ a∈S,w a*f a)-θ) := by
  classical
  obtain ⟨n₀,prior⟩ := pooled_mesh_prior line
  refine ⟨n₀,?_⟩
  intro n big ell target comp sieve x y good b O X S Q w total raw
  obtain ⟨low,_,mixPos,_,_⟩ := prior n big ell target comp sieve
  change raw/8≤total at low
  have rawPos : 0<raw := by dsimp [raw,cellMarkCount];positivity
  have totalPos : 0<total := (div_pos rawPos (by norm_num : (0:ℝ)<8)).trans_le low
  have wn (a : ℕ) : 0 ≤ meshWeight n ell a :=
    div_nonneg (constructor_mixture_prior_nonneg n ell (meshMix n ell) mixPos a)
      (mul_nonneg (O.probability_unit target false _).1 (O.probability_unit target true _).1)
  have sub : (univ.biUnion X).filter (fun a=>keptSmoothMark O O a x y)⊆S := by
    intro a ha
    obtain ⟨base,h⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨base,h.1,h.2.1⟩
  have lower := good.2.2.2
  rw [retained_denominator_eq_prior] at lower
  have qlow : 1/2≤Q := lower.trans (sum_le_sum_of_subset_of_nonneg sub (f:=meshWeight n ell) (fun a _ _=>wn a))
  have qp : 0<Q := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) qlow
  have fit := mul_le_mul low qlow (by norm_num : (0:ℝ)≤1/2) totalPos.le
  have norm : (∑ a∈S,w a)=1 := by dsimp only [w];rw [←sum_div,div_self qp.ne']
  refine ⟨qlow,by linarith only [fit],fun a=>div_nonneg (wn a) qp.le,norm,?_⟩
  intro f θ
  have pool (a : ℕ) : pooledMarkWeight univ X (fun _ i=>f i-θ) a =
      total*constructorMixturePrior n ell (meshMix n ell) a*(f a-θ) := by
    simp only [constructorMixturePrior,pooledMarkWeight,mul_sum,sum_mul]
    apply sum_congr rfl
    intro c _
    change (if a∈X c then f a-θ else 0) =
      total*(if a∈X c then ((X c).card:ℝ)/total/(X c).card else 0)*(f a-θ)
    by_cases hm : a∈X c
    · have pos : (0:ℝ)<(X c).card := Nat.cast_pos.mpr (card_pos.mpr ⟨a,hm⟩)
      simp only [if_pos hm]
      field_simp [totalPos.ne',pos.ne']
    · simp only [if_neg hm,mul_zero,zero_mul]
  have score : twoFieldScore (univ.biUnion X)
      (fun a=>pooledMarkWeight univ X (fun _ i=>f i-θ) a/smoothMarkProbability O O a)
      (smoothMarkEvent O false) (smoothMarkEvent O true) x y =
      ∑ a∈S,total*Q*(w a*(f a-θ)) := by
    dsimp only [twoFieldScore,S,smoothMesh]
    rw [sum_filter]
    apply sum_congr rfl
    intro a _
    split
    · rw [mul_one,pool]
      dsimp only [w,meshWeight]
      field_simp [qp.ne'] <;> ring
    · rw [mul_zero]
  rw [score,←mul_sum]
  simp only [mul_sub,sum_sub_distrib,←sum_mul,norm,one_mul]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.normalized_mesh_score
