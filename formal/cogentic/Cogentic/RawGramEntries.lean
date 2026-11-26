import Cogentic.Rank

namespace Cogentic.Construction
open Finset Real
noncomputable section

/-- On the target-miss branch, the intercept and logarithms have fixed
coordinates `h` at each mesh position. Ordinary rows have first and second
moments `m` and `R` at that position. -/
def missMomentEntry {H I : Type*} (h : H → ℝ) (m : I → ℝ) (R : I → I → ℝ) :
    Matrix (H ⊕ I) (H ⊕ I) ℝ :=
  fun i j => match i, j with
  | .inl a, .inl b => h a*h b
  | .inl a, .inr b => h a*m b
  | .inr a, .inl b => m a*h b
  | .inr a, .inr b => R a b

private theorem outer {A C : Type*} [Fintype A] [Fintype C] (a f : A → ℝ) (b l : C → ℝ) :
      (∑ i,∑ j,a i*(f i*l j)*b j)=(∑ i,f i*a i)*(∑ j,l j*b j) := by
  rw [sum_mul];apply sum_congr rfl;intro i _;rw [mul_sum];apply sum_congr rfl;intro j _;ring

/-- The quadratic form of the raw Gram separates into the squared conditional
mean and the ordinary-row variance, before averaging over mesh positions. -/
theorem miss_moment_quadratic {H I : Type*} [Fintype H] [Fintype I]
    (h : H → ℝ) (m : I → ℝ) (R : I → I → ℝ) (v : H ⊕ I → ℝ) :
    let g := ∑ i,h i*v (.inl i)
    let s := ∑ i,m i*v (.inr i)
    (∑ i,∑ j,v i*missMomentEntry h m R i j*v j) =
      (g+s)^2+((∑ i,∑ j,v (.inr i)*R i j*v (.inr j))-s^2) := by
  intro g s
  simp only [Fintype.sum_sum_type,sum_add_distrib,missMomentEntry]
  rw [outer (fun i=>v (.inl i)) h (fun i=>v (.inl i)) h,
    outer (fun i=>v (.inr i)) m (fun i=>v (.inl i)) h,
    outer (fun i=>v (.inl i)) h (fun i=>v (.inr i)) m]
  dsimp only [g,s]
  ring

end
end Cogentic.Construction

#print axioms Cogentic.Construction.miss_moment_quadratic
