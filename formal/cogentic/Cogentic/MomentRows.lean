import Cogentic.ModelRank

/-! Entrywise finite-saddle hypotheses for the centered Gram comparison. -/

open scoped Matrix BigOperators
namespace Cogentic

/-- Local diagonal, mean, rank-one and relative two-prime remainder bounds
imply the required finite-block inequalities on every perpendicular vector.
Only the empirical perturbation in the last two premises uses its full
coefficient energy. -/
theorem centered_bounds_of_local_entries {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
    (p g : α → ℝ) (v : ι → ℝ) (w : κ → ι → ℝ)
    (m vari : α → ι → ℝ) (c : α → κ → ι → ℝ) (multiple δ : α → κ → ℝ)
    (R : α → Matrix ι ι ℝ) (ρ : α → ℝ) (h : ι → ℝ) (u cells arch actual ε : ℝ)
    (hp : ∀ a, 0≤p a) (mass : ∑ a, p a=1) (perp : ∀ k, w k ⬝ᵥ v=0)
    (mean : ∑ a, p a*(∑ i, (m a i)^2) ≤ 12*u) (diag : ∀ a i, 15≤16*vari a i)
    (direction : ∀ a k, ∑ i, (c a k i-multiple a k*w k i)^2 ≤ δ a k)
    (oneRank : 16*(∑ a, p a*(∑ k, δ a k)) ≤ 1)
    (nonneg : ∀ a, 0≤ρ a) (relative : ∀ a i j, |R a i j| ≤ ρ a*h i*h j)
    (residual : 16*(∑ a, p a*ρ a)*(∑ i, (h i)^2) ≤ 1) :
    let F := ∑ i, (v i)^2
    let meanScore := fun a => m a ⬝ᵥ v
    let D := ∑ a, p a*(∑ i, vari a i * (v i)^2)
    let C := ∑ a, p a*(∑ k, (c a k ⬝ᵥ v)^2)
    let E := ∑ a, p a*(∑ i, ∑ j, v i*R a i j*v j)
    (∑ a, p a*(g a+meanScore a)^2)+D-C+E ≤ actual+ε →
    768*u*cells*ε ≤ F+arch →
    CenteredMomentBounds p g u cells F arch actual := by
  intro F meanScore D C E observed error
  have fpos : 0≤F := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  refine ⟨meanScore,D,C,-E,ε,?_,?_,?_,?_,by linarith,error⟩
  · have weighted := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => mul_le_mul_of_nonneg_left
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (m a) v) (hp a))
    change ∑ a, p a*(meanScore a)^2 ≤ _ at weighted
    have total : ∑ a, p a*((∑ i, (m a i)^2)*F)=(∑ a, p a*(∑ i, (m a i)^2))*F := by
      simp only [Finset.sum_mul,mul_assoc]
    change ∑ a, p a*(meanScore a)^2 ≤ ∑ a, p a*((∑ i, (m a i)^2)*F) at weighted
    rw [total] at weighted
    exact weighted.trans (mul_le_mul_of_nonneg_right mean fpos)
  · have point (a) : 15*F≤16*∑ i, vari a i*(v i)^2 := by
      dsimp only [F]
      simp only [Finset.mul_sum,←mul_assoc]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (diag a i) (sq_nonneg _))
    have avg := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => mul_le_mul_of_nonneg_left (point a) (hp a))
    calc
      15*F = ∑ a, p a*(15*F) := by rw [←Finset.sum_mul,mass,one_mul]
      _ ≤ _ := avg
      _ = 16*D := by simp only [D,Finset.mul_sum,mul_left_comm]
  · have pt (a) : ∑ k, (c a k ⬝ᵥ v)^2 ≤ (∑ k, δ a k)*F := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun k _ => perpendicular_covariance v (c a k) (w k) (multiple a k) (δ a k)
        (perp k) (direction a k))
    have avg := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => mul_le_mul_of_nonneg_left (pt a) (hp a))
    have sum : ∑ a, p a*((∑ k, δ a k)*F) = (∑ a, p a*(∑ k, δ a k))*F := by simp only [Finset.sum_mul,mul_assoc]
    change C ≤ ∑ a, p a*((∑ k, δ a k)*F) at avg
    rw [sum] at avg
    nlinarith [mul_le_mul_of_nonneg_right oneRank fpos]
  · have pt (a) : -(∑ i, ∑ j, v i*R a i j*v j) ≤ ρ a*(∑ i, (h i)^2)*F :=
      (neg_le_abs _).trans (covariance_remainder (R a) v h (ρ a) (nonneg a) (relative a))
    have avg := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => mul_le_mul_of_nonneg_left (pt a) (hp a))
    have total : ∑ a, p a*(ρ a*(∑ i, (h i)^2)*F)=(∑ a, p a*ρ a)*(∑ i, (h i)^2)*F := by
      simp only [Finset.sum_mul,mul_assoc]
    simp only [mul_neg,Finset.sum_neg_distrib,←show E=(∑ a, p a*(∑ i, ∑ j, v i*R a i j*v j)) by rfl,total] at avg
    nlinarith [mul_le_mul_of_nonneg_right residual fpos]

/-- The summed squared entry errors, including off-diagonal entries, control
all coefficient vectors simultaneously without a factor for the row count. -/
theorem gram_frobenius_error {ι : Type*} [Fintype ι] (E : Matrix ι ι ℝ) (v : ι → ℝ)
    (δ : ℝ) (dp : 0≤δ) (budget : ∑ i, ∑ j, (E i j)^2 ≤ δ^2) :
    |∑ i, ∑ j, v i*E i j*v j| ≤ δ*(∑ i, (v i)^2) := by
  let mass := ∑ i, (v i)^2
  have mp : 0 ≤ mass := Finset.sum_nonneg fun i _ => sq_nonneg _
  let e := fun ij : ι × ι => E ij.1 ij.2
  let t := fun ij : ι × ι => v ij.1*v ij.2
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ e t
  have ee : ∑ ij, (e ij)^2 ≤ δ^2 := by simpa only [e,Fintype.sum_prod_type] using budget
  have tt : ∑ ij, (t ij)^2=mass^2 := by
    rw [Fintype.sum_prod_type]
    change (∑ i, ∑ j, (v i*v j)^2)=(∑ i, (v i)^2)^2
    simp only [mul_pow,←Finset.mul_sum,←Finset.sum_mul]
    ring
  have linear : ∑ ij, e ij*t ij = ∑ i, ∑ j, v i*E i j*v j := by
    simp only [Fintype.sum_prod_type,e,t,mul_left_comm,mul_assoc]
  rw [linear,tt] at cs
  apply le_of_sq_le_sq _ (mul_nonneg dp mp)
  rw [sq_abs,mul_pow]
  exact cs.trans (mul_le_mul_of_nonneg_right ee (sq_nonneg _))

/-- A squared log replacement error can be absorbed directly into the
empirical scores, without an upper bound on the original mark scores. -/
theorem positive_true_scores_of_nominal {ι : Type*} [Fintype ι] (p old new : ι → ℝ)
    (budget energy : ℝ) (positive : 0<energy) (bp : 0<budget) (np : ∀i, 0≤p i)
    (nominal : energy ≤ budget*(∑ i, p i*(old i)^2))
    (error : 4*budget*(∑ i, p i*(old i-new i)^2) ≤ energy) :
    energy ≤ 4*budget*(∑ i, p i*(new i)^2) ∧ 0<∑ i, p i*(new i)^2 := by
  have each (i) : (old i)^2 ≤ 2*(new i)^2+2*(old i-new i)^2 := by nlinarith [sq_nonneg (old i-2*new i)]
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left (each i) (np i))
  have rhs : (∑ i, p i*(2*(new i)^2+2*(old i-new i)^2)) =
      2*(∑ i, p i*(new i)^2)+2*(∑ i, p i*(old i-new i)^2) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_left_comm]
  rw [rhs] at total
  have lower : energy ≤ 4*budget*(∑ i, p i*(new i)^2) := by
    nlinarith [mul_le_mul_of_nonneg_left total bp.le]
  exact ⟨lower,pos_of_mul_pos_right (positive.trans_le lower) (by positivity)⟩

end Cogentic

#print axioms Cogentic.centered_bounds_of_local_entries
