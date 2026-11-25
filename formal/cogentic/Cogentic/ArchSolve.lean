import Cogentic.Pivot
import Cogentic.Reconstruction

/-! Exact rational unit coordinates and certified perturbation of the archimedean solve. -/

open scoped BigOperators Matrix
open Matrix
namespace Cogentic

private theorem int_fraction_den_dvd (a b : ℤ) : ((a : ℚ)/b).den ∣ b.natAbs := by
  rw [← Rat.divInt_eq_div]
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd a b)

/-- The rational unit coordinates in the true archimedean solve simultaneously
cancel the actual integral lattice coordinates. Their least denominator divides
the selected integral unit-class determinant. -/
theorem exact_archimedean_coordinates {ι L : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup L] [Module ℤ L] (base : Module.Basis ι ℤ L)
    (v : ι → L) (t : L) (obs : L →ₗ[ℤ] (ι → ℝ)) (nz : (base.toMatrix v).det ≠ 0) :
    ∃ x : ι → ℚ,
      (∀ j, (base.repr t j : ℚ) + ∑ i, (base.repr (v i) j : ℚ)*x i = 0) ∧
      (∀ j, obs t j + ∑ i, obs (v i) j * (x i : ℝ) = 0) ∧
      (Finset.univ.lcm (fun i => (x i).den) ∣ (base.toMatrix v).det.natAbs) := by
  classical
  let d := (base.toMatrix v).det
  obtain ⟨c,hc⟩ := adjugate_lattice_relation base v t
  let x (i) : ℚ := (c i : ℚ) / (d : ℚ)
  refine ⟨x, ?_, ?_, Finset.lcm_dvd (fun i _ => int_fraction_den_dvd _ _)⟩
  · intro j
    have e := congrFun (congrArg base.equivFun hc) j
    have ints : d * (base.repr t j) + ∑ i, (base.repr (v i) j) * c i = 0 := by
      simpa [d, Module.Basis.equivFun_apply, mul_comm] using e
    have rat : (d : ℚ) * (base.repr t j : ℚ) + ∑ i, (base.repr (v i) j : ℚ) * (c i : ℚ) = 0 := by
      exact_mod_cast ints
    have dn : (d : ℚ) ≠ 0 := by exact_mod_cast nz
    apply (mul_left_inj' dn).mp
    simpa only [add_mul, Finset.sum_mul, x, mul_assoc, div_mul_cancel₀ _ dn, zero_mul,
      mul_comm (base.repr t j : ℚ) (d : ℚ)] using rat
  · intro j
    have e := congrFun (congrArg obs hc) j
    have real : (d : ℝ) * obs t j + ∑ i, obs (v i) j * (c i : ℝ) = 0 := by
      simpa only [d, map_add, map_zsmul, map_sum, map_zero, Pi.add_apply, Pi.smul_apply,
        Finset.sum_apply, Pi.zero_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, mul_comm] using e
    have dn : (d : ℝ) ≠ 0 := by exact_mod_cast nz
    apply (mul_left_inj' dn).mp
    simpa only [add_mul, Finset.sum_mul, x, Rat.cast_div, Rat.cast_intCast, mul_assoc,
      div_mul_cancel₀ _ dn, zero_mul, mul_comm (obs t j) (d : ℝ)] using real

/-- An approximate rational linear solve, with its inverse and entry errors
certified, controls every coordinate of the exact real solve. -/
theorem arch_solve_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B C R : Matrix ι ι ℝ) (t s x y : ι → ℝ) (ε X M : ℝ) (he : 0 ≤ ε)
    (hX : 0 ≤ X)
    (exact : B *ᵥ x = t) (approx : C *ᵥ y = s) (inverse : R*C = 1)
    (entries : ∀ i j, |C i j-B i j| ≤ ε) (rhs : ∀ i, |s i-t i| ≤ ε)
    (size : ∀ j, |x j| ≤ X) (invsize : ∀ i, ∑ j, |R i j| ≤ M) :
    ∀ i, |y i-x i| ≤ M * (ε + Fintype.card ι * (ε*X)) := by
  let E := ε + Fintype.card ι * (ε*X)
  have err (i) : |((C-B) *ᵥ x) i| ≤ Fintype.card ι * (ε*X) := by
    calc
      _ ≤ ∑ j, |(C i j-B i j)*x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ι, ε*X := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (entries i j) (size j) (abs_nonneg _) he
      _ = _ := by simp
  have res (i) : |(C *ᵥ (y-x)) i| ≤ E := by
    have eq : C *ᵥ (y-x) = (s-t) - (C-B) *ᵥ x := by
      rw [Matrix.mulVec_sub, approx, Matrix.sub_mulVec, exact]
      abel
    rw [eq]
    exact (abs_sub _ _).trans (add_le_add (rhs i) (err i))
  intro i
  have e : y-x = R *ᵥ (C *ᵥ (y-x)) := by rw [Matrix.mulVec_mulVec, inverse, Matrix.one_mulVec]
  change |(y-x) i| ≤ M * E
  rw [e]
  calc
    _ ≤ ∑ j, |R i j * (C *ᵥ (y-x)) j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |R i j| * E := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]; gcongr; exact res j
    _ = (∑ j, |R i j|) * E := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (invsize i) (by dsimp [E]; positivity)


/-- The reconstruction check can use the magnitude of the computed
solution. If the inverse times the matrix error is at most one half,
no prior size estimate for the unknown exact coordinates is needed. -/
theorem arch_solve_a_posteriori {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B C R : Matrix ι ι ℝ) (t s x y : ι → ℝ) (ε Y M : ℝ) (he : 0 ≤ ε)
    (hY : 0 ≤ Y)
    (exact : B *ᵥ x = t) (approx : C *ᵥ y = s) (inverse : R*C = 1)
    (entries : ∀ i j, |C i j-B i j| ≤ ε) (rhs : ∀ i, |s i-t i| ≤ ε)
    (size : ∀ j, |y j| ≤ Y) (invsize : ∀ i, ∑ j, |R i j| ≤ M)
    (small : M * Fintype.card ι * ε ≤ 1/2) :
    ∀ i, |y i-x i| ≤ 2*M*(ε + Fintype.card ι*(ε*Y)) := by
  classical
  intro i
  obtain ⟨k,_,maximal⟩ := Finset.exists_max_image Finset.univ (fun j => |y j-x j|)
    ⟨i,Finset.mem_univ i⟩
  let δ := |y k-x k|
  have δpos : 0 ≤ δ := abs_nonneg _
  have maxj (j) : |y j-x j| ≤ δ := maximal j (Finset.mem_univ j)
  have xb (j) : |x j| ≤ Y+δ := by
    calc
      |x j| = |y j - (y j - x j)| := by congr 1; abel
      _ ≤ |y j|+|y j-x j| := abs_sub _ _
      _ ≤ _ := add_le_add (size _) (maxj _)
  have h := arch_solve_error B C R t s x y ε (Y+δ) M he (add_nonneg hY δpos)
    exact approx inverse entries rhs xb invsize k
  change δ ≤ _ at h
  have squeeze := mul_le_mul_of_nonneg_right small δpos
  exact (maxj i).trans (by nlinarith only [h,squeeze])

/-- The numerical acceptance inequalities supply the exact rational coordinates,
all the per-coordinate approximation hypotheses of the continued-fraction
extractor, and a single bound on the lcm of its returned denominators. -/
theorem certified_archimedean_reconstruction {ι L : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup L] [Module ℤ L] (base : Module.Basis ι ℤ L) (v : ι → L) (t : L)
    (obs : L →ₗ[ℤ] (ι → ℝ)) (nz : (base.toMatrix v).det ≠ 0)
    (Q : ℕ) (denCap : (base.toMatrix v).det.natAbs ≤ Q) (C R : Matrix ι ι ℝ)
    (s : ι → ℝ) (y : ι → ℚ) (ε Y M : ℝ) (he : 0 ≤ ε) (hY : 0 ≤ Y)
    (approx : C *ᵥ (fun j => (y j : ℝ)) = s) (inverse : R*C = 1)
    (entries : ∀ i j, |C i j-obs (v j) i| ≤ ε) (rhs : ∀ i, |s i+obs t i| ≤ ε)
    (size : ∀ j, |(y j : ℝ)| ≤ Y) (invsize : ∀ i, ∑ j, |R i j| ≤ M)
    (contract : M * Fintype.card ι * ε ≤ 1/2)
    (precision : 2*M*(ε + Fintype.card ι*(ε*Y)) < 1/(2*(Q:ℝ)^2)) :
    ∃ x : ι → ℚ,
      (∀ j, (base.repr t j : ℚ) + ∑ i, (base.repr (v i) j : ℚ)*x i = 0) ∧
      (∀ i, (x i).den ≤ Q) ∧ (∀ i, |y i-x i| < 1/(2*(Q:ℚ)^2)) ∧
      Reconstruction.multiplier y Q = some (Finset.univ.lcm (fun i => (x i).den)) ∧
      Finset.univ.lcm (fun i => (x i).den) ≤ Q := by
  obtain ⟨x,lattice,real,den⟩ := exact_archimedean_coordinates base v t obs nz
  have lcmBound := (Nat.le_of_dvd (Int.natAbs_pos.mpr nz) den).trans denCap
  have pos : 0 < Finset.univ.lcm (fun i => (x i).den) := by
    apply Nat.pos_of_ne_zero; simp [Finset.lcm_eq_zero_iff]
  have widths (i) : (x i).den ≤ Q :=
    (Nat.le_of_dvd pos (Finset.dvd_lcm (Finset.mem_univ i))).trans lcmBound
  let B : Matrix ι ι ℝ := fun i j => obs (v j) i
  have solves : B *ᵥ (fun j => (x j : ℝ)) = -obs t := by
    funext i
    exact eq_neg_of_add_eq_zero_right (real i)
  have bound := arch_solve_a_posteriori B C R (-obs t) s _ _ ε Y M he hY
    solves approx inverse entries (by simpa only [Pi.neg_apply, sub_neg_eq_add] using rhs)
    size invsize contract
  have near (i) : |y i-x i| < 1/(2*(Q:ℚ)^2) := by
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact (bound i).trans_lt precision
  exact ⟨x,lattice,widths,near,Reconstruction.multiplier_exact y x Q widths near,lcmBound⟩

end Cogentic
