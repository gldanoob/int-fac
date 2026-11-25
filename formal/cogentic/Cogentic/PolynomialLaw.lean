import Cogentic.PolynomialLattice

namespace Cogentic.Construction
open Real Cogentic.Window

noncomputable section

/-- The discrete Gaussian weight on the two integer coefficient coordinates
    of either polynomial in the construction. -/
def coefficientWeight (n : ℕ) (k : ℤ×ℤ) : ℝ :=
  let b := n.log2+1
  let U : ℝ := Fixed.U b
  let A : ℝ := Fixed.A b
  coeffGaussian k.1 ((b:ℝ)^2*U*A) (U*A)*coeffGaussian k.2 ((b:ℝ)^2*U) U

def projectedConditionalCenter (n a : ℕ) (x : ℤ) : ℝ :=
  let b := n.log2+1
  let U : ℝ := Fixed.U b
  (b:ℝ)^2*U+(a:ℝ)*U^2/(projectionScale n a)^2*((x:ℝ)-lineCenter n a)

def conditionalScale (n a : ℕ) : ℝ :=
  let b := n.log2+1
  (Fixed.U b:ℝ)*Fixed.A b*Fixed.U b/projectionScale n a

theorem proj_sq (n a : ℕ) :
    let b := n.log2+1; let U : ℝ := Fixed.U b; let A : ℝ := Fixed.A b
    (projectionScale n a)^2=(U*A)^2+(a:ℝ)^2*U^2 := by
  dsimp only [projectionScale]
  rw [Real.sq_sqrt (by positivity)]
  ring

theorem coefficient_weight_projection (n a : ℕ) (x y : ℤ) :
    coefficientWeight n (x-a*y,y) = coeffGaussian x (lineCenter n a) (projectionScale n a)*
      coeffGaussian y (projectedConditionalCenter n a x) (conditionalScale n a) := by
  let b := n.log2+1; let U : ℝ := Fixed.U b; let A : ℝ := Fixed.A b
  have up : 0<U := by dsimp [U,Fixed.U]; positivity
  have ap : 0<A := by dsimp [A,Fixed.A]; positivity
  have center : (lineCenter n a:ℝ)=(b:ℝ)^2*U*A+a*((b:ℝ)^2*U) := by simp [lineCenter,b,U,A]
  have scale : projectionScale n a=Real.sqrt ((U*A)^2+(a:ℝ)^2*U^2) := by simp [projectionScale,U,A,b,mul_pow]
  have h := conditional_gaussian_weight (↑(x-a*y:ℤ)) y ((b:ℝ)^2*U*A) ((b:ℝ)^2*U) a (U*A) U (mul_pos up ap) up
  dsimp only at h
  simp only [coefficientWeight,projectedConditionalCenter,conditionalScale,center,scale,Real.sq_sqrt (show 0 ≤ (U*A)^2+(a:ℝ)^2*U^2 by positivity),
    Int.cast_sub,Int.cast_mul,Int.cast_natCast,sub_add_cancel] at h ⊢
  exact h

theorem conditional_schedule {n a : ℕ} (cap : a≤Fixed.A (n.log2+1)) {H M : ℕ}
    (hp : 0<H) (mp : 0<M) (hc : H≤(Fixed.B (n.log2+1))^2) (mc : M≤(Fixed.B (n.log2+1))^2) :
    let b := n.log2+1
    let τ := projectionScale n a/H; let υ := conditionalScale n a/M
    2≤τ ∧ 2≤υ ∧ 6*max (3*exp (-π*τ^2)) (3*exp (-π*υ^2)) ≤ 18*exp (-(Fixed.U b:ℝ)) := by
  let b := n.log2+1; let x := dyadicUnit b; let B := Fixed.B b; let U := Fixed.U b; let A := Fixed.A b
  have ⟨xl,_,_,beq,_,ueq,_⟩ := dyadic_data (b := b) (Nat.succ_pos _)
  have ap : 0 < A := Nat.pow_pos (by decide)
  have bp : 0 < B := Nat.pow_pos (by decide)
  have xp : 0 < x := Nat.pow_pos (by decide)
  have dp := Fixed.degree_pos (b := b) (Nat.succ_pos _)
  have ub : 4*B^4 ≤ U := by
    have four : 4 ≤ x^2 := (Nat.pow_le_pow_left xl 2 : 2^2≤x^2)
    dsimp only [B,U]
    rw [beq,ueq,←pow_mul]
    exact (Nat.mul_le_mul_right _ four).trans ((pow_add x 2 (1000*4)) ▸ Nat.pow_le_pow_right xp (by omega))
  have geo := two_point_schedule_widths a A U B H M (by exact_mod_cast ap)
    (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast cap) (by exact_mod_cast bp)
    (by exact_mod_cast ub) (by exact_mod_cast hp) (by exact_mod_cast mp) (by exact_mod_cast hc) (by exact_mod_cast mc)
  simpa only [projectionScale,conditionalScale,mul_pow,A,U,B,b] using geo

/-- Conditional on the actual prescribed roots, the entire admissible
    coefficient lattice has a positive finite Gaussian normalizer. The
    same CRT parametrization computes every event from the two scalar
    Gaussian factors, with relative normalization error at most 18 exp(-U). -/
theorem PrescribedRows.coefficient_law {n ell a : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool) (cap : a≤Fixed.A (n.log2+1)) :
    let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
    let H := R.hitProduct a; let M := prodPrimes (R.miss a)
    let τ := projectionScale n a/H; let υ := conditionalScale n a/M
    let Z := ∑' k : C, coefficientWeight n k.val
    ∃ (c : ℤ) (t : ℤ→ℤ) (e : (ℤ×ℤ) ≃ C),
      let x := fun i : ℤ => c+(H:ℤ)*i
      let y := fun i j : ℤ => t i+(M:ℤ)*j
      let W := fun k : ℤ×ℤ => coeffGaussian (x k.1) (lineCenter n a) (projectionScale n a)*
        coeffGaussian (y k.1 k.2) (projectedConditionalCenter n a (x k.1)) (conditionalScale n a)
      (∀ i j, (e (i,j)).val = (x i-a*y i j,y i j)) ∧ Summable W ∧ 0<Z ∧
        |τ*υ/Z-1| ≤ 18*exp (-(Fixed.U (n.log2+1):ℝ)) ∧
        ∀ (E : ℤ×ℤ→Prop) [DecidablePred E],
          (∑' k : C, if E k.val then coefficientWeight n k.val else 0)/Z =
            (∑' k : ℤ×ℤ, if E (x k.1-a*y k.1 k.2,y k.1 k.2) then W k else 0)/Z := by
  classical
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  let H := R.hitProduct a; let M := prodPrimes (R.miss a)
  have ⟨c,t,e,law⟩ := R.polynomial_lattice target side a
  let x := fun i : ℤ => c+(H:ℤ)*i
  let y := fun i j : ℤ => t i+(M:ℤ)*j
  let W := fun k : ℤ×ℤ => coeffGaussian (x k.1) (lineCenter n a) (projectionScale n a)*
    coeffGaussian (y k.1 k.2) (projectedConditionalCenter n a (x k.1)) (conditionalScale n a)
  have coords (k : ℤ×ℤ) : (e k).val=(x k.1-a*y k.1 k.2,y k.1 k.2) := law k.1 k.2
  have weight (k : ℤ×ℤ) : coefficientWeight n (e k).val = W k := by rw [coords]; exact coefficient_weight_projection ..
  have hbounds := R.subprod_bounds (Finset.filter_subset (fun q => (R.residue q:ZMod q)=a) R.primes)
  have mbounds := R.subprod_bounds (s := R.miss a) Finset.sdiff_subset
  have ⟨hs,ht,err⟩ := conditional_schedule cap (H := H) (M := M) hbounds.1 mbounds.1 hbounds.2 mbounds.2
  have normal := gaussian_joint_normalizer c H (projectionScale n a) M (conditionalScale n a) (lineCenter n a)
    (fun i => (t i:ℝ)) (fun i => projectedConditionalCenter n a (x i))
    (by exact_mod_cast hbounds.1) (by exact_mod_cast mbounds.1) hs ht
  have bound : Summable W ∧ 0 < ∑' k, W k ∧
      |((projectionScale n a/H)*(conditionalScale n a/M))/(∑' k, W k)-1| ≤ 18*exp (-(Fixed.U (n.log2+1):ℝ)) := by
    have ⟨s,p,h⟩ := normal
    refine ⟨?_,?_,?_⟩
    · simpa only [W,x,y,Int.cast_add,Int.cast_mul,Int.cast_natCast] using s
    · simpa only [W,x,y,Int.cast_add,Int.cast_mul,Int.cast_natCast] using p
    · exact (by simpa only [W,x,y,Int.cast_add,Int.cast_mul,Int.cast_natCast] using h : _ ≤ _).trans err
  have den : (∑' k : C, coefficientWeight n k.val) = ∑' k, W k := by
    rw [←e.tsum_eq (fun k : C => coefficientWeight n k.val)]; exact tsum_congr weight
  dsimp only
  refine ⟨c,t,e,law,bound.1,den ▸ bound.2.1,den ▸ bound.2.2,?_⟩
  intro E inst
  congr 1
  rw [←e.tsum_eq (fun k : C => if E k.val then coefficientWeight n k.val else 0)]
  apply tsum_congr
  intro k
  change (if E (e k).val then coefficientWeight n (e k).val else 0) = if E (x k.1-a*y k.1 k.2,y k.1 k.2) then W k else 0
  rw [weight,coords]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.coefficient_law
