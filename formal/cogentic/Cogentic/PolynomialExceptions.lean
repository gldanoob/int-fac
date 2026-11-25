import Cogentic.PolynomialProbability
import Cogentic.ExceptionalClasses

namespace Cogentic.Construction
open Real Cogentic.Window

/-- Every auxiliary prime up to the full mark diameter fits in the
    original first-polynomial conductor envelope, including primes
    outside the smooth factor base. -/
theorem first_extra_conductor {n ell a p : ℕ} (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (pa : p≤Fixed.A (n.log2+1)) (am : a<Fixed.rootBase n) (side : Bool) :
    (firstStep n ell a side).natAbs*p ≤ conductorCap n := by
  let b := n.log2+1; let P := primorial (Fixed.d b); let m := Fixed.rootBase n
  let A := Fixed.A b; let B := Fixed.B b
  have ep := (mem_dyadicTargets.mp target).1.pos
  have eb : ell≤B := (mem_dyadicTargets.mp target).2.2
  have bp : 0<B := Nat.pow_pos (by decide)
  rw [(firstStep_size am ep side).1]
  have t : (if hitsTarget n ell a side then 1 else ell) ≤ B := by split <;> omega
  calc firstModulus n ell a (hitsTarget n ell a side)*p ≤ P*B*m*A :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left P t) (Nat.sub_le m a)) pa
       _=P*m*A*B := by ring
       _≤conductorCap n := Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) B)

/-- Uniform conditional costs of either exceptional residue of the first
    signed evaluation. The saddle and both divided windows are obtained
    from the actual compatible polynomial lattice. -/
theorem first_polynomial_exceptional (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell), b₀≤n.log2+1 → 2≤n → ¬n.Prime →
    ell∈dyadicTargets (Fixed.beta (n.log2+1)) →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none →
    a∈(construct n ell 0 0 0 0).marks → ∀ (side : Bool) (u v : ℤ), R.compatible side u v →
    let b := n.log2+1; let pre := R.prefactor a side; let q := (firstStep n ell a side).natAbs
    let Y := (exactMean n ell a side:ℝ)/pre; let S := oneWidth n ell a/pre
    let J := (sieveBand n ell pre).filter (fun t => ¬t∣q)
    ∃ α, α∈Set.Icc (199/200:ℝ) 1 ∧ saddleMean (primeBand b) α=log Y ∧
      ∀ (p : ℕ), p.Prime → p≤Fixed.A b → q.Coprime p → ∀ r : (ZMod q)ˣ,
        (∀ h : (ZMod p)ˣ, classPart J Y S r (fun j => (h:ZMod p)=(j:ZMod p)) ≤
          (9/((p:ℝ)-1))*classWeight J Y S r) ∧
        classPart J Y S r (p∣·) ≤ (18*primeProbability α p)*classWeight J Y S r := by
  obtain ⟨n₁,exc⟩ := constructed_exceptional_residues line
  obtain ⟨C,_,n₂,one⟩ := first_polynomial_progression line 1 le_rfl
  obtain ⟨n₃,deg⟩ := Fixed.degree_grows 10004
  refine ⟨max n₁ (max n₂ n₃),?_⟩
  intro n ell a R huge hn comp target none mark side u v ok
  have ⟨bs,bs'⟩ := max_le_iff.mp huge
  have ⟨bs₂,bs₃⟩ := max_le_iff.mp bs'
  let b := n.log2+1; let A := Fixed.A b; let B := Fixed.B b; let pre := R.prefactor a side
  let q := (firstStep n ell a side).natAbs
  let Y := (exactMean n ell a side:ℝ)/pre; let S := oneWidth n ell a/pre
  obtain ⟨gcd,_,α,model⟩ := one R bs₂ hn comp target none mark side u v ok
  have eq : saddleMean (primeBand b) α = log Y := by simpa only [gcd,Nat.cast_one,mul_one,Y,pre,b] using model.2.1
  refine ⟨α,model.1,eq,?_⟩
  intro p pp pa cop r
  obtain ⟨_,cap,grid,_⟩ := (constructed_marks_iff n ell 0 0 0 0 a).mp mark
  have big := deg b bs₃
  have am := mark_range hn big cap
  have ep := (mem_dyadicTargets.mp target).1.pos
  have qp : 0<q := Int.natAbs_pos.mpr (firstStep_size am ep side).2
  have ⟨pf,fc⟩ := R.pre_bounds target a side
  have bp : 0<B := Nat.pow_pos (by decide)
  have ap : 0<A := Nat.pow_pos (by decide)
  have bound (p' : ℕ) (hp : 0<p') (hc : p'≤A) : InWindow b (Y/p') (S/p') := by
    have size : pre*p' ≤ A*B^40 :=
      (Nat.mul_le_mul fc hc).trans (by rw [Nat.mul_comm _ A]; exact Nat.mul_le_mul_left A (Nat.pow_le_pow_right bp (by decide)))
    have h := one_point_window hn big target cap grid side ((pre:ℝ)*p') ⟨by exact_mod_cast Nat.mul_pos pf hp,by exact_mod_cast size⟩
    simpa only [Y,S,div_div] using h
  have base : InWindow b Y S := by simpa only [Nat.cast_one,div_one] using bound 1 (by decide) ap
  exact exc bs hn comp target none pf fc qp dvd_rfl qp (first_extra_conductor target pa am side) pp cop base (bound p pp.pos pa) model.1.1 eq r

end Cogentic.Construction

#print axioms Cogentic.Construction.first_polynomial_exceptional
