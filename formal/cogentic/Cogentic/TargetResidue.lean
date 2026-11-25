import Cogentic.FirstResidueLoss

namespace Cogentic.Construction
open Cogentic.Window Finset

private theorem target_quotient_identity {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (a : ℕ)
    (side : Bool) (hit : hitsTarget n ell a side) (u v : ℤ) (ok : R.compatible side u v) :
    R.intercept a side u v*(R.hitProduct a:ℤ) =
      markSign n a side*(eval (a:ℤ) (basePolynomial n ell side)/(ell:ℤ) +
        (primorial (Fixed.d (n.log2+1)):ℤ)*((a:ℤ)-Fixed.rootBase n)*(u+a*v)) := by
  have df : (ell:ℤ)∣eval (a:ℤ) (basePolynomial n ell side) := of_decide_eq_true hit
  have total := Int.ediv_mul_cancel (dvd_mul_of_dvd_right (R.pre_dvd target a side u v ok) (markSign n a side))
  change R.intercept a side u v*(R.prefactor a side:ℤ)=_ at total
  simp only [PrescribedRows.prefactor,targetPart,if_pos hit,Nat.cast_mul,affineValue] at total
  apply mul_right_cancel₀ (show (ell:ℤ)≠0 by exact_mod_cast (mem_dyadicTargets.mp target).1.ne_zero)
  linear_combination total - markSign n a side*(Int.ediv_mul_cancel df)

private theorem target_hit_unit {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (a : ℕ) :
    (R.hitProduct a:ZMod ell)≠0 := by
  intro zero
  have sub : R.hit a ⊆ R.primes := filter_subset ..
  have nz := (R.subprod_bounds sub).1.ne'
  have pm := Nat.mem_primeFactors.mpr ⟨(mem_dyadicTargets.mp target).1,(ZMod.natCast_eq_zero_iff ..).mp zero,nz⟩
  have eq : (R.hitProduct a).primeFactors=R.hit a := Nat.primeFactors_prod (fun p hp => R.prime (sub hp))
  exact R.excluded (sub (eq ▸ pm))

/-- At congruent marks both hit by the target, the second quotient is
divisible by the target exactly on one explicit residue of the first.
The two fixed base evaluations are divided in the integers. -/
theorem PrescribedRows.common_target_residue {n ell a y : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool)
    (hitA : hitsTarget n ell a side) (hitY : hitsTarget n ell y side)
    (same : (a:ZMod ell)=(y:ZMod ell)) (u v : ℤ) (ok : R.compatible side u v) :
    letI : Fact ell.Prime := ⟨(mem_dyadicTargets.mp target).1⟩
    let f := basePolynomial n ell side
    let d := eval (a:ℤ) f/(ell:ℤ)-eval (y:ℤ) f/(ell:ℤ)
    let z : ZMod ell := (markSign n a side:ZMod ell)*d/(R.hitProduct a:ZMod ell)
    (ell:ℤ)∣R.intercept y side u v ↔ z=(R.intercept a side u v:ZMod ell) := by
  intro f d z
  let : Fact ell.Prime := ⟨(mem_dyadicTargets.mp target).1⟩
  have lift (i : ℕ) (hit : hitsTarget n ell i side) :=
    congrArg (Int.cast (R:=ZMod ell)) (target_quotient_identity R target i side hit u v ok)
  have aeq := lift a hitA
  have yeq := lift y hitY
  push_cast at aeq yeq
  have hnA := target_hit_unit R target a
  have hnY := target_hit_unit R target y
  have sgn (i : ℕ) : (markSign n i side:ZMod ell)≠0 := by unfold markSign; split <;> simp
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (R.intercept y side u v:ZMod ell)=0 ↔
    (markSign n a side:ZMod ell)*(d:ZMod ell)/(R.hitProduct a:ZMod ell)=(R.intercept a side u v:ZMod ell)
  rw [div_eq_iff hnA]
  dsimp only [d,f]
  rw [Int.cast_sub]
  let w (i : ℕ) : ZMod ell := (primorial (Fixed.d (n.log2+1)):ZMod ell)*
    ((i:ZMod ell)-(Fixed.rootBase n:ZMod ell))*((u:ZMod ell)+(i:ZMod ell)*v)
  let base (i : ℕ) : ZMod ell := ((eval (i:ℤ) (basePolynomial n ell side)/(ell:ℤ):ℤ):ZMod ell)
  change (R.intercept a side u v:ZMod ell)*(R.hitProduct a:ZMod ell) =
    (markSign n a side:ZMod ell)*(base a + w a) at aeq
  change (R.intercept y side u v:ZMod ell)*(R.hitProduct y:ZMod ell) =
    (markSign n y side:ZMod ell)*(base y + w y) at yeq
  have ww : w a=w y := by simp only [w,same]
  rw [aeq,ww,mul_right_inj' (sgn a)]
  constructor
  · intro zero
    rw [zero,zero_mul] at yeq
    have add := (mul_eq_zero.mp yeq.symm).resolve_left (sgn y)
    linear_combination -add
  · intro eq
    have add : base y+w y=0 := by linear_combination -eq
    rw [add,mul_zero] at yeq
    exact (mul_eq_zero.mp yeq).resolve_right hnY

/-- A target hit at a surviving mark makes its divided first modulus
coprime to the target, as required for the exceptional residue bound. -/
theorem target_hit_first_step_coprime {n ell a : ℕ}
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (side : Bool) (hit : hitsTarget n ell a side) :
    (firstStep n ell a side).natAbs.Coprime ell := by
  have cap := ((constructed_marks_iff ..).mp mark).2.1
  have size := (firstStep_size (mark_range hn big cap) (mem_dyadicTargets.mp target).1.pos side).1
  rw [size,firstModulus,if_pos hit,mul_one]
  have dvd := Int.natAbs_dvd_natAbs.mpr ((target_hits_iff n ell a side 0).mp hit)
  have co := affine_fixed_coprime hn big comp target absent mark side 0
  exact (Nat.Coprime.of_dvd_left (by simpa only [Int.natAbs_natCast] using dvd) co).symm

theorem dyadic_target_in_primeBand {b ell : ℕ} (bp : 0<b) (mem : ell∈dyadicTargets (Fixed.beta b)) :
    ell∈primeBand b := by
  obtain ⟨pp,lower,upper⟩ := mem_dyadicTargets.mp mem
  have βp : 0<Fixed.beta b := Nat.mul_pos (by decide) (Nat.mul_pos (Fixed.degree_pos bp) (Nat.succ_pos _))
  have eq : Fixed.B b=2^(Fixed.beta b-1)*2 := by
    rw [←pow_succ,Nat.sub_add_cancel βp]
    rfl
  refine mem_primeBand.mpr ⟨pp,upper,?_⟩
  rw [eq,pow_two]
  exact (Nat.mul_lt_mul_of_pos_right lower (by decide : 0<2)).trans_le (Nat.mul_le_mul_left ell pp.two_le)

/-- The exceptional common-target class has small actual probability
conditional on smoothness at the first mark. -/
theorem PrescribedRows.common_target_probability (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a y : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    hitsTarget n ell a side → hitsTarget n ell y side → (a:ZMod ell)=(y:ZMod ell) →
    let J := sieveBand n ell (R.prefactor a side)
    let smooth := fun k : ℤ×ℤ => supportedValue J (R.intercept a side k.1 k.2)
    let bad := fun k : ℤ×ℤ => (ell:ℤ)∣R.intercept y side k.1 k.2
    prescribedProbability R side (fun k => smooth k ∧ bad k) ≤
      (36*(Fixed.B b:ℝ)^(-199/400:ℝ))*prescribedProbability R side smooth := by
  classical
  obtain ⟨b₁,exception⟩ := PrescribedRows.band_first_residue_probability line
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ b₂,?_⟩
  intro n ell a y R b large hn comp target absent mark side ha hy same J smooth bad
  have prime := (mem_dyadicTargets.mp target).1
  let : Fact ell.Prime := ⟨prime⟩
  let f := basePolynomial n ell side
  let d := eval (a:ℤ) f/(ell:ℤ)-eval (y:ℤ) f/(ell:ℤ)
  let z : ZMod ell := (markSign n a side:ZMod ell)*d/(R.hitProduct a:ZMod ell)
  let first := fun k : ℤ×ℤ => z=(R.intercept a side k.1 k.2:ZMod ell)
  have ident : prescribedProbability R side (fun k => smooth k ∧ bad k) =
      prescribedProbability R side (fun k => smooth k ∧ first k) := by
    unfold prescribedProbability
    dsimp only
    congr 1
    apply tsum_congr
    intro k
    have loc : bad k.val ↔ first k.val := R.common_target_residue target side ha hy same k.val.1 k.val.2 k.property
    simp only [loc]
  have co := target_hit_first_step_coprime hn (degree b (max_le_iff.mp large).2) comp target absent mark side ha
  rw [ident]
  exact exception R (max_le_iff.mp large).1 hn comp target absent mark side ell
    (dyadic_target_in_primeBand (Nat.succ_pos _) target) co z

open scoped Classical in
/-- The same bound applies when the witness to divisibility may be any
compatible tuple with the given first quotient. -/
theorem PrescribedRows.common_target_quotient_probability (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a y : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    hitsTarget n ell a side → hitsTarget n ell y side → (a:ZMod ell)=(y:ZMod ell) →
    let J := sieveBand n ell (R.prefactor a side)
    let smooth := fun k : ℤ×ℤ => supportedValue J (R.intercept a side k.1 k.2)
    let bad := fun z : ℤ => ∃ u v : ℤ, R.compatible side u v ∧
      R.intercept a side u v=z ∧ ell∣(R.intercept y side u v).natAbs
    prescribedProbability R side (fun k => smooth k ∧ bad (R.intercept a side k.1 k.2)) ≤
      (36*(Fixed.B b:ℝ)^(-199/400:ℝ))*prescribedProbability R side smooth := by
  classical
  obtain ⟨b₀,bound⟩ := PrescribedRows.common_target_probability line
  refine ⟨b₀,?_⟩
  intro n ell a y R b large hn comp target absent mark side ha hy same J smooth bad
  have h := bound R large hn comp target absent mark side ha hy same
  let actual (k : ℤ×ℤ) := (ell:ℤ)∣R.intercept y side k.1 k.2
  have eq : prescribedProbability R side (fun k => smooth k ∧ bad (R.intercept a side k.1 k.2)) =
      prescribedProbability R side (fun k => smooth k ∧ actual k) := by
    unfold prescribedProbability
    dsimp only
    congr 1
    apply tsum_congr
    intro k
    have iff : bad (R.intercept a side k.val.1 k.val.2) ↔ actual k.val := by
      constructor
      · rintro ⟨u,v,ok,first,last⟩
        have div : (ell:ℤ)∣R.intercept y side u v :=
          Int.natAbs_dvd_natAbs.mp (by simpa only [Int.natAbs_natCast] using last)
        have residue := (R.common_target_residue target side ha hy same u v ok).mp div
        exact (R.common_target_residue target side ha hy same k.val.1 k.val.2 k.property).mpr
          (residue.trans (congrArg (Int.cast (R:=ZMod ell)) first))
      · intro d
        exact ⟨k.val.1,k.val.2,k.property,rfl,by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr d⟩
    simp only [iff]
  exact eq.le.trans h

end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.common_target_residue
#print axioms Cogentic.Construction.target_hit_first_step_coprime

#print axioms Cogentic.Construction.PrescribedRows.common_target_probability

#print axioms Cogentic.Construction.PrescribedRows.common_target_quotient_probability
