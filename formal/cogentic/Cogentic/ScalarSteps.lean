import Cogentic.ScalarAffine
import Cogentic.ForcedRows

namespace Cogentic.Construction

def markSign (n a : ℕ) (side : Bool) : ℤ := if idealAt n a side < 0 then -1 else 1

theorem markSign_eq (n a : ℕ) (side : Bool) : (markSign n a side:ℚ) = orientation n a side := by
  unfold markSign orientation; split <;> simp

private theorem sign_abs (n a : ℕ) (side : Bool) : (markSign n a side).natAbs = 1 := by
  unfold markSign; split <;> decide

def PrescribedRows.intercept {n ell : ℕ} (R : PrescribedRows n ell) (a : ℕ) (side : Bool) (u v : ℤ) :=
  markSign n a side*affineValue n ell a side (u+a*v)/(R.prefactor a side:ℤ)

def firstStep (n ell a : ℕ) (side : Bool) : ℤ :=
  markSign n a side*(primorial (Fixed.d (n.log2+1)):ℤ)*
    (if hitsTarget n ell a side then (1:ℤ) else ell)*((a:ℤ)-Fixed.rootBase n)

def PrescribedRows.secondStep {n ell : ℕ} (R : PrescribedRows n ell) (a a' : ℕ) (side : Bool) : ℤ :=
  let both := prodPrimes (R.hit a ∩ R.hit a')
  let free := prodPrimes (R.miss a \ R.hit a')
  firstStep n ell a' side*(((a':ℤ)-a)/(both:ℤ))*free

theorem scaled_first (n ell a : ℕ) (side : Bool) :
    firstStep n ell a side*(targetPart n ell a side:ℤ) =
      markSign n a side*(primorial (Fixed.d (n.log2+1)):ℤ)*ell*((a:ℤ)-Fixed.rootBase n) := by
  unfold firstStep targetPart; split <;> simp_all <;> ring

private theorem eq_ediv_affine {y d s t : ℤ} (nonzero : d ≠ 0) (divides : d ∣ y) (step : t = s*d) (j : ℤ) :
    (y+t*j)/d = y/d+s*j := by
  rw [step,show s*d*j=d*(s*j) by ring,Int.add_ediv_of_dvd_right (dvd_mul_right ..),Int.mul_ediv_cancel_left _ nonzero]

theorem PrescribedRows.first_quotient {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (a : ℕ) (side : Bool) (u v : ℤ)
    (ok : R.compatible side u v) (j : ℤ) :
    markSign n a side*affineValue n ell a side (u+a*v+(R.hitProduct a:ℤ)*j)/(R.prefactor a side:ℤ) =
      R.intercept a side u v+firstStep n ell a side*j := by
  let sig := markSign n a side; let P := primorial (Fixed.d (n.log2+1)); let m := Fixed.rootBase n
  let F := affineValue n ell a side (u+a*v)
  let h := R.hitProduct a
  have affine : sig*affineValue n ell a side (u+a*v+(h:ℤ)*j) =
      sig*F+((sig*(P:ℤ)*ell*((a:ℤ)-m))*h)*j := by dsimp [F,affineValue,sig,P,m]; ring
  have hp := (R.pre_bounds target a side).1
  have dv := dvd_mul_of_dvd_right (R.pre_dvd target a side u v ok) sig
  change sig*affineValue n ell a side (u+a*v+(h:ℤ)*j)/(R.prefactor a side:ℤ) = _
  rw [affine]
  apply eq_ediv_affine (by exact_mod_cast hp.ne') dv
  rw [←scaled_first]; simp only [prefactor,Nat.cast_mul,h]; ring

theorem PrescribedRows.second_quotient {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (a a' : ℕ) (side : Bool) (u v : ℤ)
    (ok : R.compatible side u v) (j : ℤ) :
    let miss := prodPrimes (R.miss a)
    markSign n a' side*affineValue n ell a' side (u+a'*v+((a':ℤ)-a)*miss*j)/(R.prefactor a' side:ℤ) =
      R.intercept a' side u v+R.secondStep a a' side*j := by
  let both := prodPrimes (R.hit a ∩ R.hit a')
  let fresh := prodPrimes (R.hit a' \ R.hit a)
  let free := prodPrimes (R.miss a \ R.hit a')
  let miss := prodPrimes (R.miss a)
  let sig := markSign n a' side; let P := primorial (Fixed.d (n.log2+1)); let m := Fixed.rootBase n
  let F := affineValue n ell a' side (u+a'*v)
  let δ : ℤ := (a':ℤ)-a
  obtain ⟨H,M,dv,_,_,_,_⟩ := R.second_factors a a'
  change R.hitProduct a' = both*fresh at H
  change miss = fresh*free at M
  have cancel : δ/both*both = δ := Int.ediv_mul_cancel dv
  have affine : sig*affineValue n ell a' side (u+a'*v+δ*miss*j) =
      sig*F+(sig*P*ell*((a':ℤ)-m)*δ*miss)*j := by dsimp [F,affineValue,sig,P,m]; ring
  have pr := (R.pre_bounds target a' side).1
  have pre := dvd_mul_of_dvd_right (R.pre_dvd target a' side u v ok) sig
  change sig*affineValue n ell a' side (u+a'*v+δ*miss*j)/(R.prefactor a' side:ℤ) = _
  rw [affine]
  apply eq_ediv_affine (by exact_mod_cast pr.ne') pre
  rw [←scaled_first,M]
  change firstStep n ell a' side*targetPart n ell a' side*δ*(↑(fresh*free):ℤ) =
    (firstStep n ell a' side*(δ/both)*free)*↑(targetPart n ell a' side*R.hitProduct a')
  rw [H]; push_cast
  linear_combination -(firstStep n ell a' side*targetPart n ell a' side*fresh*free)*cancel

theorem PrescribedRows.scaled_second {n ell : ℕ} (R : PrescribedRows n ell) (a a' : ℕ) (side : Bool) :
    R.secondStep a a' side*(R.prefactor a' side:ℤ) =
      markSign n a' side*(primorial (Fixed.d (n.log2+1)):ℤ)*ell*((a':ℤ)-Fixed.rootBase n)*
        ((a':ℤ)-a)*prodPrimes (R.miss a) := by
  obtain ⟨H,M,dv,_,_,_,_⟩ := R.second_factors a a'
  let both := prodPrimes (R.hit a ∩ R.hit a')
  let fresh := prodPrimes (R.hit a' \ R.hit a)
  let free := prodPrimes (R.miss a \ R.hit a')
  let δ := (a':ℤ)-a
  have cancel : δ/(both:ℤ)*both=δ := Int.ediv_mul_cancel dv
  rw [←scaled_first,PrescribedRows.prefactor,H,M]
  change firstStep n ell a' side*(δ/both)*free*↑(targetPart n ell a' side*(both*fresh)) =
    firstStep n ell a' side*targetPart n ell a' side*δ*↑(fresh*free)
  push_cast
  linear_combination (firstStep n ell a' side*targetPart n ell a' side*fresh*free)*cancel

theorem firstStep_size {n ell a : ℕ} (am : a < Fixed.rootBase n) (ep : 0<ell) (side : Bool) :
    (firstStep n ell a side).natAbs = firstModulus n ell a (hitsTarget n ell a side) ∧ firstStep n ell a side ≠ 0 := by
  let m := Fixed.rootBase n
  let P := primorial (Fixed.d (n.log2+1))
  have gap : ((a:ℤ)-m).natAbs = m-a := by
    rw [show (a:ℤ)-m = -((m-a:ℕ):ℤ) by rw [Nat.cast_sub am.le]; ring,Int.natAbs_neg]
    rfl
  have eq : (firstStep n ell a side).natAbs = firstModulus n ell a (hitsTarget n ell a side) := by
    unfold firstStep firstModulus
    simp only [Int.natAbs_mul,sign_abs,one_mul,Int.natAbs_natCast,gap]
    split <;> simp [gap,m]
  have pos : 0 < firstModulus n ell a (hitsTarget n ell a side) := by
    unfold firstModulus
    have pp := primorial_pos (Fixed.d (n.log2+1))
    split <;> exact Nat.mul_pos (Nat.mul_pos pp (by omega)) (Nat.sub_pos_of_lt am)
  exact ⟨eq,Int.natAbs_pos.mp (eq ▸ pos)⟩

theorem PrescribedRows.secondStep_size {n ell a a' : ℕ} (R : PrescribedRows n ell) (am : a' < Fixed.rootBase n)
    (ep : 0<ell) (neq : a'≠a) (side : Bool) :
    let both := prodPrimes (R.hit a ∩ R.hit a')
    let free := prodPrimes (R.miss a \ R.hit a')
    (R.secondStep a a' side).natAbs = secondModulus n ell a a' (hitsTarget n ell a' side) both free ∧
      R.secondStep a a' side ≠ 0 := by
  obtain ⟨_,_,divides,bp,_,fp,_⟩ := R.second_factors a a'
  let both := prodPrimes (R.hit a ∩ R.hit a')
  let free := prodPrimes (R.miss a \ R.hit a')
  let δ := (a':ℤ)-a
  have dist : δ.natAbs = a'.dist a := by
    rcases le_total a' a with h | h
    · rw [Nat.dist_eq_sub_of_le h,show δ = -((a-a':ℕ):ℤ) by dsimp [δ]; rw [Nat.cast_sub h]; ring,Int.natAbs_neg]
      rfl
    · rw [Nat.dist_comm,Nat.dist_eq_sub_of_le h,show δ = ((a'-a:ℕ):ℤ) by dsimp [δ]; rw [Nat.cast_sub h]]
      rfl
  have qsize := Int.natAbs_ediv_of_dvd divides
  change (δ/(both:ℤ)).natAbs = δ.natAbs/both at qsize
  have fraction : δ/(both:ℤ) ≠ 0 := by
    intro h
    have dv := Int.ediv_mul_cancel divides
    change δ/(both:ℤ)*both=δ at dv
    rw [h,zero_mul] at dv
    exact neq (by dsimp [δ] at dv; exact_mod_cast (sub_eq_zero.mp dv.symm))
  have one := firstStep_size am ep side
  refine ⟨?_,mul_ne_zero (mul_ne_zero one.2 fraction) (by exact_mod_cast fp.ne')⟩
  change ((firstStep n ell a' side*(δ/(both:ℤ)))*(free:ℤ)).natAbs = _
  simp only [Int.natAbs_mul,Int.natAbs_natCast,one.1,qsize,dist,secondModulus,both,free]

theorem mark_range {n a : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (cap : a≤Fixed.A (n.log2+1)) :
    a < Fixed.rootBase n := by
  have ap : 0 < Fixed.A (n.log2+1) := Nat.pow_pos (by decide)
  exact (show a < 2*Fixed.A (n.log2+1) by omega).trans_le
    ((Nat.mul_le_mul_right _ (by omega : 2≤4*Fixed.d (n.log2+1))).trans (Fixed.stage_guards hn big).markRange)

theorem PrescribedRows.intercept_coprime {n ell a : ℕ} (R : PrescribedRows n ell) (hn : 2≤n)
    (big : 10004≤Fixed.d (n.log2+1)) (composite : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (side : Bool) (u v : ℤ) (ok : R.compatible side u v) :
    (R.intercept a side u v).natAbs.Coprime (firstModulus n ell a (hitsTarget n ell a side)) := by
  let d := Fixed.d (n.log2+1); let P := primorial d; let m := Fixed.rootBase n
  let F := affineValue n ell a side (u+a*v)
  let y := R.intercept a side u v
  have den := dvd_mul_of_dvd_right (R.pre_dvd target a side u v ok) (markSign n a side)
  have prod : y*(R.prefactor a side:ℤ) = markSign n a side*F := Int.ediv_mul_cancel den
  have yd : y.natAbs ∣ F.natAbs := by
    have e := congrArg Int.natAbs prod
    simp only [Int.natAbs_mul,sign_abs,one_mul] at e
    exact ⟨_,e.symm⟩
  obtain ⟨py,dy⟩ := Nat.coprime_mul_iff_right.mp (Nat.Coprime.of_dvd_left yd
    (affine_fixed_coprime hn big composite target none mark side (u+a*v)))
  have z : y.natAbs.Coprime (if hitsTarget n ell a side then 1 else ell) := by
    split
    · simp
    next h =>
      apply Nat.Coprime.of_dvd_left yd
      apply Nat.Coprime.symm
      apply (mem_dyadicTargets.mp target).1.coprime_iff_not_dvd.mpr
      intro dv
      exact h ((target_hits_iff n ell a side (u+a*v)).mpr (Int.natCast_dvd.mpr dv))
  exact Nat.coprime_mul_iff_right.mpr ⟨Nat.coprime_mul_iff_right.mpr ⟨py,z⟩,dy⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.first_quotient
#print axioms Cogentic.Construction.PrescribedRows.second_quotient
