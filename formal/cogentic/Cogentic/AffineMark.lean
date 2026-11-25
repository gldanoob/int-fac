import Cogentic.ConstructionCofactors

namespace Cogentic.Construction

def basePolynomial (n ell : ℕ) (side : Bool) :=
  let p := construct n ell 0 0 0 0
  if side then p.second else p.first

/-- The value on the unrestricted signed Gaussian coefficient lattice,
    parametrized by L = u₀ + a u₁. -/
def affineValue (n ell a : ℕ) (side : Bool) (L : ℤ) : ℤ :=
  let d := Fixed.d (n.log2+1)
  eval (a:ℤ) (basePolynomial n ell side)+primorial d*ell*((a:ℤ)-Fixed.rootBase n)*L

def hitsTarget (n ell a : ℕ) (side : Bool) : Bool :=
  decide ((ell:ℤ) ∣ eval (a:ℤ) (basePolynomial n ell side))

theorem target_hits_iff (n ell a : ℕ) (side : Bool) (L : ℤ) :
    hitsTarget n ell a side ↔ (ell:ℤ) ∣ affineValue n ell a side L := by
  unfold hitsTarget affineValue
  simp only [decide_eq_true_eq]
  have dv : (ell:ℤ) ∣ (primorial (Fixed.d (n.log2+1)):ℤ)*ell*((a:ℤ)-Fixed.rootBase n)*L :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left ..) _) _
  exact (dvd_add_left dv).symm

theorem natAbs_gap {a m : ℕ} (hm : a ≤ m) : ((a:ℤ)-m).natAbs = m-a := by
  rw [show (a:ℤ)-m = -((m-a:ℕ):ℤ) by rw [Nat.cast_sub hm]; ring,Int.natAbs_neg]
  rfl

theorem n_coprime_gap {n a : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1)) (amin : 1 ≤ a)
    (amax : a ≤ Fixed.A (n.log2+1))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = Option.none) :
    n.Coprime (Fixed.rootBase n-a) := by
  let b := n.log2+1; let d := Fixed.d b; let A := Fixed.A b; let m := Fixed.rootBase n
  have dp : 0<d := by change 10004≤d at big; omega
  have mr := (Fixed.stage_guards hn big).markRange
  have ap : 0<A := Nat.pow_pos (by decide)
  have am : a < m := (show a < 2*A by change a≤A at amax; omega).trans_le
    ((Nat.mul_le_mul_right A (by omega : 2≤4*d)).trans mr)
  have small := (Nat.le_self_pow (n := d) dp.ne' (m-1)).trans_lt (Fixed.rootBase_spec hn).1
  have delta : 0 < m-a ∧ m-a < n := by omega
  have absent := (Option.orElse_eq_none ..).mp none
  have mem : a ∈ List.range' 1 A := List.mem_range'_1.mpr ⟨amin,by change a≤A at amax; omega⟩
  have listed : (a:ℤ) ∈ (List.range' 1 A).flatMap (fun j : ℕ => [(j:ℤ)]) := List.mem_flatMap.mpr ⟨a,mem,by simp⟩
  have miss := List.findSome?_eq_none_iff.mp absent.2 (a:ℤ) listed
  have absEq := natAbs_gap am.le
  change (if h : 1<n.gcd ((a:ℤ)-m).natAbs ∧ n.gcd ((a:ℤ)-m).natAbs<n then some _ else Option.none) = Option.none at miss
  split at miss
  · contradiction
  next bad =>
    rw [absEq] at bad
    have lo : 0 < n.gcd (m-a) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hi := (Nat.gcd_le_right n delta.1).trans_lt delta.2
    change n.gcd (m-a) = 1
    omega

private theorem cast_eval_of_eq {q : ℕ} (a m : ℕ) (eq : (a:ZMod q) = m) (f : List ℤ) :
    ((eval (a:ℤ) f:ℤ):ZMod q) = ((eval (m:ℤ) f:ℤ):ZMod q) := by
  induction f with
  | nil => rfl
  | cons t ts ih => simp [eval,eq,ih]

/-- Every value on the signed affine evaluation lattice, at any sieved
    grid mark, is coprime to the primorial and its base difference. -/
theorem affine_fixed_coprime {n ell a : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = Option.none)
    (mark : a ∈ (construct n ell 0 0 0 0).marks) (side : Bool) (L : ℤ) :
    (affineValue n ell a side L).natAbs.Coprime (primorial (Fixed.d (n.log2+1))*(Fixed.rootBase n-a)) := by
  let b := n.log2+1; let d := Fixed.d b; let P := primorial d; let m := Fixed.rootBase n
  let k := markModulus n ell; let f := basePolynomial n ell side
  let y := affineValue n ell a side L
  obtain ⟨amin,amax,_,guard⟩ := (constructed_marks_iff n ell 0 0 0 0 a).mp mark
  have dp : 0<d := by change 10004≤d at big; omega
  have am : a ≤ m := amax.trans ((Nat.le_mul_of_pos_left _ (by positivity : 0 < 4*d)).trans (Fixed.stage_guards hn big).markRange)
  rw [natAbs_gap am] at guard
  have cval := values_mod_primorial (by omega : 2≤Fixed.d (n.log2+1)) target 0 0 0 0 (a:ℤ)
  have fix : (P:ℤ) ∣ eval (a:ℤ) f-1 := by cases side <;> first | exact cval.1 | exact cval.2
  have cv := constructed_root hn (surviving_coprime hn composite target none) 0 0 0 0
  have divN : (n:ℤ) ∣ eval (m:ℤ) f := by cases side <;> first | exact cv.1 | exact cv.2
  have ratio : ((eval (m:ℤ) f)/(n:ℤ)).natAbs ∣ k := by cases side <;> first | exact dvd_mul_left .. | exact dvd_mul_right ..
  have ko := Nat.Coprime.of_dvd_right ratio guard
  have kn := n_coprime_gap hn big amin amax none
  have allcop : (m-a).Coprime (eval (m:ℤ) f).natAbs := by
    have h := Int.ediv_mul_cancel divN
    rw [←h,Int.natAbs_mul]
    exact Nat.coprime_mul_iff_right.mpr ⟨ko,kn.symm⟩
  have lift (q : ℕ) (qd : q ∣ y.natAbs) : ((y:ℤ):ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr qd))
  apply Nat.coprime_of_dvd'
  intro q prime qy qfix
  have z := lift q qy
  change ((eval (a:ℤ) f + (P:ℤ)*ell*((a:ℤ)-m)*L:ℤ):ZMod q) = 0 at z
  push_cast at z
  rcases prime.dvd_mul.mp qfix with qP | gap
  · have zp := (ZMod.natCast_eq_zero_iff ..).mpr qP
    rw [zp] at z
    simp only [zero_mul,add_zero] at z
    have zd := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr ((Int.natCast_dvd_natCast.mpr qP).trans fix)
    push_cast at zd
    rw [z] at zd
    have unit : (1:ZMod q)=0 := by linear_combination -zd
    exact (ZMod.natCast_eq_zero_iff 1 q).mp (by simpa using unit)
  · have zg : ((m-a:ℕ):ZMod q)=0 := (ZMod.natCast_eq_zero_iff ..).mpr gap
    rw [Nat.cast_sub am] at zg
    have eq : (a:ZMod q)=m := (sub_eq_zero.mp zg).symm
    rw [eq,sub_self,mul_zero,zero_mul,add_zero,cast_eval_of_eq a m eq f] at z
    have qm := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp z))
    exact (prime.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left gap allcop) qm).elim

end Cogentic.Construction

#print axioms Cogentic.Construction.affine_fixed_coprime
