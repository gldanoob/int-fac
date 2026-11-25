import Cogentic.ConstructionTarget

namespace Cogentic.Construction

open Polynomial

private theorem low_odd {d P ell : ℕ} (half : Nat.Coprime 2 (P/2)) (even : 2 ∣ P)
    (cop : P.Coprime ell) (A m leading : ℕ) (side : Bool) :
    reduction (P/2) (preliminary d A m P ell leading side) =
      (List.range d).map (fun j => if j = 0 then (1:ZMod (P/2)) else 0) := by
  unfold reduction preliminary
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  dsimp only [Function.comp_apply]
  have dv := Nat.div_dvd_of_dvd even
  rw [reduce_nearest (dv.trans (dvd_mul_right P ell))]
  have congr := (((crt_spec cop _ (modulusResidue ((localCoeffs d ell m leading side).getD j 0) ell)).1).of_dvd dv).trans
    ((crt_spec half (bitCoeff (binaryMask d) j) (if j=0 then 1 else 0)).2)
  split <;> rename_i hj <;> simpa [hj] using (ZMod.natCast_eq_natCast_iff ..).mpr congr

private theorem cast_eval (q : ℕ) (a : ℤ) (cs : List ℤ) :
    ((eval a cs : ℤ):ZMod q) = eval (a:ZMod q) (reduction q cs) := by
  induction cs with
  | nil => simp [eval,reduction]
  | cons c cs ih => simpa [eval,reduction] using congrArg (fun v : ZMod q => c+a*v) ih

private theorem binary_eval (a : ℤ) (cs : List ℤ) :
    ((eval a cs : ℤ):ZMod 2) = ((Marking.polynomial cs).map (Int.castRingHom (ZMod 2))).eval (a:ZMod 2) := by
  induction cs with
  | nil => simp [eval,Marking.polynomial]
  | cons c cs ih => simp [eval,Marking.polynomial,ih]

/-- Every integer value of either perturbed polynomial is one modulo the
    entire primorial, including the binary component of the CRT. -/
theorem values_mod_primorial {n ell : ℕ} (hd : 2 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (u₀ u₁ v₀ v₁ : ℕ) (x : ℤ) :
    let p := construct n ell u₀ u₁ v₀ v₁
    let P := primorial (Fixed.d (n.log2+1))
    (P:ℤ) ∣ eval x p.first-1 ∧ (P:ℤ) ∣ eval x p.second-1 := by
  let b := n.log2+1
  let d := Fixed.d b
  let P := primorial d
  let c := leadingCoefficient n
  let m := Fixed.rootBase n
  have dp : 2 ≤ d := hd
  have even : 2 ∣ P := Nat.prime_two.dvd_primorial_iff.mpr hd
  have dv : P/2 ∣ P := Nat.div_dvd_of_dvd even
  have half := (primorial_half_odd hd).coprime_two_left
  have cop := target_primorial target
  have bin := constructed_mod_two hd target u₀ u₁ v₀ v₁
  have top : (c:ZMod (P/2)) = 0 := (ZMod.natCast_eq_zero_iff ..).mpr (dvd_mul_right ..)
  have zeroes (k : ℕ) : eval (x:ZMod (P/2)) (List.replicate k 0) = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ,eval,ih]
  have first : eval (x:ZMod (P/2)) ((List.range d).map (fun j => if j=0 then (1:ZMod (P/2)) else 0)) = 1 := by
    obtain ⟨k,eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    rw [eq,List.range_succ_eq_map]
    simp [List.map_map,Function.comp_def,List.map_const',eval,zeroes]
  let poly (s : Bool) (a z : ℕ) := perturb (P*ell) m a z
        (corrected n m (P*ell) c (preliminary d (Fixed.A b) m P ell c s))
  have side (s : Bool) (a z : ℕ) (eq : (Marking.polynomial (poly s a z)).map (Int.castRingHom (ZMod 2)) = binaryPoly d (binaryMask d)) :
      (P:ℤ) ∣ eval x (poly s a z)-1 := by
    let cs := poly s a z
    have oddVal : ((eval x cs : ℤ):ZMod (P/2)) = 1 := by
      rw [cast_eval]
      change eval (x:ZMod (P/2)) (reduction (P/2) (perturb _ _ _ _ _)) = 1
      rw [reduce_final (dv.trans (dvd_mul_right P ell)),low_odd half even cop,top,eval_append,first]
      simp [eval]
    have binary : ((eval x cs : ℤ):ZMod 2) = 1 := by
      rw [binary_eval,eq]
      apply Fin.eq_one_of_ne_zero
      exact (binaryMask_irreducible (by omega : 0<d)).2.not_isRoot_of_natDegree_ne_one (by rw [binaryPoly_degree]; omega)
    have divisor (q : ℕ) (h : ((eval x cs : ℤ):ZMod q) = 1) : q ∣ (eval x cs-1).natAbs := by
      apply Int.natCast_dvd_natCast.mp; apply Int.dvd_natAbs.mpr
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
      simp [h]
    have both := half.mul_dvd_of_dvd_of_dvd (divisor 2 binary) (divisor (P/2) oddVal)
    rw [Nat.mul_div_cancel' even] at both
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr both)
  exact ⟨side false u₀ u₁ bin.1,side true v₀ v₁ bin.2⟩

/-- No prime dividing any of the common leading coefficient's factors can
    divide every coefficient of either constructed integer polynomial. -/
theorem constructed_primitive {n ell : ℕ} (hd : 3 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (u₀ u₁ v₀ v₁ : ℕ) :
    let p := construct n ell u₀ u₁ v₀ v₁
    (Marking.polynomial p.first).IsPrimitive ∧ (Marking.polynomial p.second).IsPrimitive := by
  let d := Fixed.d (n.log2+1)
  let P := primorial d
  let c := leadingCoefficient n
  have even : 2 ∣ P := Nat.prime_two.dvd_primorial_iff.mpr (by omega)
  have three : 3 ∣ P := Nat.prime_three.dvd_primorial_iff.mpr hd
  have values := values_mod_primorial (by omega : 2 ≤ Fixed.d (n.log2+1)) target u₀ u₁ v₀ v₁ 0
  have support (q : ℕ) (hq : q.Prime) (qc : q ∣ c) : q ∣ P := by
    rcases hq.dvd_mul.mp qc with half | power
    · exact half.trans (Nat.div_dvd_of_dvd even)
    · exact (hq.dvd_of_dvd_pow power).trans three
  have side (cs : List ℤ) (len : cs.length = d+1) (last : cs.getLast? = some (c:ℤ))
      (val : (P:ℤ) ∣ eval 0 cs-1) : (Marking.polynomial cs).IsPrimitive := by
    have eq : cs[d]? = some (c:ℤ) := by simpa [List.getLast?_eq_getElem?,len] using last
    have co : (Marking.polynomial cs).coeff d = (c:ℤ) := by
      simpa [List.getD_eq_getElem?_getD,eq] using coefficient_rep (R := ℤ) cs d
    have atZero : eval 0 cs = (Marking.polynomial cs).coeff 0 := by
      cases cs <;> simp [eval,Marking.polynomial]
    intro r divides
    have all := (C_dvd_iff_dvd_coeff ..).mp divides
    apply Int.isUnit_iff_natAbs_eq.mpr
    by_contra bad
    obtain ⟨q,prime,qr⟩ := Nat.exists_prime_and_dvd bad
    have qri : (q:ℤ) ∣ r := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr qr)
    have qc := qri.trans (co ▸ all d)
    have qp : (q:ℤ) ∣ (P:ℤ) := Int.natCast_dvd_natCast.mpr (support q prime (Int.natCast_dvd_natCast.mp qc))
    have qv : (q:ℤ) ∣ eval 0 cs := atZero ▸ qri.trans (all 0)
    have one : (q:ℤ) ∣ 1 := by simpa using dvd_sub qv (qp.trans val)
    exact prime.not_dvd_one (by exact_mod_cast one)
  have s := shape (ell := ell) hd false u₀ u₁
  have t := shape (ell := ell) hd true v₀ v₁
  exact ⟨side _ s.1 s.2 values.1,side _ t.1 t.2 values.2⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.values_mod_primorial
#print axioms Cogentic.Construction.constructed_primitive
