import Cogentic.ConstructionReduction

namespace Cogentic.Construction

open Polynomial

private theorem shift_spec {ell : ℕ} [NeZero ell] (d a : ℕ) :
    ((ModularPower.powMod a d ell : ℤ)-a)%ell =
      (((a:ZMod ell)^d-a).val : ℤ) := by
  rw [←ZMod.val_intCast]
  push_cast
  rw [ModularPower.powMod_def,ZMod.natCast_mod,Nat.cast_pow]

/-- The implementation searches the finite image of x^d-x; 0 and 1 collide,
    hence a missing residue always exists. -/
theorem missingShift_avoids {ell d : ℕ} (prime : ell.Prime) (dp : 0 < d) :
    missingShift d ell < ell ∧ ∀ x : ZMod ell, x^d-x ≠ (missingShift d ell : ZMod ell) := by
  let : Fact ell.Prime := ⟨prime⟩
  let f := fun x : ZMod ell => x^d-x
  have nonsurj : ¬Function.Surjective f := by
    intro surj
    have inj := Finite.injective_iff_surjective.mpr surj
    have same : f 0 = f 1 := by simp [f,zero_pow dp.ne']
    exact zero_ne_one (inj same)
  obtain ⟨t,miss⟩ : ∃ t, ∀ x, f x ≠ t := by simpa [Function.Surjective] using nonsurj
  let values := (List.range ell).map (fun a : ℕ => ((ModularPower.powMod a d ell:ℤ)-a)%ell)
  have spec {j : ℕ} (hj : j < ell) : (j:ℤ) ∈ values ↔ ∃ x, f x = (j:ZMod ell) := by
    constructor
    · intro mem
      obtain ⟨a,_,eq⟩ := List.mem_map.mp mem
      rw [shift_spec] at eq
      exact ⟨a,by simpa [f] using congrArg (fun a : ℤ => (a : ZMod ell)) eq⟩
    · rintro ⟨x,hx⟩
      apply List.mem_map.mpr
      refine ⟨x.val,List.mem_range.mpr (ZMod.val_lt _),?_⟩
      rw [shift_spec,ZMod.natCast_zmod_val]
      change ((f x).val : ℤ) = j
      rw [hx,ZMod.val_natCast_of_lt hj]
  have outside : (t.val:ℤ) ∉ values := by
    intro mem
    obtain ⟨x,eq⟩ := (spec (ZMod.val_lt t)).mp mem
    exact miss x (eq.trans (ZMod.natCast_zmod_val _))
  let predicate := fun j : ℕ => !values.contains (j:ℤ)
  have found : ((List.range ell).find? predicate).isSome :=
    List.find?_isSome.mpr ⟨t.val,List.mem_range.mpr (ZMod.val_lt _),by simpa [predicate] using outside⟩
  change ((List.range ell).find? predicate).getD 0 < ell ∧ _
  cases eq : (List.range ell).find? predicate with
  | none => simp [eq] at found
  | some s =>
    have good := List.find?_some eq
    have small := List.mem_range.mp (List.mem_of_find?_eq_some eq)
    have out : (s:ℤ) ∉ values := by simpa [predicate] using good
    have m : missingShift d ell = s := by change ((List.range ell).find? predicate).getD 0 = s; rw [eq]; rfl
    exact ⟨small,fun x hx => out ((spec small).mpr ⟨x,by simpa only [m] using hx⟩)⟩

theorem wanted_spec {d ell : ℕ} (large : d < ell) (m : ℕ) :
    (wanted d ell m).length = d ∧ (wanted d ell m).Nodup ∧
    ∀ r ∈ wanted d ell m, r < ell ∧ r ≠ m%ell := by
  let rs := (List.range ell).filter (fun r => r != m%ell)
  have hmod : m%ell ∈ List.range ell := List.mem_range.mpr (Nat.mod_lt _ (by omega))
  have len : rs.length = ell-1 := by
    rw [show rs = (List.range ell).erase (m%ell) from ((List.nodup_range).erase_eq_filter _).symm,
      List.length_erase_of_mem hmod,List.length_range]
  refine ⟨?_,?_,?_⟩
  · change (rs.take d).length = d
    rw [List.length_take,len,Nat.min_eq_left (by omega)]
  · exact ((List.nodup_range).filter _).take
  · intro r hr
    have mem := List.mem_filter.mp (List.mem_of_mem_take hr)
    exact ⟨List.mem_range.mp mem.1,by simpa using mem.2⟩

private theorem linear_shape {R : Type*} [Ring R] (r prev : R) (p : List R) :
    (linear r prev p).length = p.length+1 ∧
      (linear r prev p).getLast? = some (p.getLast?.getD prev) := by
  induction p generalizing prev with
  | nil => simp [linear]
  | cons a as ih =>
    have ⟨len,last⟩ := ih a
    constructor
    · simp [linear,len]
    · have nonempty : linear r a as ≠ [] := by intro h; simp [h] at len
      simp only [linear,List.getLast?_cons_of_ne_nil nonempty,last]
      cases as with
      | nil => rfl
      | cons x xs => simp [List.getLast?_eq_some_getLast]

theorem fromRoots_shape {R : Type*} [Ring R] (roots : List R) :
    (fromRoots roots).length = roots.length+1 ∧ (fromRoots roots).getLast? = some 1 := by
  have go (ls p : List R) (last : p.getLast? = some 1) :
      (ls.foldl (fun q r => linear r 0 q) p).length = ls.length+p.length ∧
      (ls.foldl (fun q r => linear r 0 q) p).getLast? = some 1 := by
    induction ls generalizing p with
    | nil => simp [last]
    | cons r rs ih =>
      have ⟨len,tail⟩ := linear_shape r 0 p
      rw [last] at tail
      obtain ⟨ls,lt⟩ := ih (linear r 0 p) tail
      exact ⟨by simp only [List.foldl_cons,List.length_cons]; omega,lt⟩
  simpa [fromRoots] using go roots [1] (by simp)

private theorem local_shape {d ell : ℕ} (large : d < ell) (m leading : ℕ) (side : Bool) :
    (localCoeffs d ell m leading side).length = d+1 ∧
      (localCoeffs d ell m leading side).getLast? = some (leading:ℤ) := by
  cases side with
  | false =>
    obtain ⟨len,last⟩ := fromRoots_shape ((wanted d ell m).map Int.ofNat)
    simp [localCoeffs,len,last,(wanted_spec large m).1]
  | true =>
    simp [localCoeffs,List.getLast?_eq_getElem?]

private theorem residue_cast {ell : ℕ} [NeZero ell] (z : ℤ) : (modulusResidue z ell : ZMod ell) = z := by
  have nonneg : 0 ≤ z%(ell:ℤ) := Int.emod_nonneg _ (by exact_mod_cast NeZero.ne ell)
  change (((z%(ell:ℤ)).toNat:ℕ):ZMod ell) = _
  rw [←Int.cast_natCast,Int.toNat_of_nonneg nonneg,ZMod.intCast_mod]

private theorem low_target {d P ell : ℕ} [NeZero ell] (cop : P.Coprime ell) (A m leading : ℕ) (side : Bool) :
    reduction ell (preliminary d A m P ell leading side) =
      (List.range d).map (fun j => ((localCoeffs d ell m leading side).getD j 0 : ZMod ell)) := by
  unfold reduction preliminary
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  dsimp only [Function.comp_apply]
  rw [reduce_nearest (dvd_mul_left ell P)]
  exact ((ZMod.natCast_eq_natCast_iff ..).mpr (crt_spec cop _ _).2).trans (residue_cast _)

private theorem list_shape_reconstruct {d : ℕ} {p : List ℤ} {top : ℤ} (ell : ℕ)
    (len : p.length = d+1) (last : p.getLast? = some top) :
    (List.range d).map (fun j => ((p.getD j 0 : ℤ) : ZMod ell)) ++ [(top : ZMod ell)] = reduction ell p := by
  apply List.ext_getElem (by simp [reduction,len])
  intro i ha hb
  by_cases il : i < d
  · rw [List.getElem_append_left (by simpa using il)]
    simp [reduction,List.getD_eq_getElem?_getD,show i < p.length by omega]
  · have id : i = d := by simp at ha; omega
    subst i
    rw [List.getElem_concat_length (by simp)]
    have last' : p[d]? = some top := by simpa [List.getLast?_eq_getElem?,len] using last
    simpa [reduction] using congrArg (fun z : ℤ => (z : ZMod ell))
      (List.getElem_of_getElem? last').choose_spec.symm

theorem constructed_target_residues {n ell : ℕ} (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (u₀ u₁ v₀ v₁ : ℕ) :
    let p := construct n ell u₀ u₁ v₀ v₁
    let localPoly := localCoeffs (Fixed.d (n.log2+1)) ell (Fixed.rootBase n) (leadingCoefficient n)
    reduction ell p.first = reduction ell (localPoly false) ∧
      reduction ell p.second = reduction ell (localPoly true) := by
  let : NeZero ell := ⟨(mem_dyadicTargets.mp target).1.ne_zero⟩
  let b := n.log2+1
  let d := Fixed.d b
  let m := Fixed.rootBase n
  let P := primorial d
  let lead := leadingCoefficient n
  have side (second : Bool) (z w : ℕ) :
      reduction ell (perturb (P*ell) m z w (corrected n m (P*ell) lead
        (preliminary d (Fixed.A b) m P ell lead second))) = reduction ell (localCoeffs d ell m lead second) := by
    rw [reduce_final (dvd_mul_left ell P),low_target (target_primorial target)]
    have ⟨len,last⟩ := local_shape (target_gt_degree target) m lead second
    simpa only [Int.cast_natCast] using list_shape_reconstruct ell len last
  exact ⟨side false u₀ u₁,side true v₀ v₁⟩

private theorem polynomial_of_reduction (q : ℕ) (p : List ℤ) :
    (Marking.polynomial p).map (Int.castRingHom (ZMod q)) =
      eval (X : Polynomial (ZMod q)) ((reduction q p).map C) := by
  induction p with
  | nil => simp [Marking.polynomial,reduction,eval]
  | cons c cs ih => simp [Marking.polynomial,reduction,eval,ih]

private theorem mapped_eval_linear {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : S) (r prev : R) (p : List R) :
    eval x ((linear r prev p).map φ) = φ prev+(x-φ r)*eval x (p.map φ) := by
  induction p generalizing prev with
  | nil => simp [linear,eval]
  | cons a as ih => simp only [linear,List.map_cons,eval,ih,map_sub,map_mul]; ring

theorem mapped_eval_roots {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : S) (roots : List R) :
    eval x ((fromRoots roots).map φ) = (roots.map (fun r => x-φ r)).prod := by
  have go (rs p : List R) : eval x ((rs.foldl (fun q r => linear r 0 q) p).map φ) =
      (rs.map (fun r => x-φ r)).prod * eval x (p.map φ) := by
    induction rs generalizing p with
    | nil => simp
    | cons r rs ih =>
      simp only [List.foldl_cons,ih,mapped_eval_linear,map_zero,zero_add,List.map_cons,List.prod_cons]
      ring
  simpa [fromRoots,eval] using go roots [1]

theorem eval_scaled {R : Type*} [CommRing R] (x a : R) (p : List R) :
    eval x (p.map (a*·)) = a*eval x p := by
  induction p with
  | nil => simp [eval]
  | cons c cs ih => simp [eval,ih]; ring

private theorem local_first (d ell m c : ℕ) :
    (Marking.polynomial (localCoeffs d ell m c false)).map (Int.castRingHom (ZMod ell)) =
      C (c : ZMod ell) * ((wanted d ell m).map (fun r : ℕ => X-C (r : ZMod ell))).prod := by
  let φ := C.comp (Int.castRingHom (ZMod ell))
  let roots := (wanted d ell m).map Int.ofNat
  rw [polynomial_of_reduction]
  change eval X (((((fromRoots roots).map ((c:ℤ)*·)).map (fun a : ℤ => (a:ZMod ell))).map C)) = _
  have eq : (((fromRoots roots).map ((c:ℤ)*·)).map (fun a : ℤ => (a:ZMod ell))).map C =
      ((fromRoots roots).map φ).map ((C (c:ZMod ell))*·) := by simp [φ,List.map_map,Function.comp_def]
  rw [eq,eval_scaled,mapped_eval_roots]
  simp [roots,φ,List.map_map,Function.comp_def]

private theorem local_second {d : ℕ} (dp : 2 ≤ d) (ell m c : ℕ) :
    (Marking.polynomial (localCoeffs d ell m c true)).map (Int.castRingHom (ZMod ell)) =
      C (c:ZMod ell)*(X^d-X-C (missingShift d ell : ZMod ell)) := by
  ext i
  rw [coefficient_rep,coeff_C_mul,coeff_sub,coeff_sub,coeff_X_pow,coeff_X,coeff_C]
  by_cases le : i < d+1
  · simp [localCoeffs,List.getD_eq_getElem?_getD,le]
    split_ifs <;> try (exfalso; omega)
    all_goals simp
  · have out : d+1 ≤ i := by omega
    simp [localCoeffs,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa using out :
        (List.range (d+1)).length ≤ i),show i ≠ d by omega,show i ≠ 0 by omega, show (1:ℕ) ≠ i by omega]

theorem target_polynomials {n ell : ℕ} (hd : 2 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (u₀ u₁ v₀ v₁ : ℕ) :
    let p := construct n ell u₀ u₁ v₀ v₁
    let d := Fixed.d (n.log2+1)
    let c := C (leadingCoefficient n : ZMod ell)
    (Marking.polynomial p.first).map (Int.castRingHom (ZMod ell)) =
      c * ((wanted d ell (Fixed.rootBase n)).map (fun r : ℕ => X-C (r:ZMod ell))).prod ∧
    (Marking.polynomial p.second).map (Int.castRingHom (ZMod ell)) =
      c * (X^d-X-C (missingShift d ell : ZMod ell)) := by
  have h := constructed_target_residues target u₀ u₁ v₀ v₁
  have equal {p r : List ℤ} (hr : reduction ell p = reduction ell r) :
      (Marking.polynomial p).map (Int.castRingHom (ZMod ell)) =
        (Marking.polynomial r).map (Int.castRingHom (ZMod ell)) := by
    rw [polynomial_of_reduction,polynomial_of_reduction,hr]
  exact ⟨(equal h.1).trans (local_first ..),(equal h.2).trans (local_second hd ..)⟩

theorem leading_unit_at_target {n ell : ℕ} (hd : 3 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) :
    (leadingCoefficient n : ZMod ell) ≠ 0 := by
  have prime := (mem_dyadicTargets.mp target).1
  have greater := target_gt_degree target
  have two := Nat.prime_two.dvd_primorial_iff.mpr (show 2 ≤ Fixed.d (n.log2+1) by omega)
  have half := (target_primorial target).of_dvd_left (Nat.div_dvd_of_dvd two)
  have three : Nat.Coprime 3 ell := (Nat.coprime_primes Nat.prime_three prime).mpr (by omega)
  have cop : (leadingCoefficient n).Coprime ell := Nat.coprime_mul_iff_left.mpr ⟨half,three.pow_left _⟩
  exact fun zero => (prime.coprime_iff_not_dvd.mp cop.symm) ((ZMod.natCast_eq_zero_iff ..).mp zero)

/-- At the target prime the first polynomial has exactly d distinct roots,
    all away from m, while the second has no roots. -/
theorem target_roots {n ell : ℕ} (hd : 3 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (u₀ u₁ v₀ v₁ : ℕ) :
    letI : Fact ell.Prime := ⟨(mem_dyadicTargets.mp target).1⟩
    let p := construct n ell u₀ u₁ v₀ v₁
    let first := (Marking.polynomial p.first).map (Int.castRingHom (ZMod ell))
    let second := (Marking.polynomial p.second).map (Int.castRingHom (ZMod ell))
    first.roots.card = Fixed.d (n.log2+1) ∧ first.roots.Nodup ∧
      (Fixed.rootBase n : ZMod ell) ∉ first.roots ∧ ∀ x, second.eval x ≠ 0 := by
  let : Fact ell.Prime := ⟨(mem_dyadicTargets.mp target).1⟩
  let b := n.log2+1
  let d := Fixed.d b
  let m := Fixed.rootBase n
  let rs := wanted d ell m
  have ⟨len,unique,inRange⟩ := wanted_spec (target_gt_degree target) m
  have c0 := leading_unit_at_target hd target
  have ⟨first,second⟩ := target_polynomials (by omega : 2 ≤ Fixed.d (n.log2+1)) target u₀ u₁ v₀ v₁
  have roots : ((Marking.polynomial (construct n ell u₀ u₁ v₀ v₁).first).map (Int.castRingHom (ZMod ell))).roots =
      ((rs.map (fun r : ℕ => (r : ZMod ell)) : List (ZMod ell)) : Multiset (ZMod ell)) := by
    rw [first,roots_C_mul _ c0]
    simpa [rs,List.map_map,Function.comp_def] using roots_multiset_prod_X_sub_C
      ((rs.map (fun r : ℕ => (r : ZMod ell)) : List (ZMod ell)) : Multiset (ZMod ell))
  dsimp only
  rw [roots,second]
  refine ⟨by simpa [rs] using len,?_,?_,?_⟩
  · apply List.Nodup.map_on _ unique
    intro a ha b hb eq
    simpa [ZMod.val_natCast_of_lt (inRange a ha).1,ZMod.val_natCast_of_lt (inRange b hb).1] using congrArg ZMod.val eq
  · intro mem
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp mem
    have val := congrArg ZMod.val eq
    exact (inRange a ha).2 (by simpa [ZMod.val_natCast_of_lt (inRange a ha).1,ZMod.val_natCast] using val)
  · intro x
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X]
    exact mul_ne_zero c0 (sub_ne_zero.mpr ((missingShift_avoids (mem_dyadicTargets.mp target).1 (d := d)
      (by change 3 ≤ d at hd; omega)).2 x))

private theorem eval_at_base (p : List ℤ) (m ell : ℕ) :
    ((eval (m:ℤ) p : ℤ): ZMod ell) =
      ((Marking.polynomial p).map (Int.castRingHom (ZMod ell))).eval (m:ZMod ell) := by
  induction p with
  | nil => simp [eval,Marking.polynomial]
  | cons a as ih => simp [eval,Marking.polynomial,ih]

/-- The actual target survives the precomputed cofactor exclusion and the
    second filtering pass in the relation matrix constructor. -/
theorem target_in_base {n ell : ℕ} (hn : 2 ≤ n) (hd : 3 ≤ Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1))
      (Fixed.rootBase n) = Option.none) (u₀ u₁ v₀ v₁ : ℕ) :
    ell ∈ (TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)).base := by
  let b := n.log2+1
  let m := Fixed.rootBase n
  let P := construct n ell u₀ u₁ v₀ v₁
  let f := (Marking.polynomial P.first).map (Int.castRingHom (ZMod ell))
  let g := (Marking.polynomial P.second).map (Int.castRingHom (ZMod ell))
  have ⟨prime,lower,upper⟩ := mem_dyadicTargets.mp target
  let : Fact ell.Prime := ⟨prime⟩
  have ⟨card,_,notroot,nog⟩ := target_roots hd target u₀ u₁ v₀ v₁
  change f.roots.card = Fixed.d b at card
  change (m:ZMod ell) ∉ f.roots at notroot
  have fne : f ≠ 0 := by
    intro zero; rw [zero,roots_zero,Multiset.card_zero] at card
    change 3 ≤ Fixed.d b at hd; omega
  have m1 : f.eval (m:ZMod ell) ≠ 0 := fun root => notroot ((mem_roots fne).mpr root)
  have m2 : g.eval (m:ZMod ell) ≠ 0 := nog _
  have cop := surviving_coprime hn composite target none
  have shared := constructed_root hn cop u₀ u₁ v₀ v₁
  have keep (l : List ℤ) (div : (n:ℤ) ∣ eval (m:ℤ) l)
      (nz : ((Marking.polynomial l).map (Int.castRingHom (ZMod ell))).eval (m:ZMod ell) ≠ 0) :
      ¬ell ∣ ((eval (m:ℤ) l)/(n:ℤ)).natAbs := by
    intro h
    have dvd : (ell:ℤ) ∣ (eval (m:ℤ) l)/(n:ℤ) := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)
    apply nz
    rw [←eval_at_base,ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd.trans ⟨(n:ℤ),(Int.ediv_mul_cancel div).symm⟩
  have cofactor : ¬ell ∣ ((eval (m:ℤ) P.first)/(n:ℤ)).natAbs * ((eval (m:ℤ) P.second)/(n:ℤ)).natAbs :=
    fun h => (prime.dvd_mul.mp h).elim (keep P.first shared.1 m1) (keep P.second shared.2 m2)
  have bp : 2 ≤ Fixed.beta b := by
    have hp : 0 < Fixed.h b := Nat.mul_pos (Fixed.degree_pos (by simp [b])) (by simp [Fixed.z])
    unfold Fixed.beta; omega
  have square : Fixed.B b < ell^2 := by
    have bound := Nat.pow_le_pow_right (n := 2) (by decide) (show Fixed.beta b ≤ (Fixed.beta b-1)*2 by omega)
    rw [Nat.pow_mul] at bound
    exact bound.trans_lt (Nat.pow_lt_pow_left lower (by decide))
  have member : ell ∈ P.factorBase := by
    apply List.mem_filter.mpr
    have ep := prime.two_le
    refine ⟨List.mem_range'.mpr ⟨ell-2,by change ell-2 < Fixed.B b-1; change ell ≤ Fixed.B b at upper; omega,
      by have := prime.two_le; omega⟩,?_⟩
    simp only [decide_eq_true_eq]
    exact ⟨prime,square,by simpa only [P,construct,perturb_at_base,m,b] using cofactor⟩
  apply Marking.mem_base.mpr
  have c : ell.Coprime (leadingCoefficient n) := prime.coprime_iff_not_dvd.mpr
    (fun dvd => (leading_unit_at_target hd target) ((ZMod.natCast_eq_zero_iff ..).mpr dvd))
  exact ⟨member,prime,upper,Nat.coprime_mul_iff_right.mpr ⟨c,(Nat.coprime_mul_iff_left.mp cop).2⟩⟩

/-- Every target row produced by the actual Step 1 is on the first side,
    has nonzero derivative, and passes the cross-polynomial bad-row test. -/
theorem target_rows_clean {n ell : ℕ} (hd : 3 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (u₀ u₁ v₀ v₁ : ℕ) :
    let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
    ∀ row ∈ s.rows, row.q = ell → row.second = false ∧ row ∈ s.clean := by
  let : Fact ell.Prime := ⟨(mem_dyadicTargets.mp target).1⟩
  let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
  let f := (Marking.polynomial s.first).map (Int.castRingHom (ZMod ell))
  let g := (Marking.polynomial s.second).map (Int.castRingHom (ZMod ell))
  obtain ⟨card,nodup,_,nog⟩ := target_roots hd target u₀ u₁ v₀ v₁
  change f.roots.card = Fixed.d (n.log2+1) at card
  change f.roots.Nodup at nodup
  change ∀ x, g.eval x ≠ 0 at nog
  have fne : f ≠ 0 := by intro zero; rw [zero,roots_zero,Multiset.card_zero] at card; omega
  change ∀ row ∈ s.rows, row.q = ell → row.second = false ∧ row ∈ s.clean
  rintro ⟨second,q,r⟩ member key
  change q = ell at key
  subst q
  have atR := (Marking.mem_rows.mp member).2.2
  cases second with
  | true => exact False.elim ((nog (r:ZMod ell)) ((Polynomial.eval_map ..).trans atR))
  | false =>
    have root : f.IsRoot (r:ZMod ell) := (Polynomial.eval_map ..).trans atR
    have count : f.rootMultiplicity (r:ZMod ell) = 1 :=
      (f.count_roots.symm).trans (Multiset.count_eq_one_of_mem nodup ((mem_roots fne).mpr root))
    have derivative : ¬f.derivative.IsRoot (r:ZMod ell) := fun atD =>
      (by have := (one_lt_rootMultiplicity_iff_isRoot fne).mpr ⟨root,atD⟩; omega)
    refine ⟨rfl,Marking.mem_clean.mpr ⟨member,?_,?_⟩⟩
    · intro h
      apply derivative
      change f.derivative.eval (r:ZMod ell) = 0
      rw [show f.derivative = (Marking.polynomial s.first).derivative.map (Int.castRingHom (ZMod ell))
          from Polynomial.derivative_map ..,Polynomial.eval_map]
      exact h
    · exact fun h => nog (r:ZMod ell) ((Polynomial.eval_map ..).trans h)

/-- The row-count guard is an equality of lengths of the actual filtered
    relation rows and the root multiset of the first reduced polynomial. -/
theorem target_row_count {n ell : ℕ} (hn : 2 ≤ n) (hd : 3 ≤ Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1))
      (Fixed.rootBase n) = Option.none) (u₀ u₁ v₀ v₁ : ℕ) :
    let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
    (s.clean.filter (fun row => !row.second && row.q == ell)).length = s.degree := by
  classical
  let : Fact ell.Prime := ⟨(mem_dyadicTargets.mp target).1⟩
  let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
  let f := (Marking.polynomial s.first).map (Int.castRingHom (ZMod ell))
  let code := fun r : ZMod ell => Marking.Row.mk false ell r.val
  let rows := s.clean.filter (fun row => !row.second && row.q == ell)
  have base := target_in_base hn hd composite target none u₀ u₁ v₀ v₁
  obtain ⟨card,nodup,_,_⟩ := target_roots hd target u₀ u₁ v₀ v₁
  change f.roots.card = Fixed.d (n.log2+1) at card
  change f.roots.Nodup at nodup
  have fne : f ≠ 0 := by intro zero; rw [zero,roots_zero,Multiset.card_zero] at card; omega
  have un : rows.Nodup := ((List.nodup_dedup _).filter _).filter _
  have inj : Function.Injective code := by
    intro a b eq
    apply ZMod.val_injective
    exact congrArg Marking.Row.r eq
  have uniq : (f.roots.toList.map code).Nodup := List.Nodup.map inj (by change ((f.roots.toList : Multiset (ZMod ell))).Nodup; simpa using nodup)
  have eq : rows.Perm (f.roots.toList.map code) := by
    apply (List.perm_ext_iff_of_nodup un uniq).mpr
    rintro ⟨side,q,r⟩
    constructor
    · intro member
      obtain ⟨clean,pred⟩ := List.mem_filter.mp member
      obtain ⟨hside,hq⟩ : side = false ∧ q = ell := by simpa using pred
      subst side; subst q
      obtain ⟨_,range,atRoot⟩ := Marking.mem_rows.mp (Marking.mem_clean.mp clean).1
      have root : f.IsRoot (r:ZMod ell) := (Polynomial.eval_map ..).trans atRoot
      exact List.mem_map.mpr ⟨(r:ZMod ell),by simpa using (mem_roots fne).mpr root,
        by dsimp [code]; rw [ZMod.val_natCast_of_lt range]⟩
    · intro m
      obtain ⟨x,hx,eq⟩ := List.mem_map.mp m
      have root : f.IsRoot x := (mem_roots fne).mp (by simpa using hx)
      have atRoot : code x ∈ s.rows := Marking.mem_rows.mpr ⟨base,ZMod.val_lt _,by
        change (Marking.polynomial s.first).eval₂ _ (x.val:ZMod ell) = 0
        rw [ZMod.natCast_zmod_val,Polynomial.eval₂_eq_eval_map]; exact root⟩
      have clean := (target_rows_clean hd target u₀ u₁ v₀ v₁ (code x) atRoot rfl).2
      rw [←eq]
      exact List.mem_filter.mpr ⟨clean,by simp [code]⟩
  change rows.length = Fixed.d (n.log2+1)
  exact eq.length_eq.trans (by simpa using card)

/-- For all valid perturbations neither the input guard, the factor-base
    guard nor the target-row-count guard can make Step 1 reject the trial. -/
theorem stageOne_succeeds {n ell u₀ u₁ v₀ v₁ : ℕ} (hn : 2 ≤ n)
    (big : 130000 ≤ Fixed.d (n.log2+1)) (composite : ¬n.Prime)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1))
      (Fixed.rootBase n) = Option.none)
    (box : let b := n.log2+1
      u₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ u₁ ≤ 2*b^2*Fixed.U b ∧
      v₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ v₁ ≤ 2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
    ∃ out, Marking.stageOne s = some out := by
  let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
  have three : 3 ≤ Fixed.d (n.log2+1) := by omega
  have guard := box_inputGuard hn big composite target none box
  have base := target_in_base hn three composite target none u₀ u₁ v₀ v₁
  have count := target_row_count hn three composite target none u₀ u₁ v₀ v₁
  change ∃ out, Marking.stageOne s = some out
  unfold Marking.stageOne
  rw [if_pos ⟨guard,base,count⟩]
  exact ⟨_,rfl⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.target_roots
#print axioms Cogentic.Construction.target_in_base
#print axioms Cogentic.Construction.target_rows_clean

#print axioms Cogentic.Construction.stageOne_succeeds
