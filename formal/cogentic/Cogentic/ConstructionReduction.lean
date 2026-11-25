import Cogentic.BinaryIrreducible
import Cogentic.ConstructionHeight
import Mathlib.RingTheory.Polynomial.GaussLemma

namespace Cogentic.Construction

open Polynomial

def reduction (q : ℕ) (p : List ℤ) : List (ZMod q) := p.map (fun a : ℤ => (a : ZMod q))

private theorem reduce_correctLower {q step : ℕ} (zero : (step : ZMod q) = 0) (m t : ℕ) (p : List ℤ) :
    reduction q (correctLower m step t p) = reduction q p := by
  induction p generalizing t with
  | nil => rfl
  | cons a as ih =>
    simp only [correctLower,reduction,List.map_cons,Int.cast_sub,Int.cast_mul,Int.cast_natCast,zero,
      zero_mul,sub_zero,List.cons.injEq,true_and]
    exact ih _

private theorem reduce_perturb {q step : ℕ} (zero : (step : ZMod q) = 0) (m a z : ℕ) (p : List ℤ) :
    reduction q (perturb step m a z p) = reduction q p := by
  rcases p with _ | ⟨x,xs⟩
  · rfl
  rcases xs with _ | ⟨y,ys⟩
  · rfl
  rcases ys with _ | ⟨w,ws⟩
  · rfl
  simp [perturb,reduction,zero]

theorem reduce_final {q step : ℕ} (dvd : q ∣ step) (m n leading a z : ℕ) (low : List ℤ) :
    reduction q (perturb step m a z (corrected n m step leading low)) =
      reduction q low ++ [(leading : ZMod q)] := by
  have zero := (ZMod.natCast_eq_zero_iff ..).mpr dvd
  rw [reduce_perturb zero]
  simp only [corrected,reduction,List.map_append,List.map_singleton,Int.cast_natCast]
  rw [show ∀ t, List.map (fun a : ℤ => (a : ZMod q)) (correctLower m step t low) = reduction q low
    from fun t => reduce_correctLower zero m t low]
  rfl

theorem primorial_half_odd {d : ℕ} (hd : 2 ≤ d) : Odd (primorial d/2) := by
  let s := Nat.primesLE d
  have mem : 2 ∈ s := Nat.mem_primesLE.mpr ⟨hd,Nat.prime_two⟩
  have prod := Finset.prod_erase_mul (s := s) (fun p : ℕ => p) mem
  have eq : (∏ p ∈ s.erase 2, p) = primorial d/2 := by
    rw [primorial_eq_prod_primesLE,←prod,Nat.mul_div_cancel _ (by decide)]
  rw [←eq,←Nat.coprime_two_left,Nat.coprime_prod_right_iff]
  intro p hp
  have prime := Nat.prime_of_mem_primesLE (Finset.mem_erase.mp hp).2
  exact (Nat.coprime_primes Nat.prime_two prime).mpr (Finset.mem_erase.mp hp).1.symm

theorem target_gt_degree {n ell : ℕ} (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) :
    Fixed.d (n.log2+1) < ell := by
  let b := n.log2+1
  have dp := Fixed.degree_pos (b := b) (by simp [b])
  have dsmall : Fixed.d b ≤ Fixed.h b := Nat.le_mul_of_pos_right _ (by simp [Fixed.z])
  have exp : Fixed.d b ≤ Fixed.beta b-1 := by unfold Fixed.beta; omega
  have lower := (mem_dyadicTargets.mp target).2.1
  exact (Nat.lt_two_pow_self (n := Fixed.d b)).le.trans_lt
    ((Nat.pow_le_pow_right (by decide) exp).trans_lt lower)

theorem target_primorial {n ell : ℕ} (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) :
    (primorial (Fixed.d (n.log2+1))).Coprime ell := by
  have prime := (mem_dyadicTargets.mp target).1
  exact (prime.coprime_iff_not_dvd.mpr (fun divides =>
    (target_gt_degree target).not_ge (prime.dvd_primorial_iff.mp divides))).symm

theorem reduce_nearest {step q : ℕ} (dvd : q ∣ step) (res : ℕ) (target : ℚ) :
    ((nearest step res target : ℤ) : ZMod q) = res := by
  have zero := (ZMod.natCast_eq_zero_iff ..).mpr dvd
  simp [nearest,zero]

private theorem low_binary {d P ell : ℕ} (half : Nat.Coprime 2 (P/2)) (even : 2 ∣ P)
    (cop : P.Coprime ell) (A m leading : ℕ) (second : Bool) :
    reduction 2 (preliminary d A m P ell leading second) =
      (List.range d).map (fun j => (bitCoeff (binaryMask d) j : ZMod 2)) := by
  unfold reduction preliminary
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  dsimp only [Function.comp_apply]
  rw [reduce_nearest (even.trans (dvd_mul_right P ell))]
  apply (ZMod.natCast_eq_natCast_iff ..).mpr
  exact (((crt_spec cop _ _).1).of_dvd even).trans (crt_spec half _ _).1

theorem coefficient_rep {R : Type*} [CommRing R] (p : List ℤ) (j : ℕ) :
    ((Marking.polynomial p).map (Int.castRingHom R)).coeff j = ((p.getD j 0 : ℤ) : R) := by
  have integer (p : List ℤ) (j : ℕ) : (Marking.polynomial p).coeff j = p.getD j 0 := by
    induction p generalizing j with
    | nil => simp [Marking.polynomial]
    | cons c cs ih =>
      cases j with
      | zero => simp [Marking.polynomial]
      | succ j => rw [Marking.polynomial,coeff_add,coeff_C,coeff_X_mul,if_neg (by omega),zero_add,ih]; rfl
  rw [coeff_map,integer]; rfl

private theorem represented {p : List ℤ} {d a : ℕ}
    (red : reduction 2 p = (List.range d).map (fun j => (bitCoeff a j : ZMod 2)) ++ [1]) :
    (Marking.polynomial p).map (Int.castRingHom (ZMod 2)) = binaryPoly d a := by
  ext j
  rw [coefficient_rep]
  have r := congrArg (fun ls : List (ZMod 2) => ls.getD j 0) red
  have val : ((p.getD j 0 : ℤ) : ZMod 2) = (reduction 2 p).getD j 0 := by
    simp only [reduction,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases p[j]? <;> simp
  rw [val,r]
  rcases lt_trichotomy j d with h | rfl | h
  · rw [binaryPoly_coeff_lt _ h]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append,h]
  · have mon := (binaryPoly_monic j a).coeff_natDegree
    simp only [binaryPoly_degree] at mon
    simp [List.getD_eq_getElem?_getD,mon]
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [binaryPoly_degree])]
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa using h : ((List.range d).map (fun j => (bitCoeff a j : ZMod 2)) ++ [1]).length ≤ j)]
    rfl

/-- Reduction modulo two of either final polynomial is the irreducible selected
    by the genuine binary factor test. The statement covers every perturbation. -/
theorem constructed_mod_two {n ell : ℕ}
    (hd : 2 ≤ Fixed.d (n.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (u₀ u₁ v₀ v₁ : ℕ) :
    let p := construct n ell u₀ u₁ v₀ v₁
    let d := Fixed.d (n.log2+1)
    (Marking.polynomial p.first).map (Int.castRingHom (ZMod 2)) = binaryPoly d (binaryMask d) ∧
      (Marking.polynomial p.second).map (Int.castRingHom (ZMod 2)) = binaryPoly d (binaryMask d) := by
  let b := n.log2+1
  let d := Fixed.d b
  let P := primorial d
  have odd := primorial_half_odd hd
  have even : 2 ∣ P := Nat.prime_two.dvd_primorial_iff.mpr hd
  have c1 : (leadingCoefficient n : ZMod 2) = 1 := by
    apply ZMod.natCast_eq_one_iff_odd.mpr
    exact odd.mul ((by decide : Odd (3:ℕ)).pow)
  have side (second : Bool) (z w : ℕ) : (Marking.polynomial
      (perturb (P*ell) (Fixed.rootBase n) z w (corrected n (Fixed.rootBase n) (P*ell)
          (leadingCoefficient n) (preliminary d (Fixed.A b) (Fixed.rootBase n) P ell (leadingCoefficient n) second)))
      ).map (Int.castRingHom (ZMod 2)) = binaryPoly d (binaryMask d) := by
    have red := reduce_final (even.trans (dvd_mul_right P ell)) (Fixed.rootBase n) n
      (leadingCoefficient n) z w (preliminary d (Fixed.A b) (Fixed.rootBase n) P ell (leadingCoefficient n) second)
    rw [low_binary odd.coprime_two_left even (target_primorial target),c1] at red
    exact represented red
  exact ⟨side false u₀ u₁,side true v₀ v₁⟩

private theorem primitive_irreducible_from_mod_two {p : Polynomial ℤ} (hp : p.IsPrimitive)
    (irred : Irreducible (p.map (Int.castRingHom (ZMod 2))))
    (deg : (p.map (Int.castRingHom (ZMod 2))).natDegree = p.natDegree) : Irreducible p := by
  let φ := Int.castRingHom (ZMod 2)
  refine ⟨fun unit => irred.not_isUnit (unit.map (mapRingHom φ)),?_⟩
  intro f g eq
  have image : p.map φ = f.map φ*g.map φ := by rw [eq,Polynomial.map_mul]
  have nz : f.map φ ≠ 0 ∧ g.map φ ≠ 0 := mul_ne_zero_iff.mp (image ▸ irred.ne_zero)
  have fg : f ≠ 0 ∧ g ≠ 0 := mul_ne_zero_iff.mp (eq ▸ hp.ne_zero)
  have sum := congrArg natDegree image
  rw [natDegree_mul nz.1 nz.2] at sum
  change (p.map φ).natDegree = p.natDegree at deg
  have sumInt := congrArg natDegree eq
  rw [natDegree_mul fg.1 fg.2] at sumInt
  have smallF : (f.map φ).natDegree ≤ f.natDegree := natDegree_map_le
  have smallG : (g.map φ).natDegree ≤ g.natDegree := natDegree_map_le
  have constant (a : Polynomial ℤ) (dv : a ∣ p) (d : a.natDegree = 0) : IsUnit a := by
    have ca := eq_C_of_natDegree_eq_zero d
    exact ca ▸ isUnit_C.mpr (hp _ (ca ▸ dv))
  rcases irred.isUnit_or_isUnit image with f0 | g0
  · have := natDegree_eq_zero_of_isUnit f0
    exact Or.inl (constant _ (eq ▸ dvd_mul_right ..) (by omega))
  · have := natDegree_eq_zero_of_isUnit g0
    exact Or.inr (constant _ (eq ▸ dvd_mul_left ..) (by omega))

/-- A degree-preserving irreducible reduction certifies rational irreducibility,
    including integer polynomials with nontrivial content. -/
theorem rational_irreducible_of_binary {p : Polynomial ℤ}
    (irred : Irreducible (p.map (Int.castRingHom (ZMod 2))))
    (deg : (p.map (Int.castRingHom (ZMod 2))).natDegree = p.natDegree) :
    Irreducible (p.map (Int.castRingHom ℚ)) := by
  let φ := Int.castRingHom (ZMod 2)
  have split (R : Type) [CommRing R] : p.map (Int.castRingHom R) =
      C (p.content : R) * p.primPart.map (Int.castRingHom R) := by
    calc p.map _ = (C p.content*p.primPart).map (Int.castRingHom R) :=
          congrArg (Polynomial.map _) p.eq_C_content_mul_primPart
         _ = _ := by rw [Polynomial.map_mul,map_C]; rfl
  have residue : (p.content : ZMod 2) ≠ 0 := by
    intro h
    exact irred.ne_zero (by rw [split (ZMod 2),h,map_zero,zero_mul])
  have cnz : p.content ≠ 0 := fun zero => residue (by simp [zero])
  have cQ : (p.content : ℚ) ≠ 0 := by exact_mod_cast cnz
  have ppIrred : Irreducible (p.primPart.map φ) :=
    (irreducible_isUnit_mul (isUnit_C.mpr residue.isUnit)).mp ((split (ZMod 2)) ▸ irred)
  have ppDegree : (p.primPart.map φ).natDegree = p.primPart.natDegree := by
    rw [p.natDegree_primPart,←deg,split (ZMod 2),natDegree_C_mul residue]
  have pp := primitive_irreducible_from_mod_two p.isPrimitive_primPart ppIrred ppDegree
  rw [split ℚ,irreducible_isUnit_mul (isUnit_C.mpr cQ.isUnit)]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast p.isPrimitive_primPart).mp pp

private theorem length_degree (p : List ℤ) (d : ℕ) (len : p.length = d+1) :
    (Marking.polynomial p).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have eq := coefficient_rep (R := ℤ) p j
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : p.length ≤ j)] using eq

/-- Both actual field polynomials are of the requested degree and irreducible
    over the rationals for every perturbation and every target. -/
theorem constructed_rational_fields {n ell : ℕ}
    (hd : 3 ≤ Fixed.d (n.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (u₀ u₁ v₀ v₁ : ℕ) :
    let p := construct n ell u₀ u₁ v₀ v₁
    let d := Fixed.d (n.log2+1)
    ((Marking.polynomial p.first).natDegree = d ∧ Irreducible ((Marking.polynomial p.first).map (Int.castRingHom ℚ))) ∧
    ((Marking.polynomial p.second).natDegree = d ∧ Irreducible ((Marking.polynomial p.second).map (Int.castRingHom ℚ))) := by
  let d := Fixed.d (n.log2+1)
  have red := constructed_mod_two (by omega : 2 ≤ Fixed.d (n.log2+1)) target u₀ u₁ v₀ v₁
  have side (p : List ℤ) (len : p.length = d+1)
      (eq : (Marking.polynomial p).map (Int.castRingHom (ZMod 2)) = binaryPoly d (binaryMask d)) :
      (Marking.polynomial p).natDegree = d ∧ Irreducible ((Marking.polynomial p).map (Int.castRingHom ℚ)) := by
    have bin := congrArg natDegree eq
    rw [binaryPoly_degree] at bin
    have degree := (length_degree _ _ len).antisymm (bin ▸ natDegree_map_le)
    exact ⟨degree,rational_irreducible_of_binary (eq ▸ (binaryMask_irreducible (by change 3 ≤ d at hd; omega)).2)
      (bin.trans degree.symm)⟩
  exact ⟨side _ (shape (ell := ell) hd false u₀ u₁).1 red.1,
    side _ (shape (ell := ell) hd true v₀ v₁).1 red.2⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.constructed_rational_fields
