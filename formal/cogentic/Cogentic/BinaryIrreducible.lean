import Cogentic.Construction
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Data.Nat.Bitwise

namespace Cogentic.Construction

open Polynomial

/-- The binary polynomial encoded by one lower-coefficient mask. -/
noncomputable def binaryPoly (d a : ℕ) : Polynomial (ZMod 2) :=
  X^d + ofFn d (fun i => (bitCoeff a i : ZMod 2))

theorem binaryPoly_monic (d a : ℕ) : (binaryPoly d a).Monic :=
  monic_X_pow_add (ofFn_degree_lt _)

theorem binaryPoly_degree (d a : ℕ) : (binaryPoly d a).natDegree = d := by
  unfold binaryPoly
  rw [natDegree_add_eq_left_of_degree_lt (by simpa using ofFn_degree_lt _),natDegree_X_pow]

theorem binaryPoly_coeff_lt {d i : ℕ} (a : ℕ) (lt : i < d) :
    (binaryPoly d a).coeff i = (bitCoeff a i : ZMod 2) := by
  simp [binaryPoly,coeff_X_pow,lt.ne,ofFn_coeff_eq_val_of_lt _ lt]

private theorem binaryPoly_coeff {d a : ℕ} (ha : a < 2^d) (i : ℕ) :
    (binaryPoly d a).coeff i = (bitCoeff (2^d+a) i : ZMod 2) := by
  rcases lt_trichotomy i d with h | rfl | h
  · rw [binaryPoly_coeff_lt a h]; simp [bitCoeff,Nat.testBit_two_pow_add_gt h]
  · rw [show (binaryPoly i a).coeff i = 1 by simpa only [binaryPoly_degree] using (binaryPoly_monic i a).coeff_natDegree]
    simp [bitCoeff,Nat.testBit_two_pow_add_eq,Nat.testBit_eq_false_of_lt ha]
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [binaryPoly_degree])]
    have big : 2^d+a < 2^i := (show 2^d+a < 2^(d+1) by rw [Nat.pow_succ]; omega).trans_le
      (Nat.pow_le_pow_right (by decide) h)
    simp [bitCoeff,Nat.testBit_eq_false_of_lt big]

private theorem all_masks (d : ℕ) (v : ℕ → ZMod 2) :
    ∃ a < 2^d, ∀ i < d, (bitCoeff a i : ZMod 2) = v i := by
  induction d with
  | zero => exact ⟨0,by decide,by simp⟩
  | succ d ih =>
    obtain ⟨a,ha,mem⟩ := ih
    have bits (z : ZMod 2) : z = 0 ∨ z = 1 := by
      have hv : z.val = 0 ∨ z.val = 1 := by have := ZMod.val_lt z; omega
      rcases hv with hz | hz
      · left; simpa [hz] using (ZMod.natCast_zmod_val z).symm
      · right; simpa [hz] using (ZMod.natCast_zmod_val z).symm
    rcases bits (v d) with z | o
    · refine ⟨a,by rw [Nat.pow_succ]; omega,fun i hi => ?_⟩
      by_cases id : i = d
      · subst i; simp [bitCoeff,Nat.testBit_eq_false_of_lt ha,z]
      · exact mem _ (by omega)
    · refine ⟨2^d+a,by rw [Nat.pow_succ]; omega,fun i hi => ?_⟩
      by_cases id : i = d
      · subst i; simp [bitCoeff,Nat.testBit_two_pow_add_eq,Nat.testBit_eq_false_of_lt ha,o]
      · have lt : i < d := by omega
        simpa [bitCoeff,Nat.testBit_two_pow_add_gt lt] using mem i lt

private theorem monic_repr {p : Polynomial (ZMod 2)} (mon : p.Monic) :
    ∃ a < 2^p.natDegree, binaryPoly p.natDegree a = p := by
  obtain ⟨a,ha,bits⟩ := all_masks p.natDegree p.coeff
  refine ⟨a,ha,?_⟩
  ext i
  rcases lt_trichotomy i p.natDegree with h | rfl | h
  · exact (binaryPoly_coeff_lt _ h).trans (bits _ h)
  · rw [mon.coeff_natDegree]; simpa only [binaryPoly_degree] using (binaryPoly_monic p.natDegree a).coeff_natDegree
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [binaryPoly_degree]),coeff_eq_zero_of_natDegree_lt h]

private theorem primePolynomial_exists {d : ℕ} (pos : 0 < d) :
    ∃ p : Polynomial (ZMod 2), p.Monic ∧ p.natDegree = d ∧ Irreducible p := by
  let F := ZMod 2
  let K := GaloisField 2 d
  let base := Field.powerBasisOfFiniteOfSeparable F K
  have integral := Algebra.IsIntegral.isIntegral (R := F) base.gen
  exact ⟨minpoly F base.gen, minpoly.monic integral,
    base.natDegree_minpoly.trans (base.finrank.symm.trans (GaloisField.finrank 2 pos.ne')),
    minpoly.irreducible integral⟩

private theorem test_coeff {k l a b mask i : ℕ} (ha : a < 2^k) (hb : b < 2^l) (hi : i < k+l) :
    ((Finset.range (i+1)).sum (fun j =>
      bitCoeff (2^k+a) j * bitCoeff (2^l+b) (i-j)))%2 = bitCoeff mask i ↔
      (binaryPoly k a*binaryPoly l b).coeff i = (binaryPoly (k+l) mask).coeff i := by
  rw [binaryPoly_coeff_lt _ hi,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [binaryPoly_coeff ha,binaryPoly_coeff hb,←Nat.cast_mul,←Nat.cast_sum]
  rw [ZMod.natCast_eq_natCast_iff]
  unfold Nat.ModEq
  have small : bitCoeff mask i < 2 := by unfold bitCoeff; cases mask.testBit i <;> decide
  simp [Nat.mod_eq_of_lt small]

private theorem same_monic_of_lower {p q : Polynomial (ZMod 2)} {d : ℕ}
    (mp : p.Monic) (mq : q.Monic) (dp : p.natDegree = d) (dq : q.natDegree = d)
    (lower : ∀ i < d, p.coeff i = q.coeff i) : p = q := by
  ext i
  rcases lt_trichotomy i d with h | rfl | h
  · exact lower i h
  · exact (dp ▸ mp.coeff_natDegree).trans (dq ▸ mq.coeff_natDegree).symm
  · rw [coeff_eq_zero_of_natDegree_lt (dp.trans_lt h),coeff_eq_zero_of_natDegree_lt (dq.trans_lt h)]

private theorem factor_test {d mask : ℕ} :
    hasBinaryFactor d mask = true ↔
      ∃ k, 0 < k ∧ k < d ∧ ∃ a < 2^k, ∃ b < 2^(d-k),
        binaryPoly k a * binaryPoly (d-k) b = binaryPoly d mask := by
  unfold hasBinaryFactor
  simp only [List.any_eq_true,List.mem_range',List.mem_range,List.all_eq_true,beq_iff_eq]
  constructor
  · rintro ⟨k,ks,a,ha,b,hb,test⟩
    have kp : 0 < k := by omega
    have kd : k < d := by omega
    have eq : k+(d-k) = d := by omega
    refine ⟨k,kp,kd,a,ha,b,hb,same_monic_of_lower ((binaryPoly_monic ..).mul (binaryPoly_monic ..))
      (binaryPoly_monic ..) (by rw [natDegree_mul (binaryPoly_monic ..).ne_zero (binaryPoly_monic ..).ne_zero,
        binaryPoly_degree,binaryPoly_degree,eq]) (binaryPoly_degree ..) ?_⟩
    intro i hi
    simpa only [eq] using ((test_coeff (mask := mask) ha hb (show i < k+(d-k) by omega)).mp (test i hi))
  · rintro ⟨k,hk,kd,a,ha,b,hb,eq⟩
    have sum : k+(d-k) = d := by omega
    refine ⟨k,⟨k-1,by omega,by omega⟩,a,ha,b,hb,fun i hi => ?_⟩
    apply (test_coeff (mask := mask) ha hb (show i < k+(d-k) by omega)).mpr
    rw [sum,eq]

theorem hasBinaryFactor_iff {d mask : ℕ} (dp : 0 < d) :
    hasBinaryFactor d mask = false ↔ Irreducible (binaryPoly d mask) := by
  rw [(binaryPoly_monic ..).irreducible_iff_natDegree]
  have ne : binaryPoly d mask ≠ 1 := fun eq => by
    have deg := congrArg natDegree eq
    simp only [binaryPoly_degree,natDegree_one] at deg
    omega
  refine ⟨fun no => ⟨ne,?_⟩,?_⟩
  · intro f g fm gm prod
    by_contra! nonzero
    obtain ⟨a,ha,fa⟩ := monic_repr fm
    obtain ⟨b,hb,gb⟩ := monic_repr gm
    have degrees := congrArg natDegree prod
    rw [natDegree_mul fm.ne_zero gm.ne_zero,binaryPoly_degree] at degrees
    have matchdeg : d-f.natDegree = g.natDegree := by omega
    have yes := (factor_test (d := d) (mask := mask)).mpr
      ⟨f.natDegree,by omega,by omega,a,ha,b,matchdeg ▸ hb,by rw [matchdeg,fa,gb,prod]⟩
    simp [no] at yes
  · rintro ⟨_,prime⟩
    by_contra! h
    obtain ⟨k,hp,lt,a,_,b,_,prod⟩ := factor_test.mp (Bool.eq_true_of_not_eq_false h)
    have degrees := prime _ _ (binaryPoly_monic ..) (binaryPoly_monic ..) prod
    simp only [binaryPoly_degree] at degrees
    omega

/-- The actual finite enumeration terminates with an irreducible monic polynomial
    of the required degree, for every positive degree. -/
theorem binaryMask_irreducible {d : ℕ} (dp : 0 < d) :
    binaryMask d < 2^d ∧ Irreducible (binaryPoly d (binaryMask d)) := by
  obtain ⟨p,mon,deg,irred⟩ := primePolynomial_exists dp
  obtain ⟨a,ha,repr⟩ := monic_repr mon
  rw [deg] at ha repr
  have witness : hasBinaryFactor d a = false := (hasBinaryFactor_iff dp).mpr (repr ▸ irred)
  have found : ((List.range (2^d)).find? (fun mask => !(hasBinaryFactor d mask))).isSome :=
    List.find?_isSome.mpr ⟨a,List.mem_range.mpr ha,by simp [witness]⟩
  unfold binaryMask
  cases eq : (List.range (2^d)).find? (fun mask => !(hasBinaryFactor d mask)) with
  | none => simp [eq] at found
  | some out =>
    have good := List.find?_some eq
    exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some eq),
      (hasBinaryFactor_iff dp).mp (by simpa using good)⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.binaryMask_irreducible
