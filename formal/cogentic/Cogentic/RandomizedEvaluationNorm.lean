import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Norm.Basic

/-! An evaluation that kills an element also kills its finite free algebra norm. -/

namespace Cogentic.RandomizedEvaluationNorm

open Polynomial

/-- Apply the evaluation map to Cayley–Hamilton for left multiplication.
The characteristic polynomial then evaluates at zero, leaving its constant term. -/
theorem map_norm_eq_zero_of_map_eq_zero {R A B : Type*}
    [CommRing R] [Ring A] [Ring B] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (ψ : A →+* B) (z : A) (hz : ψ z = 0) :
    (ψ.comp (algebraMap R A)) (Algebra.norm R z) = 0 := by
  have h := congrArg ψ (Algebra.aeval_self_charpoly_lmul (R := R) z)
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hz, Polynomial.eval₂_at_zero,
    map_zero] at h
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul, h, mul_zero]

variable {A : Type*} [Ring A]
variable [freeA : Module.Free ℤ A] [finiteA : Module.Finite ℤ A]
include freeA finiteA
variable {N : ℕ}

/-- A modular evaluation that kills an element forces divisibility of its algebra norm. -/
theorem dvd_norm_of_eval_eq_zero (ψ : A →+* ZMod N) (z : A) (hz : ψ z = 0) :
    (N : ℤ) ∣ Algebra.norm ℤ z := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa [RingHom.comp_apply, algebraMap_int_eq] using map_norm_eq_zero_of_map_eq_zero (R := ℤ) ψ z hz

/-- A nonzero norm killed by evaluation has absolute value at least the modulus. -/
theorem le_natAbs_norm_of_eval_eq_zero (ψ : A →+* ZMod N) (z : A)
    (hz : ψ z = 0) (hne : Algebra.norm ℤ z ≠ 0) :
    N ≤ (Algebra.norm ℤ z).natAbs := by
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hne)
    (Int.natCast_dvd.mp (dvd_norm_of_eval_eq_zero ψ z hz))

/-- In a finite free domain, distinct elements with a common evaluation give a norm
of their difference at least as large as the modulus. -/
theorem le_natAbs_norm_sub_of_eval_eq [IsDomain A] (ψ : A →+* ZMod N)
    {x y : A} (hxy : x ≠ y) (he : ψ x = ψ y) :
    N ≤ (Algebra.norm ℤ (x - y)).natAbs :=
  le_natAbs_norm_of_eval_eq_zero ψ (x - y) (by rw [map_sub, he, sub_self])
    (Algebra.norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))

end Cogentic.RandomizedEvaluationNorm
