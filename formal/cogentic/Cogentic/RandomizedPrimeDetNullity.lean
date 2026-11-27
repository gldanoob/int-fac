import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Int.Basic

open scoped BigOperators Matrix

namespace Cogentic.RandomizedPrimeDetNullity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reduction of each matrix entry modulo p. -/
def modulo (p : ℕ) (A : Matrix ι ι ℤ) : Matrix ι ι (ZMod p) :=
  A.map (Int.castRingHom (ZMod p))

private theorem pow_card_dvd_of_columns (p : ℤ) (A : Matrix ι ι ℤ) (columns : Finset ι)
    (hcolumns : ∀ i j, j ∈ columns → p ∣ A i j) : p ^ columns.card ∣ A.det := by
  let scale : ι → ℤ := fun j => if j ∈ columns then p else 1
  let B : Matrix ι ι ℤ := fun i j => if j ∈ columns then A i j / p else A i j
  have hfac : B * Matrix.diagonal scale = A := by
    ext i j
    rw [Matrix.mul_diagonal]
    by_cases hj : j ∈ columns
    · simpa only [B, scale, if_pos hj] using Int.ediv_mul_cancel (hcolumns i j hj)
    · simp only [B, scale, if_neg hj, mul_one]
  have hdet : (Matrix.diagonal scale).det = p ^ columns.card := by
    rw [Matrix.det_diagonal]
    simp [scale]
  refine ⟨B.det, ?_⟩
  rw [← hfac, Matrix.det_mul, hdet, mul_comm]

/-- A k-element independent family in the kernel modulo p forces p^k to
divide the integral determinant. -/
theorem pow_dvd_det_of_independent_kernel {p k : ℕ} (hp : p.Prime) (A : Matrix ι ι ℤ)
    (v : Fin k → ι → ZMod p) (hind : LinearIndependent (ZMod p) v)
    (hker : ∀ t, modulo p A *ᵥ v t = 0) : (p : ℤ) ^ k ∣ A.det := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let original := Module.Basis.extend hind.linearIndepOn_id
  let std := Pi.basisFun (ZMod p) ι
  let e := original.indexEquiv std
  let basis := original.reindex e
  let index : Fin k ↪ ι :=
    ⟨fun t => e ⟨v t, hind.linearIndepOn_id.subset_extend _ ⟨t, rfl⟩⟩,
      fun _ _ h => hind.injective (congrArg Subtype.val (e.injective h))⟩
  have hindex (t : Fin k) : basis (index t) = v t := by
    rw [show basis = original.reindex e from rfl, Module.Basis.reindex_apply]
    change original (e.symm (e ⟨v t, hind.linearIndepOn_id.subset_extend _ ⟨t, rfl⟩⟩)) = v t
    rw [e.symm_apply_apply]
    exact Module.Basis.extend_apply_self _ _
  let B : Matrix ι ι (ZMod p) := std.toMatrix basis
  let C : Matrix ι ι ℤ := fun i j => (B i j).val
  have hcast : modulo p C = B := by
    ext i j
    change (((B i j).val : ℤ) : ZMod p) = B i j
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hBdet : B.det ≠ 0 := by
    have hprod : B * basis.toMatrix std = 1 := std.toMatrix_mul_toMatrix_flip basis
    have hdet := congrArg Matrix.det hprod
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact left_ne_zero_of_mul_eq_one hdet
  have hcoprime : IsCoprime (p : ℤ) C.det := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    change Nat.Coprime p C.det.natAbs
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd C.det p).mpr (Int.natCast_dvd.mpr h)
    have hdet := (Int.castRingHom (ZMod p)).map_det C
    change (C.det : ZMod p) = (modulo p C).det at hdet
    rw [hcast, hzero] at hdet
    exact hBdet hdet.symm
  let columns := Finset.univ.map index
  have hcolumns (i j : ι) (hj : j ∈ columns) : (p : ℤ) ∣ (A * C) i j := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hj
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    change modulo p (A * C) i (index t) = 0
    have hmap : modulo p (A * C) = modulo p A * B := by
      unfold modulo
      rw [Matrix.map_mul, show C.map (Int.castRingHom (ZMod p)) = B from hcast]
    rw [hmap]
    simpa only [Matrix.mul_apply, B, Module.Basis.toMatrix_apply, std, Pi.basisFun_repr,
      hindex, Matrix.mulVec, dotProduct, Pi.zero_apply] using congrFun (hker t) i
  have hdiv := pow_card_dvd_of_columns (p : ℤ) (A * C) columns hcolumns
  have hcard : columns.card = k := by simp [columns]
  rw [hcard, Matrix.det_mul, mul_comm] at hdiv
  exact hcoprime.pow_left.dvd_of_dvd_mul_left hdiv

/-- Two independent kernel vectors modulo a prime force its square to divide
the determinant. -/
theorem sq_dvd_det_of_two_independent_kernel {p : ℕ} (hp : p.Prime) (A : Matrix ι ι ℤ)
    (v : Fin 2 → ι → ZMod p) (hind : LinearIndependent (ZMod p) v)
    (hker : ∀ t, modulo p A *ᵥ v t = 0) : (p : ℤ) ^ 2 ∣ A.det :=
  pow_dvd_det_of_independent_kernel hp A v hind hker

/-- The dimension of the kernel modulo p is a lower bound on the p-adic
valuation of a nonzero determinant, expressed by divisibility. -/
theorem pow_finrank_ker_dvd_det {p : ℕ} (hp : p.Prime) (A : Matrix ι ι ℤ) :
    (p : ℤ) ^ Module.finrank (ZMod p) (LinearMap.ker (modulo p A).mulVecLin) ∣ A.det := by
  let : Fact p.Prime := ⟨hp⟩
  let K := LinearMap.ker (modulo p A).mulVecLin
  let b := Module.finBasis (ZMod p) K
  apply pow_dvd_det_of_independent_kernel hp A (K.subtype ∘ b)
  · exact b.linearIndependent.map' K.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  · intro i
    exact LinearMap.mem_ker.mp (b i).property

/-- A determinant divisible by p but not p^2 gives a one-dimensional
kernel modulo p. -/
theorem finrank_ker_eq_one_of_dvd_not_sq {p : ℕ} (hp : p.Prime) (A : Matrix ι ι ℤ)
    (hdiv : (p : ℤ) ∣ A.det) (hnot : ¬ (p : ℤ) ^ 2 ∣ A.det) :
    Module.finrank (ZMod p) (LinearMap.ker (modulo p A).mulVecLin) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let K := LinearMap.ker (modulo p A).mulVecLin
  have hdet : (modulo p A).det = 0 := by
    have hcast : (A.det : ZMod p) = (modulo p A).det :=
      (Int.castRingHom (ZMod p)).map_det A
    rw [← hcast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let w : K := ⟨v, LinearMap.mem_ker.mpr hker⟩
  have hw : w ≠ 0 := fun h => hv (congrArg (fun x : K => (x : ι → ZMod p)) h)
  have hpos : 0 < Module.finrank (ZMod p) K :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨w, hw⟩
  have hupper : Module.finrank (ZMod p) K ≤ 1 := by
    by_contra! hlarge
    exact hnot ((pow_dvd_pow (p : ℤ) (show 2 ≤ Module.finrank (ZMod p) K by omega)).trans
      (pow_finrank_ker_dvd_det hp A))
  exact Nat.le_antisymm hupper hpos

/-- Any given nonzero kernel vector spans the kernel when the determinant
is divisible by exactly one power of p. -/
theorem ker_eq_span_of_dvd_not_sq {p : ℕ} (hp : p.Prime) (A : Matrix ι ι ℤ)
    (hdiv : (p : ℤ) ∣ A.det) (hnot : ¬ (p : ℤ) ^ 2 ∣ A.det)
    {v : ι → ZMod p} (hv : v ≠ 0) (hker : modulo p A *ᵥ v = 0) :
    LinearMap.ker (modulo p A).mulVecLin = Submodule.span (ZMod p) {v} := by
  let : Fact p.Prime := ⟨hp⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact (Submodule.span_singleton_le_iff_mem v _).mpr (LinearMap.mem_ker.mpr hker)
  · rw [finrank_span_singleton hv, finrank_ker_eq_one_of_dvd_not_sq hp A hdiv hnot]

#print axioms pow_dvd_det_of_independent_kernel
#print axioms sq_dvd_det_of_two_independent_kernel
#print axioms pow_finrank_ker_dvd_det
#print axioms finrank_ker_eq_one_of_dvd_not_sq
#print axioms ker_eq_span_of_dvd_not_sq

end Cogentic.RandomizedPrimeDetNullity
