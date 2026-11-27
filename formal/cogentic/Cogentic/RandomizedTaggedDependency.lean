import Cogentic.RandomizedGramRank
import Cogentic.RandomizedSingularProbe
import Cogentic.RandomizedTaggedKernel
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Projection

/-! Tagged binary extraction from a finite projected Krylov recurrence. -/

namespace Cogentic.RandomizedTaggedDependency

open Polynomial
open Cogentic.Randomized
open Cogentic.RandomizedGramMinor Cogentic.RandomizedGramRank
open Cogentic.RandomizedKrylovProbe Cogentic.RandomizedSparseDependency Cogentic.RandomizedSingularProbe

section BinaryDescent

variable {K Row Col Tag BasisIndex : Type*} [Field K] [Algebra (ZMod 2) K] [Fintype Col]

/-- Applying a base-linear coordinate to one row commutes with binary matrix action. -/
theorem project_mulVec_apply (A : Matrix Row Col (ZMod 2)) (v : Col → K)
    (project : K →ₗ[ZMod 2] ZMod 2) (i : Row) :
    project ((A.map (algebraMap (ZMod 2) K)).mulVec v i) =
      A.mulVec (fun j => project (v j)) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, ← Algebra.smul_def, map_sum,
    map_smul, smul_eq_mul]

/-- Choosing a nonzero coordinate of the extension-field tag preserves a nonzero
    binary tag as well as all original kernel constraints. -/
theorem exists_tagged_binary_coordinate
    (M : Matrix Row Col (ZMod 2)) (H : Matrix Tag Col (ZMod 2))
    (b : Module.Basis BasisIndex (ZMod 2) K) (v : Col → K)
    (hv : (M.map (algebraMap (ZMod 2) K)).mulVec v = 0)
    (hTag : (H.map (algebraMap (ZMod 2) K)).mulVec v ≠ 0) :
    ∃ bit : BasisIndex, M.mulVec (fun j => b.coord bit (v j)) = 0 ∧
      H.mulVec (fun j => b.coord bit (v j)) ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hTag
  change (H.map (algebraMap (ZMod 2) K)).mulVec v i ≠ 0 at hi
  obtain ⟨bit, hbit⟩ := not_forall.mp (mt b.forall_coord_eq_zero_iff.mp hi)
  refine ⟨bit, project_mulVec M v (b.coord bit) hv, ?_⟩
  intro hzero
  exact hbit ((project_mulVec_apply H v (b.coord bit) i).trans (congrFun hzero i))

/-- A tagged binary witness also supplies a tagged extension-field kernel vector. -/
theorem exists_tagged_extension_kernel
    (M : Matrix Row Col (ZMod 2)) (H : Matrix Tag Col (ZMod 2))
    (h : ∃ w : Col → ZMod 2, M.mulVec w = 0 ∧ H.mulVec w ≠ 0) :
    ∃ v ∈ (M.map (algebraMap (ZMod 2) K)).mulVecLin.ker,
      (H.map (algebraMap (ZMod 2) K)).mulVec v ≠ 0 := by
  obtain ⟨w, hM, hH⟩ := h
  let f := algebraMap (ZMod 2) K
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨f ∘ w, LinearMap.mem_ker.mpr ?_, ?_⟩
  · funext i
    change (M.map f).mulVec (f ∘ w) i = 0
    rw [← RingHom.map_mulVec, congrFun hM i, Pi.zero_apply, map_zero]
  · intro hz
    apply hH
    funext i
    apply f.injective
    change f (H.mulVec w i) = f (0 : ZMod 2)
    rw [RingHom.map_mulVec, congrFun hz i, Pi.zero_apply, map_zero]

end BinaryDescent

section StartCount

open Cogentic.RandomizedProbeCount

variable {K Col Tag : Type*} [Field K] [Algebra (ZMod 2) K] [DecidableEq K] [Fintype K]
variable [Fintype Col] [DecidableEq Col] [Fintype Tag]

omit [Algebra (ZMod 2) K] in
private theorem card_zeros_of_nonzero_tag
    (L : (Col → K) →ₗ[K] (Tag → K)) (hL : L ≠ 0) :
    (Finset.univ.filter fun x => L x = 0).card ≤
      Fintype.card K ^ (Fintype.card Col - 1) := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hL
  change L x ≠ 0 at hx
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  let f : (Col → K) →ₗ[K] K := (LinearMap.proj i).comp L
  have hf : f ≠ 0 := fun h => hi (LinearMap.congr_fun h x)
  let e := dotProductEquiv K Col
  let w := e.symm f
  have hw : w ≠ 0 := by
    intro h
    apply hf
    rw [← e.apply_symm_apply f, ← show w = e.symm f from rfl, h, map_zero]
  have hsubset : (Finset.univ.filter fun x => L x = 0) ⊆
      (Finset.univ.filter fun x => w ⬝ᵥ x = 0) := by
    intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change e w v = 0
    rw [e.apply_symm_apply f]
    exact congrFun (Finset.mem_filter.mp hv).2 i
  refine (Finset.card_le_card hsubset).trans (le_of_eq ?_)
  rw [← Fintype.card_subtype]
  exact card_probe_fiber_of_nonzero w hw 0

/-- Starting vectors whose projection to the kernel has zero tag. -/
noncomputable def badTaggedStarts (S : Module.End K (Col → K))
    (H : Matrix Tag Col (ZMod 2)) (hcomp : IsCompl S.ker S.range) : Finset (Col → K) :=
  Finset.univ.filter fun x =>
    (H.map (algebraMap (ZMod 2) K)).mulVec (S.ker.projection S.range hcomp x) = 0

/-- If some kernel vector has nonzero tag, at most one field-size fraction
    of starting vectors have zero tag on their kernel component. -/
theorem card_bad_tagged_starts (S : Module.End K (Col → K))
    (H : Matrix Tag Col (ZMod 2)) (hcomp : IsCompl S.ker S.range)
    (htag : ∃ z ∈ S.ker, (H.map (algebraMap (ZMod 2) K)).mulVec z ≠ 0) :
    (badTaggedStarts S H hcomp).card ≤ Fintype.card K ^ (Fintype.card Col - 1) := by
  let L := (H.map (algebraMap (ZMod 2) K)).mulVecLin.comp (S.ker.projection S.range hcomp)
  have hL : L ≠ 0 := by
    intro h
    obtain ⟨z, hz, htz⟩ := htag
    apply htz
    have hp : S.ker.projection S.range hcomp z = z :=
      Submodule.projection_apply_left hcomp ⟨z, hz⟩
    simpa only [L, LinearMap.comp_apply, LinearMap.zero_apply, Matrix.mulVecLin_apply, hp] using
      LinearMap.congr_fun h z
  exact card_zeros_of_nonzero_tag L hL

/-- A start outside the bad set has the decomposition used by tagged extraction. -/
theorem tagged_start_components (S : Module.End K (Col → K))
    (H : Matrix Tag Col (ZMod 2)) (hcomp : IsCompl S.ker S.range) (x : Col → K)
    (hx : x ∉ badTaggedStarts S H hcomp) :
    ∃ z ∈ S.ker, ∃ w ∈ S.range, x = z + w ∧
      (H.map (algebraMap (ZMod 2) K)).mulVec z ≠ 0 := by
  let e := S.ker.prodEquivOfIsCompl S.range hcomp
  let zw := e.symm x
  refine ⟨zw.1, zw.1.property, zw.2, zw.2.property, (e.apply_symm_apply x).symm, ?_⟩
  intro h
  exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

end StartCount

section ScaledGram

variable {K Row Col Tag BasisIndex : Type*} [Field K] [Algebra (ZMod 2) K]
variable [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]

/-- Apply the scaled Gram matrix over the probe field. -/
def taggedOperator (M : Matrix Row Col (ZMod 2)) (d : Row → K) (e : Col → K) :
    Module.End K (Col → K) :=
  (scaledGram (M.map (algebraMap (ZMod 2) K)) d e).mulVecLin

variable [DecidableEq K] [Fintype K]

/-- For good diagonals, a tagged kernel component in the start and a good scalar
    probe make the finite recurrence quotient yield a tagged binary dependency. -/
theorem tagged_dependency_of_good_finite_probe
    (M : Matrix Row Col (ZMod 2)) (H : Matrix Tag Col (ZMod 2))
    (b : Module.Basis BasisIndex (ZMod 2) K) (d : Row → K) (e : Col → K)
    (hdiag : (scaledGram (M.map (algebraMap (ZMod 2) K)) d e).charpoly.coeff
      (Fintype.card Col - (M.map (algebraMap (ZMod 2) K)).rank) ≠ 0)
    (x u z w : Col → K) (hx : x = z + w)
    (hz : z ∈ (M.map (algebraMap (ZMod 2) K)).mulVecLin.ker)
    (hw : w ∈ (taggedOperator M d e).range)
    (hTag : (H.map (algebraMap (ZMod 2) K)).mulVec z ≠ 0)
    (p g : K[X]) (hp : p.Monic) (hg : g.Monic)
    (hpann : (aeval (taggedOperator M d e) p) x = 0)
    (pmin : ∀ r : K[X], r ≠ 0 → (aeval (taggedOperator M d e) r) x = 0 →
      p.natDegree ≤ r.natDegree)
    (hpdeg : p.natDegree ≤ Fintype.card Col) (hgdeg : g.natDegree ≤ Fintype.card Col)
    (hleft : u ∉ missedFactorProbes (taggedOperator M d e) x p)
    (fit : KrylovRecurrenceFits (taggedOperator M d e) x (dotProbe u) (Fintype.card Col) g)
    (fitmin : ∀ r : K[X], r ≠ 0 → r.natDegree ≤ Fintype.card Col →
      KrylovRecurrenceFits (taggedOperator M d e) x (dotProbe u) (Fintype.card Col) r →
      g.natDegree ≤ r.natDegree) :
    g = p ∧ g.coeff 0 = 0 ∧
      ∃ bit : BasisIndex,
        let v := (aeval (taggedOperator M d e) (g /ₘ X)) x
        M.mulVec (fun j => b.coord bit (v j)) = 0 ∧
          H.mulVec (fun j => b.coord bit (v j)) ≠ 0 := by
  let A := M.map (algebraMap (ZMod 2) K)
  let S := taggedOperator M d e
  have hker : S.ker = A.mulVecLin.ker := (scaledGram_rank_and_ker A d e hdiag).2
  have hcomp : IsCompl S.ker S.range := by
    rw [hker]
    exact scaledGram_isCompl A d e hdiag
  have hzS : z ∈ S.ker := by rwa [hker]
  have hp0 : p.coeff 0 = 0 := by
    by_contra hc
    have hxr := mem_range_of_annihilator_constant_ne_zero S x p hpann hc
    have hzr : z ∈ S.range := by
      have hs := S.range.sub_mem hxr hw
      rwa [hx, add_sub_cancel_right] at hs
    have hzero := Submodule.disjoint_def.mp hcomp.disjoint z hzS hzr
    exact hTag (by simp [hzero])
  have hgEq := minimal_projected_eq_of_good_probe_finite S x u p g (Fintype.card Col)
    hp hg hpdeg hgdeg hpann hleft fit fitmin
  obtain ⟨q, hq⟩ := X_dvd_iff.mpr hp0
  have hqa : (aeval S (X * q)) x = 0 := by simpa only [← hq] using hpann
  have hqne : q ≠ 0 := fun h => hp.ne_zero (by simp [hq, h])
  let v := (aeval S q) x
  have hvne : v ≠ 0 := quotient_action_ne_zero_of_minimal S q x hqne
    (fun r hr hzero => by simpa only [← hq] using pmin r hr hzero)
  have hvker : v ∈ S.ker :=
    LinearMap.mem_ker.mpr (quotient_action_in_kernel S q x hqa)
  have hqrange := tagged_range_component_annihilated S q hcomp.disjoint hx hzS hw hqa
  have hvEq : v = q.eval 0 • z := tagged_kernel_project S q hx hzS hqrange
  have hq0 : q.eval 0 ≠ 0 := fun hzero => hvne (by simp [hvEq, hzero])
  have hvTag : (H.map (algebraMap (ZMod 2) K)).mulVec v ≠ 0 :=
    (tagged_kernel_project_tag_ne_zero_iff S q (H.map (algebraMap (ZMod 2) K)).mulVecLin
      hx hzS hqrange hq0).mpr hTag
  have hvA : A.mulVec v = 0 := LinearMap.mem_ker.mp (hker ▸ hvker)
  have hquot : g /ₘ X = q := by rw [hgEq, hq, mul_divByMonic_cancel_left _ monic_X]
  refine ⟨hgEq, by rwa [hgEq], ?_⟩
  rw [hquot]
  exact exists_tagged_binary_coordinate M H b v hvA hvTag

end ScaledGram

#print axioms project_mulVec_apply
#print axioms exists_tagged_binary_coordinate
#print axioms exists_tagged_extension_kernel
#print axioms card_bad_tagged_starts
#print axioms tagged_start_components
#print axioms tagged_dependency_of_good_finite_probe

end Cogentic.RandomizedTaggedDependency
