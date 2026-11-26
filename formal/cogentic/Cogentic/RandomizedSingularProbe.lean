import Cogentic.RandomizedKrylovProbe
import Cogentic.RandomizedSparseDependency
import Mathlib.Data.Finset.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Dual

/-! Counting the right-vector loss for a singular sparse Wiedemann operator. -/

namespace Cogentic.RandomizedSingularProbe

open Polynomial
open Cogentic.RandomizedKrylovProbe
open Cogentic.RandomizedProbeCount

/-- A vector annihilated by a polynomial with nonzero constant coefficient
    belongs to the image of the operator. -/
theorem mem_range_of_annihilator_constant_ne_zero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (M : Module.End K V) (v : V) (p : K[X])
    (hp : (aeval M p) v = 0) (hc : p.coeff 0 ≠ 0) :
    v ∈ LinearMap.range M := by
  obtain ⟨r, hr⟩ := (X_dvd_sub_C : X ∣ p - C (p.coeff 0))
  have hdecomp : p = C (p.coeff 0) + X * r := by
    rw [← hr, add_comm, sub_add_cancel]
  let y := (aeval M r) v
  have hsum : p.coeff 0 • v + M y = 0 := by
    conv_lhs at hp => rw [hdecomp]
    rw [map_add, map_mul, aeval_C, aeval_X, LinearMap.add_apply] at hp
    exact hp
  have hsmul : p.coeff 0 • v = M (-y) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left hsum
  refine ⟨(p.coeff 0)⁻¹ • (-y), ?_⟩
  rw [map_smul, ← hsmul, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- A starting vector has a monic minimal annihilator whose degree is bounded
    by the number of coordinates. -/
theorem exists_minimal_vector_annihilator {K I : Type*} [Field K] [Fintype I]
    (M : Module.End K (I → K)) (v : I → K) :
    ∃ p : K[X], p.Monic ∧ (aeval M p) v = 0 ∧ p.natDegree ≤ Fintype.card I ∧
      ∀ r : K[X], r ≠ 0 → (aeval M r) v = 0 → p.natDegree ≤ r.natDegree := by
  classical
  let P : ℕ → Prop := fun d => ∃ p : K[X], p.Monic ∧ (aeval M p) v = 0 ∧ p.natDegree = d
  have hc : P M.charpoly.natDegree :=
    ⟨M.charpoly, M.charpoly_monic, by simp [M.aeval_self_charpoly], rfl⟩
  have hex : ∃ d, P d := ⟨_, hc⟩
  obtain ⟨p, hmonic, hann, hdeg⟩ := Nat.find_spec hex
  refine ⟨p, hmonic, hann, ?_, ?_⟩
  · rw [hdeg, ← Module.finrank_fintype_fun_eq_card K, ← M.charpoly_natDegree]
    exact Nat.find_min' hex hc
  · intro r hr hrann
    have hnorm : (aeval M (r * C r.leadingCoeff⁻¹)) v = 0 := by
      rw [mul_comm, map_mul, aeval_C]
      change r.leadingCoeff⁻¹ • ((aeval M r) v) = 0
      rw [hrann, smul_zero]
    rw [hdeg]
    exact Nat.find_min' hex ⟨r * C r.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hr,
      hnorm, natDegree_mul_leadingCoeff_inv r hr⟩

section Counting

variable {K I : Type*} [Field K] [DecidableEq K] [Fintype K] [Fintype I] [DecidableEq I]

/-- A bad right vector has a selected annihilator with nonzero constant. -/
def badRightVectors (p : (I → K) → K[X]) : Finset (I → K) :=
  Finset.univ.filter fun v => (p v).coeff 0 ≠ 0

/-- Bad right vectors are contained in one hyperplane if the operator is singular. -/
theorem card_bad_right_vectors (M : Module.End K (I → K)) (p : (I → K) → K[X])
    (hsingular : LinearMap.range M ≠ ⊤) (hann : ∀ v, (aeval M (p v)) v = 0) :
    (badRightVectors p).card ≤ Fintype.card K ^ (Fintype.card I - 1) := by
  obtain ⟨f, hf, hrange⟩ := (LinearMap.range M).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr hsingular)
  let e := dotProductEquiv K I
  let w := e.symm f
  have hw : w ≠ 0 := by
    intro hz
    apply hf
    rw [← e.apply_symm_apply f, ← show w = e.symm f from rfl, hz, map_zero]
  have hsub : badRightVectors p ⊆ Finset.univ.filter (fun v => w ⬝ᵥ v = 0) := by
    intro v hv
    change v ∈ Finset.univ.filter (fun v => (p v).coeff 0 ≠ 0) at hv
    have hc := (Finset.mem_filter.mp hv).2
    have hfv := LinearMap.mem_ker.mp
      (hrange (mem_range_of_annihilator_constant_ne_zero M v (p v) (hann v) hc))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change e w v = 0
    rw [e.apply_symm_apply f]
    exact hfv
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [← Fintype.card_subtype]
  exact card_probe_fiber_of_nonzero w hw 0

private def pairWithRight (v : I → K) : (I → K) ↪ (I → K) × (I → K) :=
  ⟨fun u => (v, u), fun _ _ h => congrArg Prod.snd h⟩

private noncomputable def badLeftPairs (M : Module.End K (I → K))
    (p : (I → K) → K[X]) : Finset ((I → K) × (I → K)) :=
  Finset.univ.biUnion fun v => (missedFactorProbes M v (p v)).map (pairWithRight v)

/-- Pairs are indexed as (right vector, left probe). A pair fails if either
    the right vector loses X or the left probe misses an irreducible test. -/
noncomputable def badProbePairs (M : Module.End K (I → K))
    (p : (I → K) → K[X]) : Finset ((I → K) × (I → K)) :=
  (badRightVectors p).product Finset.univ ∪ badLeftPairs M p

private theorem card_bad_left_pairs (M : Module.End K (I → K))
    (p : (I → K) → K[X]) (hmonic : ∀ v, (p v).Monic)
    (hdegree : ∀ v, (p v).natDegree ≤ Fintype.card I)
    (minimal : ∀ v (r : K[X]), r ≠ 0 → (aeval M r) v = 0 →
      (p v).natDegree ≤ r.natDegree) :
    (badLeftPairs M p).card ≤
      Fintype.card (I → K) * (Fintype.card I * Fintype.card K ^ (Fintype.card I - 1)) := by
  unfold badLeftPairs
  rw [← Finset.card_univ]
  apply Finset.card_biUnion_le_card_mul
  intro v _
  rw [Finset.card_map]
  have hcount := card_bad_probe_union (UniqueFactorizationMonoid.normalizedFactors (p v)).toFinset
    (fun f => (aeval M (p v /ₘ f)) v)
    (fun f hf => factor_action_ne_zero M v (p v) f (hmonic v)
      (Multiset.mem_toFinset.mp hf) (minimal v))
  exact hcount.trans (Nat.mul_le_mul_right _
    ((card_factor_tests_le_degree (p v) (hmonic v)).trans (hdegree v)))

/-- For dimension s over a field of size q, the proportion of bad pairs is
    at most (s+1)/q, written as an integer inequality. -/
theorem card_bad_probe_pairs_mul_field_le [Nonempty I]
    (M : Module.End K (I → K)) (p : (I → K) → K[X])
    (hsingular : LinearMap.range M ≠ ⊤)
    (hmonic : ∀ v, (p v).Monic) (hann : ∀ v, (aeval M (p v)) v = 0)
    (hdegree : ∀ v, (p v).natDegree ≤ Fintype.card I)
    (minimal : ∀ v (r : K[X]), r ≠ 0 → (aeval M r) v = 0 →
      (p v).natDegree ≤ r.natDegree) :
    (badProbePairs M p).card * Fintype.card K ≤
      (Fintype.card I + 1) * Fintype.card (I → K) ^ 2 := by
  let s := Fintype.card I
  let q := Fintype.card K
  let d := Fintype.card (I → K)
  have hr := card_bad_right_vectors M p hsingular hann
  have hl := card_bad_left_pairs M p hmonic hdegree minimal
  have hsum : (badProbePairs M p).card ≤ (s + 1) * (d * q ^ (s - 1)) := by
    calc
      (badProbePairs M p).card ≤
          ((badRightVectors p).product (Finset.univ : Finset (I → K))).card +
            (badLeftPairs M p).card := Finset.card_union_le _ _
      _ ≤ q ^ (s - 1) * d + d * (s * q ^ (s - 1)) := by
        have hprod := Finset.card_product (badRightVectors p) (Finset.univ : Finset (I → K))
        change ((badRightVectors p).product (Finset.univ : Finset (I → K))).card = _ at hprod
        rw [hprod, Finset.card_univ]
        exact Nat.add_le_add (Nat.mul_le_mul_right _ hr) hl
      _ = (s + 1) * (d * q ^ (s - 1)) := by
        rw [Nat.add_mul, Nat.one_mul]
        ac_rfl
  have hpos : 0 < s := Fintype.card_pos
  have hd : q ^ (s - 1) * q = d := by
    rw [← pow_succ, Nat.sub_add_cancel hpos]
    exact Fintype.card_fun.symm
  calc
    (badProbePairs M p).card * q ≤ ((s + 1) * (d * q ^ (s - 1))) * q :=
      Nat.mul_le_mul_right _ hsum
    _ = (s + 1) * d ^ 2 := by
      rw [Nat.mul_assoc, Nat.mul_assoc d, hd, pow_two]

/-- A good pair retains X and passes every irreducible-factor test. -/
theorem good_probe_pair_conditions (M : Module.End K (I → K)) (p : (I → K) → K[X])
    (v u : I → K) (hgood : (v, u) ∉ badProbePairs M p) :
    (p v).coeff 0 = 0 ∧ u ∉ missedFactorProbes M v (p v) := by
  constructor
  · by_contra hc
    apply hgood
    apply Finset.mem_union_left
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, Finset.mem_univ _⟩
  · intro hu
    apply hgood
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, Finset.mem_map.mpr ⟨u, hu, rfl⟩⟩

end Counting

section PaddedMatrix

open Cogentic.RandomizedSparseDependency

variable {K Row BasisIndex : Type*} [Field K] [DecidableEq K] [Fintype K]
  [Algebra (ZMod 2) K] [Fintype Row] [DecidableEq Row]

omit [DecidableEq K] [Fintype K] in
/-- The zero padding row makes the extension-field operator singular. -/
theorem padded_operator_range_ne_top (A : Matrix Row (Option Row) (ZMod 2)) :
    LinearMap.range (paddedOperator (K := K) A) ≠ ⊤ := by
  intro htop
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.mp htop (Pi.single none (1 : K))
  have hn := congrFun hv none
  simp [paddedOperator, padZeroRow, Matrix.mulVec, dotProduct] at hn

/-- The padded binary operator admits a choice of minimal polynomials with
    the combined right-vector and left-probe failure bound. -/
theorem exists_padded_annihilators_with_pair_bound (A : Matrix Row (Option Row) (ZMod 2)) :
    ∃ p : (Option Row → K) → K[X],
      (∀ v, (p v).Monic ∧ (aeval (paddedOperator A) (p v)) v = 0 ∧
        (p v).natDegree ≤ Fintype.card (Option Row) ∧
        ∀ r : K[X], r ≠ 0 → (aeval (paddedOperator A) r) v = 0 →
          (p v).natDegree ≤ r.natDegree) ∧
      (badProbePairs (paddedOperator A) p).card * Fintype.card K ≤
        (Fintype.card (Option Row) + 1) * Fintype.card (Option Row → K) ^ 2 := by
  let M := paddedOperator (K := K) A
  let p := fun v => Classical.choose (exists_minimal_vector_annihilator M v)
  have hp := fun v => Classical.choose_spec (exists_minimal_vector_annihilator M v)
  refine ⟨p, hp, ?_⟩
  exact card_bad_probe_pairs_mul_field_le M p (padded_operator_range_ne_top A)
    (fun v => (hp v).1) (fun v => (hp v).2.1) (fun v => (hp v).2.2.1) (fun v => (hp v).2.2.2)

/-- A good pair and a least-degree recurrence from the finite samples give
    the vector polynomial and a nonzero binary dependency. -/
theorem binary_dependency_of_good_finite_pair
    (A : Matrix Row (Option Row) (ZMod 2)) (b : Module.Basis BasisIndex (ZMod 2) K)
    (p : (Option Row → K) → K[X]) (v u : Option Row → K) (g : K[X])
    (hgood : (v, u) ∉ badProbePairs (paddedOperator A) p)
    (hmonic : (p v).Monic) (hann : (aeval (paddedOperator A) (p v)) v = 0)
    (hdegree : (p v).natDegree ≤ Fintype.card (Option Row))
    (hmin : ∀ r : K[X], r ≠ 0 → (aeval (paddedOperator A) r) v = 0 →
      (p v).natDegree ≤ r.natDegree)
    (hg : g.Monic) (hgdegree : g.natDegree ≤ Fintype.card (Option Row))
    (fit : KrylovRecurrenceFits (paddedOperator A) v (dotProbe u) (Fintype.card (Option Row)) g)
    (fitmin : ∀ r : K[X], r ≠ 0 → r.natDegree ≤ Fintype.card (Option Row) →
      KrylovRecurrenceFits (paddedOperator A) v (dotProbe u) (Fintype.card (Option Row)) r →
      g.natDegree ≤ r.natDegree) :
    g = p v ∧ ∃ w : Option Row → ZMod 2, w ≠ 0 ∧ A.mulVec w = 0 := by
  obtain ⟨hconstant, hleft⟩ := good_probe_pair_conditions (paddedOperator A) p v u hgood
  exact ⟨minimal_projected_eq_of_good_probe_finite _ v u (p v) g _ hmonic hg hdegree
    hgdegree hann hleft fit fitmin,
    binary_dependency_of_padded_minimal_annihilator A b v (p v) hmonic.ne_zero
      hconstant hann hmin⟩

end PaddedMatrix

#print axioms mem_range_of_annihilator_constant_ne_zero
#print axioms exists_minimal_vector_annihilator
#print axioms card_bad_right_vectors
#print axioms card_bad_probe_pairs_mul_field_le
#print axioms good_probe_pair_conditions
#print axioms padded_operator_range_ne_top
#print axioms exists_padded_annihilators_with_pair_bound
#print axioms binary_dependency_of_good_finite_pair

end Cogentic.RandomizedSingularProbe
