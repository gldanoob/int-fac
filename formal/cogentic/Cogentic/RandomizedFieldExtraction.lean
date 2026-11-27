import Cogentic.RandomizedEpochSuccess
import Cogentic.RandomizedHiddenSpan
import Cogentic.RandomizedRationalChildRouting
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Norm.Basic

/-!
# Field-Labelled Multi-Field Relation Assembly and Exact Extraction

This file formalizes:
1. The odd-degree norm-square criterion (KeyBreak Lemma E.1): in an odd-degree
   finite field extension `K / F`, if `γ = r * δ^2` has a square norm in `F`,
   then `r` is a square in `F` (when `δ ≠ 0`) and `γ` is a square in `K`.
2. The homogeneous norm formula (KeyBreak E.7), its integral scaled-coordinate
   form `β = A * α` (KeyBreak E.16–E.19), and occurrence-parity cancellation:
   when `∑ c_P` is even, `Algebra.norm k γ` is a square iff `∏ F_hom(a_P, b_P)^c_P`
   is a square.
3. Multi-field public root assembly and modular square congruence in `(ZMod N)ˣ`,
   connecting per-field extracted roots and rational corrections to `labelProduct`.
4. Sparse Krylov/Padé binary dependency mask extraction and direct wiring into
   `RandomizedEpochSuccess.epoch_verified_split_probability_half` and
   `RandomizedEpochSuccess.epochTrial_budget_sound`.
-/

open scoped Polynomial BigOperators ENNReal

namespace Cogentic.RandomizedFieldExtraction

open Polynomial
open Cogentic.RandomizedHiddenLabels
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedVerifiedHiddenSplit
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedEpochSuccess
open Cogentic.RandomizedTaggedDependency
open Cogentic.RandomizedKrylovProbe
open Cogentic.RandomizedPadeRecurrence

/-! ## Section 1: Odd-Degree Norm-Square Criterion (KeyBreak Lemma E.1) -/

section OddDegreeNormSquare

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]

/-- Multiplicative norm formula for an element of rational squareclass `r`:
`Norm_{K/F}(r * δ^2) = r^[K:F] * Norm_{K/F}(δ)^2`. -/
theorem norm_algebraMap_mul_sq (r : F) (δ : K) :
    Algebra.norm F (algebraMap F K r * δ ^ 2) =
      r ^ Module.finrank F K * (Algebra.norm F δ) ^ 2 := by
  rw [map_mul, Algebra.norm_algebraMap, map_pow]

/-- Explicit square-root formula for the base scalar in an odd-degree extension:
if `[K : F] = 2m + 1`, `γ = r * δ^2`, and `Norm(γ) = s^2` with `r, δ ≠ 0`, then
`r = (s / (r^m * Norm(δ)))^2`. -/
theorem odd_finrank_base_eq_sq {γ δ : K} {r s : F} {m : ℕ}
    (hdeg : Module.finrank F K = 2 * m + 1)
    (hγ : γ = algebraMap F K r * δ ^ 2)
    (hnorm : Algebra.norm F γ = s ^ 2)
    (hr : r ≠ 0) (hδ : δ ≠ 0) :
    r = (s / (r ^ m * Algebra.norm F δ)) ^ 2 := by
  have hnormδ : Algebra.norm F δ ≠ 0 := by
    intro hz
    exact hδ ((Algebra.norm_eq_zero_iff (R := F)).mp hz)
  have hu : r ^ m * Algebra.norm F δ ≠ 0 := mul_ne_zero (pow_ne_zero m hr) hnormδ
  have hcalc : s ^ 2 = r * (r ^ m * Algebra.norm F δ) ^ 2 := by
    calc
      s ^ 2 = Algebra.norm F γ := hnorm.symm
      _ = r ^ (2 * m + 1) * (Algebra.norm F δ) ^ 2 := by
        rw [hγ, norm_algebraMap_mul_sq, hdeg]
      _ = r * (r ^ m * Algebra.norm F δ) ^ 2 := by
        rw [pow_succ, mul_pow, ← pow_mul, mul_comm m 2]
        ring
  rw [div_pow, hcalc, mul_div_cancel_right₀ _ (pow_ne_zero 2 hu)]

/-- If `K / F` has odd degree, `γ = r * δ^2` with `δ ≠ 0`, and `Norm_{K/F}(γ)` is a
square in `F`, then `r` is a square in `F`. -/
theorem isSquare_base_of_odd_finrank_norm_sq {γ δ : K} {r : F}
    (hodd : Odd (Module.finrank F K))
    (hγ : γ = algebraMap F K r * δ ^ 2)
    (hnorm : IsSquare (Algebra.norm F γ))
    (hδ : δ ≠ 0) :
    IsSquare r := by
  by_cases hr : r = 0
  · subst hr
    exact ⟨0, by simp⟩
  · obtain ⟨m, hm⟩ := hodd
    obtain ⟨s, hs⟩ := hnorm
    have hs' : Algebra.norm F γ = s ^ 2 := by simpa only [pow_two] using hs
    refine ⟨s / (r ^ m * Algebra.norm F δ), ?_⟩
    simpa only [pow_two] using odd_finrank_base_eq_sq hm hγ hs' hr hδ

/-- KeyBreak Lemma E.1: in an odd-degree finite field extension `K / F`, an element
`γ = r * δ^2` of rational squareclass whose norm is a square in `F` is itself a
square in `K`. -/
theorem isSquare_of_odd_finrank_norm_sq {γ δ : K} {r : F}
    (hodd : Odd (Module.finrank F K))
    (hγ : γ = algebraMap F K r * δ ^ 2)
    (hnorm : IsSquare (Algebra.norm F γ)) :
    IsSquare γ := by
  by_cases hδ : δ = 0
  · subst hδ
    rw [hγ]
    exact ⟨0, by simp⟩
  · obtain ⟨t, ht⟩ := isSquare_base_of_odd_finrank_norm_sq hodd hγ hnorm hδ
    refine ⟨algebraMap F K t * δ, ?_⟩
    rw [hγ, ht, map_mul, pow_two]
    ring

end OddDegreeNormSquare

/-! ## Section 2: Homogeneous Norm Formula (KeyBreak E.7) and Occurrence-Parity Cancellation -/

section HomogeneousNormFormula

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [Module.Finite k K]

/-- Homogeneous evaluation `F_hom(a, b) = ∑_{i=0}^d F_i a^i b^{d-i}` of a polynomial
of degree `d = F.natDegree`. -/
def homEval (F : k[X]) (a b : k) : k :=
  ∑ i ∈ Finset.range (F.natDegree + 1), F.coeff i * a ^ i * b ^ (F.natDegree - i)

theorem homEval_zero_right (F : k[X]) (a : k) :
    homEval F a 0 = F.leadingCoeff * a ^ F.natDegree := by
  unfold homEval
  rw [Finset.sum_eq_single F.natDegree]
  · rw [Nat.sub_self, pow_zero, mul_one, Polynomial.coeff_natDegree]
  · intro i hi hne
    have hlt : i < F.natDegree := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
    have hpos : 0 < F.natDegree - i := Nat.sub_pos_of_lt hlt
    rw [zero_pow hpos.ne', mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim

theorem homEval_eq_mul_eval (F : k[X]) (a : k) {b : k} (hb : b ≠ 0) :
    homEval F a b = b ^ F.natDegree * F.eval (a / b) := by
  unfold homEval
  rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i ≤ F.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [div_pow]
  have hsplit : b ^ F.natDegree = b ^ i * b ^ (F.natDegree - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  rw [hsplit]
  have hbi : b ^ i ≠ 0 := pow_ne_zero i hb
  field_simp [hbi]

/-- Evaluating the characteristic polynomial of left multiplication by `α` at `t`
gives the algebra norm of `t - α`. -/
theorem norm_sub_eq_eval_charpoly (α : K) (t : k) :
    Algebra.norm k (algebraMap k K t - α) =
      (LinearMap.charpoly (Algebra.lmul k K α)).eval t := by
  rw [LinearMap.eval_charpoly, Algebra.norm_apply]
  congr 1
  ext x
  simp [Algebra.algebraMap_eq_smul_one]

/-- When the minimal polynomial of `α` has degree equal to `[K : k]`, it coincides
with the characteristic polynomial of left multiplication by `α`. -/
theorem charpoly_lmul_eq_minpoly_of_natDegree_eq (α : K)
    (hdeg : (minpoly k α).natDegree = Module.finrank k K) :
    LinearMap.charpoly (Algebra.lmul k K α) = minpoly k α := by
  have hdvd : minpoly k α ∣ LinearMap.charpoly (Algebra.lmul k K α) :=
    minpoly.dvd k α (Algebra.aeval_self_charpoly_lmul (R := k) α)
  have hmon_char : (LinearMap.charpoly (Algebra.lmul k K α)).Monic :=
    LinearMap.charpoly_monic _
  have hmon_min : (minpoly k α).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral α)
  have hdeg_char : (LinearMap.charpoly (Algebra.lmul k K α)).natDegree = Module.finrank k K :=
    LinearMap.charpoly_natDegree _
  obtain ⟨q, hq⟩ := hdvd
  have hq_ne : q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hq
    exact hmon_char.ne_zero hq
  have hq_deg : q.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hmon_min.ne_zero hq_ne
    rw [← hq, hdeg_char, hdeg] at hmul
    omega
  have hq_mon : q.Monic := by
    have hl : (LinearMap.charpoly (Algebra.lmul k K α)).leadingCoeff =
        (minpoly k α).leadingCoeff * q.leadingCoeff := by
      rw [hq, Polynomial.leadingCoeff_mul]
    rw [hmon_char.leadingCoeff, hmon_min.leadingCoeff, one_mul] at hl
    exact hl.symm
  have hq_one : q = 1 := Polynomial.eq_one_of_monic_natDegree_zero hq_mon hq_deg
  rw [hq, hq_one, mul_one]

omit [Module.Finite k K] in
/-- An irreducible polynomial vanishing at `α` determines `minpoly k α` after
normalizing by its leading coefficient. -/
theorem minpoly_eq_C_inv_mul_of_irreducible (F : k[X]) (α : K)
    (hirr : Irreducible F) (hroot : Polynomial.aeval α F = 0) :
    minpoly k α = Polynomial.C F.leadingCoeff⁻¹ * F := by
  have hFne : F ≠ 0 := hirr.ne_zero
  have hA : F.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hFne
  have hmon : (Polynomial.C F.leadingCoeff⁻¹ * F).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ hA]
  have hunit : IsUnit (Polynomial.C F.leadingCoeff⁻¹) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hA)).map Polynomial.C
  have hirr' : Irreducible (Polynomial.C F.leadingCoeff⁻¹ * F) :=
    (associated_unit_mul_left F _ hunit).symm.irreducible hirr
  have hroot' : Polynomial.aeval α (Polynomial.C F.leadingCoeff⁻¹ * F) = 0 := by
    rw [map_mul, hroot, mul_zero]
  exact (minpoly.eq_of_irreducible_of_monic hirr' hroot' hmon).symm

/-- Single linear-factor norm identity (base case of KeyBreak E.7):
`A * Norm_{K/k}(a - b * α) = F_hom(a, b)`. -/
theorem leadingCoeff_mul_norm_linear (F : k[X]) (α : K)
    (hirr : Irreducible F) (hroot : Polynomial.aeval α F = 0)
    (hdeg : Module.finrank k K = F.natDegree) (a b : k) :
    F.leadingCoeff * Algebra.norm k (algebraMap k K a - algebraMap k K b * α) =
      homEval F a b := by
  have hA : F.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
  by_cases hb : b = 0
  · subst hb
    rw [map_zero, zero_mul, sub_zero, Algebra.norm_algebraMap, hdeg, homEval_zero_right]
  · have hmin : minpoly k α = Polynomial.C F.leadingCoeff⁻¹ * F :=
      minpoly_eq_C_inv_mul_of_irreducible F α hirr hroot
    have hmin_deg : (minpoly k α).natDegree = Module.finrank k K := by
      rw [hmin, Polynomial.natDegree_C_mul (inv_ne_zero hA), hdeg]
    have hchar : LinearMap.charpoly (Algebra.lmul k K α) = Polynomial.C F.leadingCoeff⁻¹ * F := by
      rw [charpoly_lmul_eq_minpoly_of_natDegree_eq α hmin_deg, hmin]
    have hfac : algebraMap k K a - algebraMap k K b * α =
        algebraMap k K b * (algebraMap k K (a / b) - α) := by
      rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hb]
    calc
      F.leadingCoeff * Algebra.norm k (algebraMap k K a - algebraMap k K b * α)
          = F.leadingCoeff * Algebra.norm k (algebraMap k K b * (algebraMap k K (a / b) - α)) := by
            rw [hfac]
      _ = F.leadingCoeff * (b ^ F.natDegree * Algebra.norm k (algebraMap k K (a / b) - α)) := by
            rw [map_mul, Algebra.norm_algebraMap, hdeg]
      _ = F.leadingCoeff * (b ^ F.natDegree * (F.leadingCoeff⁻¹ * F.eval (a / b))) := by
            rw [norm_sub_eq_eval_charpoly, hchar, Polynomial.eval_mul, Polynomial.eval_C]
      _ = b ^ F.natDegree * F.eval (a / b) := by
            field_simp [hA]
      _ = homEval F a b := (homEval_eq_mul_eval F a hb).symm

/-- Scaled integral-coordinate norm identity (KeyBreak E.16–E.19):
for `β = A * α` with `A = F.leadingCoeff`,
`Norm_{K/k}(A * a - b * β) = A^{d - 1} * F_hom(a, b)`. -/
theorem norm_scaled_linear (F : k[X]) (α : K)
    (hirr : Irreducible F) (hroot : Polynomial.aeval α F = 0)
    (hdeg : Module.finrank k K = F.natDegree) (a b : k) :
    Algebra.norm k (algebraMap k K (F.leadingCoeff * a) -
        algebraMap k K b * (algebraMap k K F.leadingCoeff * α)) =
      F.leadingCoeff ^ (F.natDegree - 1) * homEval F a b := by
  have hd : 1 ≤ F.natDegree := by
    have hpos : 0 < Module.finrank k K := Module.finrank_pos
    omega
  have hfac : algebraMap k K (F.leadingCoeff * a) -
      algebraMap k K b * (algebraMap k K F.leadingCoeff * α) =
      algebraMap k K F.leadingCoeff * (algebraMap k K a - algebraMap k K b * α) := by
    rw [map_mul]
    ring
  rw [hfac, map_mul, Algebra.norm_algebraMap, hdeg]
  have hsplit : F.leadingCoeff ^ F.natDegree =
      F.leadingCoeff ^ (F.natDegree - 1) * F.leadingCoeff := by
    conv_lhs => rw [← Nat.sub_add_cancel hd, pow_succ]
  rw [hsplit, mul_assoc, leadingCoeff_mul_norm_linear F α hirr hroot hdeg a b]

/-- Algebra norm preserves arbitrary integer powers in any finite field extension. -/
theorem norm_zpow (x : K) (n : ℤ) :
    Algebra.norm k (x ^ n) = (Algebra.norm k x) ^ n := by
  have h0 : Algebra.norm k (0 : K) = 0 :=
    Algebra.norm_zero (R := k) (S := K)
  cases n with
  | ofNat m =>
    simp [map_pow]
  | negSucc m =>
    simp only [zpow_negSucc]
    by_cases hx : x = 0
    · subst hx
      rw [zero_pow (Nat.succ_ne_zero m), inv_zero, h0, zero_pow (Nat.succ_ne_zero m), inv_zero]
    · have hpow : x ^ (m + 1) ≠ 0 := pow_ne_zero _ hx
      have hnorm : Algebra.norm k (x ^ (m + 1)) ≠ 0 := by
        intro hz
        exact hpow ((Algebra.norm_eq_zero_iff (R := k)).mp hz)
      have hmul : Algebra.norm k ((x ^ (m + 1))⁻¹) * Algebra.norm k (x ^ (m + 1)) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hpow, map_one]
      have hinv : Algebra.norm k ((x ^ (m + 1))⁻¹) = (Algebra.norm k (x ^ (m + 1)))⁻¹ :=
        eq_inv_of_mul_eq_one_left hmul
      rw [hinv, map_pow]

private theorem zpow_sum_eq_prod {ι : Type*} {a : k} (ha : a ≠ 0) (S : Finset ι) (c : ι → ℤ) :
    a ^ (∑ P ∈ S, c P) = ∏ P ∈ S, a ^ c P := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert P s hP ih =>
    rw [Finset.sum_insert hP, Finset.prod_insert hP, zpow_add₀ ha, ih]

/-- KeyBreak formula (E.7) for signed integer exponents:
`A^{∑_{P ∈ S} c_P} * Norm_{K/k}(∏_{P ∈ S} (a_P - b_P α)^{c_P}) = ∏_{P ∈ S} F_hom(a_P, b_P)^{c_P}`. -/
theorem hom_norm_prod_zpow {ι : Type*} (F : k[X]) (α : K)
    (hirr : Irreducible F) (hroot : Polynomial.aeval α F = 0)
    (hdeg : Module.finrank k K = F.natDegree)
    (S : Finset ι) (a b : ι → k) (c : ι → ℤ) :
    F.leadingCoeff ^ (∑ P ∈ S, c P) *
        Algebra.norm k (∏ P ∈ S, (algebraMap k K (a P) - algebraMap k K (b P) * α) ^ c P) =
      ∏ P ∈ S, (homEval F (a P) (b P)) ^ c P := by
  have hA : F.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
  rw [map_prod, zpow_sum_eq_prod hA, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  rw [norm_zpow, ← mul_zpow, leadingCoeff_mul_norm_linear F α hirr hroot hdeg (a P) (b P)]

/-- Natural-number exponent version of KeyBreak formula (E.7). -/
theorem hom_norm_prod_pow {ι : Type*} (F : k[X]) (α : K)
    (hirr : Irreducible F) (hroot : Polynomial.aeval α F = 0)
    (hdeg : Module.finrank k K = F.natDegree)
    (S : Finset ι) (a b : ι → k) (c : ι → ℕ) :
    F.leadingCoeff ^ (∑ P ∈ S, c P) *
        Algebra.norm k (∏ P ∈ S, (algebraMap k K (a P) - algebraMap k K (b P) * α) ^ c P) =
      ∏ P ∈ S, (homEval F (a P) (b P)) ^ c P := by
  rw [map_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  rw [map_pow, ← mul_pow, leadingCoeff_mul_norm_linear F α hirr hroot hdeg (a P) (b P)]

/-- Occurrence-parity cancellation: when the signed occurrence sum `∑_{P ∈ S} c_P`
is even, `A^{∑ c_P}` is a nonzero square in `k`, so `Norm_{K/k}(γ)` is a square
in `k` if and only if the homogeneous product `∏ F_hom(a_P, b_P)^{c_P}` is a square. -/
theorem isSquare_norm_iff_isSquare_hom_prod_of_even_sum {ι : Type*} (F : k[X]) (α : K)
    (hirr : Irreducible F) (hroot : Polynomial.aeval α F = 0)
    (hdeg : Module.finrank k K = F.natDegree)
    (S : Finset ι) (a b : ι → k) (c : ι → ℤ)
    (heven : Even (∑ P ∈ S, c P)) :
    IsSquare (Algebra.norm k (∏ P ∈ S, (algebraMap k K (a P) - algebraMap k K (b P) * α) ^ c P)) ↔
      IsSquare (∏ P ∈ S, (homEval F (a P) (b P)) ^ c P) := by
  have hA : F.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
  obtain ⟨m, hm⟩ := heven
  have hE := hom_norm_prod_zpow F α hirr hroot hdeg S a b c
  rw [hm, zpow_add₀ hA] at hE
  have hAm : F.leadingCoeff ^ m ≠ 0 := zpow_ne_zero m hA
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨F.leadingCoeff ^ m * s, ?_⟩
    rw [← hE, hs]
    ring
  · rintro ⟨t, ht⟩
    refine ⟨(F.leadingCoeff ^ m)⁻¹ * t, ?_⟩
    have hnorm : Algebra.norm k
        (∏ P ∈ S, (algebraMap k K (a P) - algebraMap k K (b P) * α) ^ c P) =
        (F.leadingCoeff ^ m * F.leadingCoeff ^ m)⁻¹ *
          (∏ P ∈ S, (homEval F (a P) (b P)) ^ c P) := by
      rw [← hE, inv_mul_cancel_left₀ (mul_ne_zero hAm hAm)]
    rw [hnorm, ht]
    field_simp [hAm]

/-- End-to-end per-field exact square certification combining KeyBreak Lemma E.1,
formula (E.7), and occurrence-parity cancellation: if `F` is irreducible of odd degree,
`γ = ∏ (a_P - b_P α)^{c_P}` lies in a rational squareclass `r * δ^2`, the occurrence
parity `∑ c_P` is even, and the homogeneous product `∏ F_hom(a_P, b_P)^{c_P}` is a
square in `k`, then `γ` is a square in `K`. -/
theorem isSquare_field_product_of_odd_degree_and_even_parity {ι : Type*} (F : k[X]) (α : K)
    (hirr : Irreducible F) (hodd : Odd F.natDegree) (hroot : Polynomial.aeval α F = 0)
    (hdeg : Module.finrank k K = F.natDegree)
    (S : Finset ι) (a b : ι → k) (c : ι → ℤ) (r : k) (δ : K)
    (hclass : (∏ P ∈ S, (algebraMap k K (a P) - algebraMap k K (b P) * α) ^ c P) =
      algebraMap k K r * δ ^ 2)
    (heven : Even (∑ P ∈ S, c P))
    (hhom : IsSquare (∏ P ∈ S, (homEval F (a P) (b P)) ^ c P)) :
    IsSquare (∏ P ∈ S, (algebraMap k K (a P) - algebraMap k K (b P) * α) ^ c P) := by
  have hnorm : IsSquare
      (Algebra.norm k (∏ P ∈ S, (algebraMap k K (a P) - algebraMap k K (b P) * α) ^ c P)) :=
    (isSquare_norm_iff_isSquare_hom_prod_of_even_sum F α hirr hroot hdeg S a b c heven).mpr hhom
  exact isSquare_of_odd_finrank_norm_sq (hdeg.symm ▸ hodd) hclass hnorm

end HomogeneousNormFormula

/-! ## Section 3: Multi-Field Public Root Assembly and Modular Congruence -/

section MultiFieldAssembly

variable {Label FieldId : Type*} {N : ℕ}

/-- Assemble the public modular square root from the rational correction root
and the evaluated roots from each used field. -/
def publicAssembledRoot (fields : Finset FieldId) (wQ : (ZMod N)ˣ)
    (wField : FieldId → (ZMod N)ˣ) : (ZMod N)ˣ :=
  wQ * ∏ j ∈ fields, wField j

/-- Multi-field modular congruence: if each selected row's private coefficient
`A_i = privateRoots i ^ 2` satisfies the global product identity
`∏_{i ∈ mask} A_i = ratCorr * ∏_{j ∈ fields} rowFieldProd_j`, and `wQ`, `wField j`
are square roots of `ratCorr` and `rowFieldProd_j`, then `w_pub = wQ * ∏ wField j`
satisfies `(labelProduct mask (fun _ => 1) privateRoots)^2 = w_pub^2`. -/
theorem labelProduct_sq_eq_assembled_publicRoot
    (mask : Finset Label) (fields : Finset FieldId)
    (privateRoots A : Label → (ZMod N)ˣ)
    (ratCorr wQ : (ZMod N)ˣ) (rowFieldProd wField : FieldId → (ZMod N)ˣ)
    (hA : ∀ i ∈ mask, A i = privateRoots i ^ 2)
    (hQ : wQ ^ 2 = ratCorr)
    (hF : ∀ j ∈ fields, wField j ^ 2 = rowFieldProd j)
    (hglobal : (∏ i ∈ mask, A i) = ratCorr * ∏ j ∈ fields, rowFieldProd j) :
    (labelProduct mask (fun _ => 1) privateRoots) ^ 2 =
      (publicAssembledRoot fields wQ wField) ^ 2 := by
  unfold labelProduct publicAssembledRoot
  rw [← Finset.prod_pow, mul_pow, ← Finset.prod_pow, hQ]
  have hL : (∏ i ∈ mask, (privateRoots i ^ 1) ^ 2) = ∏ i ∈ mask, A i := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [pow_one, hA i hi]
  have hR : (∏ j ∈ fields, wField j ^ 2) = ∏ j ∈ fields, rowFieldProd j := by
    apply Finset.prod_congr rfl
    intro j hj
    exact hF j hj
  rw [hL, hR, hglobal]

/-- Routed multi-field assembly directly from per-row decompositions and per-field
extracted square roots mapped via each field's evaluation homomorphism. -/
theorem labelProduct_sq_eq_routed_field_roots
    {F : FieldId → Type*} [∀ j, CommGroup (F j)]
    (mask : Finset Label) (fields : Finset FieldId)
    (privateRoots rowCorr : Label → (ZMod N)ˣ)
    (evaluate : ∀ j, F j →* (ZMod N)ˣ)
    (comp : ∀ j, Label → F j)
    (wQ : (ZMod N)ˣ) (fieldRoot : ∀ j, F j)
    (hrow : ∀ i ∈ mask, privateRoots i ^ 2 =
      rowCorr i * ∏ j ∈ fields, evaluate j (comp j i))
    (hQ : wQ ^ 2 = ∏ i ∈ mask, rowCorr i)
    (hfieldRoot : ∀ j ∈ fields, fieldRoot j ^ 2 = ∏ i ∈ mask, comp j i) :
    (labelProduct mask (fun _ => 1) privateRoots) ^ 2 =
      (publicAssembledRoot fields wQ (fun j => evaluate j (fieldRoot j))) ^ 2 := by
  apply labelProduct_sq_eq_assembled_publicRoot mask fields privateRoots
    (fun i => privateRoots i ^ 2)
    (∏ i ∈ mask, rowCorr i) wQ
    (fun j => evaluate j (∏ i ∈ mask, comp j i))
    (fun j => evaluate j (fieldRoot j))
    (fun _ _ => rfl) hQ
  · intro j hj
    rw [← map_pow, hfieldRoot j hj]
  · calc
      (∏ i ∈ mask, privateRoots i ^ 2)
          = ∏ i ∈ mask, (rowCorr i * ∏ j ∈ fields, evaluate j (comp j i)) :=
            Finset.prod_congr rfl hrow
      _ = (∏ i ∈ mask, rowCorr i) * ∏ i ∈ mask, ∏ j ∈ fields, evaluate j (comp j i) :=
            Finset.prod_mul_distrib
      _ = (∏ i ∈ mask, rowCorr i) * ∏ j ∈ fields, ∏ i ∈ mask, evaluate j (comp j i) := by
            rw [Finset.prod_comm]
      _ = (∏ i ∈ mask, rowCorr i) * ∏ j ∈ fields, evaluate j (∏ i ∈ mask, comp j i) := by
            congr 1
            apply Finset.prod_congr rfl
            intro j _
            rw [map_prod]

/-- Discharge per-row signed children via `RandomizedRationalChildRouting.discharge_signed_children`
and assemble the resulting per-field roots and global rational correction root into a
modular square congruence for `labelProduct mask (fun _ => 1) privateRoots`. -/
theorem labelProduct_sq_eq_discharged_children [DecidableEq FieldId]
    {Child : Type*} {F : FieldId → Type*} [∀ j, CommGroup (F j)]
    (mask : Finset Label) (fields : Finset FieldId)
    (privateRoots base : Label → (ZMod N)ˣ)
    (children : Label → Finset Child) (lane : Label → Child → FieldId)
    (hroute : ∀ i ∈ mask, ∀ c ∈ children i, lane i c ∈ fields)
    (evaluate : ∀ j, F j →* (ZMod N)ˣ)
    (component : Label → ∀ j, Child → F j)
    (mult : Label → Child → ℤ)
    (childVal correction : Label → Child → (ZMod N)ˣ)
    (hrow : ∀ i ∈ mask,
      privateRoots i ^ 2 = base i * ∏ c ∈ children i, childVal i c ^ mult i c)
    (hchild : ∀ i ∈ mask, ∀ c ∈ children i,
      childVal i c = correction i c * evaluate (lane i c) (component i (lane i c) c))
    (wQ : (ZMod N)ˣ) (fieldRoot : ∀ j, F j)
    (hQ : wQ ^ 2 = ∏ i ∈ mask, (base i * ∏ c ∈ children i, correction i c ^ mult i c))
    (hfieldRoot : ∀ j ∈ fields,
      fieldRoot j ^ 2 = ∏ i ∈ mask,
        ∏ c ∈ (children i).filter (fun c => lane i c = j), component i j c ^ mult i c) :
    (labelProduct mask (fun _ => 1) privateRoots) ^ 2 =
      (publicAssembledRoot fields wQ (fun j => evaluate j (fieldRoot j))) ^ 2 := by
  apply labelProduct_sq_eq_routed_field_roots mask fields privateRoots
    (fun i => base i * ∏ c ∈ children i, correction i c ^ mult i c)
    evaluate
    (fun j i => ∏ c ∈ (children i).filter (fun c => lane i c = j), component i j c ^ mult i c)
    wQ fieldRoot
  · intro i hi
    exact RandomizedRationalChildRouting.discharge_signed_children
      (children i) fields (lane i) (hroute i hi) evaluate (component i)
      (mult i) (childVal i) (correction i) (hrow i hi) (hchild i hi)
  · exact hQ
  · exact hfieldRoot

end MultiFieldAssembly

/-! ## Section 4: Sparse Binary Dependency Mask and Krylov/Padé Solver Bridge -/

section SparseBinaryDependency

variable {Label : Type*} [Fintype Label]

/-- Support finset of a binary dependency vector `v : Label → ZMod 2`. -/
def binarySupport (v : Label → ZMod 2) : Finset Label :=
  Finset.univ.filter (fun i => v i ≠ 0)

theorem mem_binarySupport {v : Label → ZMod 2} {i : Label} :
    i ∈ binarySupport v ↔ v i ≠ 0 := by
  simp [binarySupport]

theorem binarySupport_nonempty_iff {v : Label → ZMod 2} :
    (binarySupport v).Nonempty ↔ v ≠ 0 := by
  constructor
  · rintro ⟨i, hi⟩ hv
    exact (mem_binarySupport.mp hi) (congrFun hv i)
  · intro hv
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact ⟨i, mem_binarySupport.mpr hi⟩

/-- Whenever there are strictly more binary rows (columns of the constraint matrix)
than parity constraints, the constraint matrix has a nonzero binary kernel vector,
equivalently a nonempty binary dependency mask. -/
theorem exists_nonempty_binary_dependency_of_card_lt {Row : Type*} [Fintype Row]
    [DecidableEq Row] [DecidableEq Label]
    (M : Matrix Row Label (ZMod 2)) (hlt : Fintype.card Row < Fintype.card Label) :
    ∃ w : Label → ZMod 2, M.mulVec w = 0 ∧ (binarySupport w).Nonempty := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective M.mulVecLin := LinearMap.ker_eq_bot.mp hbot
    have hle : Module.finrank (ZMod 2) (Label → ZMod 2) ≤
        Module.finrank (ZMod 2) (Row → ZMod 2) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_pi] at hle
    omega
  obtain ⟨w, hwker, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨w, LinearMap.mem_ker.mp hwker, binarySupport_nonempty_iff.mpr hwne⟩

/-- A successful trial of the sparse Krylov/Padé tagged solver produces a binary
coordinate vector in the kernel of `M` whose support mask is nonempty. -/
theorem nonempty_mask_of_taggedSolverSucceeds
    {K Row Tag BasisIndex : Type*} [Field K] [Algebra (ZMod 2) K]
    [Fintype Row] [DecidableEq Row] [DecidableEq Label] [DecidableEq K] [Fintype K]
    (M : Matrix Row Label (ZMod 2)) (H : Matrix Tag Label (ZMod 2))
    (b : Module.Basis BasisIndex (ZMod 2) K)
    (d : Row → K) (e : Label → K) (x u : Label → K)
    (hsucc : TaggedSolverSucceeds M H b d e x u) :
    ∃ bit : BasisIndex,
      let S := taggedOperator M d e
      let g := euclideanRecurrence (Fintype.card Label) (fun j => dotProbe u ((S ^ j) x))
      let w : Label → ZMod 2 := fun j => b.coord bit (((aeval S (g /ₘ X)) x) j)
      M.mulVec w = 0 ∧ (binarySupport w).Nonempty := by
  obtain ⟨_, bit, hM, hH⟩ := hsucc
  refine ⟨bit, hM, binarySupport_nonempty_iff.mpr ?_⟩
  intro hw
  exact hH (by rw [hw, Matrix.mulVec_zero])

/-- With the identity tag matrix `H = 1`, any oversampled binary constraint system
(`|Row| < |Label|`) fails to yield a nonempty sparse Krylov/Padé binary dependency
mask on at most `(2 * M.rank + 1 + |Label|) / |K|` of uniform trials. -/
theorem sparse_pade_nonempty_mask_failure_fraction_le
    {K Row BasisIndex : Type*} {N : ℕ} [Field K] [Algebra (ZMod 2) K]
    [Fintype Row] [DecidableEq Row] [DecidableEq Label] [DecidableEq K] [Fintype K]
    (numbering : Row ⊕ Label ≃ Fin N)
    (M : Matrix Row Label (ZMod 2))
    (b : Module.Basis BasisIndex (ZMod 2) K)
    (hlt : Fintype.card Row < Fintype.card Label) :
    ((badTaggedTrials numbering M (1 : Matrix Label Label (ZMod 2)) b).card : ℚ≥0) /
        Fintype.card (TaggedTrial K Label N) ≤
      (↑(2 * M.rank + 1 + Fintype.card Label) : ℚ≥0) / Fintype.card K := by
  apply bad_tagged_trials_fraction_le numbering M (1 : Matrix Label Label (ZMod 2)) b
  obtain ⟨w, hM, hne⟩ := exists_nonempty_binary_dependency_of_card_lt M hlt
  exact ⟨w, hM, by simpa using binarySupport_nonempty_iff.mp hne⟩

end SparseBinaryDependency

/-! ## Section 5: Direct Wiring into `RandomizedEpochSuccess` -/

section EpochWiring

/-- Construct `TranscriptData` from any nonempty binary mask and verified public root,
choosing a coordinate in the mask with odd multiplicity `1`. -/
noncomputable def transcriptDataOfNonemptyMask {Label : Type*} {N : ℕ}
    (mask : Finset Label) (hne : mask.Nonempty) (publicRoot : (ZMod N)ˣ) :
    TranscriptData Label N where
  labels := mask
  multiplicity := fun _ => 1
  publicRoot := publicRoot
  privateIndex := hne.choose
  mem_labels := hne.choose_spec
  odd_multiplicity := odd_one

/-- Construct `TranscriptData` directly from a nonzero binary dependency vector
`v : Label → ZMod 2` and a verified public root. -/
noncomputable def transcriptDataOfBinaryDependency {Label : Type*} [Fintype Label] {N : ℕ}
    (v : Label → ZMod 2) (hv : v ≠ 0) (publicRoot : (ZMod N)ˣ) :
    TranscriptData Label N :=
  transcriptDataOfNonemptyMask (binarySupport v) (binarySupport_nonempty_iff.mpr hv) publicRoot

/-- Public output of multi-field relation assembly on a good transcript, computed
entirely from public transcript data without accessing private roots. -/
structure PublicMultiFieldTranscript (Label FieldId : Type*) (N : ℕ) where
  mask : Finset Label
  mask_nonempty : mask.Nonempty
  fields : Finset FieldId
  ratCorr : (ZMod N)ˣ
  ratRoot : (ZMod N)ˣ
  ratRoot_sq : ratRoot ^ 2 = ratCorr
  fieldProd : FieldId → (ZMod N)ˣ
  fieldRoot : FieldId → (ZMod N)ˣ
  fieldRoot_sq : ∀ j ∈ fields, fieldRoot j ^ 2 = fieldProd j

/-- The assembled public root `w_Q * ∏_{j ∈ fields} w_j` attached to a public
multi-field transcript. -/
def PublicMultiFieldTranscript.publicRoot {Label FieldId : Type*} {N : ℕ}
    (tr : PublicMultiFieldTranscript Label FieldId N) : (ZMod N)ˣ :=
  publicAssembledRoot tr.fields tr.ratRoot tr.fieldRoot

/-- Convert a public multi-field transcript into `TranscriptData` for the charged
epoch verifier, selecting a coordinate in the nonempty mask with odd multiplicity `1`. -/
noncomputable def PublicMultiFieldTranscript.toTranscriptData {Label FieldId : Type*} {N : ℕ}
    (tr : PublicMultiFieldTranscript Label FieldId N) : TranscriptData Label N :=
  transcriptDataOfNonemptyMask tr.mask tr.mask_nonempty tr.publicRoot

/-- Drop zero-ideal-mass transcripts without losing ideal probability or weakening
the actual acceptance probability of `epochTrial`. -/
private theorem epoch_verified_split_probability_half_of_good
    {Coins Label Public : Type*} [Fintype Coins] [Fintype Label] [DecidableEq Label]
    [DecidableEq Public] {N : ℕ}
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (ideal actual : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public) (data : good → TranscriptData Label N)
    (hcheck : ∀ (t : good) x, observe trace x = t.val →
      (labelProduct (data t).labels (data t).multiplicity x.2) ^ 2 = (data t).publicRoot ^ 2)
    (huniform : ∀ (t : good) x y, observe trace x = t.val → x.1 = y.1 →
      (x.2 (data t).privateIndex) ^ 2 = (y.2 (data t).privateIndex) ^ 2 →
      (∀ j, j ≠ (data t).privateIndex → x.2 j = y.2 j) → ideal x = ideal y)
    (γ ε : ℝ) (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ (ideal.toOuterMeasure {x | observe trace x ∈ good}).toReal)
    (hTV : pmfTotalVariation ideal actual ≤ ε) :
    γ / 2 - ε ≤
      ((actual.map (epochTrial trace good data)).toOuterMeasure {o | o.1 ≠ none}).toReal := by
  classical
  let goodSeen : Finset Public :=
    good.filter (fun t => ∃ x ∈ {x | observe trace x = t}, x ∈ ideal.support)
  have hsub : goodSeen ⊆ good := Finset.filter_subset _ _
  let dataSeen : goodSeen → TranscriptData Label N := fun t => data ⟨t.val, hsub t.property⟩
  have hseen : ∀ t : goodSeen, ∃ x ∈ {x | observe trace x = t.val}, x ∈ ideal.support :=
    fun t => (Finset.mem_filter.mp t.property).2
  have hmass_eq :
      ideal.toOuterMeasure {x | observe trace x ∈ goodSeen} =
        ideal.toOuterMeasure {x | observe trace x ∈ good} := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ ideal.support
    · have hiff : observe trace x ∈ goodSeen ↔ observe trace x ∈ good := by
        constructor
        · exact fun h => hsub h
        · exact fun h => Finset.mem_filter.mpr ⟨h, ⟨x, rfl, hx⟩⟩
      simp [Set.indicator_apply, hiff]
    · have hzero : ideal x = 0 := by
        simpa [PMF.mem_support_iff] using hx
      simp [Set.indicator_apply, hzero]
  have hboundSeen := epoch_verified_split_probability_half hN ho hnot ideal actual trace
    goodSeen dataSeen hseen
    (fun t x hx => hcheck ⟨t.val, hsub t.property⟩ x hx)
    (fun t x y hx h1 h2 h3 => huniform ⟨t.val, hsub t.property⟩ x y hx h1 h2 h3)
    γ ε hγ₀ (by rwa [hmass_eq]) hTV
  refine hboundSeen.trans ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact actual.tsum_coe_indicator_ne_top _
  · apply MeasureTheory.OuterMeasure.mono
    intro x hx
    change (epochTrial trace goodSeen dataSeen x).1 ≠ none at hx
    change (epochTrial trace good data x).1 ≠ none
    unfold epochTrial at hx ⊢
    split_ifs at hx with h1
    · have h2 : observe trace x ∈ good := hsub h1
      rw [dif_pos h2]
      exact hx
    · exact (hx rfl).elim

/-- End-to-end epoch split probability and post-ratio budget theorem for a public
nonempty binary mask and verified public root, wired directly into
`RandomizedEpochSuccess.epoch_verified_split_probability_half`. -/
theorem mask_epoch_verified_split_probability_half
    {Coins Label Public : Type*} [Fintype Coins] [Fintype Label] [DecidableEq Label]
    [DecidableEq Public] {N : ℕ}
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (ideal actual : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public)
    (mask : good → Finset Label) (hne : ∀ t : good, (mask t).Nonempty)
    (publicRoot : good → (ZMod N)ˣ)
    (hcheck : ∀ (t : good) x, observe trace x = t.val →
      (labelProduct (mask t) (fun _ => 1) x.2) ^ 2 = (publicRoot t) ^ 2)
    (huniform : ∀ (t : good) x y, observe trace x = t.val → x.1 = y.1 →
      ∀ i ∈ mask t, (x.2 i) ^ 2 = (y.2 i) ^ 2 →
      (∀ j, j ≠ i → x.2 j = y.2 j) → ideal x = ideal y)
    (γ ε : ℝ) (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ (ideal.toOuterMeasure {x | observe trace x ∈ good}).toReal)
    (hTV : pmfTotalVariation ideal actual ≤ ε) :
    let data : good → TranscriptData Label N :=
      fun t => transcriptDataOfNonemptyMask (mask t) (hne t) (publicRoot t)
    γ / 2 - ε ≤
        ((actual.map (epochTrial trace good data)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
      ∀ x, (epochTrial trace good data x).2 ≤ trialBudget N ∧
        ∀ pair, (epochTrial trace good data x).1 = some pair →
          2 ≤ pair.1 ∧ 2 ≤ pair.2 ∧ pair.1 * pair.2 = N := by
  intro data
  refine ⟨?_, fun x => epochTrial_budget_sound hN trace good data x⟩
  exact epoch_verified_split_probability_half_of_good hN ho hnot ideal actual trace good data
    (fun t x hx => hcheck t x hx)
    (fun t x y hx h1 h2 h3 => huniform t x y hx h1 (hne t).choose (hne t).choose_spec h2 h3)
    γ ε hγ₀ hγ hTV

/-- Full multi-field extraction epoch theorem: given a good public-transcript event
of ideal mass `≥ γ` on which the public solver and multi-field extractor produce a
`PublicMultiFieldTranscript` satisfying the global modular product identity, and a
joint total-variation bound `≤ ε` between ideal and actual samplers, the charged
epoch verifier splits `N` with probability at least `γ / 2 - ε` and post-ratio
gate work at most `trialBudget N`. -/
theorem multiField_epoch_verified_split_probability_half
    {Coins Label FieldId Public : Type*} [Fintype Coins] [Fintype Label] [DecidableEq Label]
    [DecidableEq Public] {N : ℕ}
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (ideal actual : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public)
    (extract : good → PublicMultiFieldTranscript Label FieldId N)
    (hglobal : ∀ (t : good) x, observe trace x = t.val →
      (∏ i ∈ (extract t).mask, (x.2 i) ^ 2) =
        (extract t).ratCorr * ∏ j ∈ (extract t).fields, (extract t).fieldProd j)
    (huniform : ∀ (t : good) x y, observe trace x = t.val → x.1 = y.1 →
      ∀ i ∈ (extract t).mask, (x.2 i) ^ 2 = (y.2 i) ^ 2 →
      (∀ j, j ≠ i → x.2 j = y.2 j) → ideal x = ideal y)
    (γ ε : ℝ) (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ (ideal.toOuterMeasure {x | observe trace x ∈ good}).toReal)
    (hTV : pmfTotalVariation ideal actual ≤ ε) :
    let data : good → TranscriptData Label N := fun t => (extract t).toTranscriptData
    γ / 2 - ε ≤
        ((actual.map (epochTrial trace good data)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
      ∀ x, (epochTrial trace good data x).2 ≤ trialBudget N ∧
        ∀ pair, (epochTrial trace good data x).1 = some pair →
          2 ≤ pair.1 ∧ 2 ≤ pair.2 ∧ pair.1 * pair.2 = N := by
  intro data
  have hcheck : ∀ (t : good) x, observe trace x = t.val →
      (labelProduct (extract t).mask (fun _ => 1) x.2) ^ 2 = (extract t).publicRoot ^ 2 := by
    intro t x hx
    exact labelProduct_sq_eq_assembled_publicRoot
      (extract t).mask (extract t).fields x.2 (fun i => x.2 i ^ 2)
      (extract t).ratCorr (extract t).ratRoot (extract t).fieldProd (extract t).fieldRoot
      (fun _ _ => rfl) (extract t).ratRoot_sq (extract t).fieldRoot_sq (hglobal t x hx)
  exact mask_epoch_verified_split_probability_half hN ho hnot ideal actual trace good
    (fun t => (extract t).mask) (fun t => (extract t).mask_nonempty)
    (fun t => (extract t).publicRoot) hcheck huniform γ ε hγ₀ hγ hTV

end EpochWiring

#print axioms isSquare_base_of_odd_finrank_norm_sq
#print axioms isSquare_of_odd_finrank_norm_sq
#print axioms hom_norm_prod_zpow
#print axioms norm_scaled_linear
#print axioms isSquare_norm_iff_isSquare_hom_prod_of_even_sum
#print axioms isSquare_field_product_of_odd_degree_and_even_parity
#print axioms labelProduct_sq_eq_assembled_publicRoot
#print axioms labelProduct_sq_eq_routed_field_roots
#print axioms labelProduct_sq_eq_discharged_children
#print axioms nonempty_mask_of_taggedSolverSucceeds
#print axioms sparse_pade_nonempty_mask_failure_fraction_le
#print axioms mask_epoch_verified_split_probability_half
#print axioms multiField_epoch_verified_split_probability_half

end Cogentic.RandomizedFieldExtraction
