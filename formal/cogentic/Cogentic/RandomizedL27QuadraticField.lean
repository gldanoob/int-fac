import Cogentic.RandomizedL27MaximalOrder
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.Tactic.ComputeDegree

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
# L27: the ring of integers and discriminant of `ℚ(√-D)`

This file closes the geometric part of `QuadraticFieldGap`: for squarefree `D > 0`
the maximal order of `K = AdjoinRoot (X^2 + D) = ℚ(√-D)` is

* `ℤ[√-D]` if `D ≡ 1, 2 (mod 4)`, with discriminant `-4D`, and
* `ℤ[(1 + √-D)/2]` if `D ≡ 3 (mod 4)`, with discriminant `-D`.

It then proves that `K` is totally complex (`r₁ = 0`, `r₂ = 1`) and that its
regulator is `1`, and hence computes the discriminant of
`ImaginaryQuadraticField D` for every fundamental discriminant `D`.  The only
remaining inputs of `QuadraticFieldGap` are the identifications of the class
number with `h(D)` and of the torsion order with `w(D)`; they are isolated as
`QuadraticArithmeticInput`.

No `sorry`, `admit`, `axiom` or `native_decide` is used.
-/

namespace Cogentic.RandomizedL27ClassNumberFormula

open Polynomial Module NumberField
open scoped BigOperators Matrix NumberField

noncomputable section

/-- The quadratic polynomial `X^2 + D`. -/
abbrev QuadPoly (D : ℤ) : ℚ[X] := Polynomial.X ^ 2 + Polynomial.C (D : ℚ)

theorem quadPoly_monic (D : ℤ) : (QuadPoly D).Monic := by
  unfold QuadPoly
  exact monic_X_pow_add (lt_of_le_of_lt degree_C_le (by norm_num))

theorem algebraMap_int_eq (D : ℤ) (a : ℤ) :
    algebraMap ℤ (ImaginaryQuadraticField D) a =
      algebraMap ℚ (ImaginaryQuadraticField D) (a : ℚ) := by
  rw [IsScalarTower.algebraMap_apply ℤ ℚ (ImaginaryQuadraticField D)]
  norm_num

theorem quadPoly_natDegree (D : ℤ) : (QuadPoly D).natDegree = 2 := by
  unfold QuadPoly
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · simp

variable {D : ℤ} (hD : 0 < D) (hsf : Squarefree D)

/-! ## 1. The quadratic field and its basic structure -/

section Basic

variable [Fact (Irreducible (QuadPoly D))]

/-- The distinguished root `√(-D)`. -/
def sqrtNegD : ImaginaryQuadraticField D :=
  AdjoinRoot.root (QuadPoly D)

theorem sqrtNegD_sq_add :
    (sqrtNegD (D := D)) ^ 2 +
      algebraMap ℚ (ImaginaryQuadraticField D) (D : ℚ) = 0 := by
  have h : (AdjoinRoot.mk (QuadPoly D) Polynomial.X) ^ 2 +
      AdjoinRoot.mk (QuadPoly D) (Polynomial.C (D : ℚ)) = 0 := by
    rw [← map_pow, ← map_add]
    exact AdjoinRoot.mk_self
  simpa [sqrtNegD, AdjoinRoot.algebraMap_eq, AdjoinRoot.of] using h

theorem sqrtNegD_sq :
    (sqrtNegD (D := D)) ^ 2 =
      algebraMap ℚ (ImaginaryQuadraticField D) (-(D : ℚ)) := by
  rw [map_neg, eq_neg_iff_add_eq_zero]
  exact sqrtNegD_sq_add (D := D)

theorem finrank_eq_two : Module.finrank ℚ (ImaginaryQuadraticField D) = 2 := by
  let pb := AdjoinRoot.powerBasis (f := QuadPoly D) (quadPoly_monic D).ne_zero
  rw [PowerBasis.finrank pb]
  rw [AdjoinRoot.powerBasis_dim]
  exact quadPoly_natDegree D

theorem sqrtNegD_notMem_rat (hD0 : 0 < D) :
    sqrtNegD (D := D) ∉ Set.range (algebraMap ℚ (ImaginaryQuadraticField D)) := by
  rintro ⟨q, hq⟩
  have hq2 : q ^ 2 = -(D : ℚ) := by
    apply (algebraMap ℚ (ImaginaryQuadraticField D)).injective
    calc
      algebraMap ℚ (ImaginaryQuadraticField D) (q ^ 2) =
          (algebraMap ℚ (ImaginaryQuadraticField D) q) ^ 2 := by rw [map_pow]
      _ = (sqrtNegD (D := D)) ^ 2 := by rw [← hq]
      _ = algebraMap ℚ (ImaginaryQuadraticField D) (-(D : ℚ)) := sqrtNegD_sq
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD0
  nlinarith [sq_nonneg q]

/-- Every element of the quadratic field is a rational linear combination of `1` and `√(-D)`. -/
theorem exists_rat_coeffs (x : ImaginaryQuadraticField D) :
    ∃ a b : ℚ, x = algebraMap ℚ _ a + algebraMap ℚ _ b * sqrtNegD (D := D) := by
  let pb := AdjoinRoot.powerBasis (f := QuadPoly D) (quadPoly_monic D).ne_zero
  have hdim : pb.dim = 2 := by
    rw [AdjoinRoot.powerBasis_dim]
    exact quadPoly_natDegree D
  let i0 : Fin pb.dim := ⟨0, by omega⟩
  let i1 : Fin pb.dim := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hx' : pb.basis.repr x i0 • pb.basis i0 +
      pb.basis.repr x i1 • pb.basis i1 = x := by
    have hsum : (∑ i ∈ ({i0, i1} : Finset (Fin pb.dim)),
        pb.basis.repr x i • pb.basis i) = x := by
      rw [Finset.sum_subset (Finset.subset_univ _)]
      · exact pb.basis.sum_repr x
      · intro i _ hi
        exfalso
        have hi2 : (i : ℕ) < 2 := by
          have := i.isLt
          omega
        have h01 : i = i0 ∨ i = i1 := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi2 with h0 | h1
          · left; ext; simp [i0]; omega
          · right; ext; simp [i1]; omega
        rcases h01 with rfl | rfl <;> simp at hi
    rwa [Finset.sum_pair hi01] at hsum
  refine ⟨pb.basis.repr x i0, pb.basis.repr x i1, ?_⟩
  have h0 : pb.basis i0 = 1 := by
    rw [PowerBasis.basis_eq_pow]
    simp [i0]
  have h1 : pb.basis i1 = sqrtNegD (D := D) := by
    have hgen : pb.gen = sqrtNegD (D := D) := by
      rw [AdjoinRoot.powerBasis_gen]; rfl
    rw [PowerBasis.basis_eq_pow]
    simp only [i1, pow_one]
    exact hgen
  calc x = pb.basis.repr x i0 • pb.basis i0 + pb.basis.repr x i1 • pb.basis i1 := hx'.symm
    _ = algebraMap ℚ _ (pb.basis.repr x i0) +
          algebraMap ℚ _ (pb.basis.repr x i1) * sqrtNegD := by
        rw [h0, h1, Algebra.smul_def, Algebra.smul_def]
        simp only [mul_one]
        rfl

/-- `√(-D)` is integral over `ℤ`. -/
theorem isIntegral_sqrtNegD : IsIntegral ℤ (sqrtNegD (D := D)) := by
  refine ⟨(Polynomial.X : ℤ[X]) ^ 2 + Polynomial.C D, ?_, ?_⟩
  · exact monic_X_pow_add (lt_of_le_of_lt degree_C_le (by norm_num))
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    simpa using sqrtNegD_sq_add (D := D)

/-- `1` and `√(-D)` are `ℤ`-linearly independent. -/
theorem linearIndependent_one_sqrtNegD (hD0 : 0 < D) :
    LinearIndependent ℤ (fun i : Fin 2 =>
      (![(1 : ImaginaryQuadraticField D), sqrtNegD (D := D)] : Fin 2 → _) i) := by
  change LinearIndependent ℤ ![(1 : ImaginaryQuadraticField D), sqrtNegD (D := D)]
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hst' : algebraMap ℤ (ImaginaryQuadraticField D) s +
      algebraMap ℤ (ImaginaryQuadraticField D) t * sqrtNegD (D := D) = 0 := by
    simpa [Algebra.smul_def] using hst
  have ht : t = 0 := by
    by_contra ht
    apply sqrtNegD_notMem_rat hD0
    have htK : (algebraMap ℤ (ImaginaryQuadraticField D) t) ≠ 0 := by
      intro h
      exact ht ((algebraMap ℤ (ImaginaryQuadraticField D)).injective_int (by simpa using h))
    have h1 : sqrtNegD (D := D) =
        -(algebraMap ℤ (ImaginaryQuadraticField D) s) /
          (algebraMap ℤ (ImaginaryQuadraticField D) t) := by
      field_simp [htK]
      linear_combination hst' 
    refine ⟨-(s : ℚ) / (t : ℚ), ?_⟩
    rw [h1]
    push_cast
    rw [algebraMap_int_eq D s, algebraMap_int_eq D t]
    rfl
  constructor
  · subst ht
    have hs : algebraMap ℤ (ImaginaryQuadraticField D) s = 0 := by
      simpa using hst'
    exact (algebraMap ℤ (ImaginaryQuadraticField D)).injective_int (by simpa using hs)
  · exact ht

end Basic

/-! ## 2. The arithmetic of an integral element -/

/-- If `D` is squarefree and `D * c^2` is an integer for a rational `c`, then `c` is an
integer. -/
theorem int_of_squarefree_mul_sq {D : ℤ} (hsf : Squarefree D) {c : ℚ}
    (h : ∃ k : ℤ, (k : ℚ) = (D : ℚ) * c ^ 2) :
    ∃ n : ℤ, (n : ℚ) = c := by
  let p := c.num
  let q := c.den
  have hqpos : 0 < q := c.pos
  have hqne : (q : ℚ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hc : c = (p : ℚ) / (q : ℚ) := by
    rw [← Rat.num_div_den c]
  obtain ⟨k, hk⟩ := h
  have hkq : (k : ℚ) * (q : ℚ) ^ 2 = (D : ℚ) * (p : ℚ) ^ 2 := by
    rw [hc] at hk
    field_simp at hk ⊢
    rw [hk]
  have hkqZ : k * (q : ℤ) ^ 2 = D * p ^ 2 := by
    have h := hkq
    push_cast at h
    exact_mod_cast h
  have hcop : IsCoprime (p : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using c.reduced
  have hcop2 : IsCoprime ((q : ℤ) ^ 2) ((p : ℤ) ^ 2) :=
    (hcop.symm).pow (m := 2) (n := 2)
  have hdvd : (q : ℤ) ^ 2 ∣ D := by
    refine hcop2.dvd_of_dvd_mul_right ?_
    refine ⟨k, ?_⟩
    rw [← hkqZ]
    ring
  have hunit : IsUnit (q : ℤ) := hsf (q : ℤ) (by simpa [pow_two] using hdvd)
  have hq_one : q = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h
    · exact_mod_cast h
    · have : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hqpos
      omega
  refine ⟨p, ?_⟩
  rw [hc, hq_one]
  norm_num

/-- Squares of even integers are divisible by `4`. -/
theorem four_dvd_sq_of_even {m : ℤ} (h : Even m) : (4 : ℤ) ∣ m ^ 2 := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t ^ 2, by ring⟩

/-- The square of an odd integer is `4 * t + 1`. -/
theorem odd_sq_eq {m : ℤ} (h : Odd m) : ∃ t : ℤ, m ^ 2 = 4 * t + 1 := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t ^ 2 + t, by ring⟩

/-- The square of an even integer is `4 * t ^ 2`. -/
theorem even_sq_eq {m : ℤ} (h : Even m) : ∃ t : ℤ, m ^ 2 = 4 * t ^ 2 := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t, by ring⟩

/-- `4 ∣ m^2` forces `m` to be even. -/
theorem even_of_four_dvd_sq {m : ℤ} (h : (4 : ℤ) ∣ m ^ 2) : Even m := by
  rcases Int.even_or_odd m with hm | hm
  · exact hm
  · exfalso
    obtain ⟨t, ht⟩ := odd_sq_eq hm
    rw [ht] at h
    obtain ⟨u, hu⟩ := h
    omega


/-! ## 3. Parity lemmas in `ZMod 4` -/

private lemma zmod_sq_eq_zero_of_even {m : ℤ} (h : Even m) :
    ((m : ZMod 4)) ^ 2 = 0 := by
  obtain ⟨t, ht⟩ := h
  have h4 : (4 : ZMod 4) = 0 := by decide
  have hm : ((m : ZMod 4)) = (2 : ZMod 4) * (t : ZMod 4) := by
    rw [ht]; push_cast; ring
  rw [hm]
  calc ((2 : ZMod 4) * (t : ZMod 4)) ^ 2 =
      (4 : ZMod 4) * (t : ZMod 4) ^ 2 := by ring
    _ = 0 := by rw [h4, zero_mul]

private lemma zmod_sq_eq_one_of_odd {m : ℤ} (h : Odd m) :
    ((m : ZMod 4)) ^ 2 = 1 := by
  have h1 : (((m ^ 2 : ℤ) : ZMod 4)) = 1 := by
    change (((m ^ 2 : ℤ) : ZMod 4)) = ((1 : ℤ) : ZMod 4)
    rw [ZMod.intCast_eq_intCast_iff']
    simpa using Int.sq_mod_four_eq_one_of_odd h
  calc ((m : ZMod 4)) ^ 2 = (((m ^ 2 : ℤ) : ZMod 4)) := by push_cast; ring
    _ = 1 := h1

private lemma even_of_zmod_sq_eq_zero {m : ℤ} (h : ((m : ZMod 4)) ^ 2 = 0) :
    Even m := by
  rcases Int.even_or_odd m with hm | hm
  · exact hm
  · have h1 := zmod_sq_eq_one_of_odd hm
    rw [h] at h1
    exact absurd h1 (by decide)

private lemma odd_of_zmod_sq_eq_one {m : ℤ} (h : ((m : ZMod 4)) ^ 2 = 1) :
    Odd m := by
  rcases Int.even_or_odd m with hm | hm
  · have h0 := zmod_sq_eq_zero_of_even hm
    rw [h0] at h
    exact absurd h (by decide)
  · exact hm

/-! ## 4. Coefficients of an integral element -/

section Coefficients

variable [Fact (Irreducible (QuadPoly D))]

theorem integral_coefficients (hD : 0 < D) {x : ImaginaryQuadraticField D}
    (hx : IsIntegral ℤ x) (a b : ℚ)
    (hxab : x = algebraMap ℚ _ a + algebraMap ℚ _ b * sqrtNegD (D := D))
    (hb : b ≠ 0) :
    (∃ m : ℤ, (m : ℚ) = 2 * a) ∧
      (∃ k : ℤ, (k : ℚ) = a ^ 2 + (D : ℚ) * b ^ 2) := by
  let P : ℚ[X] := Polynomial.X ^ 2 - Polynomial.C (2 * a) * Polynomial.X +
    Polynomial.C (a ^ 2 + (D : ℚ) * b ^ 2)
  have hPmonic : P.Monic := by
    unfold P
    monicity!
  have hPdeg : P.natDegree = 2 := by
    unfold P
    compute_degree!
  have hP : Polynomial.aeval x P = 0 := by
    rw [hxab]
    simp only [P, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_ofNat]
    linear_combination (algebraMap ℚ (ImaginaryQuadraticField D) b) ^ 2 *
      sqrtNegD_sq_add (D := D)
  have hPirr : Irreducible P := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hPdeg]; norm_num
    · intro r hr
      have hDq : (0 : ℚ) < D := by exact_mod_cast hD
      have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
      have hpos : 0 < (r - a) ^ 2 + (D : ℚ) * b ^ 2 := by positivity
      have heval : P.eval r = (r - a) ^ 2 + (D : ℚ) * b ^ 2 := by
        simp [P]; ring
      rw [Polynomial.IsRoot.def] at hr
      rw [heval] at hr
      nlinarith
  have hmin : P = minpoly ℚ x :=
    minpoly.eq_of_irreducible_of_monic hPirr hP hPmonic
  have hmap : minpoly ℚ x = (minpoly ℤ x).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) hx
  have hPeq : P = (minpoly ℤ x).map (algebraMap ℤ ℚ) := hmin.trans hmap
  have hPcoeff1 : P.coeff 1 = -(2 * a) := by
    simp only [P, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    norm_num
  have hPcoeff0 : P.coeff 0 = a ^ 2 + (D : ℚ) * b ^ 2 := by
    simp only [P, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    norm_num
  have hcoeff1 : ((minpoly ℤ x).coeff 1 : ℚ) = -(2 * a) := by
    have h1 := congrArg (fun p : ℚ[X] => p.coeff 1) hPeq
    rw [hPcoeff1] at h1
    simpa using h1.symm
  have hcoeff0 : ((minpoly ℤ x).coeff 0 : ℚ) =
      a ^ 2 + (D : ℚ) * b ^ 2 := by
    have h0 := congrArg (fun p : ℚ[X] => p.coeff 0) hPeq
    rw [hPcoeff0] at h0
    simpa using h0.symm
  refine ⟨⟨-(minpoly ℤ x).coeff 1, ?_⟩, ⟨(minpoly ℤ x).coeff 0, hcoeff0⟩⟩
  push_cast
  linarith

/-- The common parity analysis: for squarefree `D`, an integral element has half-integral
coefficients, and in the residues `1, 2` modulo `4` the coefficients are integral. -/
theorem half_integral_coefficients (hD : 0 < D) (hsf : Squarefree D)
    {x : ImaginaryQuadraticField D} (hx : IsIntegral ℤ x)
    (hxab : ∃ a b : ℚ, x = algebraMap ℚ _ a + algebraMap ℚ _ b * sqrtNegD (D := D)) :
    ∃ (a b : ℚ) (m n k : ℤ),
      x = algebraMap ℚ _ a + algebraMap ℚ _ b * sqrtNegD (D := D) ∧
      (m : ℚ) = 2 * a ∧ (n : ℚ) = 2 * b ∧
      (k : ℚ) = a ^ 2 + (D : ℚ) * b ^ 2 := by
  classical
  by_cases hb : ∃ b : ℚ, ∃ a : ℚ,
      x = algebraMap ℚ _ a + algebraMap ℚ _ b * sqrtNegD (D := D) ∧ b ≠ 0
  · obtain ⟨b, a, hxab', hb0⟩ := hb
    obtain ⟨⟨m, hm⟩, ⟨k, hk⟩⟩ := integral_coefficients hD hx a b hxab' hb0
    have hDsq : ∃ t : ℤ, (t : ℚ) = (D : ℚ) * (2 * b) ^ 2 := by
      refine ⟨4 * k - m ^ 2, ?_⟩
      push_cast
      rw [hm, hk]
      ring
    obtain ⟨n, hn⟩ := int_of_squarefree_mul_sq hsf hDsq
    exact ⟨a, b, m, n, k, hxab', hm, hn, hk⟩
  · obtain ⟨a, b, hxab'⟩ := hxab
    have hb0 : b = 0 := by
      by_contra h
      exact hb ⟨b, a, hxab', h⟩
    have hxq : x = algebraMap ℚ _ a := by simpa [hb0] using hxab'
    have hint : IsIntegral ℤ a := by
      apply (isIntegral_algebraMap_iff (algebraMap ℚ (ImaginaryQuadraticField D)).injective).mp
      rwa [← hxq]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨a, 0, 2 * z, 0, z ^ 2, ?_, ?_, ?_, ?_⟩
    · simpa [hb0] using hxab'
    · push_cast; rw [show (z : ℚ) = a from hz]
    · norm_num
    · push_cast; rw [show (z : ℚ) = a from hz]; ring

end Coefficients

/-! ## 5. The ring of integers in the two residue classes -/

section RingOfIntegers

variable [Fact (Irreducible (QuadPoly D))]

/-- `(1 + √(-D)) / 2`. -/
def halfSqrtNegD : ImaginaryQuadraticField D := (1 + sqrtNegD (D := D)) / 2

theorem isIntegral_halfSqrtNegD (hmod : D % 4 = 3) :
    IsIntegral ℤ (halfSqrtNegD (D := D)) := by
  let c : ℤ := (D + 1) / 4
  have hDc : D = 4 * c - 1 := by
    dsimp [c]
    omega
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C c, ?_, ?_⟩
  · monicity!
  · have hc : (algebraMap ℤ (ImaginaryQuadraticField D) c : ImaginaryQuadraticField D) =
        ((algebraMap ℚ (ImaginaryQuadraticField D) (D : ℚ)) + 1) / 4 := by
      have hcQ : (c : ℚ) = ((D : ℚ) + 1) / 4 := by
        rw [hDc]; push_cast; ring
      have := congrArg (algebraMap ℚ (ImaginaryQuadraticField D)) hcQ
      simpa [map_div₀, map_add] using this
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, halfSqrtNegD]
    rw [hc]
    linear_combination (1 / 4 : ImaginaryQuadraticField D) * sqrtNegD_sq_add (D := D)

theorem exists_int_coeffs_of_mod_one_two (hD : 0 < D) (hsf : Squarefree D)
    (hmod : D % 4 = 1 ∨ D % 4 = 2) (x : 𝓞 (ImaginaryQuadraticField D)) :
    ∃ a b : ℤ, (x : ImaginaryQuadraticField D) =
      algebraMap ℤ _ a + algebraMap ℤ _ b * sqrtNegD (D := D) := by
  obtain ⟨a, b, m, n, k, hxab, hm, hn, hk⟩ :=
    half_integral_coefficients hD hsf (NumberField.RingOfIntegers.isIntegral_coe x)
      (exists_rat_coeffs (D := D) (x : ImaginaryQuadraticField D))
  have h4 : (4 * k : ℚ) = (m : ℚ) ^ 2 + (D : ℚ) * (n : ℚ) ^ 2 := by
    rw [hm, hk, hn]; ring
  have h4Z : 4 * k = m ^ 2 + D * n ^ 2 := by
    have h := h4
    push_cast at h
    exact_mod_cast h
  have hDz : (D : ZMod 4) = 1 ∨ (D : ZMod 4) = 2 := by
    rcases hmod with h | h
    · left
      change (D : ZMod 4) = ((1 : ℤ) : ZMod 4)
      rw [ZMod.intCast_eq_intCast_iff']
      norm_num
      exact h
    · right
      change (D : ZMod 4) = ((2 : ℤ) : ZMod 4)
      rw [ZMod.intCast_eq_intCast_iff']
      norm_num
      exact h
  have h4z : ((m : ZMod 4) ^ 2 + (D : ZMod 4) * (n : ZMod 4) ^ 2) = 0 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 4)) h4Z
    push_cast at h
    have h4zero : (4 : ZMod 4) = 0 := by decide
    rw [h4zero, zero_mul] at h
    simpa using h.symm
  have hn_even : Even n := by
    by_contra hne
    have hno : Odd n := Int.not_even_iff_odd.mp hne
    have hnz := zmod_sq_eq_one_of_odd hno
    rw [hnz] at h4z
    rcases Int.even_or_odd m with hme | hmo
    · have hmz := zmod_sq_eq_zero_of_even hme
      rw [hmz] at h4z
      rcases hDz with hD1 | hD2
      · rw [hD1] at h4z
        exact (by decide : ¬ ((0 : ZMod 4) + 1 * 1 = 0)) h4z
      · rw [hD2] at h4z
        exact (by decide : ¬ ((0 : ZMod 4) + 2 * 1 = 0)) h4z
    · have hmz := zmod_sq_eq_one_of_odd hmo
      rw [hmz] at h4z
      rcases hDz with hD1 | hD2
      · rw [hD1] at h4z
        exact (by decide : ¬ ((1 : ZMod 4) + 1 * 1 = 0)) h4z
      · rw [hD2] at h4z
        exact (by decide : ¬ ((1 : ZMod 4) + 2 * 1 = 0)) h4z
  obtain ⟨v, hv⟩ := hn_even
  have hnsq : n ^ 2 = 4 * v ^ 2 := by rw [hv]; ring
  have h4m : (4 : ℤ) ∣ m ^ 2 := by
    refine ⟨k - D * v ^ 2, ?_⟩
    rw [hnsq] at h4Z
    ring_nf at h4Z ⊢
    linarith
  have hm_even := even_of_four_dvd_sq h4m
  obtain ⟨u, hu⟩ := hm_even
  have ha : a = (u : ℚ) := by
    have h : (m : ℚ) = (u : ℚ) + (u : ℚ) := by exact_mod_cast hu
    linarith
  have hb : b = (v : ℚ) := by
    have h : (n : ℚ) = (v : ℚ) + (v : ℚ) := by exact_mod_cast hv
    linarith
  refine ⟨u, v, ?_⟩
  change (algebraMap (𝓞 (ImaginaryQuadraticField D)) (ImaginaryQuadraticField D)) x =
    (algebraMap ℤ (ImaginaryQuadraticField D)) u +
      (algebraMap ℤ (ImaginaryQuadraticField D)) v * sqrtNegD
  rw [hxab, ha, hb]
  rw [algebraMap_int_eq D u, algebraMap_int_eq D v]
  ac_rfl

theorem exists_int_coeffs_of_mod_three (hD : 0 < D) (hsf : Squarefree D)
    (hmod : D % 4 = 3) (x : 𝓞 (ImaginaryQuadraticField D)) :
    ∃ a b : ℤ, (x : ImaginaryQuadraticField D) =
      algebraMap ℤ _ a + algebraMap ℤ _ b * halfSqrtNegD := by
  obtain ⟨a, b, m, n, k, hxab, hm, hn, hk⟩ :=
    half_integral_coefficients hD hsf (NumberField.RingOfIntegers.isIntegral_coe x)
      (exists_rat_coeffs (D := D) (x : ImaginaryQuadraticField D))
  have h4 : (4 * k : ℚ) = (m : ℚ) ^ 2 + (D : ℚ) * (n : ℚ) ^ 2 := by
    rw [hm, hk, hn]; ring
  have h4Z : 4 * k = m ^ 2 + D * n ^ 2 := by
    have h := h4
    push_cast at h
    exact_mod_cast h
  have hDz : (D : ZMod 4) = 3 := by
    change (D : ZMod 4) = ((3 : ℤ) : ZMod 4)
    rw [ZMod.intCast_eq_intCast_iff']
    norm_num
    exact hmod
  have h4z : ((m : ZMod 4) ^ 2 + (D : ZMod 4) * (n : ZMod 4) ^ 2) = 0 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 4)) h4Z
    push_cast at h
    have h4zero : (4 : ZMod 4) = 0 := by decide
    rw [h4zero, zero_mul] at h
    simpa using h.symm
  rcases Int.even_or_odd n with hne | hno
  · -- n even, hence m even
    obtain ⟨v, hv⟩ := hne
    have hnsq : n ^ 2 = 4 * v ^ 2 := by rw [hv]; ring
    have h4m : (4 : ℤ) ∣ m ^ 2 := by
      refine ⟨k - D * v ^ 2, ?_⟩
      rw [hnsq] at h4Z
      ring_nf at h4Z ⊢
      linarith
    obtain ⟨u, hu⟩ := even_of_four_dvd_sq h4m
    have ha : a = (u : ℚ) := by
      have h : (m : ℚ) = (u : ℚ) + (u : ℚ) := by exact_mod_cast hu
      linarith
    have hb : b = (v : ℚ) := by
      have h : (n : ℚ) = (v : ℚ) + (v : ℚ) := by exact_mod_cast hv
      linarith
    refine ⟨u - v, 2 * v, ?_⟩
    change (algebraMap (𝓞 (ImaginaryQuadraticField D)) (ImaginaryQuadraticField D)) x =
      (algebraMap ℤ (ImaginaryQuadraticField D)) (u - v) +
        (algebraMap ℤ (ImaginaryQuadraticField D)) (2 * v) * halfSqrtNegD
    rw [hxab, ha, hb]
    simp only [halfSqrtNegD]
    push_cast
    norm_num
    ring
  · -- n odd, hence m odd
    have hnz := zmod_sq_eq_one_of_odd hno
    rw [hnz] at h4z
    simp only [mul_one] at h4z
    have hm_odd : Odd m := by
      rcases Int.even_or_odd m with hme | hmo
      · have hmz := zmod_sq_eq_zero_of_even hme
        rw [hmz, hDz] at h4z
        exfalso
        exact (by decide : ¬ ((0 : ZMod 4) + 3 * 1 = 0)) h4z
      · exact hmo
    obtain ⟨v, hv⟩ := hno
    obtain ⟨u, hu⟩ := hm_odd
    have ha : a = (u : ℚ) + 1 / 2 := by
      have h : (m : ℚ) = (2 * u + 1 : ℚ) := by exact_mod_cast hu
      linarith
    have hb : b = (v : ℚ) + 1 / 2 := by
      have h : (n : ℚ) = (2 * v + 1 : ℚ) := by exact_mod_cast hv
      linarith
    refine ⟨u - v, 2 * v + 1, ?_⟩
    change (algebraMap (𝓞 (ImaginaryQuadraticField D)) (ImaginaryQuadraticField D)) x =
      (algebraMap ℤ (ImaginaryQuadraticField D)) (u - v) +
        (algebraMap ℤ (ImaginaryQuadraticField D)) (2 * v + 1) * halfSqrtNegD
    rw [hxab, ha, hb]
    simp only [halfSqrtNegD]
    push_cast
    norm_num
    ring

/-- **The ring of integers of `ℚ(√-D)` for `D ≡ 1, 2 (mod 4)` is `ℤ[√-D]`.** -/
theorem mem_ringOfIntegers_iff_zsqrt (hD : 0 < D) (hsf : Squarefree D)
    (hmod : D % 4 = 1 ∨ D % 4 = 2) (x : ImaginaryQuadraticField D) :
    x ∈ (algebraMap (𝓞 (ImaginaryQuadraticField D)) (ImaginaryQuadraticField D)).range ↔
      ∃ a b : ℤ, x = algebraMap ℤ _ a + algebraMap ℤ _ b * sqrtNegD (D := D) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact exists_int_coeffs_of_mod_one_two hD hsf hmod y
  · rintro ⟨a, b, rfl⟩
    have h : IsIntegral ℤ (algebraMap ℤ (ImaginaryQuadraticField D) a +
        algebraMap ℤ (ImaginaryQuadraticField D) b * sqrtNegD (D := D)) := by
      refine IsIntegral.add isIntegral_algebraMap ?_
      exact IsIntegral.mul isIntegral_algebraMap isIntegral_sqrtNegD
    exact ⟨IsIntegralClosure.mk' (𝓞 (ImaginaryQuadraticField D)) _ h,
      IsIntegralClosure.algebraMap_mk' _ _ h⟩

/-- **The ring of integers of `ℚ(√-D)` for `D ≡ 3 (mod 4)` is `ℤ[(1+√-D)/2]`.** -/
theorem mem_ringOfIntegers_iff_half (hD : 0 < D) (hsf : Squarefree D)
    (hmod : D % 4 = 3) (x : ImaginaryQuadraticField D) :
    x ∈ (algebraMap (𝓞 (ImaginaryQuadraticField D)) (ImaginaryQuadraticField D)).range ↔
      ∃ a b : ℤ, x = algebraMap ℤ _ a + algebraMap ℤ _ b * halfSqrtNegD := by
  constructor
  · rintro ⟨y, rfl⟩
    exact exists_int_coeffs_of_mod_three hD hsf hmod y
  · rintro ⟨a, b, rfl⟩
    have h : IsIntegral ℤ (algebraMap ℤ (ImaginaryQuadraticField D) a +
        algebraMap ℤ (ImaginaryQuadraticField D) b * halfSqrtNegD) := by
      refine IsIntegral.add isIntegral_algebraMap ?_
      exact IsIntegral.mul isIntegral_algebraMap (isIntegral_halfSqrtNegD hmod)
    exact ⟨IsIntegralClosure.mk' (𝓞 (ImaginaryQuadraticField D)) _ h,
      IsIntegralClosure.algebraMap_mk' _ _ h⟩

end RingOfIntegers

/-! ## 6. Discriminants -/

section Discriminant

variable [Fact (Irreducible (QuadPoly D))]

theorem trace_one :
    Algebra.trace ℚ (ImaginaryQuadraticField D) (1 : ImaginaryQuadraticField D) = 2 := by
  rw [show (1 : ImaginaryQuadraticField D) = algebraMap ℚ _ 1 by simp,
    Algebra.trace_algebraMap]
  simp [finrank_eq_two]

theorem trace_sqrtNegD :
    Algebra.trace ℚ (ImaginaryQuadraticField D) (sqrtNegD (D := D)) = 0 := by
  change Algebra.trace ℚ (AdjoinRoot (QuadPoly D)) (sqrtNegD (D := D)) = 0
  let pb := AdjoinRoot.powerBasis (f := QuadPoly D) (quadPoly_monic D).ne_zero
  have hgen : pb.gen = sqrtNegD (D := D) := by
    rw [AdjoinRoot.powerBasis_gen]; rfl
  have htrace := PowerBasis.trace_gen_eq_nextCoeff_minpoly pb
  rw [hgen] at htrace
  have hmin : minpoly ℚ (sqrtNegD (D := D)) = QuadPoly D := by
    have := AdjoinRoot.minpoly_powerBasis_gen_of_monic (f := QuadPoly D) (quadPoly_monic D)
    rwa [hgen] at this
  calc Algebra.trace ℚ (AdjoinRoot (QuadPoly D)) (sqrtNegD (D := D))
      = -(minpoly ℚ (sqrtNegD (D := D))).nextCoeff := htrace
    _ = 0 := by
        rw [hmin]
        have hcoeff : (QuadPoly D).coeff 1 = 0 := by
          rw [QuadPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]
          norm_num
        have hnext : (QuadPoly D).nextCoeff = 0 := by
          unfold Polynomial.nextCoeff
          rw [quadPoly_natDegree]
          simp [hcoeff]
        rw [hnext]
        ring

theorem trace_sqrtNegD_sq :
    Algebra.trace ℚ (ImaginaryQuadraticField D)
      ((sqrtNegD (D := D)) ^ 2) = -(2 * (D : ℚ)) := by
  rw [sqrtNegD_sq (D := D), Algebra.trace_algebraMap]
  simp [finrank_eq_two]

theorem discr_pair (x y : ImaginaryQuadraticField D) :
    Algebra.discr ℚ (fun i : Fin 2 => ![x, y] i) =
      Algebra.trace ℚ _ (x * x) * Algebra.trace ℚ _ (y * y) -
        (Algebra.trace ℚ _ (x * y)) ^ 2 := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, mul_comm]
  ring

theorem discr_one_sqrtNegD :
    Algebra.discr ℚ (fun i : Fin 2 =>
      ![(1 : ImaginaryQuadraticField D), sqrtNegD (D := D)] i) = -(4 * (D : ℚ)) := by
  rw [discr_pair]
  rw [show (1 : ImaginaryQuadraticField D) * 1 = 1 by ring,
    show sqrtNegD (D := D) * sqrtNegD (D := D) = (sqrtNegD (D := D)) ^ 2 by ring,
    show (1 : ImaginaryQuadraticField D) * sqrtNegD (D := D) = sqrtNegD (D := D) by ring]
  rw [trace_one, trace_sqrtNegD_sq, trace_sqrtNegD]
  ring

theorem discr_one_halfSqrtNegD :
    Algebra.discr ℚ (fun i : Fin 2 =>
      ![(1 : ImaginaryQuadraticField D), halfSqrtNegD (D := D)] i) = -(D : ℚ) := by
  have h := Algebra.discr_of_matrix_vecMul (A := ℚ) (B := ImaginaryQuadraticField D)
    (b := fun i : Fin 2 => ![(1 : ImaginaryQuadraticField D), sqrtNegD (D := D)] i)
    (P := !![(1 : ℚ), (1 / 2 : ℚ); 0, (1 / 2 : ℚ)])
  have hb : ((fun j : Fin 2 => ![(1 : ImaginaryQuadraticField D), sqrtNegD (D := D)] j) ᵥ*
        (!![(1 : ℚ), (1 / 2 : ℚ); 0, (1 / 2 : ℚ)]).map
          (algebraMap ℚ (ImaginaryQuadraticField D))) =
      (fun i : Fin 2 =>
        ![(1 : ImaginaryQuadraticField D), halfSqrtNegD (D := D)] i) := by
    funext i
    fin_cases i <;>
      simp [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two, halfSqrtNegD] <;> ring
  rw [hb] at h
  rw [h, discr_one_sqrtNegD]
  have hdet : Matrix.det (!![(1 : ℚ), (1 / 2 : ℚ); 0, (1 / 2 : ℚ)] :
      Matrix (Fin 2) (Fin 2) ℚ) = 1 / 2 := by
    rw [Matrix.det_fin_two_of]; norm_num
  rw [hdet]
  ring

theorem discr_eq_neg_four_mul_of_mod_one_two (hD : 0 < D) (hsf : Squarefree D)
    (hmod : D % 4 = 1 ∨ D % 4 = 2) :
    NumberField.discr (ImaginaryQuadraticField D) = -(4 * D) := by
  have hint : ∀ i : Fin 2, IsIntegral ℤ
      (![(1 : ImaginaryQuadraticField D), sqrtNegD (D := D)] i) := by
    intro i
    fin_cases i
    · simpa using (isIntegral_one : IsIntegral ℤ (1 : ImaginaryQuadraticField D))
    · simpa using isIntegral_sqrtNegD (D := D)
  let w : Fin 2 → 𝓞 (ImaginaryQuadraticField D) :=
    fun i => ⟨![(1 : ImaginaryQuadraticField D), sqrtNegD (D := D)] i, hint i⟩
  have hli : LinearIndependent ℤ w := by
    have hli_v := linearIndependent_one_sqrtNegD hD
    rw [linearIndependent_iff] at hli_v ⊢
    intro l hl
    apply hli_v l
    have hcomp : (Finsupp.linearCombination ℤ
        ((algebraMap (𝓞 (ImaginaryQuadraticField D))
          (ImaginaryQuadraticField D)) ∘ w)) l = 0 := by
      have h := Finsupp.apply_linearCombination
        (f := (algebraMap (𝓞 (ImaginaryQuadraticField D))
          (ImaginaryQuadraticField D)).toAddMonoidHom.toIntLinearMap) (v := w) (l := l)
      rw [hl] at h
      simpa using h.symm
    have hcomp' : (Finsupp.linearCombination ℤ
        (fun i => ![ (1 : ImaginaryQuadraticField D), sqrtNegD (D := D)] i)) l = 0 := by
      have hfun : (⇑(algebraMap (𝓞 (ImaginaryQuadraticField D))
          (ImaginaryQuadraticField D)) ∘ w) =
          (fun i => ![ (1 : ImaginaryQuadraticField D), sqrtNegD (D := D)] i) := by
        funext i
        rfl
      rw [hfun] at hcomp
      exact hcomp
    exact hcomp'
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range w) := by
    intro x _
    obtain ⟨a, b, hx⟩ := exists_int_coeffs_of_mod_one_two hD hsf hmod x
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr
      ⟨fun i : Fin 2 => if i = 0 then a else b, ?_⟩
    have hsum : (∑ i : Fin 2, (if i = 0 then a else b) • w i) =
        a • w 0 + b • w 1 := by
      rw [Fin.sum_univ_two]
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp [h10]
    rw [hsum]
    apply Subtype.ext
    change (algebraMap (𝓞 (ImaginaryQuadraticField D)) (ImaginaryQuadraticField D)
      (a • w 0 + b • w 1)) =
      (algebraMap (𝓞 (ImaginaryQuadraticField D)) (ImaginaryQuadraticField D) x)
    rw [map_add, map_zsmul, map_zsmul]
    have h1w : (algebraMap (𝓞 (ImaginaryQuadraticField D))
        (ImaginaryQuadraticField D) (w 0)) = 1 := by rfl
    have h2w : (algebraMap (𝓞 (ImaginaryQuadraticField D))
        (ImaginaryQuadraticField D) (w 1)) = sqrtNegD (D := D) := by rfl
    rw [h1w, h2w]
    simp only [Algebra.smul_def, mul_one]
    exact hx.symm
  let bZ : Basis (Fin 2) ℤ (𝓞 (ImaginaryQuadraticField D)) := Basis.mk hli hsp
  have hdiscrZ : Algebra.discr ℤ bZ = NumberField.discr (ImaginaryQuadraticField D) :=
    NumberField.discr_eq_discr _ bZ
  have hloc := Algebra.discr_localizationLocalization (R := ℤ) (Rₘ := ℚ)
    (M := nonZeroDivisors ℤ) (S := 𝓞 (ImaginaryQuadraticField D))
    (Sₘ := ImaginaryQuadraticField D) bZ
  have heq : (bZ.localizationLocalization ℚ (nonZeroDivisors ℤ)
      (ImaginaryQuadraticField D)) =
      (fun i : Fin 2 => ![(1 : ImaginaryQuadraticField D), sqrtNegD (D := D)] i) := by
    ext i
    rw [Basis.localizationLocalization_apply, Basis.mk_apply]
    rfl
  have hloc' : Algebra.discr ℚ (bZ.localizationLocalization ℚ (nonZeroDivisors ℤ)
      (ImaginaryQuadraticField D)) = (NumberField.discr (ImaginaryQuadraticField D) : ℚ) := by
    rw [hloc, hdiscrZ]
    rfl
  have : (NumberField.discr (ImaginaryQuadraticField D) : ℚ) = -(4 * (D : ℚ)) := by
    rw [← hloc', heq, discr_one_sqrtNegD]
  exact_mod_cast this

theorem discr_eq_neg_of_mod_three (hD : 0 < D) (hsf : Squarefree D) (hmod : D % 4 = 3) :
    NumberField.discr (ImaginaryQuadraticField D) = -D := by
  have hint : ∀ i : Fin 2, IsIntegral ℤ
      (![(1 : ImaginaryQuadraticField D), halfSqrtNegD (D := D)] i) := by
    intro i
    fin_cases i
    · simpa using (isIntegral_one : IsIntegral ℤ (1 : ImaginaryQuadraticField D))
    · simpa using isIntegral_halfSqrtNegD hmod
  let w : Fin 2 → 𝓞 (ImaginaryQuadraticField D) :=
    fun i => ⟨![(1 : ImaginaryQuadraticField D), halfSqrtNegD (D := D)] i, hint i⟩
  have hli : LinearIndependent ℤ w := by
    have hli_v : LinearIndependent ℤ (fun i : Fin 2 =>
        ![(1 : ImaginaryQuadraticField D), halfSqrtNegD (D := D)] i) := by
      change LinearIndependent ℤ ![(1 : ImaginaryQuadraticField D), halfSqrtNegD (D := D)]
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have hst' : algebraMap ℤ (ImaginaryQuadraticField D) s +
          algebraMap ℤ (ImaginaryQuadraticField D) t *
            halfSqrtNegD (D := D) = 0 := by
        simpa [Algebra.smul_def] using hst
      have hβ : (2 : ImaginaryQuadraticField D) * halfSqrtNegD (D := D) =
          1 + sqrtNegD (D := D) := by
        simp [halfSqrtNegD]; ring
      have hαβ : sqrtNegD (D := D) =
          2 * halfSqrtNegD (D := D) - 1 := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact hβ.symm
      have hmul : algebraMap ℤ (ImaginaryQuadraticField D) (2 * s + t) +
          algebraMap ℤ (ImaginaryQuadraticField D) t *
            sqrtNegD (D := D) = 0 := by
        calc algebraMap ℤ (ImaginaryQuadraticField D) (2 * s + t) +
              algebraMap ℤ (ImaginaryQuadraticField D) t * sqrtNegD (D := D)
            = algebraMap ℤ (ImaginaryQuadraticField D) (2 * s + t) +
                algebraMap ℤ (ImaginaryQuadraticField D) t *
                  (2 * halfSqrtNegD (D := D) - 1) := by rw [hαβ]
          _ = 2 * (algebraMap ℤ (ImaginaryQuadraticField D) s +
                algebraMap ℤ (ImaginaryQuadraticField D) t * halfSqrtNegD (D := D)) := by
              push_cast
              norm_num
              ring
          _ = 0 := by rw [hst']; ring
      have hli0 := linearIndependent_one_sqrtNegD hD
      change LinearIndependent ℤ ![(1 : ImaginaryQuadraticField D), sqrtNegD (D := D)] at hli0
      rw [LinearIndependent.pair_iff] at hli0
      have hmul' : (2 * s + t) • (1 : ImaginaryQuadraticField D) +
          t • sqrtNegD (D := D) = 0 := by
        simpa [Algebra.smul_def] using hmul
      obtain ⟨h2st, ht⟩ := hli0 (2 * s + t) t hmul'
      constructor
      · omega
      · exact ht
    rw [linearIndependent_iff] at hli_v ⊢
    intro l hl
    apply hli_v l
    have hcomp : (Finsupp.linearCombination ℤ
        ((algebraMap (𝓞 (ImaginaryQuadraticField D))
          (ImaginaryQuadraticField D)) ∘ w)) l = 0 := by
      have h := Finsupp.apply_linearCombination
        (f := (algebraMap (𝓞 (ImaginaryQuadraticField D))
          (ImaginaryQuadraticField D)).toAddMonoidHom.toIntLinearMap) (v := w) (l := l)
      rw [hl] at h
      simpa using h.symm
    have hcomp' : (Finsupp.linearCombination ℤ
        (fun i => ![ (1 : ImaginaryQuadraticField D), halfSqrtNegD (D := D)] i)) l = 0 := by
      have hfun : (⇑(algebraMap (𝓞 (ImaginaryQuadraticField D))
          (ImaginaryQuadraticField D)) ∘ w) =
          (fun i => ![ (1 : ImaginaryQuadraticField D), halfSqrtNegD (D := D)] i) := by
        funext i
        rfl
      rw [hfun] at hcomp
      exact hcomp
    exact hcomp'
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range w) := by
    intro x _
    obtain ⟨a, b, hx⟩ := exists_int_coeffs_of_mod_three hD hsf hmod x
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr
      ⟨fun i : Fin 2 => if i = 0 then a else b, ?_⟩
    have hsum : (∑ i : Fin 2, (if i = 0 then a else b) • w i) =
        a • w 0 + b • w 1 := by
      rw [Fin.sum_univ_two]
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp [h10]
    rw [hsum]
    apply Subtype.ext
    change (algebraMap (𝓞 (ImaginaryQuadraticField D)) (ImaginaryQuadraticField D)
      (a • w 0 + b • w 1)) =
      (algebraMap (𝓞 (ImaginaryQuadraticField D)) (ImaginaryQuadraticField D) x)
    rw [map_add, map_zsmul, map_zsmul]
    have h1w : (algebraMap (𝓞 (ImaginaryQuadraticField D))
        (ImaginaryQuadraticField D) (w 0)) = 1 := by rfl
    have h2w : (algebraMap (𝓞 (ImaginaryQuadraticField D))
        (ImaginaryQuadraticField D) (w 1)) = halfSqrtNegD (D := D) := by rfl
    rw [h1w, h2w]
    simp only [Algebra.smul_def, mul_one]
    exact hx.symm
  let bZ : Basis (Fin 2) ℤ (𝓞 (ImaginaryQuadraticField D)) := Basis.mk hli hsp
  have hdiscrZ : Algebra.discr ℤ bZ = NumberField.discr (ImaginaryQuadraticField D) :=
    NumberField.discr_eq_discr _ bZ
  have hloc := Algebra.discr_localizationLocalization (R := ℤ) (Rₘ := ℚ)
    (M := nonZeroDivisors ℤ) (S := 𝓞 (ImaginaryQuadraticField D))
    (Sₘ := ImaginaryQuadraticField D) bZ
  have heq : (bZ.localizationLocalization ℚ (nonZeroDivisors ℤ)
      (ImaginaryQuadraticField D)) =
      (fun i : Fin 2 => ![(1 : ImaginaryQuadraticField D), halfSqrtNegD (D := D)] i) := by
    ext i
    rw [Basis.localizationLocalization_apply, Basis.mk_apply]
    rfl
  have hloc' : Algebra.discr ℚ (bZ.localizationLocalization ℚ (nonZeroDivisors ℤ)
      (ImaginaryQuadraticField D)) = (NumberField.discr (ImaginaryQuadraticField D) : ℚ) := by
    rw [hloc, hdiscrZ]
    rfl
  have : (NumberField.discr (ImaginaryQuadraticField D) : ℚ) = -(D : ℚ) := by
    rw [← hloc', heq, discr_one_halfSqrtNegD]
  exact_mod_cast this

end Discriminant

/-! ## 7. Signature and regulator -/

section Signature

variable [Fact (Irreducible (QuadPoly D))]

theorem isTotallyComplex (hD : 0 < D) : NumberField.IsTotallyComplex (ImaginaryQuadraticField D) := by
  refine ⟨fun w => ?_⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  obtain ⟨φ, hφ, _⟩ := hw
  let f : ImaginaryQuadraticField D →+* ℝ := hφ.embedding
  have hsq : (f (sqrtNegD (D := D))) ^ 2 = -(D : ℝ) := by
    rw [← map_pow, sqrtNegD_sq (D := D)]
    simp
  have hpos : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [sq_nonneg (f (sqrtNegD (D := D)))]

theorem nrRealPlaces_eq_zero (hD : 0 < D) :
    NumberField.InfinitePlace.nrRealPlaces (ImaginaryQuadraticField D) = 0 :=
  NumberField.nrRealPlaces_eq_zero_iff.mpr (isTotallyComplex hD)

theorem nrComplexPlaces_eq_one (hD : 0 < D) :
    NumberField.InfinitePlace.nrComplexPlaces (ImaginaryQuadraticField D) = 1 := by
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
    (ImaginaryQuadraticField D)
  rw [nrRealPlaces_eq_zero hD, finrank_eq_two] at h
  omega

theorem regulator_eq_one (hD : 0 < D) :
    NumberField.Units.regulator (ImaginaryQuadraticField D) = 1 :=
  regulator_eq_one_of_imaginary_quadratic (ImaginaryQuadraticField D)
    (nrRealPlaces_eq_zero hD) (nrComplexPlaces_eq_one hD)

end Signature

/-! ## 8. From squarefree `D` to fundamental discriminants -/

/-- The field isomorphism `ℚ(√(-4m)) ≅ ℚ(√-m)`, sending the root of `X^2 + 4m` to
twice the root of `X^2 + m`. -/
noncomputable def algEquiv_four_mul {m : ℤ} (hm : 0 < m)
    [Fact (Irreducible (QuadPoly (4 * m)))] [Fact (Irreducible (QuadPoly m))] :
    ImaginaryQuadraticField (4 * m) ≃ₐ[ℚ] ImaginaryQuadraticField m := by
  let φ : ImaginaryQuadraticField (4 * m) →ₐ[ℚ] ImaginaryQuadraticField m :=
    AdjoinRoot.liftAlgHom (QuadPoly (4 * m)) (Algebra.ofId ℚ _) (2 * sqrtNegD (D := m)) (by
      simp only [QuadPoly, map_add, map_pow, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
      norm_num
      rw [show (2 * sqrtNegD (D := m)) ^ 2 = 4 * (sqrtNegD (D := m)) ^ 2 by ring]
      change 4 * (sqrtNegD (D := m)) ^ 2 +
        4 * (algebraMap ℚ (ImaginaryQuadraticField m) (m : ℚ)) = 0
      linear_combination (4 : ImaginaryQuadraticField m) * sqrtNegD_sq_add (D := m))
  let ψ : ImaginaryQuadraticField m →ₐ[ℚ] ImaginaryQuadraticField (4 * m) :=
    AdjoinRoot.liftAlgHom (QuadPoly m) (Algebra.ofId ℚ _) (sqrtNegD (D := 4 * m) / 2) (by
      simp only [QuadPoly, map_add, map_pow, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
      norm_num
      rw [show (sqrtNegD (D := 4 * m) / 2) ^ 2 =
        (1 / 4) * (sqrtNegD (D := 4 * m)) ^ 2 by ring]
      have h' : (sqrtNegD (D := 4 * m)) ^ 2 +
          4 * (algebraMap ℚ (ImaginaryQuadraticField (4 * m)) (m : ℚ)) = 0 := by
        have h := sqrtNegD_sq_add (D := 4 * m)
        have h4 : (algebraMap ℚ (ImaginaryQuadraticField (4 * m))
            (((4 * m : ℤ) : ℚ))) =
            4 * (algebraMap ℚ (ImaginaryQuadraticField (4 * m)) (m : ℚ)) := by
          norm_num
        calc (sqrtNegD (D := 4 * m)) ^ 2 +
              4 * (algebraMap ℚ (ImaginaryQuadraticField (4 * m)) (m : ℚ))
            = (sqrtNegD (D := 4 * m)) ^ 2 +
                (algebraMap ℚ (ImaginaryQuadraticField (4 * m))
                  (((4 * m : ℤ) : ℚ))) := by rw [h4]
          _ = 0 := h
      change (1 / 4) * (sqrtNegD (D := 4 * m)) ^ 2 +
        (algebraMap ℚ (ImaginaryQuadraticField (4 * m)) (m : ℚ)) = 0
      linear_combination (1 / 4 : ImaginaryQuadraticField (4 * m)) * h')
  have hφ : φ (AdjoinRoot.root (QuadPoly (4 * m))) = 2 * sqrtNegD (D := m) := by
    dsimp [φ]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hψ : ψ (AdjoinRoot.root (QuadPoly m)) = sqrtNegD (D := 4 * m) / 2 := by
    dsimp [ψ]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  refine AlgEquiv.ofAlgHom φ ψ ?_ ?_
  · apply AdjoinRoot.algHom_ext
    change φ (ψ (AdjoinRoot.root (QuadPoly m))) = AdjoinRoot.root (QuadPoly m)
    rw [hψ, map_div₀, map_ofNat]
    change φ (AdjoinRoot.root (QuadPoly (4 * m))) / 2 = sqrtNegD (D := m)
    rw [hφ]
    ring
  · apply AdjoinRoot.algHom_ext
    change ψ (φ (AdjoinRoot.root (QuadPoly (4 * m)))) =
      AdjoinRoot.root (QuadPoly (4 * m))
    rw [hφ, map_mul, map_ofNat]
    change 2 * ψ (AdjoinRoot.root (QuadPoly m)) = sqrtNegD (D := 4 * m)
    rw [hψ]
    ring

theorem discr_four_mul {m : ℤ} (hm : 0 < m) (hsf : Squarefree m)
    (hmod : m % 4 = 1 ∨ m % 4 = 2)
    [Fact (Irreducible (QuadPoly (4 * m)))] [Fact (Irreducible (QuadPoly m))] :
    NumberField.discr (ImaginaryQuadraticField (4 * m)) = -(4 * m) := by
  rw [NumberField.discr_eq_discr_of_ringEquiv (K := ImaginaryQuadraticField (4 * m))
    (L := ImaginaryQuadraticField m) (algEquiv_four_mul hm).toRingEquiv]
  exact discr_eq_neg_four_mul_of_mod_one_two hm hsf hmod

theorem discr_of_mod_zero {D m : ℤ} (hm : 0 < m) (hDm : D = 4 * m)
    (hsfm : Squarefree m) (hmodm : m % 4 = 1 ∨ m % 4 = 2) :
    letI : Fact (Irreducible (QuadPoly D)) :=
      ⟨irreducible_quadraticPoly (by omega)⟩
    NumberField.discr (ImaginaryQuadraticField D) = -D := by
  letI : Fact (Irreducible (QuadPoly D)) := ⟨irreducible_quadraticPoly (by omega)⟩
  subst hDm
  letI : Fact (Irreducible (QuadPoly m)) := ⟨irreducible_quadraticPoly hm⟩
  exact discr_four_mul hm hsfm hmodm

/-- **The discriminant of the concrete field `ℚ(√-D)` at a fundamental discriminant.** -/
theorem discr_of_fundamental {D : ℤ} (hDfund : IsFundamentalDiscriminant D) :
    letI : Fact (Irreducible (QuadPoly D)) :=
      ⟨irreducible_quadraticPoly (isFundamentalDiscriminant_pos hDfund)⟩
    NumberField.discr (ImaginaryQuadraticField D) = -D := by
  letI : Fact (Irreducible (QuadPoly D)) :=
    ⟨irreducible_quadraticPoly (isFundamentalDiscriminant_pos hDfund)⟩
  obtain ⟨hpos, hcases⟩ := hDfund
  rcases hcases with ⟨hmod3, hsfD⟩ | ⟨hmod0, hsfm, hmodm⟩
  · exact discr_eq_neg_of_mod_three hpos hsfD hmod3
  · let m := D / 4
    have hDm : D = 4 * m := by omega
    have hmpos : 0 < m := by omega
    have hsfm' : Squarefree m := by simpa [m] using hsfm
    have hmodm' : m % 4 = 1 ∨ m % 4 = 2 := by simpa [m] using hmodm
    exact discr_of_mod_zero (D := D) hmpos hDm hsfm' hmodm'

/-! ## 9. Cross-checks at `D = 3, 4` -/

theorem discr_imaginaryQuadraticField_four :
    letI : Fact (Irreducible (QuadPoly 4)) := ⟨irreducible_quadraticPoly (by norm_num)⟩
    NumberField.discr (ImaginaryQuadraticField 4) = -4 := by
  letI : Fact (Irreducible (QuadPoly 4)) := ⟨irreducible_quadraticPoly (by norm_num)⟩
  exact discr_of_fundamental isFundamentalDiscriminant_four

theorem discr_imaginaryQuadraticField_three :
    letI : Fact (Irreducible (QuadPoly 3)) := ⟨irreducible_quadraticPoly (by norm_num)⟩
    NumberField.discr (ImaginaryQuadraticField 3) = -3 := by
  letI : Fact (Irreducible (QuadPoly 3)) := ⟨irreducible_quadraticPoly (by norm_num)⟩
  exact discr_of_fundamental isFundamentalDiscriminant_three

theorem discr_four_agrees_with_cyclotomic :
    letI : Fact (Irreducible (QuadPoly 4)) := ⟨irreducible_quadraticPoly (by norm_num)⟩
    NumberField.discr (ImaginaryQuadraticField 4) =
      NumberField.discr GaussianCyclotomicField := by
  rw [discr_imaginaryQuadraticField_four, discr_gaussian]

theorem discr_three_agrees_with_cyclotomic :
    letI : Fact (Irreducible (QuadPoly 3)) := ⟨irreducible_quadraticPoly (by norm_num)⟩
    NumberField.discr (ImaginaryQuadraticField 3) =
      NumberField.discr EisensteinCyclotomicField := by
  rw [discr_imaginaryQuadraticField_three, discr_eisenstein]

/-! ## 10. The isolated arithmetic input and the reduction to `QuadraticFieldGap` -/

/-- The only remaining arithmetic inputs of `QuadraticFieldGap`: the class number is `h(D)` and
the unit torsion order is `w(D)`. -/
def QuadraticArithmeticInput (classNumber weight : ℤ → ℝ) : Prop :=
  ∀ (D : ℤ) (hD : IsFundamentalDiscriminant D),
    letI : Fact (Irreducible (QuadPoly D)) :=
      ⟨irreducible_quadraticPoly (isFundamentalDiscriminant_pos hD)⟩
    (NumberField.classNumber (ImaginaryQuadraticField D) : ℝ) = classNumber D ∧
      (NumberField.Units.torsionOrder (ImaginaryQuadraticField D) : ℝ) = weight D

/-- **The reduction to `QuadraticFieldGap`.**  All the geometric invariants are proved; only the
class number and torsion identifications remain. -/
theorem quadraticFieldGap_of_arithmeticInput {classNumber weight : ℤ → ℝ}
    (h : QuadraticArithmeticInput classNumber weight) :
    QuadraticFieldGap classNumber weight := by
  intro D hD
  letI : Fact (Irreducible (QuadPoly D)) :=
    ⟨irreducible_quadraticPoly (isFundamentalDiscriminant_pos hD)⟩
  obtain ⟨hc, hw⟩ := h D hD
  exact ⟨discr_of_fundamental hD, hc, hw,
    nrRealPlaces_eq_zero (isFundamentalDiscriminant_pos hD),
    nrComplexPlaces_eq_one (isFundamentalDiscriminant_pos hD),
    regulator_eq_one (isFundamentalDiscriminant_pos hD)⟩

/-- Conversely, `QuadraticFieldGap` contains the arithmetic input. -/
theorem arithmeticInput_of_quadraticFieldGap {classNumber weight : ℤ → ℝ}
    (h : QuadraticFieldGap classNumber weight) :
    QuadraticArithmeticInput classNumber weight := by
  intro D hD
  letI : Fact (Irreducible (QuadPoly D)) :=
    ⟨irreducible_quadraticPoly (isFundamentalDiscriminant_pos hD)⟩
  exact ⟨(h D hD).2.1, (h D hD).2.2.1⟩

/-- **`QuadraticFieldGap` is exactly the arithmetic input.** -/
theorem quadraticFieldGap_iff_arithmeticInput {classNumber weight : ℤ → ℝ} :
    QuadraticFieldGap classNumber weight ↔ QuadraticArithmeticInput classNumber weight :=
  ⟨arithmeticInput_of_quadraticFieldGap, quadraticFieldGap_of_arithmeticInput⟩

end

end Cogentic.RandomizedL27ClassNumberFormula
