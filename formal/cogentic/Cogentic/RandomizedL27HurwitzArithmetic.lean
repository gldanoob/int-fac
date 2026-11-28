import Cogentic.RandomizedL27ClassNumberFormula
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

/-!
# L27: arithmetic residuals of the Hurwitz class-number formula

`Cogentic.RandomizedL27ClassNumberFormula` reduced the class-number part of L27
to five named inputs:

* `OrderConductorCover`, the order/conductor decomposition of a Frobenius
  discriminant;
* `HurwitzOrderDecomposition`, the identity expressing the Hurwitz class number
  as the weighted sum of the order class numbers;
* `NonMaximalOrderConductorFormula`, the conductor factor for non-maximal
  orders;
* `ConductorProductGeometric` and `ConductorProductNormalized`, the Euler-product
  bounds for the conductor factor;
* `L1OrderInvariant`, `OrderWeightPositive` and `OrderClassNumberNonneg`, the
  invariance of the quadratic character and the signs of the weights and class
  numbers.

This file separates the *arithmetic* content from the *class-number* content.

## What is proved

* `orderConductorCover`: **every** Frobenius discriminant is `D₀ f²` with `D₀`
  fundamental and `f > 0`.  The proof is elementary: write `t = 2q` or
  `t = 2q + 1`, so that `D = 4(p - q²)` or `D ≡ 3 (mod 4)`, and take the
  squarefree decomposition of `D` (resp. `D / 4`).  The only arithmetic input is
  `Nat.sq_mul_squarefree`.
* `conductorProductOf`, `conductorProductGeometric_of_chi`,
  `conductorProductNormalized_of`: for the standard conductor product
  `∏_{p | f} (1 - χ_D(p)/p)` with `χ_D(p) ≤ 1`, the Euler product dominates
  `φ(f)/f`.  The proof is the pointwise comparison `1 - χ/p ≥ 1 - 1/p` and
  Euler's formula `φ(f)/f = ∏_{p|f} (1 - 1/p)`.
* `l1OrderInvariant_const`, `l1OrderInvariant_affine`: the character-invariance
  input is closed under the constant and affine constructions (it is a genuine
  input for a nonconstant `L1`).
* `orderWeightPositive_of_pos`, `orderClassNumberNonneg_of_nonneg`,
  `unitWeightPositive_of_orderWeightPositive`,
  `unitClassNumberNonneg_of_orderClassNumberNonneg`: the sign fields are
  definitional consequences of pointwise positivity.
* `hurwitzOrderDecomposition_at_one`,
  `hurwitzOrderDecomposition_self`: the arithmetic content of the Hurwitz
  decomposition at the maximal order (`f = 1`) and after splitting off the
  maximal order.
* `hurwitzDominates_of_orderDecomposition`: the Hurwitz decomposition and the
  sign fields imply the domination `h(D)/w(D) ≤ H(D)` used in
  `RandomizedL27ClassNumber`.
* `nonMaximalOrderConductorFormula_of_weighted` and
  `weightedOrderConductorFormula_iff_fundamental_and_nonmaximal`: the
  non-maximal conductor formula is exactly the `f > 1` part of the weighted
  order formula; the `f = 1` part is the fundamental Dirichlet formula.
* `classNumberFormulaInput_of_components`: assembling the arithmetic results
  above with the genuine class-number inputs yields the bundled
  `ClassNumberFormulaInput`, hence the Hurwitz lower bound.

## What remains a genuine input

The following are *not* consequences of the definitions and are not proved
here; they are the class-number content of the theorem:

* `FundamentalOrderRealization`: Mathlib's Dedekind-zeta residue formula plus
  the identification `res = L(1, χ_D)` for the maximal order;
* `HurwitzOrderDecomposition` for the actual Hurwitz class number (the
  arithmetic skeleton is proved below, but the value of `H(D)` is a theorem
  about orders);
* `NonMaximalOrderConductorFormula`: the order class number of conductor `f` is
  the maximal-order class number times `∏(1 - χ(p)/p)`;
* `L1OrderInvariant` for the actual Kronecker character (only its constant and
  affine models are proved invariant here).

No `sorry`, `admit`, `axiom` or `native_decide` is used.  No class number,
weight or count is set to zero.
-/

namespace Cogentic.RandomizedL27HurwitzArithmetic

open scoped BigOperators
open Cogentic.RandomizedL27ClassNumberFormula
open Cogentic.RandomizedL27Siegel
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27ClassNumber

noncomputable section

/-! ## 1. The order/conductor cover -/

/-- A natural-number presentation of `IsFundamentalDiscriminant`. -/
theorem isFundamentalDiscriminant_natCast {n : ℕ} (hn : 0 < n)
    (h : (n % 4 = 3 ∧ Squarefree n) ∨
      (n % 4 = 0 ∧ Squarefree (n / 4) ∧ (n / 4 % 4 = 1 ∨ n / 4 % 4 = 2))) :
    IsFundamentalDiscriminant (n : ℤ) := by
  refine ⟨by exact_mod_cast hn, ?_⟩
  rcases h with ⟨h3, hsf⟩ | ⟨h0, hsf, h14⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, ← Int.natCast_mod, h3]
      norm_num
    · simpa using hsf
  · right
    refine ⟨?_, ?_, ?_⟩
    · rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, ← Int.natCast_mod, h0]
      norm_num
    · rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, ← Int.natCast_div]
      exact Int.squarefree_natCast.mpr hsf
    · rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, ← Int.natCast_div,
        ← Int.natCast_mod]
      rcases h14 with h1 | h2
      · left; rw [h1]; norm_num
      · right; rw [h2]; norm_num

/-- Squaring an odd natural number gives `1` in `ZMod 4`. -/
theorem zmod_four_sq_of_odd {b : ℕ} (hb : Odd b) : ((b : ZMod 4) ^ 2) = 1 := by
  obtain ⟨s, rfl⟩ := hb
  push_cast
  have h4 : (4 : ZMod 4) = 0 := by decide
  calc (2 * (s : ZMod 4) + 1) ^ 2
      = 4 * (s : ZMod 4) ^ 2 + 4 * (s : ZMod 4) + 1 := by ring
    _ = 1 := by rw [h4]; ring

/-- If `a * b² = 3` in `ZMod 4` and `b` is odd, then `a ≡ 3 (mod 4)`. -/
theorem mod_four_eq_three_of_zmod {a b : ℕ} (hb : Odd b)
    (h : (a : ZMod 4) * (b : ZMod 4) ^ 2 = 3) : a % 4 = 3 := by
  rw [zmod_four_sq_of_odd hb, mul_one] at h
  have hv := congrArg ZMod.val h
  have h3 : ZMod.val (3 : ZMod 4) = 3 := by decide
  simpa [ZMod.val_natCast, h3] using hv

/-- The discriminant of an even trace is four times an integer. -/
theorem traceDisc_even (p : ℕ) (q : ℤ) :
    traceDisc p (2 * q) = 4 * ((p : ℤ) - q ^ 2) := by
  unfold traceDisc
  ring

/-- The discriminant of an odd trace is `4K - 1`. -/
theorem traceDisc_odd (p : ℕ) (q : ℤ) :
    traceDisc p (2 * q + 1) = 4 * ((p : ℤ) - q ^ 2 - q) - 1 := by
  unfold traceDisc
  ring

/-- `(8a)/4 = 2a`. -/
theorem eight_mul_div_four (a : ℕ) : (8 * a) / 4 = 2 * a := by
  rw [show 8 * a = (2 * a) * 4 by ring, Nat.mul_div_left _ (by norm_num : 0 < 4)]

/-- `(4a)/4 = a`. -/
theorem four_mul_div_four (a : ℕ) : (4 * a) / 4 = a := by
  rw [show 4 * a = a * 4 by ring, Nat.mul_div_left _ (by norm_num : 0 < 4)]

/-- `4 ∣ 8a`. -/
theorem eight_mul_mod_four (a : ℕ) : (8 * a) % 4 = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  exact ⟨2 * a, by ring⟩

/-- `4 ∣ 4a`. -/
theorem four_mul_mod_four (a : ℕ) : (4 * a) % 4 = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  exact ⟨a, by ring⟩

/-- **Every Frobenius discriminant is `D₀ f²` with `D₀` fundamental.**

Write the trace as `t = 2q` or `t = 2q + 1`.  In the even case
`D = 4(p - q²)`; take the squarefree decomposition of `p - q²` and adjust the
factor `4` according to the residue of the squarefree part modulo `4`.  In the
odd case `D ≡ 3 (mod 4)`; take the squarefree decomposition of `D` itself and
observe that the squarefree part is `3 (mod 4)`. -/
theorem orderConductorCover : OrderConductorCover := by
  intro D hD
  obtain ⟨p, hp, t, ht, rfl⟩ := hD
  rcases Int.even_or_odd' t with ⟨q, hq | hq⟩
  · -- `t = 2q`: `D = 4(p - q²)`.
    have hform : traceDisc p t = 4 * ((p : ℤ) - q ^ 2) := by
      rw [hq]; exact traceDisc_even p q
    have he : 0 < (p : ℤ) - q ^ 2 := by
      rw [hform] at ht
      linarith
    let e : ℕ := ((p : ℤ) - q ^ 2).toNat
    have hec : (e : ℤ) = (p : ℤ) - q ^ 2 := Int.toNat_of_nonneg he.le
    have hepos : 0 < e := by
      have : (0 : ℤ) < (e : ℤ) := by rw [hec]; exact he
      exact_mod_cast this
    obtain ⟨a, b, ha, hb, hba, hsf⟩ := Nat.sq_mul_squarefree_of_pos hepos
    have hD4 : traceDisc p t = 4 * (e : ℤ) := by rw [hform, hec]
    have heb : (e : ℤ) = ((b ^ 2 * a : ℕ) : ℤ) := by rw [hba]
    rcases Nat.even_or_odd' a with ⟨a', ha' | ha'⟩
    · -- `a = 2a'`: `D = 8a' · b²`.
      have hsf' : Squarefree (2 * a') := by rwa [ha'] at hsf
      have ha'odd : Odd a' := by
        by_contra hodd
        have hev : Even a' := by simpa using hodd
        obtain ⟨k, hk⟩ := hev
        have h4 : 2 * 2 ∣ 2 * a' := by
          refine ⟨k, ?_⟩
          rw [hk]
          ring
        exact (Nat.squarefree_iff_prime_squarefree.mp hsf' 2 Nat.prime_two) h4
      have hmod : (2 * a') % 4 = 2 := by
        obtain ⟨k, hk⟩ := ha'odd
        omega
      have hfund : IsFundamentalDiscriminant ((8 * a' : ℕ) : ℤ) := by
        refine isFundamentalDiscriminant_natCast (by omega)
          (Or.inr ⟨eight_mul_mod_four a', ?_, ?_⟩)
        · rw [eight_mul_div_four]
          exact hsf'
        · rw [eight_mul_div_four]
          exact Or.inr hmod
      refine ⟨((8 * a' : ℕ) : ℤ), b, hfund, hb, ?_⟩
      rw [hD4, heb, ha']
      push_cast
      ring
    · -- `a = 2a' + 1` is odd.
      have haodd : Odd a := ⟨a', ha'⟩
      have hmodsplit : a % 4 = 1 ∨ a % 4 = 3 := by
        obtain ⟨k, hk⟩ := haodd
        omega
      rcases hmodsplit with hm1 | hm3
      · -- `a ≡ 1 (mod 4)`: `D = 4a · b²`.
        have hfund : IsFundamentalDiscriminant ((4 * a : ℕ) : ℤ) := by
          refine isFundamentalDiscriminant_natCast (by omega)
            (Or.inr ⟨four_mul_mod_four a, ?_, ?_⟩)
          · rw [four_mul_div_four]
            exact hsf
          · rw [four_mul_div_four]
            exact Or.inl hm1
        refine ⟨((4 * a : ℕ) : ℤ), b, hfund, hb, ?_⟩
        rw [hD4, heb]
        push_cast
        ring
      · -- `a ≡ 3 (mod 4)`: `D = a · (2b)²`.
        have hfund : IsFundamentalDiscriminant (a : ℤ) :=
          isFundamentalDiscriminant_natCast ha (Or.inl ⟨hm3, hsf⟩)
        refine ⟨(a : ℤ), 2 * b, hfund, by omega, ?_⟩
        rw [hD4, heb]
        push_cast
        ring
  · -- `t = 2q + 1`: `D = 4K - 1 ≡ 3 (mod 4)`.
    have hform : traceDisc p t = 4 * ((p : ℤ) - q ^ 2 - q) - 1 := by
      rw [hq]; exact traceDisc_odd p q
    have hnpos : 0 < (traceDisc p t).toNat := by
      have hDcast : (((traceDisc p t).toNat : ℕ) : ℤ) = traceDisc p t :=
        Int.toNat_of_nonneg ht.le
      have : (0 : ℤ) < (((traceDisc p t).toNat : ℕ) : ℤ) := by
        rw [hDcast]
        exact ht
      exact_mod_cast this
    obtain ⟨a, b, ha, hb, hba, hsf⟩ := Nat.sq_mul_squarefree_of_pos hnpos
    have hDnat : ((a * b ^ 2 : ℕ) : ℤ) = traceDisc p t := by
      have h1 : (((traceDisc p t).toNat : ℕ) : ℤ) = traceDisc p t :=
        Int.toNat_of_nonneg ht.le
      calc ((a * b ^ 2 : ℕ) : ℤ) = ((b ^ 2 * a : ℕ) : ℤ) := by rw [mul_comm]
        _ = (((traceDisc p t).toNat : ℕ) : ℤ) := by rw [hba]
        _ = traceDisc p t := h1
    have hoddD : Odd (traceDisc p t) := by
      rw [hform]
      refine ⟨2 * ((p : ℤ) - q ^ 2 - q) - 1, ?_⟩
      ring
    have hoddab : Odd (a * b ^ 2) := by
      have hcast : Odd (((a * b ^ 2 : ℕ)) : ℤ) := by
        rw [hDnat]
        exact hoddD
      exact (Int.odd_coe_nat (a * b ^ 2)).mp hcast
    have hodd_a : Odd a := (Nat.odd_mul.mp hoddab).1
    have hodd_b : Odd b := by
      have hb2 : Odd (b ^ 2) := (Nat.odd_mul.mp hoddab).2
      rwa [Nat.odd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)] at hb2
    have hamod : a % 4 = 3 := by
      apply mod_four_eq_three_of_zmod hodd_b
      have hcast : ((traceDisc p t : ℤ) : ZMod 4) = 3 := by
        rw [hform]
        push_cast
        have h4 : (4 : ZMod 4) = 0 := by decide
        rw [h4]
        simp only [zero_mul, zero_sub]
        decide
      have h := hcast
      rw [← hDnat] at h
      push_cast at h
      simpa using h
    refine ⟨(a : ℤ), b, ?_, hb, ?_⟩
    · exact isFundamentalDiscriminant_natCast ha (Or.inl ⟨hamod, hsf⟩)
    · rw [← hDnat]
      push_cast
      ring

/-! ## 2. The standard conductor product -/

/-- The standard conductor product `∏_{p | f} (1 - χ(p)/p)`, with the character
value kept as an explicit function `chi D₀ p`. -/
def conductorProductOf (chi : ℤ → ℕ → ℝ) (D₀ : ℤ) (f : ℕ) : ℝ :=
  ∏ p ∈ f.primeFactors, (1 - chi D₀ p / (p : ℝ))

/-- The standard conductor product is `1` at `f = 1`. -/
theorem conductorProductOf_one (chi : ℤ → ℕ → ℝ) (D₀ : ℤ) :
    conductorProductOf chi D₀ 1 = 1 := by
  simp [conductorProductOf]

/-- `ConductorProductNormalized` holds for the standard conductor product. -/
theorem conductorProductNormalized_of (chi : ℤ → ℕ → ℝ) :
    ConductorProductNormalized (conductorProductOf chi) :=
  fun D₀ => conductorProductOf_one chi D₀

/-- Euler's product formula for the totient, in the division form
`φ(f)/f = ∏_{p | f} (1 - 1/p)` over `ℝ`. -/
theorem totient_div_eq_prod_inv {f : ℕ} (hf : 0 < f) :
    (Nat.totient f : ℝ) / (f : ℝ) =
      ∏ p ∈ f.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have hq := Nat.totient_eq_mul_prod_factors f
  have hR : (Nat.totient f : ℝ) =
      (f : ℝ) * ∏ p ∈ f.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) hq
    push_cast at hcast
    simpa using hcast
  have hfR : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  rw [hR]
  field_simp [hfR]

/-- **The standard conductor product dominates `φ(f)/f`.**  Each factor satisfies
`1 - χ(p)/p ≥ 1 - 1/p` because `χ(p) ≤ 1`; the product of the latter is
`φ(f)/f` by Euler's formula. -/
theorem conductorProductGeometric_of_chi
    (chi : ℤ → ℕ → ℝ) (hchi : ∀ D₀ p, chi D₀ p ≤ 1) :
    ConductorProductGeometric (conductorProductOf chi) := by
  intro D₀ f _ hf
  rw [totient_div_eq_prod_inv hf, conductorProductOf]
  apply Finset.prod_le_prod
  · intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      exact_mod_cast this
    have hpR : (0 : ℝ) < (p : ℝ) := by linarith
    have hinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  · intro p hp
    have hpR : (0 : ℝ) < (p : ℝ) := by
      have := Nat.pos_of_mem_primeFactors hp
      exact_mod_cast this
    have hle : chi D₀ p / (p : ℝ) ≤ (p : ℝ)⁻¹ := by
      simpa [one_div] using
        div_le_div_of_nonneg_right (hchi D₀ p) hpR.le
    linarith

/-- A strictly positive version of the pointwise bound, for characters with
`|χ(p)| ≤ 1`; the geometric bound only needs the upper half. -/
theorem conductorProductGeometric_of_chi_abs
    (chi : ℤ → ℕ → ℝ) (hchi : ∀ D₀ p, |chi D₀ p| ≤ 1) :
    ConductorProductGeometric (conductorProductOf chi) :=
  conductorProductGeometric_of_chi chi fun D₀ p => (le_abs_self _).trans (hchi D₀ p)

/-! ## 3. Character invariance and sign fields -/

/-- The constant character value gives an invariant `L1`. -/
theorem l1OrderInvariant_const (c : ℝ) : L1OrderInvariant (fun _ : ℤ => c) := by
  intro D₀ f _ _
  rfl

/-- Character invariance is preserved by affine changes of the `L`-value. -/
theorem l1OrderInvariant_affine {L1 : ℤ → ℝ} (h : L1OrderInvariant L1)
    (a b : ℝ) : L1OrderInvariant (fun D => a * L1 D + b) := by
  intro D₀ f hD hf
  dsimp only
  rw [h D₀ f hD hf]

/-- Pointwise positivity implies `OrderWeightPositive`. -/
theorem orderWeightPositive_of_pos {weight : ℤ → ℝ}
    (h : ∀ D : ℤ, 0 < weight D) : OrderWeightPositive weight :=
  fun _ _ _ _ => h _

/-- A positive constant is an `OrderWeightPositive` weight. -/
theorem orderWeightPositive_const (c : ℝ) (hc : 0 < c) :
    OrderWeightPositive (fun _ : ℤ => c) :=
  orderWeightPositive_of_pos fun _ => hc

/-- Pointwise nonnegativity implies `OrderClassNumberNonneg`. -/
theorem orderClassNumberNonneg_of_nonneg {classNumber : ℤ → ℝ}
    (h : ∀ D : ℤ, 0 ≤ classNumber D) : OrderClassNumberNonneg classNumber :=
  fun _ _ _ _ => h _

/-- `OrderWeightPositive` on the order cover is exactly `UnitWeightPositive` on
Frobenius discriminants. -/
theorem unitWeightPositive_of_orderWeightPositive {weight : ℤ → ℝ}
    (hcover : OrderConductorCover) (hweight : OrderWeightPositive weight) :
    UnitWeightPositive weight := by
  intro D hD
  obtain ⟨D₀, f, hD0, hf, rfl⟩ := hcover D hD
  exact hweight D₀ f hD0 hf

/-- `OrderClassNumberNonneg` on the order cover is exactly nonnegativity on
Frobenius discriminants. -/
theorem orderClassNumberNonneg_of_frobenius {classNumber : ℤ → ℝ}
    (hcover : OrderConductorCover) (hclass : OrderClassNumberNonneg classNumber) :
    ∀ D : ℤ, IsFrobeniusDiscriminant D → 0 ≤ classNumber D := by
  intro D hD
  obtain ⟨D₀, f, hD0, hf, rfl⟩ := hcover D hD
  exact hclass D₀ f hD0 hf

/-! ## 4. The Hurwitz order decomposition -/

/-- At `f = 1` the Hurwitz decomposition is the single maximal-order term
`H(D₀) = 2 h(D₀)/w(D₀)`. -/
theorem hurwitzOrderDecomposition_at_one
    {hurwitz classNumber weight : ℤ → ℝ}
    (h : HurwitzOrderDecomposition hurwitz classNumber weight)
    {D₀ : ℤ} (hD0 : IsFundamentalDiscriminant D₀) :
    hurwitz D₀ = 2 * (classNumber D₀ / weight D₀) := by
  simpa using h D₀ 1 hD0 one_pos

/-- The Hurwitz decomposition splits off the maximal-order term at `g = f`. -/
theorem hurwitzOrderDecomposition_self
    {hurwitz classNumber weight : ℤ → ℝ}
    (h : HurwitzOrderDecomposition hurwitz classNumber weight)
    {D₀ : ℤ} {f : ℕ} (hD0 : IsFundamentalDiscriminant D₀) (hf : 0 < f) :
    hurwitz (D₀ * (f : ℤ) ^ 2) =
      2 * (classNumber (D₀ * (f : ℤ) ^ 2) / weight (D₀ * (f : ℤ) ^ 2)) +
        ∑ g ∈ f.divisors.erase f,
          2 * (classNumber (D₀ * (g : ℤ) ^ 2) / weight (D₀ * (g : ℤ) ^ 2)) := by
  rw [h D₀ f hD0 hf]
  exact (Finset.add_sum_erase _ _ (Nat.mem_divisors_self f hf.ne')).symm

/-- **The Hurwitz decomposition implies the weighted domination.**  The
maximal-order term of the decomposition is `2 h(D)/w(D)`, and the other terms
are nonnegative by the sign fields. -/
theorem hurwitzDominates_of_orderDecomposition
    {hurwitz classNumber weight : ℤ → ℝ}
    (hcover : OrderConductorCover)
    (hdecomp : HurwitzOrderDecomposition hurwitz classNumber weight)
    (hweight : OrderWeightPositive weight)
    (hclass : OrderClassNumberNonneg classNumber) :
    HurwitzDominatesWeightedClassNumber hurwitz classNumber weight := by
  intro D hD
  obtain ⟨D₀, f, hD0, hf, rfl⟩ := hcover D hD
  have hfmem : f ∈ f.divisors := Nat.mem_divisors_self f hf.ne'
  have hterm_nonneg : ∀ g ∈ f.divisors,
      0 ≤ 2 * (classNumber (D₀ * (g : ℤ) ^ 2) / weight (D₀ * (g : ℤ) ^ 2)) := by
    intro g hg
    have hgpos : 0 < g :=
      Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hg) hf
    have hw : 0 < weight (D₀ * (g : ℤ) ^ 2) := hweight D₀ g hD0 hgpos
    have hc : 0 ≤ classNumber (D₀ * (g : ℤ) ^ 2) := hclass D₀ g hD0 hgpos
    exact mul_nonneg (by norm_num) (div_nonneg hc hw.le)
  have hsingle := Finset.single_le_sum hterm_nonneg hfmem
  rw [hdecomp D₀ f hD0 hf]
  have hfw : 0 ≤ classNumber (D₀ * (f : ℤ) ^ 2) / weight (D₀ * (f : ℤ) ^ 2) := by
    have hw : 0 < weight (D₀ * (f : ℤ) ^ 2) := hweight D₀ f hD0 hf
    have hc : 0 ≤ classNumber (D₀ * (f : ℤ) ^ 2) := hclass D₀ f hD0 hf
    exact div_nonneg hc hw.le
  have h2 : classNumber (D₀ * (f : ℤ) ^ 2) / weight (D₀ * (f : ℤ) ^ 2) ≤
      2 * (classNumber (D₀ * (f : ℤ) ^ 2) / weight (D₀ * (f : ℤ) ^ 2)) := by
    linarith
  exact le_trans h2 hsingle

/-! ## 5. The non-maximal conductor formula -/

/-- The weighted order formula restricts to the non-maximal conductor formula. -/
theorem nonMaximalOrderConductorFormula_of_weighted
    {classNumber weight L1 : ℤ → ℝ} {conductorProduct : ℤ → ℕ → ℝ}
    (h : WeightedOrderConductorFormula classNumber weight L1 conductorProduct) :
    NonMaximalOrderConductorFormula classNumber weight L1 conductorProduct :=
  fun D₀ f hD hf => h D₀ f hD (by omega)

/-- **The non-maximal formula is exactly the `f > 1` half of the weighted order
formula.**  The missing `f = 1` case is the fundamental Dirichlet formula, which
is supplied by `hfund`. -/
theorem weightedOrderConductorFormula_iff_fundamental_and_nonmaximal
    {classNumber weight L1 : ℤ → ℝ} {conductorProduct : ℤ → ℕ → ℝ}
    (hfund : ∀ D : ℤ, IsFundamentalDiscriminant D →
      classNumber D =
        (weight D / (2 * Real.pi)) * Real.sqrt (D : ℝ) * L1 D)
    (hweight : OrderWeightPositive weight)
    (hprod1 : ConductorProductNormalized conductorProduct) :
    WeightedOrderConductorFormula classNumber weight L1 conductorProduct ↔
      NonMaximalOrderConductorFormula classNumber weight L1 conductorProduct := by
  constructor
  · exact nonMaximalOrderConductorFormula_of_weighted
  · intro hnonmax
    exact weightedOrderConductorFormula_of_fundamental hfund hnonmax hweight hprod1

/-- **The conductor factor is determined by the weighted class numbers.**  Once
the weighted formula is known, the conductor product is forced to be the ratio
of the two sides.  The arithmetic content of the order formula is therefore
exactly the assertion that this ratio equals the Euler product. -/
theorem conductorProduct_eq_of_weightedFormula
    {classNumber weight L1 : ℤ → ℝ} {conductorProduct : ℤ → ℕ → ℝ}
    {D₀ : ℤ} {f : ℕ}
    (h : WeightedOrderConductorFormula classNumber weight L1 conductorProduct)
    (hD0 : IsFundamentalDiscriminant D₀) (hf : 0 < f)
    (hbase : Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) *
        L1 (D₀ * (f : ℤ) ^ 2) / (2 * Real.pi) ≠ 0) :
    conductorProduct D₀ f =
      (classNumber (D₀ * (f : ℤ) ^ 2) / weight (D₀ * (f : ℤ) ^ 2)) /
        (Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) *
          L1 (D₀ * (f : ℤ) ^ 2) / (2 * Real.pi)) := by
  rw [h D₀ f hD0 hf]
  exact (mul_div_cancel_left₀ (conductorProduct D₀ f) hbase).symm

/-! ## 6. Assembly: the arithmetic results plus the class-number inputs -/

/-- **The bundled class-number input from the arithmetic results.**  The cover,
the conductor-product bounds and the sign fields are supplied by this file; the
maximal-order realization, the Hurwitz decomposition, the non-maximal formula
and the character invariance remain explicit hypotheses. -/
def classNumberFormulaInput_of_components
    {hurwitz classNumber weight L1 : ℤ → ℝ} {conductorProduct : ℤ → ℕ → ℝ}
    (maximal : FundamentalOrderRealization classNumber weight L1)
    (decomp : HurwitzOrderDecomposition hurwitz classNumber weight)
    (nonmax : NonMaximalOrderConductorFormula classNumber weight L1 conductorProduct)
    (hprod : ConductorProductGeometric conductorProduct)
    (hprod1 : ConductorProductNormalized conductorProduct)
    (hL1inv : L1OrderInvariant L1)
    (hweight : OrderWeightPositive weight)
    (hclass : OrderClassNumberNonneg classNumber) :
    ClassNumberFormulaInput hurwitz L1 :=
  { classNumber := classNumber
    weight := weight
    conductorProduct := conductorProduct
    cover := orderConductorCover
    maximal := maximal
    decomposition := decomp
    nonmaximal := nonmax
    conductor_geometric := hprod
    conductor_one := hprod1
    L1_invariant := hL1inv
    weight_pos := hweight
    class_nonneg := hclass }

/-- The Hurwitz lower bound from the arithmetic results and the class-number
inputs. -/
theorem hurwitzClassNumberFormulaLower_of_components
    {hurwitz classNumber weight L1 : ℤ → ℝ} {conductorProduct : ℤ → ℕ → ℝ}
    (maximal : FundamentalOrderRealization classNumber weight L1)
    (decomp : HurwitzOrderDecomposition hurwitz classNumber weight)
    (nonmax : NonMaximalOrderConductorFormula classNumber weight L1 conductorProduct)
    (hprod : ConductorProductGeometric conductorProduct)
    (hprod1 : ConductorProductNormalized conductorProduct)
    (hL1inv : L1OrderInvariant L1)
    (hweight : OrderWeightPositive weight)
    (hclass : OrderClassNumberNonneg classNumber) :
    HurwitzClassNumberFormula hurwitz L1 :=
  (classNumberFormulaInput_of_components maximal decomp nonmax hprod hprod1 hL1inv
    hweight hclass).hurwitzFormulaLower

/-- The same lower bound with the standard conductor product and a character
bounded by `1`. -/
theorem hurwitzClassNumberFormulaLower_of_standardConductor
    {hurwitz classNumber weight L1 : ℤ → ℝ} {chi : ℤ → ℕ → ℝ}
    (hchi : ∀ D₀ p, chi D₀ p ≤ 1)
    (maximal : FundamentalOrderRealization classNumber weight L1)
    (decomp : HurwitzOrderDecomposition hurwitz classNumber weight)
    (nonmax : NonMaximalOrderConductorFormula classNumber weight L1
      (conductorProductOf chi))
    (hL1inv : L1OrderInvariant L1)
    (hweight : OrderWeightPositive weight)
    (hclass : OrderClassNumberNonneg classNumber) :
    HurwitzClassNumberFormula hurwitz L1 :=
  hurwitzClassNumberFormulaLower_of_components maximal decomp nonmax
    (conductorProductGeometric_of_chi chi hchi)
    (conductorProductNormalized_of chi) hL1inv hweight hclass

/-! ## Axiom audit -/

#print axioms isFundamentalDiscriminant_natCast
#print axioms mod_four_eq_three_of_zmod
#print axioms orderConductorCover
#print axioms conductorProductOf_one
#print axioms conductorProductNormalized_of
#print axioms totient_div_eq_prod_inv
#print axioms conductorProductGeometric_of_chi
#print axioms conductorProductGeometric_of_chi_abs
#print axioms l1OrderInvariant_const
#print axioms l1OrderInvariant_affine
#print axioms orderWeightPositive_of_pos
#print axioms orderClassNumberNonneg_of_nonneg
#print axioms unitWeightPositive_of_orderWeightPositive
#print axioms orderClassNumberNonneg_of_frobenius
#print axioms hurwitzOrderDecomposition_at_one
#print axioms hurwitzOrderDecomposition_self
#print axioms hurwitzDominates_of_orderDecomposition
#print axioms nonMaximalOrderConductorFormula_of_weighted
#print axioms weightedOrderConductorFormula_iff_fundamental_and_nonmaximal
#print axioms conductorProduct_eq_of_weightedFormula
#print axioms classNumberFormulaInput_of_components
#print axioms hurwitzClassNumberFormulaLower_of_components
#print axioms hurwitzClassNumberFormulaLower_of_standardConductor

end

end Cogentic.RandomizedL27HurwitzArithmetic
