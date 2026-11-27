import Cogentic.RandomizedL4Sub
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.ZMod.Basic

set_option linter.style.haveILetI false

/-!
# L4Composition: Gauss/Dirichlet composition and ideal squaring for `-8N`

`Cogentic.RandomizedL4` records two class-group inputs of the private form
sampler for the order `ℤ[√(-2N)]`, whose primitive forms have discriminant
`-8N`:

* `FormCompositionLaw N` --- the product of two primitive form classes has a
  primitive representative whose leading coefficient divides the product of
  the two leading coefficients;
* `IdealSquaringLaw N` --- the square of a primitive reduced form class has a
  primitive representative with leading coefficient `A² / d²`.

## What is proved here

* **The recorded laws are automatic as stated.**  The principal form
  `[1, 0, 2N]` is primitive and has `A = 1`; it witnesses both
  `FormCompositionLaw` and `IdealSquaringLaw` for every `N`.  Consequently
  `L4SubInputs` can be built from `BandSplit` and `BandProductSmall` alone.
  This is recorded explicitly because the two `Prop`s quantify only over the
  existence of *some* primitive representative.

* **Faithful Dirichlet composition in the coprime case.**  `DirichletComposition`
  is the genuine statement that two primitive forms with leading coefficients
  coprime to `2N` and to each other compose to a primitive form with leading
  coefficient exactly `A₁ * A₂`.  Its proof is the CRT construction
  `b ≡ b₁ (mod A₁)`, `b ≡ b₂ (mod A₂)`, followed by
  `C = (b² + 2N)/(A₁A₂)`; primitivity follows from `IsCoprime Aᵢ (2bᵢ)` and
  the congruence.  `FaithfulFormComposition` is the same statement without the
  coprimality hypotheses and implies the recorded `FormCompositionLaw`.

* **Faithful ideal squaring.**  `ExplicitIdealSquaring` asks for the actual
  squaring output: with `g = gcd(A, 2b)` and `a = (A/g)²`, a primitive form with
  leading coefficient `a`.  This is the form-level content of
  `I²/g = (a, b' + √(-2N))` in
  `research/keybreak-quadratic-class-integration.md`, and it implies
  `IdealSquaringLaw` by taking `d = g`, since `a * g² = A²`.

* **Reduction to `L4SubInputs`.**  `L4SubInputs.ofFaithfulInputs` builds the
  reduced input record from `BandSplit`, `BandProductSmall`,
  `FaithfulFormComposition`, and `ExplicitIdealSquaring`; the resulting
  `realized_of_*` corollaries have the same shape as
  `Cogentic.RandomizedL4Sub.realized_of_l4SubInputs`.

## Relation to Mathlib's class-group infrastructure

Mathlib's `ClassGroup`/`Ideal` API is developed for Dedekind domains and rings
of integers.  The order `ℤ[√(-2N)]` is non-maximal whenever `N` is not
squarefree, so the ideal class group of the full ring of integers does not
directly model the proper class group used here.  Rather than importing a
conductor/order transport that would be much larger than the two formulas
needed, this file works at the form level and isolates the exact algebraic
content.  The principal-form observations then show that the two recorded
weaker `Prop`s require no class-group input at all.

Nothing here is a `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL4Composition

open Finset
open scoped BigOperators

open Cogentic.RandomizedL4
open Cogentic.RandomizedL4Sub
open Cogentic.RandomizedFormGroup
open Cogentic.RandomizedReducedFormSupply
open Cogentic.RandomizedEpochPrivate

noncomputable section

/-!
## Section 1: The principal form and the recorded laws

The form `[1, 0, 2N]` has discriminant `-8N`, is primitive, and has leading
coefficient `1`.  It therefore witnesses both recorded class-group inputs.
-/

/-- The principal form `[1, 0, 2N]` of discriminant `-8N` is primitive. -/
theorem isPrimitiveForm_principal (N : ℕ) :
    IsPrimitiveForm N 1 0 ((2 * N : ℕ) : ℤ) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · push_cast
    ring
  · simp

/-- **The Gauss/Dirichlet composition law is automatic as stated.**  The
principal form has leading coefficient `1`, which divides every product. -/
theorem formCompositionLaw_vacuous (N : ℕ) : FormCompositionLaw N := by
  intro A₁ b₁ C₁ A₂ b₂ C₂ _h₁ _h₂
  exact ⟨1, 0, ((2 * N : ℕ) : ℤ), isPrimitiveForm_principal N, one_dvd _⟩

/-- **The ideal-squaring law is automatic as stated.**  Take the principal form
and `d = A`; then `1 * A² = A²`. -/
theorem idealSquaringLaw_vacuous (N : ℕ) : IdealSquaringLaw N := by
  intro A b C h
  refine ⟨1, 0, 2 * N, A, by norm_num, h.2.1, ?_, isPrimitiveForm_principal N⟩
  simp

/-- The reduced L4 inputs with no class-group hypotheses beyond the band data. -/
theorem L4SubInputs.ofBandInputs {N m : ℕ} {P : Fin m → Finset ℕ}
    (hsplit : BandSplit N m P) (hsmall : BandProductSmall N m P) :
    L4SubInputs N m P :=
  { band_split := hsplit
    band_small := hsmall
    form_composition := formCompositionLaw_vacuous N
    ideal_squaring := idealSquaringLaw_vacuous N }

/-- **Realization from splitting bands and the band bound alone.**  The two
recorded class-group laws are discharged by the principal form, so no further
algebraic input is needed. -/
theorem realized_of_bandInputs {N m : ℕ} {P : Fin m → Finset ℕ}
    (hsplit : BandSplit N m P) (hsmall : BandProductSmall N m P)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N)) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs (L4SubInputs.ofBandInputs hsplit hsmall) hprime hPcop

/-!
## Section 2: Genuine Dirichlet composition

The CRT step produces a root `b` of `-2N` modulo `A₁ * A₂` from roots modulo
`A₁` and `A₂`.  The resulting third coefficient is `C = (b² + 2N)/(A₁A₂)`.
-/

/-- A simultaneous congruence root for two positive coprime moduli. -/
private theorem crtRoot (a1 a2 : ℕ) (h1 : 0 < a1) (h2 : 0 < a2)
    (hcop : a1.Coprime a2) (b1 b2 : ℤ) :
    ∃ b : ℤ, (b : ZMod a1) = (b1 : ZMod a1) ∧ (b : ZMod a2) = (b2 : ZMod a2) := by
  classical
  have h1ne : a1 ≠ 0 := h1.ne'
  have h2ne : a2 ≠ 0 := h2.ne'
  haveI : NeZero a1 := ⟨h1ne⟩
  haveI : NeZero a2 := ⟨h2ne⟩
  haveI : NeZero (a1 * a2) := ⟨mul_ne_zero h1ne h2ne⟩
  let e := ZMod.chineseRemainder hcop
  let z : ZMod (a1 * a2) := e.symm ((b1 : ZMod a1), (b2 : ZMod a2))
  let b : ℤ := (z.val : ℤ)
  have hfst : (e z).1 = (ZMod.cast z : ZMod a1) := by
    dsimp only [e, ZMod.chineseRemainder, ZMod.castHom_apply]
    exact Prod.fst_zmod_cast z
  have hsnd : (e z).2 = (ZMod.cast z : ZMod a2) := by
    dsimp only [e, ZMod.chineseRemainder, ZMod.castHom_apply]
    exact Prod.snd_zmod_cast z
  refine ⟨b, ?_, ?_⟩
  · have h := congrArg Prod.fst (e.apply_symm_apply ((b1 : ZMod a1), (b2 : ZMod a2)))
    dsimp only [z] at h
    rw [hfst] at h
    have hb : (b : ZMod a1) = (ZMod.cast z : ZMod a1) := by
      dsimp only [b]
      rw [Int.cast_natCast]
      exact ZMod.natCast_val z
    rw [hb]
    exact h
  · have h := congrArg Prod.snd (e.apply_symm_apply ((b1 : ZMod a1), (b2 : ZMod a2)))
    dsimp only [z] at h
    rw [hsnd] at h
    have hb : (b : ZMod a2) = (ZMod.cast z : ZMod a2) := by
      dsimp only [b]
      rw [Int.cast_natCast]
      exact ZMod.natCast_val z
    rw [hb]
    exact h

/-- **Dirichlet composition in the coprime case.**  If two primitive forms have
leading coefficients coprime to each other, and if each leading coefficient is
coprime to the corresponding middle coefficient, then their product has a
primitive representative of discriminant `-8N` with leading coefficient exactly
`A₁ * A₂`.

The `IsCoprime Aᵢ (2bᵢ)` hypotheses are the form-level primitivity data needed
at the two factors. -/
theorem dirichletComposition (N : ℕ) :
    ∀ (A₁ b₁ C₁ A₂ b₂ C₂ : ℤ),
      IsPrimitiveForm N A₁ b₁ C₁ → IsPrimitiveForm N A₂ b₂ C₂ →
      IsCoprime A₁ (2 * b₁) → IsCoprime A₂ (2 * b₂) →
      Nat.Coprime A₁.natAbs A₂.natAbs →
        ∃ (b C : ℤ), IsPrimitiveForm N (A₁ * A₂) b C := by
  intro A₁ b₁ C₁ A₂ b₂ C₂ h1 h2 hcop1 hcop2 hc12
  obtain ⟨hA1, hdisc1, _⟩ := h1
  obtain ⟨hA2, hdisc2, _⟩ := h2
  have hA1pos : 0 < A₁ := hA1
  have hA2pos : 0 < A₂ := hA2
  set a1 : ℕ := A₁.natAbs
  set a2 : ℕ := A₂.natAbs
  have ha1 : (a1 : ℤ) = A₁ := by
    dsimp only [a1]
    exact Int.natAbs_of_nonneg hA1pos.le
  have ha2 : (a2 : ℤ) = A₂ := by
    dsimp only [a2]
    exact Int.natAbs_of_nonneg hA2pos.le
  have ha1pos : 0 < a1 := by
    dsimp only [a1]
    exact Int.natAbs_pos.mpr hA1pos.ne'
  have ha2pos : 0 < a2 := by
    dsimp only [a2]
    exact Int.natAbs_pos.mpr hA2pos.ne'
  have hcop : a1.Coprime a2 := by simpa [a1, a2] using hc12
  obtain ⟨b, hb1, hb2⟩ := crtRoot a1 a2 ha1pos ha2pos hcop b₁ b₂
  have hdvd1 : A₁ ∣ b - b₁ := by
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b b₁ a1).mp hb1
    rw [ha1] at hk
    refine ⟨-k, ?_⟩
    rw [mul_neg]
    linarith
  have hdvd2 : A₂ ∣ b - b₂ := by
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b b₂ a2).mp hb2
    rw [ha2] at hk
    refine ⟨-k, ?_⟩
    rw [mul_neg]
    linarith
  have hb1dvd : A₁ ∣ b₁ ^ 2 + 2 * (N : ℤ) := by
    have hAC : A₁ * C₁ = b₁ ^ 2 + 2 * (N : ℤ) := by linarith
    exact ⟨C₁, hAC.symm⟩
  have hb2dvd : A₂ ∣ b₂ ^ 2 + 2 * (N : ℤ) := by
    have hAC : A₂ * C₂ = b₂ ^ 2 + 2 * (N : ℤ) := by linarith
    exact ⟨C₂, hAC.symm⟩
  have hbdvd1 : A₁ ∣ b ^ 2 + 2 * (N : ℤ) := by
    obtain ⟨k, hk⟩ := hdvd1
    have hdiff : A₁ ∣ b ^ 2 - b₁ ^ 2 := by
      refine ⟨k * (b + b₁), ?_⟩
      calc
        b ^ 2 - b₁ ^ 2 = (b - b₁) * (b + b₁) := by ring
        _ = (A₁ * k) * (b + b₁) := by rw [hk]
        _ = A₁ * (k * (b + b₁)) := by ring
    obtain ⟨u, hu⟩ := hdiff
    obtain ⟨v, hv⟩ := hb1dvd
    refine ⟨u + v, ?_⟩
    calc
      b ^ 2 + 2 * (N : ℤ) = (b ^ 2 - b₁ ^ 2) + (b₁ ^ 2 + 2 * (N : ℤ)) := by ring
      _ = A₁ * u + A₁ * v := by rw [hu, hv]
      _ = A₁ * (u + v) := by ring
  have hbdvd2 : A₂ ∣ b ^ 2 + 2 * (N : ℤ) := by
    obtain ⟨k, hk⟩ := hdvd2
    have hdiff : A₂ ∣ b ^ 2 - b₂ ^ 2 := by
      refine ⟨k * (b + b₂), ?_⟩
      calc
        b ^ 2 - b₂ ^ 2 = (b - b₂) * (b + b₂) := by ring
        _ = (A₂ * k) * (b + b₂) := by rw [hk]
        _ = A₂ * (k * (b + b₂)) := by ring
    obtain ⟨u, hu⟩ := hdiff
    obtain ⟨v, hv⟩ := hb2dvd
    refine ⟨u + v, ?_⟩
    calc
      b ^ 2 + 2 * (N : ℤ) = (b ^ 2 - b₂ ^ 2) + (b₂ ^ 2 + 2 * (N : ℤ)) := by ring
      _ = A₂ * u + A₂ * v := by rw [hu, hv]
      _ = A₂ * (u + v) := by ring
  have hcopZ : IsCoprime A₁ A₂ := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
    simpa [a1, a2] using hc12.gcd_eq_one
  have hprod : A₁ * A₂ ∣ b ^ 2 + 2 * (N : ℤ) := hcopZ.mul_dvd hbdvd1 hbdvd2
  obtain ⟨C, hC⟩ := hprod
  have hcopb1 : IsCoprime A₁ (2 * b) := by
    obtain ⟨k, hk⟩ := hdvd1
    have hbk : b = b₁ + A₁ * k := by linarith
    have h2 : 2 * b = 2 * b₁ + A₁ * (2 * k) := by rw [hbk]; ring
    have := hcop1.add_mul_left_right (2 * k)
    rwa [← h2] at this
  have hcopb2 : IsCoprime A₂ (2 * b) := by
    obtain ⟨k, hk⟩ := hdvd2
    have hbk : b = b₂ + A₂ * k := by linarith
    have h2 : 2 * b = 2 * b₂ + A₂ * (2 * k) := by rw [hbk]; ring
    have := hcop2.add_mul_left_right (2 * k)
    rwa [← h2] at this
  have hcopb : IsCoprime (A₁ * A₂) (2 * b) := hcopb1.mul_left hcopb2
  refine ⟨b, C, ?_, ?_, ?_⟩
  · exact mul_pos hA1pos hA2pos
  · have hCe : (A₁ * A₂) * C = b ^ 2 + 2 * (N : ℤ) := hC.symm
    linarith
  · have hg : Nat.gcd (A₁.natAbs * A₂.natAbs) (2 * b.natAbs) = 1 := by
      have h := Int.isCoprime_iff_gcd_eq_one.mp hcopb
      rw [Int.gcd_eq_natAbs, Int.natAbs_mul, Int.natAbs_mul] at h
      simpa using h
    rw [Int.natAbs_mul, hg]
    simp

/-- The faithful composition statement: every pair of primitive forms composes
to a primitive form with leading coefficient exactly the product.  This is the
precise algebraic input behind `FormCompositionLaw`. -/
def FaithfulFormComposition (N : ℕ) : Prop :=
  ∀ (A₁ b₁ C₁ A₂ b₂ C₂ : ℤ),
    IsPrimitiveForm N A₁ b₁ C₁ → IsPrimitiveForm N A₂ b₂ C₂ →
      ∃ (b C : ℤ), IsPrimitiveForm N (A₁ * A₂) b C

/-- The faithful composition statement implies the recorded composition law. -/
theorem formCompositionLaw_of_faithful {N : ℕ}
    (h : FaithfulFormComposition N) : FormCompositionLaw N := by
  intro A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂
  obtain ⟨b, C, hprim⟩ := h A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂
  exact ⟨A₁ * A₂, b, C, hprim, dvd_refl _⟩

/-!
## Section 3: The ideal-squaring formula

For a reduced form `[A, 2b, C]` with `AC = b² + 2N`, the squaring formula uses
`g = gcd(A, 2b)` and the new leading coefficient `a = (A/g)²`.  The faithful
input is the existence of a primitive representative with this leading
coefficient; the recorded `IdealSquaringLaw` follows by taking `d = g`.
-/

/-- **Faithful ideal-squaring output.**  For every reduced form, with
`g = gcd(A, 2b)` and `a = (A/g)²`, there is a primitive form of discriminant
`-8N` with leading coefficient `a`. -/
def ExplicitIdealSquaring (N : ℕ) : Prop :=
  ∀ (A : ℕ) (b : ℤ) (C : ℕ), IsReducedForm N A b C →
    ∃ (b' : ℤ) (C' : ℕ),
      IsPrimitiveForm N (((A / Nat.gcd A (2 * b.natAbs)) ^ 2 : ℕ) : ℤ) b' C'

/-- The faithful squaring output implies `IdealSquaringLaw`, with `d = g` and
`a = (A/g)²`, using `(A/g) * g = A`. -/
theorem idealSquaringLaw_of_explicit {N : ℕ}
    (h : ExplicitIdealSquaring N) : IdealSquaringLaw N := by
  intro A b C hred
  have hA : 0 < A := hred.2.1
  set g : ℕ := Nat.gcd A (2 * b.natAbs)
  have hgpos : 0 < g := by
    dsimp only [g]
    exact Nat.gcd_pos_of_pos_left _ hA
  have hgdvd : g ∣ A := by
    dsimp only [g]
    exact Nat.gcd_dvd_left _ _
  have hgle : g ≤ A := Nat.le_of_dvd hA hgdvd
  have hdivpos : 0 < A / g := Nat.div_pos hgle hgpos
  obtain ⟨b', C', hprim⟩ := h A b C hred
  refine ⟨(A / g) ^ 2, b', C', g, pow_pos hdivpos 2, hgpos, ?_, ?_⟩
  · calc
      (A / g) ^ 2 * g ^ 2 = ((A / g) * g) ^ 2 := by rw [mul_pow]
      _ = A ^ 2 := by rw [Nat.div_mul_cancel hgdvd]
  · simpa [g] using hprim

/-- The reduced L4 inputs from the faithful composition and squaring inputs. -/
theorem L4SubInputs.ofFaithfulInputs {N m : ℕ} {P : Fin m → Finset ℕ}
    (hsplit : BandSplit N m P) (hsmall : BandProductSmall N m P)
    (hcomp : FaithfulFormComposition N) (hsq : ExplicitIdealSquaring N) :
    L4SubInputs N m P :=
  { band_split := hsplit
    band_small := hsmall
    form_composition := formCompositionLaw_of_faithful hcomp
    ideal_squaring := idealSquaringLaw_of_explicit hsq }

/-- **Realization from the faithful algebraic inputs.**  Splitting bands, the
band bound, faithful Gauss/Dirichlet composition, and the explicit ideal
squaring formula realize every principal-genus distinct band tuple. -/
theorem realized_of_faithfulInputs {N m : ℕ} {P : Fin m → Finset ℕ}
    (hsplit : BandSplit N m P) (hsmall : BandProductSmall N m P)
    (hcomp : FaithfulFormComposition N) (hsq : ExplicitIdealSquaring N)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N)) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs
    (L4SubInputs.ofFaithfulInputs hsplit hsmall hcomp hsq) hprime hPcop

/-! ## Axiom audit -/

#print axioms isPrimitiveForm_principal
#print axioms formCompositionLaw_vacuous
#print axioms idealSquaringLaw_vacuous
#print axioms L4SubInputs.ofBandInputs
#print axioms realized_of_bandInputs
#print axioms dirichletComposition
#print axioms formCompositionLaw_of_faithful
#print axioms idealSquaringLaw_of_explicit
#print axioms L4SubInputs.ofFaithfulInputs
#print axioms realized_of_faithfulInputs

end

end Cogentic.RandomizedL4Composition
