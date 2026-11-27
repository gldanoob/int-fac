import Cogentic.RandomizedL4Composition
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.ZMod.Basic

set_option linter.style.haveILetI false

/-!
# L4Faithful: auditing and reducing the faithful composition/squaring inputs

`Cogentic.RandomizedL4Composition` records two "faithful" strengthenings of the
two class-group inputs of `RandomizedL4`:

* `FaithfulFormComposition N` --- every pair of primitive forms of discriminant
  `-8N` composes to a primitive form whose leading coefficient is *exactly*
  `A₁ * A₂`;
* `ExplicitIdealSquaring N` --- for every reduced form `[A, 2b, C]`, with
  `g = gcd(A, 2b)` and `a = (A/g)²`, some primitive form has leading
  coefficient `a`.

This file audits both statements.

## What is proved here

* **`FaithfulFormComposition` is false already for odd `N`.**  In the
  principal-square case, the form `[2, 0, N]` is primitive for odd `N`, but no
  form of discriminant `-8N` has leading coefficient `4`, because
  `4C - b² = 2N ≡ 2 (mod 4)` has no solution.  Hence the recorded "faithful"
  composition cannot be the correct algebraic input in the generality stated
  in `RandomizedL4Composition` (`not_faithfulFormComposition_odd`).

* **The Dirichlet/CRT part of composition is proved in full.**  The coprime
  case is re-exported in the faithful shape
  (`FaithfulCompositionCoprime`, `faithfulCompositionCoprime`) and is proved
  *without* the auxiliary content hypotheses
  (`FaithfulCompositionCoprimeGeneral`,
  `faithfulCompositionCoprimeGeneral`): a prime common to `Aᵢ` and `2b` after
  the CRT also divides `2bᵢ`, so primitivity of the factor gives the
  contradiction.  The `d = gcd(A₁, A₂, b₁ + b₂)` form of the general
  Gauss/Dirichlet law (`FaithfulCompositionCox`) is isolated; its coprime
  instance is proved (`faithfulCompositionCox_of_coprime`), and it implies the
  recorded `FormCompositionLaw` (`formCompositionLaw_of_cox`).  The remaining
  content is only the `d²`-correction for non-coprime leading coefficients.

* **The arithmetic half of ideal squaring is proved.**  `SquaringRootLaw N`
  states that `(A/g)²` divides `b'² + 2N` for a suitable `b'`, for every
  reduced form.  Its proof is an explicit Bézout/lifting computation
  (`squaringRootLaw`): write `b' = b + q t` and solve the linear congruence
  with `gcd(q, 2b)`.  `ExplicitIdealSquaring` is then *equivalent* to this
  root law plus an explicit primitive-selection residual
  (`explicitIdealSquaring_iff_root_and_selection`).  The principal form also
  gives `ExplicitIdealSquaring` for `q = 1`
  (`explicitIdealSquaring_of_q_eq_one`).

* **Reduction to `L4SubInputs`.**  `L4SubInputs.ofFaithfulArithmetic` builds
  the reduced input record from band splitting, the band bound, the corrected
  faithful composition input and the faithful squaring input; the filtered
  version `L4SubInputs.ofSquaringRootAndSelection` uses the proved root law and
  the primitive-selection residual.  The corollaries
  `realized_of_faithfulArithmetic` have the same shape as
  `Cogentic.RandomizedL4Sub.realized_of_l4SubInputs`.

Nothing here is a `sorry`, `admit`, `axiom`, or `native_decide`, and no loss is
set to zero.
-/

namespace Cogentic.RandomizedL4Faithful

open Finset
open scoped BigOperators

open Cogentic.RandomizedL4
open Cogentic.RandomizedL4Sub
open Cogentic.RandomizedL4Composition
open Cogentic.RandomizedFormGroup
open Cogentic.RandomizedReducedFormSupply
open Cogentic.RandomizedEpochPrivate

noncomputable section

/-!
## Section 1: The Dirichlet/CRT core of faithful composition

`dirichletComposition` is the genuine CRT construction.  We first re-export it
in the exact shape of `FaithfulFormComposition` restricted to the coprime case,
then isolate the `d²`-corrected general law.
-/

/-- Faithful composition in the coprime case, with the form-level primitivity
content hypotheses that the existing CRT proof consumes.  This is
`Cogentic.RandomizedL4Composition.dirichletComposition` restated in the
`FaithfulFormComposition` shape. -/
def FaithfulCompositionCoprime (N : ℕ) : Prop :=
  ∀ (A₁ b₁ C₁ A₂ b₂ C₂ : ℤ),
    IsPrimitiveForm N A₁ b₁ C₁ → IsPrimitiveForm N A₂ b₂ C₂ →
      IsCoprime A₁ (2 * b₁) → IsCoprime A₂ (2 * b₂) →
        Nat.Coprime A₁.natAbs A₂.natAbs →
          ∃ (b C : ℤ), IsPrimitiveForm N (A₁ * A₂) b C

/-- **The existing Dirichlet composition, in faithful shape.** -/
theorem faithfulCompositionCoprime (N : ℕ) : FaithfulCompositionCoprime N :=
  dirichletComposition N

/-! ### The full coprime case

The CRT construction also proves the coprime case *without* the form-level
content hypotheses `IsCoprime Aᵢ (2 bᵢ)` consumed by `dirichletComposition`.
The extra argument is that a prime `p` dividing both `Aᵢ` and `2b` (after the
CRT) also divides the corresponding `2bᵢ`, so primitivity of the factor rules
out a common divisor with the composed third coefficient.  Hence the entire
coprime case is discharged by CRT arithmetic; only the non-coprime `d²`
correction remains in `FaithfulCompositionCox`. -/

/-- Faithful composition for coprime leading coefficients, with no extra
content hypotheses. -/
def FaithfulCompositionCoprimeGeneral (N : ℕ) : Prop :=
  ∀ (A₁ b₁ C₁ A₂ b₂ C₂ : ℤ),
    IsPrimitiveForm N A₁ b₁ C₁ → IsPrimitiveForm N A₂ b₂ C₂ →
      Nat.Coprime A₁.natAbs A₂.natAbs →
        ∃ (b C : ℤ), IsPrimitiveForm N (A₁ * A₂) b C

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

/-- Coprime composition without the content hypotheses (proof body). -/
theorem faithfulCompositionCoprimeGeneralAux (N : ℕ) :
    ∀ (A₁ b₁ C₁ A₂ b₂ C₂ : ℤ),
      IsPrimitiveForm N A₁ b₁ C₁ → IsPrimitiveForm N A₂ b₂ C₂ →
      Nat.Coprime A₁.natAbs A₂.natAbs →
        ∃ (b C : ℤ), IsPrimitiveForm N (A₁ * A₂) b C := by
  intro A₁ b₁ C₁ A₂ b₂ C₂ h1 h2 hc12
  obtain ⟨hA1, hdisc1, hgcd1⟩ := h1
  obtain ⟨hA2, hdisc2, hgcd2⟩ := h2
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
  -- Relation A₂ * C = C₁ + 2 k b₁ + A₁ k² from the CRT congruence.
  have hA2C : ∀ k : ℤ, b = b₁ + A₁ * k →
      A₂ * C = C₁ + 2 * k * b₁ + A₁ * k ^ 2 := by
    intro k hk
    have hmul : A₁ * (A₂ * C) = A₁ * (C₁ + 2 * k * b₁ + A₁ * k ^ 2) := by
      have hC' : (A₁ * A₂) * C = b ^ 2 + 2 * (N : ℤ) := hC.symm
      have hd1 : A₁ * C₁ = b₁ ^ 2 + 2 * (N : ℤ) := by linarith
      calc
        A₁ * (A₂ * C) = (A₁ * A₂) * C := by ring
        _ = b ^ 2 + 2 * (N : ℤ) := hC'
        _ = (b₁ + A₁ * k) ^ 2 + 2 * (N : ℤ) := by rw [hk]
        _ = A₁ * (C₁ + 2 * k * b₁ + A₁ * k ^ 2) := by nlinarith [hd1]
    exact mul_left_cancel₀ hA1pos.ne' hmul
  refine ⟨b, C, ?_, ?_, ?_⟩
  · exact mul_pos hA1pos hA2pos
  · have hCe : (A₁ * A₂) * C = b ^ 2 + 2 * (N : ℤ) := hC.symm
    linarith
  · -- primitivity of the composed form
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hpd
    have hpX : p ∣ Nat.gcd (A₁ * A₂).natAbs (2 * b.natAbs) :=
      hpd.trans (Nat.gcd_dvd_left _ _)
    have hpC : p ∣ C.natAbs := hpd.trans (Nat.gcd_dvd_right _ _)
    have hpAmul : p ∣ (A₁ * A₂).natAbs := hpX.trans (Nat.gcd_dvd_left _ _)
    have hpb : p ∣ 2 * b.natAbs := hpX.trans (Nat.gcd_dvd_right _ _)
    have hpCz : (p : ℤ) ∣ C := Int.natAbs_dvd_natAbs.mp (by simpa using hpC)
    have hpbranches : p = 2 ∨ p ∣ b.natAbs := by
      rcases hp.dvd_mul.mp hpb with h | h
      · left
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
      · right
        exact h
    have hpAmul' : p ∣ A₁.natAbs * A₂.natAbs := by
      simpa [Int.natAbs_mul] using hpAmul
    rcases hp.dvd_mul.mp hpAmul' with hpA1 | hpA2
    · -- the first factor is responsible
      have hpA1Z : (p : ℤ) ∣ A₁ := Int.natAbs_dvd_natAbs.mp (by simpa using hpA1)
      obtain ⟨k, hk⟩ := hdvd1
      have hbk : b = b₁ + A₁ * k := by linarith
      have hpb1branches : p = 2 ∨ p ∣ b₁.natAbs := by
        rcases hpbranches with hp2 | hpb
        · exact Or.inl hp2
        · right
          have hpbZ : (p : ℤ) ∣ b := Int.natAbs_dvd_natAbs.mp (by simpa using hpb)
          have h1 := dvd_sub hpbZ (dvd_mul_of_dvd_right hpA1Z k)
          have hb1eq : b - k * A₁ = b₁ := by linarith
          rw [hb1eq] at h1
          exact Int.natAbs_dvd_natAbs.mpr (by simpa using h1)
      have hp2b1 : p ∣ 2 * b₁.natAbs := by
        rcases hpb1branches with hp2 | hpb1
        · subst hp2
          exact ⟨b₁.natAbs, by ring⟩
        · simpa [mul_comm] using (dvd_mul_of_dvd_left hpb1 2)
      have hpg1 : p ∣ Nat.gcd A₁.natAbs (2 * b₁.natAbs) := Nat.dvd_gcd hpA1 hp2b1
      have hrel : A₂ * C = C₁ + 2 * k * b₁ + A₁ * k ^ 2 := hA2C k hbk
      have hpC1Z : (p : ℤ) ∣ C₁ := by
        have h1 : (p : ℤ) ∣ A₂ * C := dvd_mul_of_dvd_right hpCz A₂
        have h2 : (p : ℤ) ∣ 2 * k * b₁ + A₁ * k ^ 2 := by
          refine dvd_add ?_ ?_
          · rcases hpb1branches with hp2 | hpb1
            · subst hp2
              exact ⟨k * b₁, by ring⟩
            · have hb1 : (p : ℤ) ∣ b₁ :=
                Int.natAbs_dvd_natAbs.mp (by simpa using hpb1)
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (dvd_mul_of_dvd_right hb1 (2 * k))
          · exact dvd_mul_of_dvd_left hpA1Z (k ^ 2)
        have hsub : (p : ℤ) ∣ A₂ * C - (2 * k * b₁ + A₁ * k ^ 2) :=
          dvd_sub h1 h2
        rw [hrel] at hsub
        simpa using hsub
      have hpC1 : p ∣ C₁.natAbs := by
        simpa using (Int.natAbs_dvd_natAbs.mpr hpC1Z)
      have hpg : p ∣ Nat.gcd (Nat.gcd A₁.natAbs (2 * b₁.natAbs)) C₁.natAbs :=
        Nat.dvd_gcd hpg1 hpC1
      rw [hgcd1] at hpg
      exact hp.not_dvd_one hpg
    · -- the second factor is responsible
      have hpA2Z : (p : ℤ) ∣ A₂ := Int.natAbs_dvd_natAbs.mp (by simpa using hpA2)
      obtain ⟨k, hk⟩ := hdvd2
      have hbk : b = b₂ + A₂ * k := by linarith
      have hpb2branches : p = 2 ∨ p ∣ b₂.natAbs := by
        rcases hpbranches with hp2 | hpb
        · exact Or.inl hp2
        · right
          have hpbZ : (p : ℤ) ∣ b := Int.natAbs_dvd_natAbs.mp (by simpa using hpb)
          have h1 := dvd_sub hpbZ (dvd_mul_of_dvd_right hpA2Z k)
          have hb2eq : b - k * A₂ = b₂ := by linarith
          rw [hb2eq] at h1
          exact Int.natAbs_dvd_natAbs.mpr (by simpa using h1)
      have hp2b2 : p ∣ 2 * b₂.natAbs := by
        rcases hpb2branches with hp2 | hpb2
        · subst hp2
          exact ⟨b₂.natAbs, by ring⟩
        · simpa [mul_comm] using (dvd_mul_of_dvd_left hpb2 2)
      have hpg2 : p ∣ Nat.gcd A₂.natAbs (2 * b₂.natAbs) := Nat.dvd_gcd hpA2 hp2b2
      have hrel : A₁ * C = C₂ + 2 * k * b₂ + A₂ * k ^ 2 := by
        have hmul : A₂ * (A₁ * C) = A₂ * (C₂ + 2 * k * b₂ + A₂ * k ^ 2) := by
          have hC' : (A₁ * A₂) * C = b ^ 2 + 2 * (N : ℤ) := hC.symm
          have hd2 : A₂ * C₂ = b₂ ^ 2 + 2 * (N : ℤ) := by linarith
          calc
            A₂ * (A₁ * C) = (A₁ * A₂) * C := by ring
            _ = b ^ 2 + 2 * (N : ℤ) := hC'
            _ = (b₂ + A₂ * k) ^ 2 + 2 * (N : ℤ) := by rw [hbk]
            _ = A₂ * (C₂ + 2 * k * b₂ + A₂ * k ^ 2) := by nlinarith [hd2]
        exact mul_left_cancel₀ hA2pos.ne' hmul
      have hpC2Z : (p : ℤ) ∣ C₂ := by
        have h1 : (p : ℤ) ∣ A₁ * C := dvd_mul_of_dvd_right hpCz A₁
        have h2 : (p : ℤ) ∣ 2 * k * b₂ + A₂ * k ^ 2 := by
          refine dvd_add ?_ ?_
          · rcases hpb2branches with hp2 | hpb2
            · subst hp2
              exact ⟨k * b₂, by ring⟩
            · have hb2 : (p : ℤ) ∣ b₂ :=
                Int.natAbs_dvd_natAbs.mp (by simpa using hpb2)
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (dvd_mul_of_dvd_right hb2 (2 * k))
          · exact dvd_mul_of_dvd_left hpA2Z (k ^ 2)
        have hsub : (p : ℤ) ∣ A₁ * C - (2 * k * b₂ + A₂ * k ^ 2) :=
          dvd_sub h1 h2
        rw [hrel] at hsub
        simpa using hsub
      have hpC2 : p ∣ C₂.natAbs := by
        simpa using (Int.natAbs_dvd_natAbs.mpr hpC2Z)
      have hpg : p ∣ Nat.gcd (Nat.gcd A₂.natAbs (2 * b₂.natAbs)) C₂.natAbs :=
        Nat.dvd_gcd hpg2 hpC2
      rw [hgcd2] at hpg
      exact hp.not_dvd_one hpg

/-- **The full coprime case is proved.** -/
theorem faithfulCompositionCoprimeGeneral (N : ℕ) :
    FaithfulCompositionCoprimeGeneral N := by
  intro A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂ hc₁₂
  exact faithfulCompositionCoprimeGeneralAux N A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂ hc₁₂

/-- The faithful composition statement implies the coprime Dirichlet statement
(trivially, by applying it to the coprime subclass). -/
theorem faithfulCompositionCoprime_of_faithful {N : ℕ}
    (h : FaithfulFormComposition N) : FaithfulCompositionCoprime N := by
  intro A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂ _hc₁ _hc₂ _hc12
  exact h A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂

/-- The faithful composition statement also implies the full coprime case. -/
theorem faithfulCompositionCoprimeGeneral_of_faithful {N : ℕ}
    (h : FaithfulFormComposition N) : FaithfulCompositionCoprimeGeneral N := by
  intro A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂ _hc₁₂
  exact h A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂

/-- **The `d²`-corrected faithful composition law.**  With
`d = gcd(A₁, A₂, b₁ + b₂)` (the classical Cox/Dirichlet correction, written
with the half-middle coefficient), the product class has a primitive
representative of leading coefficient `A₁ A₂ / d²`.

This is the correct faithful form-level statement; for coprime leading
coefficients `d = 1` and it coincides with `FaithfulFormComposition`. -/
def FaithfulCompositionCox (N : ℕ) : Prop :=
  ∀ (A₁ b₁ C₁ A₂ b₂ C₂ : ℤ),
    IsPrimitiveForm N A₁ b₁ C₁ → IsPrimitiveForm N A₂ b₂ C₂ →
      ∃ (b C : ℤ),
        IsPrimitiveForm N
          ((A₁ * A₂) /
            ((Nat.gcd (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs : ℤ)) ^ 2) b C

/-- In the coprime case the correction factor is `1`, so the existing Dirichlet
composition proves the `d²`-corrected law. -/
theorem faithfulCompositionCox_of_dirichlet {N : ℕ} {A₁ b₁ C₁ A₂ b₂ C₂ : ℤ}
    (h₁ : IsPrimitiveForm N A₁ b₁ C₁) (h₂ : IsPrimitiveForm N A₂ b₂ C₂)
    (hc₁ : IsCoprime A₁ (2 * b₁)) (hc₂ : IsCoprime A₂ (2 * b₂))
    (hc₁₂ : Nat.Coprime A₁.natAbs A₂.natAbs) :
    ∃ (b C : ℤ),
      IsPrimitiveForm N
        ((A₁ * A₂) /
          ((Nat.gcd (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs : ℤ)) ^ 2) b C := by
  have hd : Nat.gcd (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs = 1 := by
    rw [hc₁₂.gcd_eq_one, Nat.gcd_one_left]
  obtain ⟨b, C, hprim⟩ :=
    dirichletComposition N A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂ hc₁ hc₂ hc₁₂
  exact ⟨b, C, by simpa [hd] using hprim⟩

/-- In the coprime case the correction factor is `1`, so the full coprime
result proves the `d²`-corrected law with no content hypotheses. -/
theorem faithfulCompositionCox_of_coprime {N : ℕ} {A₁ b₁ C₁ A₂ b₂ C₂ : ℤ}
    (h₁ : IsPrimitiveForm N A₁ b₁ C₁) (h₂ : IsPrimitiveForm N A₂ b₂ C₂)
    (hc₁₂ : Nat.Coprime A₁.natAbs A₂.natAbs) :
    ∃ (b C : ℤ),
      IsPrimitiveForm N
        ((A₁ * A₂) /
          ((Nat.gcd (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs : ℤ)) ^ 2) b C := by
  have hd : Nat.gcd (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs = 1 := by
    rw [hc₁₂.gcd_eq_one, Nat.gcd_one_left]
  obtain ⟨b, C, hprim⟩ :=
    faithfulCompositionCoprimeGeneral N A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂ hc₁₂
  exact ⟨b, C, by simpa [hd] using hprim⟩

/-- The correction divisor `d` squares to a divisor of `A₁ * A₂`. -/
theorem sq_correction_dvd_mul {A₁ A₂ b₁ b₂ : ℤ} :
    (((Nat.gcd (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs : ℤ)) ^ 2) ∣
      A₁ * A₂ := by
  set d : ℕ := Nat.gcd (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs
  have hd₁ : (d : ℤ) ∣ A₁ := by
    have h : d ∣ A₁.natAbs :=
      (Nat.gcd_dvd_left (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs).trans
        (Nat.gcd_dvd_left A₁.natAbs A₂.natAbs)
    exact Int.natAbs_dvd_natAbs.mp (by simpa using h)
  have hd₂ : (d : ℤ) ∣ A₂ := by
    have h : d ∣ A₂.natAbs :=
      (Nat.gcd_dvd_left (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs).trans
        (Nat.gcd_dvd_right A₁.natAbs A₂.natAbs)
    exact Int.natAbs_dvd_natAbs.mp (by simpa using h)
  obtain ⟨x, hx⟩ := hd₁
  obtain ⟨y, hy⟩ := hd₂
  refine ⟨x * y, ?_⟩
  rw [hx, hy]
  ring

/-- **The `d²`-corrected law implies the recorded composition law.**  The
corrected leading coefficient `A₁ A₂ / d²` divides `A₁ A₂`. -/
theorem formCompositionLaw_of_cox {N : ℕ} (h : FaithfulCompositionCox N) :
    FormCompositionLaw N := by
  intro A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂
  obtain ⟨b, C, hprim⟩ := h A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂
  refine ⟨_, b, C, hprim, ?_⟩
  set d : ℕ := Nat.gcd (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs
  have hdvd : ((d : ℤ) ^ 2) ∣ A₁ * A₂ :=
    sq_correction_dvd_mul (A₁ := A₁) (A₂ := A₂) (b₁ := b₁) (b₂ := b₂)
  have hdne : ((d : ℤ) ^ 2) ≠ 0 := by
    have hA₁ : 0 < A₁ := h₁.1
    have hdpos : 0 < d :=
      Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _
        (Int.natAbs_pos.mpr hA₁.ne'))
    have hdc : (d : ℤ) ≠ 0 := by exact_mod_cast hdpos.ne'
    exact pow_ne_zero 2 hdc
  have hmul : A₁ * A₂ ∣ ((d : ℤ) ^ 2) * (A₁ * A₂) := ⟨(d : ℤ) ^ 2, by ring⟩
  exact (Int.div_dvd_iff_dvd_mul hdvd hdne).mpr hmul

/-!
## Section 2: `FaithfulFormComposition` is false

The principal-square counterexample shows that the exact-leading-coefficient
statement cannot hold in the generality recorded in `RandomizedL4Composition`.
-/

/-- For odd `N`, the form `[2, 0, N]` is primitive of discriminant `-8N`. -/
theorem isPrimitiveForm_two_zero {N : ℕ} (hN : Odd N) :
    IsPrimitiveForm N 2 0 (N : ℤ) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · push_cast
    ring
  · have hcop : Nat.gcd 2 N = 1 := by
      rw [← Nat.coprime_iff_gcd_eq_one]
      exact hN.coprime_two_left
    simpa using hcop

/-- **No primitive form of discriminant `-8N` has leading coefficient `4` for
odd `N`.**  Indeed `4 C - b² = 2 N ≡ 2 (mod 4)` has no solution. -/
theorem not_isPrimitiveForm_four {N : ℕ} (hN : Odd N) (b C : ℤ) :
    ¬ IsPrimitiveForm N 4 b C := by
  rintro ⟨_hA, hdisc, _hprim⟩
  have h4 : (4 : ZMod 4) = 0 := by decide
  have hcast := congrArg (fun z : ℤ => (z : ZMod 4)) hdisc
  push_cast at hcast
  rw [h4] at hcast
  obtain ⟨k, rfl⟩ := hN
  have hNcast : ((2 * k + 1 : ℕ) : ZMod 4) = 2 * (k : ZMod 4) + 1 := by
    push_cast
    ring
  have h2N : 2 * ((2 * k + 1 : ℕ) : ZMod 4) = 2 := by
    rw [hNcast]
    calc
      2 * (2 * (k : ZMod 4) + 1) = 4 * (k : ZMod 4) + 2 := by ring
      _ = 2 := by rw [h4]; ring
  have hneg : -((b : ZMod 4) ^ 2) = 2 := by
    rw [h2N] at hcast
    simpa using hcast
  have hneg2 : (-2 : ZMod 4) = 2 := by decide
  have hb2 : (b : ZMod 4) ^ 2 = 2 := by
    calc
      (b : ZMod 4) ^ 2 = -(-((b : ZMod 4) ^ 2)) := by ring
      _ = -2 := by rw [hneg]
      _ = 2 := hneg2
  have hno : ∀ y : ZMod 4, y ^ 2 ≠ 2 := by decide
  exact hno (b : ZMod 4) hb2

/-- **`FaithfulFormComposition` is refutable for odd `N`.**  The primitive form
`[2, 0, N]` composed with itself would need a primitive form with leading
coefficient `4`, which does not exist. -/
theorem not_faithfulFormComposition_odd {N : ℕ} (hN : Odd N) :
    ¬ FaithfulFormComposition N := by
  intro h
  have hprim := isPrimitiveForm_two_zero hN
  obtain ⟨b, C, hfour⟩ := h 2 0 (N : ℤ) 2 0 (N : ℤ) hprim hprim
  exact not_isPrimitiveForm_four hN b C hfour

/-!
## Section 3: The arithmetic content of ideal squaring

For a reduced form `[A, 2b, C]` we put `g = gcd(A, 2b)` and `q = A/g`.  The
first, genuinely arithmetic step of the squaring formula is that `q²` divides
`b'² + 2N` for a suitable `b'`.  This is proved here in full.
-/

/-- **Root law for the squaring leading coefficient.**  For every reduced form
`[A, 2b, C]`, with `q = A / gcd(A, 2b)`, there is `b'` with
`q² ∣ b'² + 2N`. -/
def SquaringRootLaw (N : ℕ) : Prop :=
  ∀ (A : ℕ) (b : ℤ) (C : ℕ), IsReducedForm N A b C →
    ∃ b' : ℤ,
      ((((A / Nat.gcd A (2 * b.natAbs)) ^ 2 : ℕ) : ℤ)) ∣ b' ^ 2 + 2 * (N : ℤ)

/-- **The root law, proved by explicit Bézout lifting.**  Write
`q = A / g` and `h = gcd(q, 2b)`.  Since `h ∣ g`, the linear congruence
`q ∣ g C + 2 b t` is solvable; then `b' = b + q t` satisfies
`q² ∣ b'² + 2N`. -/
theorem squaringRootLaw (N : ℕ) : SquaringRootLaw N := by
  intro A b C hred
  obtain ⟨hdisc, hA, _hlo, _hhi, _hAC, _hb, _hprim⟩ := hred
  set g : ℕ := Nat.gcd A (2 * b.natAbs) with hg
  set q : ℕ := A / g with hq
  set h : ℕ := Nat.gcd q (2 * b.natAbs) with hh
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hA
  have hgdvd : g ∣ A := Nat.gcd_dvd_left A (2 * b.natAbs)
  have hqg : q * g = A := Nat.div_mul_cancel hgdvd
  have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hA hgdvd) hgpos
  -- `A = q * g` in `ℤ`, and `b² + 2N = q * (g C)`.
  have hAcast : (A : ℤ) = (q : ℤ) * (g : ℤ) := by
    rw [← hqg]
    push_cast
    ring
  have hD : b ^ 2 + 2 * (N : ℤ) = (q : ℤ) * ((g : ℤ) * (C : ℤ)) := by
    calc
      b ^ 2 + 2 * (N : ℤ) = (A : ℤ) * (C : ℤ) := by linarith
      _ = ((q : ℤ) * (g : ℤ)) * (C : ℤ) := by rw [hAcast]
      _ = (q : ℤ) * ((g : ℤ) * (C : ℤ)) := by ring
  -- `h = gcd(q, 2b)` in `ℤ`.
  have hgcd : Int.gcd (q : ℤ) (2 * b) = h := by
    rw [Int.gcd_eq_natAbs]
    have h2b : (2 * b).natAbs = 2 * b.natAbs := by
      rw [Int.natAbs_mul]
      norm_num
    rw [Int.natAbs_natCast, h2b]
  -- Bézout for `h`.
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ,
      (h : ℤ) = (q : ℤ) * u + (2 * b) * v := by
    refine ⟨Int.gcdA (q : ℤ) (2 * b), Int.gcdB (q : ℤ) (2 * b), ?_⟩
    have := Int.gcd_eq_gcd_ab (q : ℤ) (2 * b)
    rw [hgcd] at this
    exact this
  -- `h` divides `g`, hence `g C`.
  have hhq : h ∣ q := Nat.gcd_dvd_left q (2 * b.natAbs)
  have hh2b : h ∣ 2 * b.natAbs := Nat.gcd_dvd_right q (2 * b.natAbs)
  have hhA : h ∣ A := hhq.trans ⟨g, hqg.symm⟩
  have hhg : h ∣ g := by
    show h ∣ Nat.gcd A (2 * b.natAbs)
    exact Nat.dvd_gcd hhA hh2b
  obtain ⟨w, hw⟩ := hhg
  -- `g C = h * W` with `W = w * C`.
  let W : ℤ := (w : ℤ) * (C : ℤ)
  have hgC : (g : ℤ) * (C : ℤ) = (h : ℤ) * W := by
    dsimp only [W]
    rw [hw]
    push_cast
    ring
  -- The lifting step `t = -W * v`.
  let t : ℤ := -W * v
  have hkey : (q : ℤ) ∣ (g : ℤ) * (C : ℤ) + 2 * b * t := by
    refine ⟨W * u, ?_⟩
    calc
      (g : ℤ) * (C : ℤ) + 2 * b * t
          = (h : ℤ) * W + 2 * b * (-W * v) := by rw [hgC]
      _ = W * ((h : ℤ) - 2 * b * v) := by ring
      _ = W * ((q : ℤ) * u) := by
            have hlin : (h : ℤ) - 2 * b * v = (q : ℤ) * u := by linarith [huv]
            rw [hlin]
      _ = (q : ℤ) * (W * u) := by ring
  obtain ⟨s, hs⟩ := hkey
  refine ⟨b + (q : ℤ) * t, ?_⟩
  push_cast
  refine ⟨s + t ^ 2, ?_⟩
  calc
    (b + (q : ℤ) * t) ^ 2 + 2 * (N : ℤ)
        = (b ^ 2 + 2 * (N : ℤ)) + 2 * b * ((q : ℤ) * t) + ((q : ℤ) * t) ^ 2 := by
          ring
    _ = (q : ℤ) * ((g : ℤ) * (C : ℤ)) + 2 * b * ((q : ℤ) * t) +
          ((q : ℤ) * t) ^ 2 := by rw [hD]
    _ = (q : ℤ) * ((g : ℤ) * (C : ℤ) + 2 * b * t) + (q : ℤ) ^ 2 * t ^ 2 := by
          ring
    _ = (q : ℤ) * ((q : ℤ) * s) + (q : ℤ) ^ 2 * t ^ 2 := by rw [hs]
    _ = (q : ℤ) ^ 2 * (s + t ^ 2) := by ring

/-- The primitive-selection residual of the squaring formula: once a root
`b'` of `-2N` modulo `q²` is available, a primitive form with leading
coefficient `q²` exists.  The root law supplies such a `b'`. -/
def SquaringPrimitiveSelection (N : ℕ) : Prop :=
  ∀ (A : ℕ) (b : ℤ) (C : ℕ), IsReducedForm N A b C →
    ∀ b' : ℤ,
      ((((A / Nat.gcd A (2 * b.natAbs)) ^ 2 : ℕ) : ℤ)) ∣ b' ^ 2 + 2 * (N : ℤ) →
        ∃ (b'' : ℤ) (C'' : ℕ),
          IsPrimitiveForm N
            ((((A / Nat.gcd A (2 * b.natAbs)) ^ 2 : ℕ) : ℤ)) b'' C''

/-- **The faithful squaring input is exactly the root law plus primitive
selection.**  The forward direction extracts the discriminant identity from
`IsPrimitiveForm`; the reverse direction composes the proved root law with the
selection residual. -/
theorem explicitIdealSquaring_iff_root_and_selection (N : ℕ) :
    ExplicitIdealSquaring N ↔ SquaringRootLaw N ∧ SquaringPrimitiveSelection N := by
  constructor
  · intro h
    constructor
    · intro A b C hred
      obtain ⟨b', C', hprim⟩ := h A b C hred
      obtain ⟨_hA, hdisc, _hprim'⟩ := hprim
      refine ⟨b', ?_⟩
      refine ⟨(C' : ℤ), ?_⟩
      linarith
    · intro A b C hred b' _hb'
      obtain ⟨b'', C'', hprim⟩ := h A b C hred
      exact ⟨b'', C'', hprim⟩
  · rintro ⟨hroot, hsel⟩ A b C hred
    obtain ⟨b', hb'⟩ := hroot A b C hred
    exact hsel A b C hred b' hb'

/-- In the case `q = 1` the principal form `[1, 0, 2N]` discharges the
squaring input directly. -/
theorem explicitIdealSquaring_of_q_eq_one {N : ℕ}
    (hq : ∀ (A : ℕ) (b : ℤ) (C : ℕ), IsReducedForm N A b C →
      A / Nat.gcd A (2 * b.natAbs) = 1) :
    ExplicitIdealSquaring N := by
  intro A b C hred
  rw [hq A b C hred]
  exact ⟨0, 2 * N, isPrimitiveForm_principal N⟩

/-!
## Section 4: Reduction to `L4SubInputs`

The recorded `FormCompositionLaw` and `IdealSquaringLaw` follow from the
corrected faithful composition and the faithful squaring.  Since the two
recorded laws are themselves only needed existentially, the corrected input is
enough to build the reduced record.
-/

/-- The reduced L4 inputs from the corrected faithful composition law and the
faithful squaring formula. -/
theorem L4SubInputs.ofFaithfulArithmetic {N m : ℕ} {P : Fin m → Finset ℕ}
    (hsplit : BandSplit N m P) (hsmall : BandProductSmall N m P)
    (hcomp : FaithfulCompositionCox N) (hsq : ExplicitIdealSquaring N) :
    L4SubInputs N m P :=
  { band_split := hsplit
    band_small := hsmall
    form_composition := formCompositionLaw_of_cox hcomp
    ideal_squaring := idealSquaringLaw_of_explicit hsq }

/-- The reduced L4 inputs from the corrected faithful composition law, the
proved squaring root law, and the primitive-selection residual. -/
theorem L4SubInputs.ofSquaringRootAndSelection {N m : ℕ} {P : Fin m → Finset ℕ}
    (hsplit : BandSplit N m P) (hsmall : BandProductSmall N m P)
    (hcomp : FaithfulCompositionCox N) (hsel : SquaringPrimitiveSelection N) :
    L4SubInputs N m P :=
  L4SubInputs.ofFaithfulArithmetic hsplit hsmall hcomp
    ((explicitIdealSquaring_iff_root_and_selection N).mpr ⟨squaringRootLaw N, hsel⟩)

/-- **Realization from the corrected faithful arithmetic inputs.**  This is the
faithful analogue of `Cogentic.RandomizedL4Sub.realized_of_l4SubInputs`. -/
theorem realized_of_faithfulArithmetic {N m : ℕ} {P : Fin m → Finset ℕ}
    (hsplit : BandSplit N m P) (hsmall : BandProductSmall N m P)
    (hcomp : FaithfulCompositionCox N) (hsq : ExplicitIdealSquaring N)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N)) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs
    (L4SubInputs.ofFaithfulArithmetic hsplit hsmall hcomp hsq) hprime hPcop

/-- Realization from the corrected composition law, the proved squaring root
law, and the primitive-selection residual. -/
theorem realized_of_squaringRootAndSelection {N m : ℕ} {P : Fin m → Finset ℕ}
    (hsplit : BandSplit N m P) (hsmall : BandProductSmall N m P)
    (hcomp : FaithfulCompositionCox N) (hsel : SquaringPrimitiveSelection N)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N)) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs
    (L4SubInputs.ofSquaringRootAndSelection hsplit hsmall hcomp hsel) hprime hPcop

/-! ## Axiom audit -/

#print axioms faithfulCompositionCoprime
#print axioms faithfulCompositionCoprime_of_faithful
#print axioms faithfulCompositionCoprimeGeneral
#print axioms faithfulCompositionCoprimeGeneral_of_faithful
#print axioms faithfulCompositionCox_of_dirichlet
#print axioms faithfulCompositionCox_of_coprime
#print axioms sq_correction_dvd_mul
#print axioms formCompositionLaw_of_cox
#print axioms isPrimitiveForm_two_zero
#print axioms not_isPrimitiveForm_four
#print axioms not_faithfulFormComposition_odd
#print axioms squaringRootLaw
#print axioms explicitIdealSquaring_iff_root_and_selection
#print axioms explicitIdealSquaring_of_q_eq_one
#print axioms L4SubInputs.ofFaithfulArithmetic
#print axioms L4SubInputs.ofSquaringRootAndSelection
#print axioms realized_of_faithfulArithmetic
#print axioms realized_of_squaringRootAndSelection

end

end Cogentic.RandomizedL4Faithful
