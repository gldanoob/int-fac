import Cogentic.RandomizedL4Faithful
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.ZMod.Basic

set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-!
# L4Cox: the non-coprime `d²`-correction of Dirichlet composition

`Cogentic.RandomizedL4Faithful` isolates the classical Cox/Dirichlet composition
law

* `FaithfulCompositionCox N`: two primitive forms of discriminant `-8N` with
  leading coefficients `A₁`, `A₂` and half-middle coefficients `b₁`, `b₂`
  compose to a primitive form whose leading coefficient is exactly
  `A₁ A₂ / d²`, where `d = gcd(A₁, A₂, b₁ + b₂)`;

and proves the coprime case (`faithfulCompositionCox_of_coprime`) and the
coprime Dirichlet CRT construction (`faithfulCompositionCoprimeGeneral`).

This file supplies the non-coprime construction.  For a pair of primitive forms
we put

`d = gcd(A₁, A₂, b₁+b₂)`, `aᵢ = Aᵢ/d`, `s = (b₁+b₂)/d`,
`h = (b₁b₂-2N)/d`.

The CRT system is

* `b ≡ b₁ (mod a₁)`, `b ≡ b₂ (mod a₂)`, `s b ≡ h (mod a₁a₂)`.

Choosing a Bézout solution `u a₁ + v a₂ + w s = 1` gives the explicit solution

`b = u a₁ b₂ + v a₂ b₁ + w h`.

Then `a = a₁a₂ = A₁A₂/d²`, and with `k = (b-b₁)/a₁`, `l = (b-b₂)/a₂`,
`m = u C₂ + v C₁`, one has

* `b² + 2N = a (k l + d m)`, so `C = k l + d m`;
* `C₁ = a₂ m - k s`, `C₂ = a₁ m - l s`.

Primitivity of `[a, b, C]` is proved by a prime-divisor analysis: a common
prime `p ∣ a, 2b, C` either contradicts the primitivity of one of the factors,
or (when `p ∣ d`) is pushed into a common divisor of the associated coefficients
`Cᵢ` using the two linear relations above.  The case `p = 2` is handled
separately by parity.

Nothing here is a `sorry`, `admit`, `axiom`, or `native_decide`, and no loss is
set to zero.
-/

namespace Cogentic.RandomizedL4Cox

open Cogentic.RandomizedL4
open Cogentic.RandomizedL4Faithful

noncomputable section

/-! ## Elementary arithmetic helpers -/

/-- Nat divisibility of `a.natAbs` is the same as integral divisibility of `a`. -/
private lemma int_dvd_of_nat_dvd {p : ℕ} {a : ℤ} (h : p ∣ a.natAbs) : (p : ℤ) ∣ a :=
  Int.natAbs_dvd_natAbs.mp (by simpa using h)

/-- Integral divisibility of `a` gives Nat divisibility of `a.natAbs`. -/
private lemma nat_dvd_of_int_dvd {p : ℕ} {a : ℤ} (h : (p : ℤ) ∣ a) : p ∣ a.natAbs := by
  simpa using (Int.natAbs_dvd_natAbs.mpr h)

private lemma even_add_int {a b : ℤ} (ha : Even a) (hb : Even b) : Even (a + b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x + y, by ring⟩

private lemma even_sub_int {a b : ℤ} (ha : Even a) (hb : Even b) : Even (a - b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x - y, by ring⟩

private lemma even_mul_right_int {a : ℤ} (ha : Even a) (b : ℤ) : Even (a * b) := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨x * b, by ring⟩

private lemma even_mul_left_int {a : ℤ} (ha : Even a) (b : ℤ) : Even (b * a) := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨b * x, by ring⟩

/-- An even product with an odd factor forces the other factor to be even. -/
private lemma even_of_mul_odd {a b : ℤ} (h : Even (a * b)) (hb : Odd b) : Even a := by
  have hnot : ¬ Odd (a * b) := (Int.not_odd_iff_even).mpr h
  rw [Int.odd_mul] at hnot
  have hna : ¬ Odd a := fun ha => hnot ⟨ha, hb⟩
  exact (Int.not_odd_iff_even).mp hna

/-- If a prime divides `A`, `2b` and `C`, it divides the content of `[A,b,C]`. -/
private lemma prime_dvd_form_gcd {A b C : ℤ} {p : ℕ}
    (hA : p ∣ A.natAbs) (h2b : p ∣ (2 * b).natAbs) (hC : p ∣ C.natAbs) :
    p ∣ Nat.gcd (Nat.gcd A.natAbs (2 * b.natAbs)) C.natAbs := by
  apply Nat.dvd_gcd
  · apply Nat.dvd_gcd
    · exact hA
    · simpa [Int.natAbs_mul] using h2b
  · exact hC

/-- A prime common to `A`, `2b` and `C` contradicts primitivity of `[A,b,C]`. -/
private lemma form_contra {A b C : ℤ} {p : ℕ} (hp : p.Prime)
    (hprim : Nat.gcd (Nat.gcd A.natAbs (2 * b.natAbs)) C.natAbs = 1)
    (hA : p ∣ A.natAbs) (h2b : p ∣ (2 * b).natAbs) (hC : p ∣ C.natAbs) : False := by
  have hg := prime_dvd_form_gcd hA h2b hC
  rw [hprim] at hg
  exact hp.not_dvd_one hg

/-- Bezout for three integers whose common gcd (in absolute value) is one. -/
private lemma bezout_three {a b c : ℤ}
    (h : Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = 1) :
    ∃ u v w : ℤ, u * a + v * b + w * c = 1 := by
  set g : ℕ := Nat.gcd a.natAbs b.natAbs with hg
  have hgZ : (g : ℤ) = Int.gcd a b := by
    rw [Int.gcd_eq_natAbs]
  obtain ⟨u₀, v₀, h₀⟩ : ∃ u₀ v₀ : ℤ, (g : ℤ) = u₀ * a + v₀ * b := by
    refine ⟨Int.gcdA a b, Int.gcdB a b, ?_⟩
    have := Int.gcd_eq_gcd_ab a b
    rw [← hgZ] at this
    simpa [mul_comm] using this
  have hgc : Nat.gcd g c.natAbs = 1 := by simpa [hg] using h
  have hgZc : Int.gcd (g : ℤ) c = 1 := by
    rw [Int.gcd_eq_natAbs]
    simpa using hgc
  obtain ⟨u₁, v₁, h₁⟩ : ∃ u₁ v₁ : ℤ, u₁ * (g : ℤ) + v₁ * c = 1 := by
    refine ⟨Int.gcdA (g : ℤ) c, Int.gcdB (g : ℤ) c, ?_⟩
    have := Int.gcd_eq_gcd_ab (g : ℤ) c
    rw [hgZc] at this
    simpa [mul_comm] using this.symm
  refine ⟨u₁ * u₀, u₁ * v₀, v₁, ?_⟩
  calc
    (u₁ * u₀) * a + (u₁ * v₀) * b + v₁ * c
        = u₁ * (u₀ * a + v₀ * b) + v₁ * c := by ring
    _ = u₁ * (g : ℤ) + v₁ * c := by rw [h₀]
    _ = 1 := h₁

/-- After dividing a triple by its gcd, the three quotients have gcd `1`. -/
private lemma gcd_quotients_eq_one {x y z : ℤ} {d : ℕ}
    (hdpos : 0 < d) (hdx : (d : ℤ) ∣ x) (hdy : (d : ℤ) ∣ y) (hdz : (d : ℤ) ∣ z)
    (hgd : d = Nat.gcd (Nat.gcd x.natAbs y.natAbs) z.natAbs) :
    Nat.gcd (Nat.gcd (x / (d : ℤ)).natAbs (y / (d : ℤ)).natAbs) (z / (d : ℤ)).natAbs = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpd
  have hpx : p ∣ (x / (d : ℤ)).natAbs :=
    (hpd.trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_left _ _)
  have hpy : p ∣ (y / (d : ℤ)).natAbs :=
    (hpd.trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_right _ _)
  have hpz : p ∣ (z / (d : ℤ)).natAbs := hpd.trans (Nat.gcd_dvd_right _ _)
  have hpxZ : (p : ℤ) ∣ x / (d : ℤ) := int_dvd_of_nat_dvd hpx
  have hpyZ : (p : ℤ) ∣ y / (d : ℤ) := int_dvd_of_nat_dvd hpy
  have hpzZ : (p : ℤ) ∣ z / (d : ℤ) := int_dvd_of_nat_dvd hpz
  have hpxd : ((d : ℤ) * p) ∣ x := by
    rw [← Int.ediv_mul_cancel hdx]
    simpa [mul_comm] using (mul_dvd_mul_left (d : ℤ) hpxZ)
  have hpyd : ((d : ℤ) * p) ∣ y := by
    rw [← Int.ediv_mul_cancel hdy]
    simpa [mul_comm] using (mul_dvd_mul_left (d : ℤ) hpyZ)
  have hpzd : ((d : ℤ) * p) ∣ z := by
    rw [← Int.ediv_mul_cancel hdz]
    simpa [mul_comm] using (mul_dvd_mul_left (d : ℤ) hpzZ)
  have hpxd_nat : d * p ∣ x.natAbs := by
    apply nat_dvd_of_int_dvd
    simpa [Nat.cast_mul] using hpxd
  have hpyd_nat : d * p ∣ y.natAbs := by
    apply nat_dvd_of_int_dvd
    simpa [Nat.cast_mul] using hpyd
  have hpzd_nat : d * p ∣ z.natAbs := by
    apply nat_dvd_of_int_dvd
    simpa [Nat.cast_mul] using hpzd
  have hgcd0 : d * p ∣ Nat.gcd (Nat.gcd x.natAbs y.natAbs) z.natAbs :=
    Nat.dvd_gcd (Nat.dvd_gcd hpxd_nat hpyd_nat) hpzd_nat
  have hgcd : d * p ∣ d := by simpa [← hgd] using hgcd0
  have hle : d * p ≤ d := Nat.le_of_dvd hdpos hgcd
  have hpge : 2 ≤ p := hp.two_le
  have hdp : d * 2 ≤ d * p := Nat.mul_le_mul_left d hpge
  omega

/-!
## The non-coprime construction

The next lemma is the pure arithmetic core: given the CRT/Bezout data for a
pair of primitive forms, a common prime divisor of the constructed form
contradicts primitivity of one factor.
-/

/-- **Local primitivity/lifting lemma.**  If the CRT/Bezout data produce a
common prime divisor of the composed content, one of the two factor forms is
imprimitive. -/
lemma coxNoCommonPrime
    {A₁ b₁ C₁ A₂ b₂ C₂ d a₁ a₂ s b k l m C : ℤ}
    (hdpos : 0 < d)
    (hA₁ : A₁ = d * a₁) (hA₂ : A₂ = d * a₂)
    (hB : b₁ + b₂ = d * s)
    (hb₁ : b = b₁ + a₁ * k) (hb₂ : b = b₂ + a₂ * l)
    (hC : C = k * l + d * m)
    (hC₁ : C₁ = a₂ * m - k * s) (hC₂ : C₂ = a₁ * m - l * s)
    (hprim₁ : Nat.gcd (Nat.gcd A₁.natAbs (2 * b₁.natAbs)) C₁.natAbs = 1)
    (hprim₂ : Nat.gcd (Nat.gcd A₂.natAbs (2 * b₂.natAbs)) C₂.natAbs = 1)
    {p : ℕ} (hp : p.Prime)
    (hpA : p ∣ a₁.natAbs) (hp2b : p ∣ 2 * b.natAbs) (hpC : p ∣ C.natAbs) : False := by
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hpA_int : (p : ℤ) ∣ a₁ := int_dvd_of_nat_dvd hpA
  have hpC_int : (p : ℤ) ∣ C := int_dvd_of_nat_dvd hpC
  have hp2b_abs : p ∣ (2 * b).natAbs := by simpa [Int.natAbs_mul] using hp2b
  have hp2b_int : (p : ℤ) ∣ 2 * b := int_dvd_of_nat_dvd hp2b_abs
  -- The two linear relations used in the prime analysis.
  have hI1 : a₂ * C = d * C₁ + 2 * k * b₁ + a₁ * k ^ 2 := by
    have h1 : a₂ * C - d * C₁ = k * (b + b₁) := by
      have hstep : a₂ * C - d * C₁ = k * (a₂ * l + d * s) := by
        rw [hC, hC₁]; ring
      rw [hstep, show a₂ * l = b - b₂ by linarith [hb₂],
        show d * s = b₁ + b₂ by linarith [hB]]
      ring
    have h2 : 2 * k * b₁ + a₁ * k ^ 2 = k * (b + b₁) := by
      rw [show b = b₁ + a₁ * k by linarith [hb₁]]; ring
    linarith
  have hI2 : a₁ * C = d * C₂ + 2 * l * b₂ + a₂ * l ^ 2 := by
    have h1 : a₁ * C - d * C₂ = l * (b + b₂) := by
      have hstep : a₁ * C - d * C₂ = l * (a₁ * k + d * s) := by
        rw [hC, hC₂]; ring
      rw [hstep, show a₁ * k = b - b₁ by linarith [hb₁],
        show d * s = b₁ + b₂ by linarith [hB]]
      ring
    have h2 : 2 * l * b₂ + a₂ * l ^ 2 = l * (b + b₂) := by
      rw [show b = b₂ + a₂ * l by linarith [hb₂]]; ring
    linarith
  have hA₁dvd : p ∣ A₁.natAbs := by
    rw [hA₁, Int.natAbs_mul]
    simpa using (dvd_mul_of_dvd_right hpA (d : ℤ).natAbs)
  by_cases hp2 : p = 2
  · -- The prime is `2`: parity analysis.
    subst p
    have ha₁even : Even a₁ := by
      exact even_iff_two_dvd.mpr (int_dvd_of_nat_dvd hpA)
    have hCeven : Even C := even_iff_two_dvd.mpr (int_dvd_of_nat_dvd hpC)
    have hA₁even : Even A₁ := by
      rw [hA₁]; exact even_mul_left_int ha₁even d
    have hA₁nat : (2 : ℕ) ∣ A₁.natAbs :=
      nat_dvd_of_int_dvd (even_iff_two_dvd.mp hA₁even)
    have h2b₁nat : (2 : ℕ) ∣ (2 * b₁).natAbs := by
      exact nat_dvd_of_int_dvd (even_iff_two_dvd.mp ⟨b₁, by ring⟩)
    by_cases hd : Even d
    · -- `2 ∣ d`
      have hd_int : (2 : ℤ) ∣ d := even_iff_two_dvd.mp hd
      have hEven_kl : Even (k * l) := by
        have hsum : Even (k * l + d * m) := by rw [← hC]; exact hCeven
        have hdm : Even (d * m) := even_mul_right_int hd m
        exact (Int.even_add.mp hsum).mpr hdm
      by_cases hl : Even l
      · -- `2 ∣ l` forces `C₂` even, contradicting the second factor.
        have hC₂even : Even C₂ := by
          rw [hC₂]
          exact even_sub_int (even_mul_right_int ha₁even m) (even_mul_right_int hl s)
        have hA₂even : Even A₂ := by
          rw [hA₂]; exact even_mul_right_int hd a₂
        have hA₂nat : (2 : ℕ) ∣ A₂.natAbs :=
          nat_dvd_of_int_dvd (even_iff_two_dvd.mp hA₂even)
        have h2b₂nat : (2 : ℕ) ∣ (2 * b₂).natAbs := by
          exact nat_dvd_of_int_dvd (even_iff_two_dvd.mp ⟨b₂, by ring⟩)
        have hC₂nat : (2 : ℕ) ∣ C₂.natAbs :=
          nat_dvd_of_int_dvd (even_iff_two_dvd.mp hC₂even)
        exact form_contra Nat.prime_two hprim₂ hA₂nat h2b₂nat hC₂nat
      · -- `2 ∤ l` and `2 ∣ k l` force `2 ∣ k`; then `a₂` and `C₁` are even.
        have hlodd : Odd l := (Int.not_even_iff_odd).mp hl
        have hkeven : Even k := even_of_mul_odd hEven_kl hlodd
        have hbeven₁ : Even (b - b₁) := by
          rw [show b - b₁ = a₁ * k by linarith [hb₁]]
          exact even_mul_right_int ha₁even k
        have hb₁b₂even : Even (b₁ + b₂) := by
          rw [hB]; exact even_mul_right_int hd s
        have hbeven₂ : Even (b - b₂) := by
          have heq : b - b₂ = (b - b₁) - (b₁ + b₂) + 2 * b₁ := by ring
          rw [heq]
          exact even_add_int (even_sub_int hbeven₁ hb₁b₂even) ⟨b₁, by ring⟩
        have ha₂even : Even a₂ := by
          have : Even (a₂ * l) := by
            rw [← show b - b₂ = a₂ * l by linarith [hb₂]]
            exact hbeven₂
          exact even_of_mul_odd this hlodd
        have hC₁even : Even C₁ := by
          rw [hC₁]
          exact even_sub_int (even_mul_right_int ha₂even m) (even_mul_right_int hkeven s)
        have hC₁nat : (2 : ℕ) ∣ C₁.natAbs :=
          nat_dvd_of_int_dvd (even_iff_two_dvd.mp hC₁even)
        exact form_contra Nat.prime_two hprim₁ hA₁nat h2b₁nat hC₁nat
    · -- `2 ∤ d`: the first linear relation makes `d C₁` even, hence `C₁` even.
      have hdodd : Odd d := (Int.not_even_iff_odd).mp hd
      have hEven_dC₁ : Even (d * C₁) := by
        have heq : d * C₁ = a₂ * C - 2 * k * b₁ - a₁ * k ^ 2 := by linarith [hI1]
        rw [heq]
        exact even_sub_int
          (even_sub_int (even_mul_left_int hCeven a₂) ⟨k * b₁, by ring⟩)
          (even_mul_right_int ha₁even (k ^ 2))
      have hC₁even : Even C₁ := even_of_mul_odd (by rwa [mul_comm] at hEven_dC₁) hdodd
      have hC₁nat : (2 : ℕ) ∣ C₁.natAbs :=
        nat_dvd_of_int_dvd (even_iff_two_dvd.mp hC₁even)
      exact form_contra Nat.prime_two hprim₁ hA₁nat h2b₁nat hC₁nat
  · -- The prime is odd.
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hp_b : p ∣ b.natAbs := by
      rcases hp.dvd_mul.mp hp2b with h2 | hb
      · exfalso
        have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
        exact hp2 this
      · exact hb
    have hp_b1_sub : p ∣ (b - b₁).natAbs := by
      rw [show b - b₁ = a₁ * k by linarith [hb₁]]
      rw [Int.natAbs_mul]
      exact dvd_mul_of_dvd_left hpA k.natAbs
    have hp_b1_int : (p : ℤ) ∣ b₁ := by
      have h1 : (p : ℤ) ∣ b := int_dvd_of_nat_dvd hp_b
      have h2 : (p : ℤ) ∣ b - b₁ := int_dvd_of_nat_dvd hp_b1_sub
      have h3 : (p : ℤ) ∣ b - (b - b₁) := dvd_sub h1 h2
      simpa [show b - (b - b₁) = b₁ by ring] using h3
    have hp_b1_nat : p ∣ b₁.natAbs := nat_dvd_of_int_dvd hp_b1_int
    have hp2b1 : p ∣ (2 * b₁).natAbs := by
      rw [Int.natAbs_mul]
      norm_num
      simpa [mul_comm] using (dvd_mul_of_dvd_left hp_b1_nat 2)
    by_cases hpd : p ∣ d.natAbs
    · -- `p ∣ d`: reduce to a case split on `p ∣ a₂`, using `C = k l + d m`.
      have hpd_int : (p : ℤ) ∣ d := int_dvd_of_nat_dvd hpd
      have hA₂dvd : p ∣ A₂.natAbs := by
        rw [hA₂, Int.natAbs_mul]
        simpa using (dvd_mul_of_dvd_left hpd a₂.natAbs)
      have hp_b2_int : (p : ℤ) ∣ b₂ := by
        have hsum : (p : ℤ) ∣ b₁ + b₂ := by
          rw [hB]; exact dvd_mul_of_dvd_left hpd_int s
        have h3 : (p : ℤ) ∣ (b₁ + b₂) - b₁ := dvd_sub hsum hp_b1_int
        simpa [show (b₁ + b₂) - b₁ = b₂ by ring] using h3
      have hp_b2_nat : p ∣ b₂.natAbs := nat_dvd_of_int_dvd hp_b2_int
      have hp2b2 : p ∣ (2 * b₂).natAbs := by
        rw [Int.natAbs_mul]
        norm_num
        simpa [mul_comm] using (dvd_mul_of_dvd_left hp_b2_nat 2)
      have hp_dm_int : (p : ℤ) ∣ d * m := dvd_mul_of_dvd_left hpd_int m
      have hp_kl_int : (p : ℤ) ∣ k * l := by
        have heq : k * l = C - d * m := by linarith [hC]
        rw [heq]; exact dvd_sub hpC_int hp_dm_int
      have hp_kl_nat : p ∣ (k * l).natAbs := nat_dvd_of_int_dvd hp_kl_int
      rw [Int.natAbs_mul] at hp_kl_nat
      rcases hp.dvd_mul.mp hp_kl_nat with hpk | hpl
      · -- `p ∣ k`
        by_cases hpa2 : p ∣ a₂.natAbs
        · -- `p ∣ a₂` and `p ∣ k` make `C₁ = a₂ m - k s` divisible by `p`.
          have hpC1_int : (p : ℤ) ∣ C₁ := by
            rw [hC₁]
            exact dvd_sub (dvd_mul_of_dvd_left (int_dvd_of_nat_dvd hpa2) m)
              (dvd_mul_of_dvd_left (int_dvd_of_nat_dvd hpk) s)
          have hpC1 : p ∣ C₁.natAbs := nat_dvd_of_int_dvd hpC1_int
          exact form_contra hp hprim₁ hA₁dvd hp2b1 hpC1
        · -- `p ∤ a₂`, but `p` divides `b` and `b₂`, so `p ∣ l`; then `C₂` is divisible.
          have hp_bsub : p ∣ (b - b₂).natAbs := by
            have h1 : (p : ℤ) ∣ b := int_dvd_of_nat_dvd hp_b
            have h2 : (p : ℤ) ∣ b₂ := hp_b2_int
            exact nat_dvd_of_int_dvd (dvd_sub h1 h2)
          rw [show b - b₂ = a₂ * l by linarith [hb₂], Int.natAbs_mul] at hp_bsub
          have hpl : p ∣ l.natAbs := by
            rcases hp.dvd_mul.mp hp_bsub with hpa2' | hpl
            · exact absurd hpa2' hpa2
            · exact hpl
          have hpC2_int : (p : ℤ) ∣ C₂ := by
            rw [hC₂]
            exact dvd_sub (dvd_mul_of_dvd_left hpA_int m)
              (dvd_mul_of_dvd_left (int_dvd_of_nat_dvd hpl) s)
          have hpC2 : p ∣ C₂.natAbs := nat_dvd_of_int_dvd hpC2_int
          exact form_contra hp hprim₂ hA₂dvd hp2b2 hpC2
      · -- `p ∣ l`, and `p ∣ a₁`, so `C₂ = a₁ m - l s` is divisible by `p`.
        have hpC2_int : (p : ℤ) ∣ C₂ := by
          rw [hC₂]
          exact dvd_sub (dvd_mul_of_dvd_left hpA_int m)
            (dvd_mul_of_dvd_left (int_dvd_of_nat_dvd hpl) s)
        have hpC2 : p ∣ C₂.natAbs := nat_dvd_of_int_dvd hpC2_int
        exact form_contra hp hprim₂ hA₂dvd hp2b2 hpC2
    · -- `p ∤ d`: the first linear relation gives `p ∣ C₁`.
      have hp_dC1_int : (p : ℤ) ∣ d * C₁ := by
        have heq : d * C₁ = a₂ * C - 2 * k * b₁ - a₁ * k ^ 2 := by linarith [hI1]
        rw [heq]
        have h1 : (p : ℤ) ∣ a₂ * C := dvd_mul_of_dvd_right hpC_int a₂
        have h2 : (p : ℤ) ∣ 2 * k * b₁ := by
          have := dvd_mul_of_dvd_right hp_b1_int (2 * k)
          simpa [mul_assoc, mul_comm, mul_left_comm] using this
        have h3 : (p : ℤ) ∣ a₁ * k ^ 2 := dvd_mul_of_dvd_left hpA_int (k ^ 2)
        exact dvd_sub (dvd_sub h1 h2) h3
      have hp_dC1_nat : p ∣ (d * C₁).natAbs := nat_dvd_of_int_dvd hp_dC1_int
      rw [Int.natAbs_mul] at hp_dC1_nat
      have hpC1 : p ∣ C₁.natAbs := by
        rcases hp.dvd_mul.mp hp_dC1_nat with hpd' | hpC1
        · exact absurd hpd' hpd
        · exact hpC1
      exact form_contra hp hprim₁ hA₁dvd hp2b1 hpC1

/-! ## The main theorem -/

/-- **The `d²`-corrected faithful composition law.**  Two primitive forms of
discriminant `-8N` compose to a primitive form whose leading coefficient is
exactly `A₁ A₂ / d²`, where `d = gcd(A₁, A₂, b₁ + b₂)`. -/
theorem faithfulCompositionCox (N : ℕ) : FaithfulCompositionCox N := by
  intro A₁ b₁ C₁ A₂ b₂ C₂ h₁ h₂
  obtain ⟨hA₁pos, hdisc₁, hgcd₁⟩ := h₁
  obtain ⟨hA₂pos, hdisc₂, hgcd₂⟩ := h₂
  set d : ℕ := Nat.gcd (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs with hd
  have hdpos : 0 < d := by
    dsimp only [d]
    exact Nat.gcd_pos_of_pos_left _
      (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hA₁pos.ne'))
  have hdvd₁ : (d : ℤ) ∣ A₁ := by
    have h : d ∣ A₁.natAbs :=
      (Nat.gcd_dvd_left (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs).trans
        (Nat.gcd_dvd_left A₁.natAbs A₂.natAbs)
    exact Int.natAbs_dvd_natAbs.mp (by simpa using h)
  have hdvd₂ : (d : ℤ) ∣ A₂ := by
    have h : d ∣ A₂.natAbs :=
      (Nat.gcd_dvd_left (Nat.gcd A₁.natAbs A₂.natAbs) (b₁ + b₂).natAbs).trans
        (Nat.gcd_dvd_right A₁.natAbs A₂.natAbs)
    exact Int.natAbs_dvd_natAbs.mp (by simpa using h)
  have hdvdB : (d : ℤ) ∣ b₁ + b₂ := by
    have h : d ∣ (b₁ + b₂).natAbs := Nat.gcd_dvd_right _ _
    exact Int.natAbs_dvd_natAbs.mp (by simpa using h)
  have hdvdH : (d : ℤ) ∣ b₁ * b₂ - 2 * (N : ℤ) := by
    have hEq : b₁ * b₂ - 2 * (N : ℤ) = b₁ * (b₁ + b₂) - A₁ * C₁ := by
      linarith [hdisc₁]
    rw [hEq]
    exact dvd_sub (dvd_mul_of_dvd_right hdvdB b₁) (dvd_mul_of_dvd_left hdvd₁ C₁)
  set a₁ : ℤ := A₁ / (d : ℤ) with ha₁
  set a₂ : ℤ := A₂ / (d : ℤ) with ha₂
  set s : ℤ := (b₁ + b₂) / (d : ℤ) with hs
  set hh : ℤ := (b₁ * b₂ - 2 * (N : ℤ)) / (d : ℤ) with hhh
  have hA₁eq : A₁ = (d : ℤ) * a₁ := by
    rw [ha₁, mul_comm]
    exact (Int.ediv_mul_cancel hdvd₁).symm
  have hA₂eq : A₂ = (d : ℤ) * a₂ := by
    rw [ha₂, mul_comm]
    exact (Int.ediv_mul_cancel hdvd₂).symm
  have hBeq : b₁ + b₂ = (d : ℤ) * s := by
    rw [hs, mul_comm]
    exact (Int.ediv_mul_cancel hdvdB).symm
  have hHeq : b₁ * b₂ - 2 * (N : ℤ) = (d : ℤ) * hh := by
    rw [hhh]
    simpa [mul_comm] using (Int.ediv_mul_cancel hdvdH).symm
  have hdposZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hdpos
  have ha₁pos : 0 < a₁ := by nlinarith [hA₁eq, hA₁pos, hdposZ]
  have ha₂pos : 0 < a₂ := by nlinarith [hA₂eq, hA₂pos, hdposZ]
  have hgcd3 : Nat.gcd (Nat.gcd a₁.natAbs a₂.natAbs) s.natAbs = 1 :=
    gcd_quotients_eq_one hdpos hdvd₁ hdvd₂ hdvdB (by simp [hd])
  obtain ⟨u, v, w, huvw⟩ := bezout_three hgcd3
  set b : ℤ := u * a₁ * b₂ + v * a₂ * b₁ + w * hh with hb
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast hdpos.ne'
  -- The two shifted coefficient identities.
  have hh_sub₁ : hh - s * b₁ = -a₁ * C₁ := by
    apply mul_left_cancel₀ hdne
    calc
      (d : ℤ) * (hh - s * b₁) = (b₁ * b₂ - 2 * (N : ℤ)) - (b₁ + b₂) * b₁ := by
        rw [hHeq, hBeq]; ring
      _ = -(b₁ ^ 2 + 2 * (N : ℤ)) := by ring
      _ = -(A₁ * C₁) := by linarith [hdisc₁]
      _ = (d : ℤ) * (-a₁ * C₁) := by rw [hA₁eq]; ring
  have hh_sub₂ : hh - s * b₂ = -a₂ * C₂ := by
    apply mul_left_cancel₀ hdne
    calc
      (d : ℤ) * (hh - s * b₂) = (b₁ * b₂ - 2 * (N : ℤ)) - (b₁ + b₂) * b₂ := by
        rw [hHeq, hBeq]; ring
      _ = -(b₂ ^ 2 + 2 * (N : ℤ)) := by ring
      _ = -(A₂ * C₂) := by linarith [hdisc₂]
      _ = (d : ℤ) * (-a₂ * C₂) := by rw [hA₂eq]; ring
  -- `b ≡ b₁ (mod a₁)` and `b ≡ b₂ (mod a₂)`.
  have hbdvd₁ : a₁ ∣ b - b₁ := by
    have hdecomp : b - b₁ = a₁ * (u * (b₂ - b₁)) + w * (hh - s * b₁) := by
      calc
        b - b₁ = (u * a₁ * b₂ + v * a₂ * b₁ + w * hh) - b₁ := by rw [hb]
        _ = (u * a₁ * b₂ + v * a₂ * b₁ + w * hh) - (u * a₁ + v * a₂ + w * s) * b₁ := by
          rw [huvw]; ring
        _ = a₁ * (u * (b₂ - b₁)) + w * (hh - s * b₁) := by ring
    rw [hdecomp, hh_sub₁]
    exact ⟨u * (b₂ - b₁) + w * (-C₁), by ring⟩
  have hbdvd₂ : a₂ ∣ b - b₂ := by
    have hdecomp : b - b₂ = a₂ * (v * (b₁ - b₂)) + w * (hh - s * b₂) := by
      calc
        b - b₂ = (u * a₁ * b₂ + v * a₂ * b₁ + w * hh) - b₂ := by rw [hb]
        _ = (u * a₁ * b₂ + v * a₂ * b₁ + w * hh) - (u * a₁ + v * a₂ + w * s) * b₂ := by
          rw [huvw]; ring
        _ = a₂ * (v * (b₁ - b₂)) + w * (hh - s * b₂) := by ring
    rw [hdecomp, hh_sub₂]
    exact ⟨v * (b₁ - b₂) + w * (-C₂), by ring⟩
  set k : ℤ := (b - b₁) / a₁ with hk
  set l : ℤ := (b - b₂) / a₂ with hl
  have hbk : b - b₁ = a₁ * k := by
    rw [hk, mul_comm]
    exact (Int.ediv_mul_cancel hbdvd₁).symm
  have hbl : b - b₂ = a₂ * l := by
    rw [hl, mul_comm]
    exact (Int.ediv_mul_cancel hbdvd₂).symm
  have hb₁' : b = b₁ + a₁ * k := by linarith
  have hb₂' : b = b₂ + a₂ * l := by linarith
  -- The congruence `s b ≡ h (mod a₁a₂)`.
  have hsb₁ : s * b₁ - hh = a₁ * C₁ := by
    apply mul_left_cancel₀ hdne
    calc
      (d : ℤ) * (s * b₁ - hh) = (b₁ + b₂) * b₁ - (b₁ * b₂ - 2 * (N : ℤ)) := by
        rw [hBeq, hHeq]; ring
      _ = b₁ ^ 2 + 2 * (N : ℤ) := by ring
      _ = A₁ * C₁ := by linarith [hdisc₁]
      _ = (d : ℤ) * (a₁ * C₁) := by rw [hA₁eq]; ring
  have hsb₂ : s * b₂ - hh = a₂ * C₂ := by
    apply mul_left_cancel₀ hdne
    calc
      (d : ℤ) * (s * b₂ - hh) = (b₁ + b₂) * b₂ - (b₁ * b₂ - 2 * (N : ℤ)) := by
        rw [hBeq, hHeq]; ring
      _ = b₂ ^ 2 + 2 * (N : ℤ) := by ring
      _ = A₂ * C₂ := by linarith [hdisc₂]
      _ = (d : ℤ) * (a₂ * C₂) := by rw [hA₂eq]; ring
  set m : ℤ := u * C₂ + v * C₁ with hm
  have hcong : s * b - hh = (a₁ * a₂) * m := by
    calc
      s * b - hh = s * (u * a₁ * b₂ + v * a₂ * b₁ + w * hh) - hh := by rw [hb]
      _ = u * a₁ * (s * b₂) + v * a₂ * (s * b₁) + w * s * hh - hh := by ring
      _ = u * a₁ * (a₂ * C₂ + hh) + v * a₂ * (a₁ * C₁ + hh) + w * s * hh - hh := by
        rw [show s * b₂ = a₂ * C₂ + hh by linarith [hsb₂],
          show s * b₁ = a₁ * C₁ + hh by linarith [hsb₁]]
      _ = (a₁ * a₂) * (u * C₂ + v * C₁) + hh * (u * a₁ + v * a₂ + w * s) - hh := by
        ring
      _ = (a₁ * a₂) * m := by rw [huvw, hm]; ring
  set C : ℤ := k * l + d * m with hC
  have hdiscC : (a₁ * a₂) * C - b ^ 2 = 2 * (N : ℤ) := by
    have hmain : b ^ 2 + 2 * (N : ℤ) = (a₁ * a₂) * C := by
      calc
        b ^ 2 + 2 * (N : ℤ) = (b - b₁) * (b - b₂) + (b₁ + b₂) * b -
            (b₁ * b₂ - 2 * (N : ℤ)) := by ring
        _ = (a₁ * a₂) * (k * l) + ((d : ℤ) * s) * b - (d : ℤ) * hh := by
          rw [hbk, hbl, hBeq, hHeq]; ring
        _ = (a₁ * a₂) * (k * l) + (d : ℤ) * (s * b - hh) := by ring
        _ = (a₁ * a₂) * (k * l) + (d : ℤ) * ((a₁ * a₂) * m) := by rw [hcong]
        _ = (a₁ * a₂) * C := by rw [hC]; ring
    linarith
  -- The two factor-coefficient identities.
  have hC₁form : C₁ = a₂ * m - k * s := by
    apply mul_left_cancel₀ (show a₁ * a₂ ≠ 0 from (mul_pos ha₁pos ha₂pos).ne')
    calc
      (a₁ * a₂) * C₁ = a₂ * (a₁ * C₁) := by ring
      _ = a₂ * (s * b₁ - hh) := by rw [← hsb₁]
      _ = a₂ * (s * (b - a₁ * k) - hh) := by
        rw [show b₁ = b - a₁ * k by linarith [hbk]]
      _ = a₂ * ((s * b - hh) - s * a₁ * k) := by ring
      _ = a₂ * ((a₁ * a₂) * m - s * a₁ * k) := by rw [hcong]
      _ = (a₁ * a₂) * (a₂ * m - k * s) := by ring
  have hC₂form : C₂ = a₁ * m - l * s := by
    apply mul_left_cancel₀ (show a₁ * a₂ ≠ 0 from (mul_pos ha₁pos ha₂pos).ne')
    calc
      (a₁ * a₂) * C₂ = a₁ * (a₂ * C₂) := by ring
      _ = a₁ * (s * b₂ - hh) := by rw [← hsb₂]
      _ = a₁ * (s * (b - a₂ * l) - hh) := by
        rw [show b₂ = b - a₂ * l by linarith [hbl]]
      _ = a₁ * ((s * b - hh) - s * a₂ * l) := by ring
      _ = a₁ * ((a₁ * a₂) * m - s * a₂ * l) := by rw [hcong]
      _ = (a₁ * a₂) * (a₁ * m - l * s) := by ring
  -- Primitivity.
  have hprimgcd : Nat.gcd (Nat.gcd (a₁ * a₂).natAbs (2 * b.natAbs)) C.natAbs = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hpd
    have hp_a : p ∣ (a₁ * a₂).natAbs := hpd.trans (Nat.gcd_dvd_left _ _) |>.trans
      (Nat.gcd_dvd_left _ _)
    have hp_2b : p ∣ 2 * b.natAbs :=
      hpd.trans (Nat.gcd_dvd_left _ _) |>.trans (Nat.gcd_dvd_right _ _)
    have hp_C : p ∣ C.natAbs := hpd.trans (Nat.gcd_dvd_right _ _)
    rw [Int.natAbs_mul] at hp_a
    rcases hp.dvd_mul.mp hp_a with hp_a₁ | hp_a₂
    · exact coxNoCommonPrime hdposZ hA₁eq hA₂eq hBeq hb₁' hb₂' hC
        hC₁form hC₂form hgcd₁ hgcd₂ hp hp_a₁ hp_2b hp_C
    · -- Symmetry: apply the same lemma with the two factors interchanged.
      exact coxNoCommonPrime (A₁ := A₂) (A₂ := A₁) (b₁ := b₂) (b₂ := b₁)
        (C₁ := C₂) (C₂ := C₁) (d := d) (a₁ := a₂) (a₂ := a₁) (s := s)
        (b := b) (k := l) (l := k) (m := m) (C := C) hdposZ hA₂eq hA₁eq
        (by linarith [hBeq]) hb₂' hb₁'
        (by rw [hC]; ring) hC₂form hC₁form hgcd₂ hgcd₁ hp hp_a₂ hp_2b hp_C
  -- Assemble the corrected leading coefficient.
  have hlead : (A₁ * A₂) / ((d : ℤ) ^ 2) = a₁ * a₂ := by
    have hmul : A₁ * A₂ = (a₁ * a₂) * (d : ℤ) ^ 2 := by
      rw [hA₁eq, hA₂eq]; ring
    exact Int.ediv_eq_of_eq_mul_left (pow_ne_zero 2 hdne) hmul
  refine ⟨b, C, ?_, ?_, ?_⟩
  · rw [hlead]; exact mul_pos ha₁pos ha₂pos
  · rw [hlead]; exact hdiscC
  · rw [hlead]; exact hprimgcd

/-! ## Axiom audit -/

#print axioms coxNoCommonPrime
#print axioms faithfulCompositionCox

end

end Cogentic.RandomizedL4Cox
