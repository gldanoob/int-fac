import Cogentic.RandomizedL27MaximalOrder
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Real.Pi.Leibniz

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

/-!
# L27: the Gaussian factor `ζ_{ℚ(i)} = ζ · L(·, χ_{-4})`

`Cogentic.RandomizedL27MaximalOrder` computed the residue of the Dedekind zeta
function of `K = CyclotomicField 4 ℚ ≅ ℚ(i)` as `π / 4` and isolated the
factorization `ζ_K = ζ · L(·, χ_{-4})` as the hypothesis
`DedekindZetaFactorizationAtFour`.

This file supplies the arithmetic content of that factorization.

## 1. The character `χ_{-4}`

Mathlib already defines the nontrivial quadratic character
`ZMod.χ₄ : MulChar (ZMod 4) ℤ`.  Composing with the coercion `ℤ → ℂ` gives the
Dirichlet character `χ_{-4} : DirichletCharacter ℂ 4`.  Its values are `1` on
`1 mod 4`, `-1` on `3 mod 4`, and `0` on even integers.

## 2. The local factors

For a rational prime `p` we define

* `zetaLocal p s = (1 - p^{-s})⁻¹`,
* `chiLocal p s = (1 - χ_{-4}(p) p^{-s})⁻¹`,
* `gaussianLocal p s`, the Euler factor of `ζ_{ℚ(i)}`:
  `(1 - p^{-s})⁻¹` for `p = 2` (ramified),
  `(1 - p^{-s})⁻²` for `p ≡ 1 mod 4` (split),
  `(1 - p^{-2s})⁻¹` for `p ≡ 3 mod 4` (inert).

`gaussianLocal_eq_zetaLocal_mul_chiLocal` proves the local identity for every
prime and every `s`, by the three cases `p = 2`, `p ≡ 1 mod 4`, `p ≡ 3 mod 4`.

## 3. The Euler-product gap

Mathlib has the Euler products of `ζ` and of Dirichlet `L`-series, but **not**
the Euler product of the Dedekind zeta function.  The latter is isolated as
`GaussianDedekindZetaEulerProduct`.  From it we prove the factorization on the
half-plane `Re s > 1`, which is the range in which Mathlib's `dedekindZeta`
coincides with its Dirichlet series.  The all-`s` statement
`DedekindZetaFactorizationAtFour` is *not* a consequence of the Euler product
alone; it also needs a meromorphic continuation of `dedekindZeta` beyond
`Re s > 1`, isolated as `DedekindZetaContinuationAtFour`.

## 4. The value `L(1, χ_{-4}) = π / 4`

Mathlib has Leibniz's series `Real.tendsto_sum_pi_div_four` for the ordinary
alternating sum, but not its Abel/Dirichlet-series form nor its identification
with `DirichletCharacter.LFunction χ_{-4} 1`.  The missing value is isolated as
`DirichletBetaAtOne`, and shown equivalent to the Abel limit of the `L`-series
`DirichletBetaAbelLimitAtFour`.

## 5. The class-number formula at `D = 4`

Combining the Euler product with the value `L(1, χ_{-4}) = π / 4` gives the
residue `π / 4` and then, through
`fundamentalClassNumberFormula`, the Dirichlet class-number formula at `D = 4`
with the classical `h = 1`, `w = 4`.

No `sorry`, `admit`, `axiom` or `native_decide` is used.
-/

namespace Cogentic.RandomizedL27GaussianFactor

open Filter
open scoped BigOperators Topology
open Cogentic.RandomizedL27ClassNumberFormula

noncomputable section

/-! ## 1. The Dirichlet character `χ_{-4}` -/

/-- The nontrivial quadratic Dirichlet character modulo `4`, obtained from
Mathlib's integral character `ZMod.χ₄` by coercion to `ℂ`. -/
def chiNegFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- `χ_{-4}` vanishes at `0`. -/
@[simp]
theorem chiNegFour_zero : chiNegFour 0 = 0 := by
  simp [chiNegFour]

/-- `χ_{-4}(1) = 1`. -/
@[simp]
theorem chiNegFour_one : chiNegFour 1 = 1 := by
  simp [chiNegFour]

/-- `χ_{-4}(2) = 0`. -/
@[simp]
theorem chiNegFour_two : chiNegFour 2 = 0 := by
  simp [chiNegFour]

/-- `χ_{-4}(3) = -1`. -/
@[simp]
theorem chiNegFour_three : chiNegFour 3 = -1 := by
  simp [chiNegFour]

/-- `χ_{-4}` vanishes on even integers. -/
theorem chiNegFour_eq_zero_of_even {n : ℕ} (hn : n % 2 = 0) :
    chiNegFour n = 0 := by
  rw [chiNegFour, MulChar.ringHomComp_apply, ZMod.χ₄_nat_eq_if_mod_four]
  simp [hn]

/-- `χ_{-4}(n) = 1` for `n ≡ 1 (mod 4)`. -/
theorem chiNegFour_one_mod_four {n : ℕ} (hn : n % 4 = 1) :
    chiNegFour n = 1 := by
  rw [chiNegFour, MulChar.ringHomComp_apply, ZMod.χ₄_nat_one_mod_four hn]
  norm_num

/-- `χ_{-4}(n) = -1` for `n ≡ 3 (mod 4)`. -/
theorem chiNegFour_three_mod_four {n : ℕ} (hn : n % 4 = 3) :
    chiNegFour n = -1 := by
  rw [chiNegFour, MulChar.ringHomComp_apply, ZMod.χ₄_nat_three_mod_four hn]
  norm_num

/-- `χ_{-4}` is quadratic: it takes only the values `0`, `1`, `-1`. -/
theorem chiNegFour_isQuadratic : chiNegFour.IsQuadratic :=
  ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)

/-- `χ_{-4}` is not the principal character. -/
theorem chiNegFour_ne_one : chiNegFour ≠ 1 := by
  intro h
  have h3 : chiNegFour 3 = (1 : DirichletCharacter ℂ 4) 3 := by rw [h]
  have hone : (1 : DirichletCharacter ℂ 4) 3 = 1 :=
    MulChar.one_apply (by decide : IsUnit (3 : ZMod 4))
  rw [hone] at h3
  norm_num at h3

/-! ## 2. The local factors and their identity -/

/-- The local Euler factor of the Riemann zeta function at `p`. -/
def zetaLocal (p : Nat.Primes) (s : ℂ) : ℂ :=
  (1 - (p : ℂ) ^ (-s))⁻¹

/-- The local Euler factor of `L(s, χ_{-4})` at `p`. -/
def chiLocal (p : Nat.Primes) (s : ℂ) : ℂ :=
  (1 - chiNegFour (p : ℕ) * (p : ℂ) ^ (-s))⁻¹

/-- The local Euler factor of `ζ_{ℚ(i)}` at `p`, written by the splitting
behaviour of `p` in `ℤ[i]`:

* `p = 2` is ramified: `(1 - 2^{-s})⁻¹`;
* `p ≡ 1 (mod 4)` splits: `(1 - p^{-s})⁻²`;
* `p ≡ 3 (mod 4)` is inert: `(1 - p^{-2s})⁻¹`. -/
def gaussianLocal (p : Nat.Primes) (s : ℂ) : ℂ :=
  if (p : ℕ) = 2 then
    (1 - (p : ℂ) ^ (-s))⁻¹
  else if (p : ℕ) % 4 = 1 then
    (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (p : ℂ) ^ (-s))⁻¹
  else
    (1 - ((p : ℂ) ^ (-s)) ^ 2)⁻¹

/-- An odd prime is `1` or `3` modulo `4`. -/
theorem odd_prime_mod_four (p : Nat.Primes) (hp : (p : ℕ) ≠ 2) :
    (p : ℕ) % 4 = 1 ∨ (p : ℕ) % 4 = 3 := by
  have hp2 : (p : ℕ) % 2 = 1 := by
    have hodd : Odd (p : ℕ) := p.prop.odd_of_ne_two hp
    simpa [Nat.odd_iff] using hodd
  omega

/-- **The local Euler factor identity at every prime.**  The Euler factor of
`ζ_{ℚ(i)}` is the product of the Euler factors of `ζ` and of `L(·, χ_{-4})`. -/
theorem gaussianLocal_eq_zetaLocal_mul_chiLocal (p : Nat.Primes) (s : ℂ) :
    gaussianLocal p s = zetaLocal p s * chiLocal p s := by
  unfold gaussianLocal zetaLocal chiLocal
  by_cases hp2 : (p : ℕ) = 2
  · rw [if_pos hp2, chiNegFour_eq_zero_of_even (by omega : (p : ℕ) % 2 = 0)]
    simp
  · rw [if_neg hp2]
    rcases odd_prime_mod_four p hp2 with h1 | h3
    · rw [if_pos h1, chiNegFour_one_mod_four h1]
      ring
    · rw [if_neg (by omega : ¬ (p : ℕ) % 4 = 1), chiNegFour_three_mod_four h3]
      have hx : (1 : ℂ) - ((p : ℂ) ^ (-s)) ^ 2 =
          (1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s)) := by ring
      have hy : (1 : ℂ) - -1 * (p : ℂ) ^ (-s) = 1 + (p : ℂ) ^ (-s) := by ring
      rw [hx, hy, mul_inv_rev, mul_comm]

/-! ## 3. The Euler-product gap and the factorization on `Re s > 1` -/

/-- **The missing Dedekind-zeta Euler product for `ℚ(i)`.**  Mathlib defines
`NumberField.dedekindZeta` as the `L`-series of ideal-count coefficients and
does not provide its Euler product.  This predicate is that Euler product,
with the local factors written explicitly by the splitting behaviour of `p` in
`ℤ[i]`. -/
def GaussianDedekindZetaEulerProduct : Prop :=
  ∀ s : ℂ, 1 < s.re →
    HasProd (fun p : Nat.Primes => gaussianLocal p s)
      (NumberField.dedekindZeta GaussianCyclotomicField s)

/-- **The factorization on the convergence half-plane, from the Euler
product.**  This is the part of `DedekindZetaFactorizationAtFour` that follows
from the local factor identity and Mathlib's Euler products for `ζ` and
`L(·, χ_{-4})`. -/
theorem dedekindZeta_eq_riemannZeta_mul_LSeries_of_eulerProduct
    (h : GaussianDedekindZetaEulerProduct) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta GaussianCyclotomicField s =
      riemannZeta s * LSeries (fun n => chiNegFour n) s := by
  have hzeta := riemannZeta_eulerProduct_hasProd (s := s) hs
  have hchi :=
    DirichletCharacter.LSeries_eulerProduct_hasProd (χ := chiNegFour) (s := s) hs
  have hprod : HasProd (fun p : Nat.Primes => gaussianLocal p s)
      (riemannZeta s * LSeries (fun n => chiNegFour n) s) := by
    convert hzeta.mul hchi using 1
    ext p
    exact gaussianLocal_eq_zetaLocal_mul_chiLocal p s
  exact HasProd.unique (h s hs) hprod

/-- The factorization with the analytic continuation `LFunction` in place of
the naive `LSeries`. -/
theorem dedekindZeta_eq_riemannZeta_mul_LFunction_of_eulerProduct
    (h : GaussianDedekindZetaEulerProduct) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta GaussianCyclotomicField s =
      riemannZeta s * DirichletCharacter.LFunction chiNegFour s := by
  rw [DirichletCharacter.LFunction_eq_LSeries chiNegFour hs]
  exact dedekindZeta_eq_riemannZeta_mul_LSeries_of_eulerProduct h hs

/-- The factorization on the half-plane `Re s > 1`. -/
def DedekindZetaFactorizationAtFourRightHalfPlane (L : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 1 < s.re →
    NumberField.dedekindZeta GaussianCyclotomicField s = riemannZeta s * L s

/-- The full factorization implies the half-plane factorization. -/
theorem dedekindZetaFactorizationAtFourRightHalfPlane_of_factorization
    (L : ℂ → ℂ) (h : DedekindZetaFactorizationAtFour L) :
    DedekindZetaFactorizationAtFourRightHalfPlane L :=
  fun s _ => h s

/-- The half-plane factorization with `L = LFunction χ_{-4}`. -/
theorem dedekindZetaFactorizationAtFourRightHalfPlane_LFunction_of_eulerProduct
    (h : GaussianDedekindZetaEulerProduct) :
    DedekindZetaFactorizationAtFourRightHalfPlane
      (fun s => DirichletCharacter.LFunction chiNegFour s) :=
  fun s hs => dedekindZeta_eq_riemannZeta_mul_LFunction_of_eulerProduct (s := s) h hs

/-- **The analytic-continuation gap.**  The Euler product only gives the
factorization on `Re s > 1`.  Extending it to all `s` requires a meromorphic
continuation of `NumberField.dedekindZeta` beyond its defining `L`-series,
which Mathlib does not have. -/
def DedekindZetaContinuationAtFour (L : ℂ → ℂ) : Prop :=
  DedekindZetaFactorizationAtFourRightHalfPlane L → DedekindZetaFactorizationAtFour L

/-- **The full factorization from the Euler product and the continuation
gap.**  This identifies exactly what is still missing for the all-`s`
statement used by `residue_gaussian_eq_L_one_of_factorization`. -/
theorem dedekindZetaFactorizationAtFour_LFunction_of_eulerProduct_of_continuation
    (h : GaussianDedekindZetaEulerProduct)
    (hcont : DedekindZetaContinuationAtFour
      (fun s => DirichletCharacter.LFunction chiNegFour s)) :
    DedekindZetaFactorizationAtFour (fun s => DirichletCharacter.LFunction chiNegFour s) :=
  hcont (dedekindZetaFactorizationAtFourRightHalfPlane_LFunction_of_eulerProduct h)

/-! ## 4. The value `L(1, χ_{-4}) = π / 4` -/

/-- **The missing Dirichlet-beta value.**  This is `L(1, χ_{-4}) = π / 4`,
equivalently the value at `1` of the Dirichlet beta function. -/
def DirichletBetaAtOne : Prop :=
  (DirichletCharacter.LFunction chiNegFour 1).re = Real.pi / 4

/-- The Abel/Dirichlet-series form of `L(1, χ_{-4}) = π / 4`: the limit of the
convergent `L`-series as `s → 1⁺`. -/
def DirichletBetaAbelLimitAtFour : Prop :=
  Tendsto
    (fun s : ℝ =>
      (LSeries (fun n => chiNegFour n) (s : ℂ)).re)
    (𝓝[>] 1) (𝓝 (Real.pi / 4))

/-- **The exact reduction of the value to its Abel limit.**  Since `χ_{-4}` is
nontrivial, `LFunction χ_{-4}` is continuous at `1`, and it agrees with the
naive `L`-series on `Re s > 1`.  Hence the value at `1` is exactly the
`s → 1⁺` limit of that series. -/
theorem dirichletBetaAtOne_iff_abelLimit :
    DirichletBetaAtOne ↔ DirichletBetaAbelLimitAtFour := by
  have hcont : ContinuousAt
      (fun z : ℂ => (DirichletCharacter.LFunction chiNegFour z).re) 1 :=
    Complex.continuous_re.continuousAt.comp
      (DirichletCharacter.differentiable_LFunction chiNegFour_ne_one).continuous.continuousAt
  have hreal : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun s : ℝ => (DirichletCharacter.LFunction chiNegFour (s : ℂ)).re)
      (𝓝[>] 1) (𝓝 ((DirichletCharacter.LFunction chiNegFour 1).re)) := by
    have h := hcont.tendsto.comp hreal
    simpa [Function.comp_def] using h
  have heq : (fun s : ℝ => (DirichletCharacter.LFunction chiNegFour (s : ℂ)).re)
      =ᶠ[𝓝[>] 1]
      (fun s : ℝ =>
        (LSeries (fun n => chiNegFour n) (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [DirichletCharacter.LFunction_eq_LSeries chiNegFour (by simpa using hs)]
  constructor
  · intro h
    rw [h] at hlim
    exact Tendsto.congr' heq hlim
  · intro h
    have h' : Tendsto
        (fun s : ℝ => (DirichletCharacter.LFunction chiNegFour (s : ℂ)).re)
        (𝓝[>] 1) (𝓝 (Real.pi / 4)) :=
      Tendsto.congr' heq.symm h
    exact tendsto_nhds_unique hlim h'

/-! ## 5. The residue and the class-number formula at `D = 4` -/

/-- **The residue from the half-plane factorization.**  This is
`residue_gaussian_eq_L_one_of_factorization` with the all-`s` factorization
weakened to the half-plane `Re s > 1`, which is all the limit `s → 1⁺` uses. -/
theorem residue_gaussian_eq_L_one_of_rightHalfPlaneFactorization
    (L : ℂ → ℂ)
    (hfac : DedekindZetaFactorizationAtFourRightHalfPlane L)
    (hL : ContinuousAt L 1) :
    NumberField.dedekindZeta_residue GaussianCyclotomicField = (L 1).re := by
  have hK := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT
    GaussianCyclotomicField
  have hcoe : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact fun h => (ne_of_gt (show (1 : ℝ) < s from hs)) (Complex.ofReal_injective h)
  have hζ : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
      (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp hcoe
  have hLt : Tendsto (fun s : ℝ => L (s : ℂ)) (𝓝[>] 1) (𝓝 (L 1)) := by
    have hc : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds
    exact hL.tendsto.comp hc
  have hprod : Tendsto
      (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ) * L (s : ℂ))
      (𝓝[>] 1) (𝓝 (1 * L 1)) :=
    hζ.mul hLt
  have heq : (fun s : ℝ =>
        ((s : ℂ) - 1) * NumberField.dedekindZeta GaussianCyclotomicField (s : ℂ))
      =ᶠ[𝓝[>] 1]
      (fun s : ℝ => ((s : ℂ) - 1) * (riemannZeta (s : ℂ) * L (s : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hfac (s : ℂ) (by exact_mod_cast hs)]
  have hK' : Tendsto
      (fun s : ℝ => ((s : ℂ) - 1) *
        (riemannZeta (s : ℂ) * L (s : ℂ)))
      (𝓝[>] 1) (𝓝 ((NumberField.dedekindZeta_residue GaussianCyclotomicField : ℂ))) :=
    Tendsto.congr' heq hK
  have huniq : (NumberField.dedekindZeta_residue GaussianCyclotomicField : ℂ) = L 1 :=
    tendsto_nhds_unique hK' (by simpa [mul_assoc] using hprod)
  have hre := congr_arg Complex.re huniq
  simpa using hre

/-- The half-plane residue theorem specialises to the full-factorization
version of `RandomizedL27MaximalOrder`. -/
theorem residue_gaussian_eq_L_one_of_factorization'
    (L : ℂ → ℂ) (hfac : DedekindZetaFactorizationAtFour L)
    (hL : ContinuousAt L 1) :
    NumberField.dedekindZeta_residue GaussianCyclotomicField = (L 1).re :=
  residue_gaussian_eq_L_one_of_rightHalfPlaneFactorization L
    (dedekindZetaFactorizationAtFourRightHalfPlane_of_factorization L hfac) hL

/-- **The residue of `ζ_{ℚ(i)}` from the Euler product and the `L`-value.** -/
theorem residue_gaussian_eq_pi_div_four_of_eulerProduct_of_LValue
    (heuler : GaussianDedekindZetaEulerProduct)
    (hval : DirichletBetaAtOne) :
    NumberField.dedekindZeta_residue GaussianCyclotomicField = Real.pi / 4 := by
  have hfac := dedekindZetaFactorizationAtFourRightHalfPlane_LFunction_of_eulerProduct
    heuler
  have hcont : ContinuousAt
      (fun s => DirichletCharacter.LFunction chiNegFour s) 1 :=
    (DirichletCharacter.differentiable_LFunction chiNegFour_ne_one).continuous.continuousAt
  have h := residue_gaussian_eq_L_one_of_rightHalfPlaneFactorization
    (fun s => DirichletCharacter.LFunction chiNegFour s) hfac hcont
  rw [h, hval]

/-- **The Dirichlet class-number formula at `D = 4`, from the `L`-value
alone.**  The Euler product supplies the factorization, the value
`L(1, χ_{-4}) = π / 4` supplies the residue, and
`fundamentalClassNumberFormula` converts the residue into the class-number
formula.

The statement uses the model class-number and weight functions
`smallClassNumber` and `smallWeight` of `RandomizedL27MaximalOrder`, whose
values at `4` are `1` and `4`. -/
theorem classNumberFormula_gaussian_of_eulerProduct_of_L1
    (L1 : ℤ → ℝ) (hL1 : L1 4 = Real.pi / 4)
    (heuler : GaussianDedekindZetaEulerProduct)
    (hval : DirichletBetaAtOne) :
    smallClassNumber 4 =
      (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * L1 4 := by
  have hres : NumberField.dedekindZeta_residue GaussianCyclotomicField = L1 4 := by
    rw [hL1]
    exact residue_gaussian_eq_pi_div_four_of_eulerProduct_of_LValue heuler hval
  have hclass : (NumberField.classNumber GaussianCyclotomicField : ℝ) = smallClassNumber 4 := by
    rw [classNumber_gaussian]
    norm_num [smallClassNumber]
  have hweight : (NumberField.Units.torsionOrder GaussianCyclotomicField : ℝ) =
      smallWeight 4 := by
    rw [torsionOrder_gaussian]
    norm_num [smallWeight]
  exact fundamentalClassNumberFormula GaussianCyclotomicField discr_gaussian hclass hweight
    nrRealPlaces_gaussian nrComplexPlaces_gaussian regulator_gaussian hres
    (by norm_num : (0 : ℤ) < 4)

/-- The classical specialization: `h(-4) = 1` and `w(-4) = 4`. -/
theorem classNumberFormula_gaussian_of_eulerProduct_of_LValue
    (heuler : GaussianDedekindZetaEulerProduct)
    (hval : DirichletBetaAtOne) :
    smallClassNumber 4 =
      (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * (Real.pi / 4) :=
  classNumberFormula_gaussian_of_eulerProduct_of_L1 (fun _ => Real.pi / 4) rfl heuler hval

/-- The right-hand side at `D = 4` evaluates to `1`, so the formula recovers
`h(-4) = 1`. -/
theorem classNumberFormula_at_four_evaluates :
    (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * (Real.pi / 4) = 1 := by
  norm_num [smallWeight]
  field_simp

end

/-! ## Axiom audit -/

#print axioms chiNegFour
#print axioms chiNegFour_ne_one
#print axioms chiNegFour_isQuadratic
#print axioms gaussianLocal_eq_zetaLocal_mul_chiLocal
#print axioms dedekindZeta_eq_riemannZeta_mul_LSeries_of_eulerProduct
#print axioms dedekindZeta_eq_riemannZeta_mul_LFunction_of_eulerProduct
#print axioms dedekindZetaFactorizationAtFourRightHalfPlane_LFunction_of_eulerProduct
#print axioms dedekindZetaFactorizationAtFour_LFunction_of_eulerProduct_of_continuation
#print axioms dirichletBetaAtOne_iff_abelLimit
#print axioms residue_gaussian_eq_L_one_of_rightHalfPlaneFactorization
#print axioms residue_gaussian_eq_L_one_of_factorization'
#print axioms residue_gaussian_eq_pi_div_four_of_eulerProduct_of_LValue
#print axioms classNumberFormula_gaussian_of_eulerProduct_of_L1
#print axioms classNumberFormula_gaussian_of_eulerProduct_of_LValue
#print axioms classNumberFormula_at_four_evaluates

end Cogentic.RandomizedL27GaussianFactor
