import Cogentic.RandomizedL19Energy

/-!
# L19.4: removing the envelope-growth and marginal-mass inputs

`Cogentic.RandomizedL19Energy.EnergyScaleInputs` isolates two arithmetic
inputs of the marginal-energy certificate:

* `envelope_poly : ∀ n, envelope n ≤ exp (c * scale n)`, the paper's
  `D^{O(1)}` growth of the explicit Plancherel / prefix envelope;
* `mass_lower : ∀ n, exp (η * W n) ≤ mass n`, the paper's marginal-mass count
  `V ^ η ≤ mass`.

This file reduces both inputs to smaller explicit data.

## The envelope

For the Mellin envelope the only analytic content is the critical-line theorem
`primeBinProducts_mellin_energy_from_critical_line`, already packaged as
`mellinEnvelope`.  Its polynomial growth is pure exponent arithmetic in the
actual parameters `q`, the bin endpoints `Bᵢ`, the height `t`, and the fixed
constant `mellinK line`.  The reduction below assumes those parameters grow at
most like `exp (c · scale n)` and derives

`mellinEnvelope q (mellinK line) B t ≤ exp (cMellin · scale n)`

with an explicit exponent `cMellin`.  The same is done for the sharp-prefix
envelope `gridPrefixEnvelope`, whose parameters are the two constants
`prefixC`, `prefixK`, the product `m · B`, the bin endpoints `Uᵢ`, and the
cutoff scale `X`.

The ledger scale `scale` is not nonnegative at every index (in particular
`scale 2 < 0`), while both envelopes are positive.  Therefore no eventual
polynomial-growth estimate can imply the `∀ n` form at the finite initial
segment.  The structures below keep that finite segment as an explicit,
checkable field (`initial`), exactly as `RandomizedL19ZeroMode` keeps the
finite initial segment of the zero-mode residual.  The asymptotic content is
proved, not assumed.

## The marginal mass

For the grid-prefix marginal the mass is `√φ(m) · ν`, matching
`E_i = √C_i L_i / √φ(m_i)`.  The paper's count is

`V ^ (2η) ≤ φ(m)`

together with a positive reference count `ν = massCount`.  Taking square roots
gives `V ^ η ≤ √φ(m) · ν`, which is `mass_lower`; this is
`mass_lower_of_totient_count`.  For the Mellin marginal the Plancherel sum runs
over `(ZMod q)ˣ`, so the corresponding count is `φ(q)` and the mass is `√φ(q)`;
this is `mass_lower_sqrt_totient`.  No mass is set to zero: the count is a lower
bound and `φ(m) > 0` follows from `m ≠ 0`.

Finally `mellinEnergyScaleOfGrowth` and `gridPrefixEnergyScaleOfGrowth` build
the concrete `EnergyScaleInputs` without the two former hypothesis parameters
`henv`, `hmass`; their `...OfTotientCount` variants replace the mass input by
the explicit reduced-residue count.

Nothing here is a `sorry`, an `admit`, an `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL19EnergyMass

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open Filter Real
open scoped BigOperators Classical
open Cogentic.Randomized
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL19Energy

/-! ## 1. Elementary exponent arithmetic -/

/-- A product of `card` factors, each at most `exp (C s)`, is at most
`exp (card · C · s)`. -/
theorem prod_le_exp_card_mul {ι : Type} [Fintype ι] (f : ι → ℝ) {C s : ℝ}
    (hf_nonneg : ∀ i, 0 ≤ f i) (hf : ∀ i, f i ≤ exp (C * s)) :
    ∏ i, f i ≤ exp ((Fintype.card ι : ℝ) * C * s) := by
  calc
    ∏ i, f i ≤ ∏ i, exp (C * s) :=
      Finset.prod_le_prod (fun i _ => hf_nonneg i) (fun i _ => hf i)
    _ = (exp (C * s)) ^ Fintype.card ι := by
      rw [Finset.prod_const, Finset.card_univ]
    _ = exp ((Fintype.card ι : ℝ) * (C * s)) := by
      rw [← Real.exp_nat_mul]
    _ = exp ((Fintype.card ι : ℝ) * C * s) := by
      congr 1
      ring

/-- A square root turns a linear exponential bound into a half-exponential
bound. -/
theorem sqrt_le_exp_half {B c s : ℝ} (_hB : 0 ≤ B) (h : B ≤ exp (c * s)) :
    Real.sqrt B ≤ exp ((c / 2) * s) := by
  calc
    Real.sqrt B ≤ Real.sqrt (exp (c * s)) := Real.sqrt_le_sqrt h
    _ = exp ((c * s) / 2) := (Real.exp_half (c * s)).symm
    _ = exp ((c / 2) * s) := by
      congr 1
      ring

/-- A fixed positive constant is at most `exp (c s)` once `log K ≤ c`, `c ≥ 0`
and `s ≥ 1`. -/
theorem const_le_exp_mul {K c s : ℝ} (hK : 0 < K) (hc : Real.log K ≤ c)
    (hc₀ : 0 ≤ c) (hs : 1 ≤ s) :
    K ≤ exp (c * s) := by
  rw [← Real.exp_log hK]
  apply Real.exp_le_exp.mpr
  have hcs : c ≤ c * s := by
    calc
      c = c * 1 := by ring
      _ ≤ c * s := mul_le_mul_of_nonneg_left hs hc₀
  exact hc.trans hcs

/-- A constant factor `4` is absorbed by `exp (2 s)` for `s ≥ 2`. -/
theorem four_le_exp_two_mul {s : ℝ} (hs : 2 ≤ s) : (4 : ℝ) ≤ exp (2 * s) := by
  have h3 : (3 : ℝ) ≤ 2 * s := by linarith
  calc
    (4 : ℝ) ≤ exp 3 := by
      have h := Real.add_one_le_exp 3
      norm_num at h ⊢
      exact h
    _ ≤ exp (2 * s) := Real.exp_le_exp.mpr h3

/-- `log 4` is absorbed by `2 s` for `s ≥ 2`. -/
theorem log_four_le_two_mul {s : ℝ} (hs : 2 ≤ s) : Real.log 4 ≤ 2 * s := by
  have h4 : (4 : ℝ) ≤ exp (2 * s) := four_le_exp_two_mul hs
  have hpos : (0 : ℝ) < 4 := by norm_num
  calc
    Real.log 4 ≤ Real.log (exp (2 * s)) := Real.log_le_log hpos h4
    _ = 2 * s := Real.log_exp (2 * s)

/-! ## 2. The Mellin envelope exponent -/

/-- The exponent of the fixed constant `mellinK line` on the ledger scale. -/
noncomputable def mellinKExponent (line : DirichletLZerosOnLine) : ℝ :=
  max (Real.log (mellinK line)) 0

theorem mellinKExponent_nonneg (line : DirichletLZerosOnLine) :
    0 ≤ mellinKExponent line := le_max_right _ _

theorem mellinK_le_exp (line : DirichletLZerosOnLine) {s : ℝ} (hs : 1 ≤ s) :
    mellinK line ≤ exp (mellinKExponent line * s) :=
  const_le_exp_mul (mellinK_pos line) (le_max_left _ _)
    (mellinKExponent_nonneg line) hs

/-- The explicit exponent supplied by the arithmetic reduction of the Mellin
envelope.  Each of the `card` bins contributes `K`, `√Bᵢ` and one cube of a
logarithm; the logarithm is bounded by `q (Bᵢ + |t| + 2) ≤ exp (cA · scale)`. -/
noncomputable def mellinEnvelopeExponent {ι : Type} [Fintype ι]
    (line : DirichletLZerosOnLine) (cB cQ cT : ℝ) : ℝ :=
  (Fintype.card ι : ℝ) *
    (mellinKExponent line + cB / 2 + 3 * (cQ + max cB cT + 2))

/-- **One Mellin factor.**  If `K`, `B`, `q`, `|t|` grow like
`exp (cK s)`, `exp (cB s)`, `exp (cQ s)`, `exp (cT s)` and `s ≥ 2`, then the
per-bin factor of `mellinEnvelope` grows like `exp (cF s)` with the displayed
explicit `cF`. -/
theorem mellinFactor_le_exp {K B q t s cK cB cQ cT : ℝ}
    (_hK : 0 < K) (_hB : 2 ≤ B) (hq : 1 ≤ q)
    (_hcK : 0 ≤ cK) (hcB : 0 ≤ cB) (_hcQ : 0 ≤ cQ) (_hcT : 0 ≤ cT)
    (hs : 2 ≤ s)
    (hKle : K ≤ exp (cK * s)) (hBle : B ≤ exp (cB * s))
    (hQle : q ≤ exp (cQ * s)) (hTle : |t| ≤ exp (cT * s)) :
    K * Real.sqrt B * (1 + Real.log (q * (B + |t| + 2))) ^ 3 ≤
      exp ((cK + cB / 2 + 3 * (cQ + max cB cT + 2)) * s) := by
  have hs0 : 0 ≤ s := by linarith
  have hcM : 0 ≤ max cB cT := hcB.trans (le_max_left _ _)
  have hBle' : B ≤ exp (max cB cT * s) :=
    hBle.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hs0))
  have hTle' : |t| ≤ exp (max cB cT * s) :=
    hTle.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hs0))
  have hexpM : (1 : ℝ) ≤ exp (max cB cT * s) :=
    Real.one_le_exp (mul_nonneg hcM hs0)
  have hsum : B + |t| + 2 ≤ 4 * exp (max cB cT * s) := by
    nlinarith [hBle', hTle', hexpM]
  have hApos : 0 < q * (B + |t| + 2) := by positivity
  have hAle : q * (B + |t| + 2) ≤ exp ((cQ + max cB cT + 2) * s) := by
    calc
      q * (B + |t| + 2) ≤ exp (cQ * s) * (4 * exp (max cB cT * s)) :=
        mul_le_mul hQle hsum (by positivity) (exp_pos _).le
      _ = 4 * (exp (cQ * s) * exp (max cB cT * s)) := by ring
      _ = 4 * exp ((cQ + max cB cT) * s) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ exp (2 * s) * exp ((cQ + max cB cT) * s) := by
        exact mul_le_mul_of_nonneg_right (four_le_exp_two_mul hs) (exp_pos _).le
      _ = exp ((cQ + max cB cT + 2) * s) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hlogAle : Real.log (q * (B + |t| + 2)) ≤
      (cQ + max cB cT + 2) * s :=
    (Real.log_le_iff_le_exp hApos).mpr hAle
  have hlogA0 : 0 ≤ Real.log (q * (B + |t| + 2)) :=
    Real.log_nonneg (by nlinarith [hq, abs_nonneg t])
  have h1log : 1 + Real.log (q * (B + |t| + 2)) ≤
      exp ((cQ + max cB cT + 2) * s) := by
    calc
      1 + Real.log (q * (B + |t| + 2)) ≤
          1 + (cQ + max cB cT + 2) * s := by linarith
      _ ≤ exp ((cQ + max cB cT + 2) * s) := by
        simpa [add_comm] using Real.add_one_le_exp ((cQ + max cB cT + 2) * s)
  have hcube : (1 + Real.log (q * (B + |t| + 2))) ^ 3 ≤
      exp (3 * ((cQ + max cB cT + 2) * s)) := by
    calc
      (1 + Real.log (q * (B + |t| + 2))) ^ 3 ≤
          (exp ((cQ + max cB cT + 2) * s)) ^ 3 :=
        pow_le_pow_left₀ (by linarith) h1log 3
      _ = exp (3 * ((cQ + max cB cT + 2) * s)) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hsqrt : Real.sqrt B ≤ exp ((cB / 2) * s) :=
    sqrt_le_exp_half (by linarith) hBle
  have hfirst : K * Real.sqrt B ≤ exp (cK * s) * exp ((cB / 2) * s) :=
    mul_le_mul hKle hsqrt (Real.sqrt_nonneg _) (exp_pos _).le
  calc
    K * Real.sqrt B * (1 + Real.log (q * (B + |t| + 2))) ^ 3 ≤
        (exp (cK * s) * exp ((cB / 2) * s)) *
          exp (3 * ((cQ + max cB cT + 2) * s)) :=
      mul_le_mul hfirst hcube (by positivity)
        (mul_nonneg (exp_pos _).le (exp_pos _).le)
    _ = exp ((cK + cB / 2 + 3 * (cQ + max cB cT + 2)) * s) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- **The Mellin envelope is polynomial on the ledger scale.**  The only
asymptotic inputs are the raw parameter growth bounds for `q`, `B`, `|t|`; the
fixed constant `mellinK line` is absorbed by `mellinKExponent`. -/
theorem mellinEnvelope_le_exp_of_growth {ι : Type} [Fintype ι] [DecidableEq ι]
    (line : DirichletLZerosOnLine) (q : ℕ → ℕ) (B : ℕ → ι → ℕ) (t : ℕ → ℝ)
    {cB cQ cT S : ℝ} (hcB : 0 ≤ cB) (hcQ : 0 ≤ cQ) (hcT : 0 ≤ cT) (hS : 2 ≤ S)
    (hq : ∀ n, q n ≠ 0)
    (hB : ∀ n i, 2 ≤ B n i)
    (hBle : ∀ n, S ≤ scale n → ∀ i, (B n i : ℝ) ≤ exp (cB * scale n))
    (hQle : ∀ n, S ≤ scale n → (q n : ℝ) ≤ exp (cQ * scale n))
    (hTle : ∀ n, S ≤ scale n → |t n| ≤ exp (cT * scale n))
    {n : ℕ} (hn : S ≤ scale n) :
    mellinEnvelope (q n) (mellinK line) (B n) (t n) ≤
      exp (mellinEnvelopeExponent (ι := ι) line cB cQ cT * scale n) := by
  have hs : 2 ≤ scale n := hS.trans hn
  have hs1 : 1 ≤ scale n := by linarith
  have hq1 : (1 : ℝ) ≤ (q n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hq n)
  have hKle : mellinK line ≤ exp (mellinKExponent line * scale n) :=
    mellinK_le_exp line hs1
  have hfac : ∀ i, mellinK line * Real.sqrt (B n i) *
      (1 + Real.log ((q n : ℝ) * ((B n i : ℝ) + |t n| + 2))) ^ 3 ≤
      exp ((mellinKExponent line + cB / 2 +
        3 * (cQ + max cB cT + 2)) * scale n) := by
    intro i
    exact mellinFactor_le_exp (K := mellinK line) (B := (B n i : ℝ))
      (q := (q n : ℝ)) (t := t n) (s := scale n)
      (cK := mellinKExponent line) (cB := cB) (cQ := cQ) (cT := cT)
      (mellinK_pos line) (by exact_mod_cast hB n i) hq1
      (mellinKExponent_nonneg line) hcB hcQ hcT hs hKle (hBle n hn i)
      (hQle n hn) (hTle n hn)
  unfold mellinEnvelope
  calc
    ∏ i, mellinK line * Real.sqrt (B n i) *
        (1 + Real.log ((q n : ℝ) * ((B n i : ℝ) + |t n| + 2))) ^ 3 ≤
        exp ((Fintype.card ι : ℝ) *
          (mellinKExponent line + cB / 2 + 3 * (cQ + max cB cT + 2)) * scale n) :=
      prod_le_exp_card_mul
        (fun i => mellinK line * Real.sqrt (B n i) *
          (1 + Real.log ((q n : ℝ) * ((B n i : ℝ) + |t n| + 2))) ^ 3)
        (fun i => by
          have harg : (1 : ℝ) ≤ (q n : ℝ) * ((B n i : ℝ) + |t n| + 2) := by
            have hq1' : (1 : ℝ) ≤ (q n : ℝ) := by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hq n)
            have hB2 : (2 : ℝ) ≤ (B n i : ℝ) := by exact_mod_cast hB n i
            nlinarith [abs_nonneg (t n)]
          have hlog : 0 ≤ Real.log ((q n : ℝ) * ((B n i : ℝ) + |t n| + 2)) :=
            Real.log_nonneg harg
          exact mul_nonneg
            (mul_nonneg (mellinK_pos line).le (Real.sqrt_nonneg _))
            (by positivity)) hfac
    _ = exp (mellinEnvelopeExponent line cB cQ cT * scale n) := by
      rw [mellinEnvelopeExponent]

/-! ## 3. The sharp-prefix envelope exponent -/

/-- The exponent of the fixed constant `prefixC`. -/
noncomputable def prefixCExponent (C : ℝ) : ℝ := max (Real.log C) 0

theorem prefixCExponent_nonneg (C : ℝ) : 0 ≤ prefixCExponent C :=
  le_max_right _ _

theorem prefixC_le_exp {C : ℝ} (hC : 0 < C) {s : ℝ} (hs : 1 ≤ s) :
    C ≤ exp (prefixCExponent C * s) :=
  const_le_exp_mul hC (le_max_left _ _) (prefixCExponent_nonneg C) hs

/-- The exponent of the fixed constant `prefixK`. -/
noncomputable def prefixKExponent (K : ℝ) : ℝ := max (Real.log K) 0

theorem prefixKExponent_nonneg (K : ℝ) : 0 ≤ prefixKExponent K :=
  le_max_right _ _

theorem prefixK_le_exp {K : ℝ} (hK : 0 < K) {s : ℝ} (hs : 1 ≤ s) :
    K ≤ exp (prefixKExponent K * s) :=
  const_le_exp_mul hK (le_max_left _ _) (prefixKExponent_nonneg K) hs

/-- The exponent of the fixed cardinality `card` of the bin index type. -/
noncomputable def cardExponent (card : ℕ) : ℝ :=
  max (Real.log (2 * (card : ℝ))) 0

theorem cardExponent_nonneg (card : ℕ) : 0 ≤ cardExponent card :=
  le_max_right _ _

theorem two_mul_card_le_exp {card : ℕ} {s : ℝ} (hs : 1 ≤ s) :
    (2 * (card : ℝ)) ≤ exp (cardExponent card * s) := by
  by_cases hcard : card = 0
  · simp [hcard]
    positivity
  · have hpos : (0 : ℝ) < 2 * (card : ℝ) := by
      have : 0 < card := Nat.pos_of_ne_zero hcard
      positivity
    exact const_le_exp_mul hpos (le_max_left _ _) (cardExponent_nonneg card) hs

/-- The exponent of the fixed coefficient `4 e² / π` of the sharp-prefix
envelope. -/
noncomputable def gridCoefficientExponent : ℝ :=
  max (Real.log (4 * Real.exp 2 / Real.pi)) 0

theorem gridCoefficientExponent_nonneg : 0 ≤ gridCoefficientExponent :=
  le_max_right _ _

theorem gridCoefficient_le_exp {s : ℝ} (hs : 1 ≤ s) :
    4 * Real.exp 2 / Real.pi ≤ exp (gridCoefficientExponent * s) :=
  const_le_exp_mul (by positivity) (le_max_left _ _)
    gridCoefficientExponent_nonneg hs

/-- The explicit exponent of the sharp-prefix envelope.  It is the maximum of
the two summands (the prefix product times `log X`, and the `K/X²` remainder),
with the final `+2` absorbing the factor `2` of the sum. -/
noncomputable def gridPrefixEnvelopeExponent {ι : Type} [Fintype ι]
    (cC cU cMB cX cK cN : ℝ) : ℝ :=
  max
    (cMB / 2 + (Fintype.card ι : ℝ) *
        (cC + cU / 2 + 3 * (cMB + max cU (3 * cX) + 2)) + cX +
      gridCoefficientExponent)
    (cMB / 2 + cK + cN + 2) + 2

/-- **One sharp-prefix factor.**  If `C`, `U`, `mB = m·B`, and `X` grow like
the displayed exponentials, then each product factor of `gridPrefixEnvelope`
grows like `exp (cF s)`. -/
theorem gridPrefixFactor_le_exp {C U mB X s cC cU cMB cX : ℝ}
    (_hC : 0 < C) (_hU : 2 ≤ U) (hmB : 1 ≤ mB) (_hX : 2 ≤ X)
    (_hcC : 0 ≤ cC) (hcU : 0 ≤ cU) (_hcMB : 0 ≤ cMB) (_hcX : 0 ≤ cX)
    (hs : 2 ≤ s)
    (hCle : C ≤ exp (cC * s)) (hUle : U ≤ exp (cU * s))
    (hmBle : mB ≤ exp (cMB * s)) (hXle : X ≤ exp (cX * s)) :
    C * Real.sqrt U * (1 + Real.log (mB * (U + X ^ 3 + 2))) ^ 3 ≤
      exp ((cC + cU / 2 + 3 * (cMB + max cU (3 * cX) + 2)) * s) := by
  have hs0 : 0 ≤ s := by linarith
  have hcM : 0 ≤ max cU (3 * cX) := hcU.trans (le_max_left _ _)
  have hUle' : U ≤ exp (max cU (3 * cX) * s) :=
    hUle.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hs0))
  have hX3 : X ^ 3 ≤ exp (3 * cX * s) := by
    calc
      X ^ 3 ≤ (exp (cX * s)) ^ 3 := pow_le_pow_left₀ (by linarith) hXle 3
      _ = exp (3 * (cX * s)) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ = exp (3 * cX * s) := by congr 1; ring
  have hX3' : X ^ 3 ≤ exp (max cU (3 * cX) * s) := by
    refine hX3.trans (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hs0
  have hexpM : (1 : ℝ) ≤ exp (max cU (3 * cX) * s) :=
    Real.one_le_exp (mul_nonneg hcM hs0)
  have hsum : U + X ^ 3 + 2 ≤ 4 * exp (max cU (3 * cX) * s) := by
    nlinarith [hUle', hX3', hexpM]
  have hApos : 0 < mB * (U + X ^ 3 + 2) := by positivity
  have hA1 : 1 ≤ mB * (U + X ^ 3 + 2) := by
    have h1 : (1 : ℝ) ≤ U + X ^ 3 + 2 := by
      have hX0 : 0 ≤ X := by linarith
      have hpow : 0 ≤ X ^ 3 := pow_nonneg hX0 3
      linarith
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ mB * (U + X ^ 3 + 2) :=
        mul_le_mul hmB h1 (by norm_num) (by linarith)
  have hAle : mB * (U + X ^ 3 + 2) ≤
      exp ((cMB + max cU (3 * cX) + 2) * s) := by
    calc
      mB * (U + X ^ 3 + 2) ≤ exp (cMB * s) * (4 * exp (max cU (3 * cX) * s)) :=
        mul_le_mul hmBle hsum (by positivity) (exp_pos _).le
      _ = 4 * (exp (cMB * s) * exp (max cU (3 * cX) * s)) := by ring
      _ = 4 * exp ((cMB + max cU (3 * cX)) * s) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ exp (2 * s) * exp ((cMB + max cU (3 * cX)) * s) := by
        exact mul_le_mul_of_nonneg_right (four_le_exp_two_mul hs) (exp_pos _).le
      _ = exp ((cMB + max cU (3 * cX) + 2) * s) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hlogAle : Real.log (mB * (U + X ^ 3 + 2)) ≤
      (cMB + max cU (3 * cX) + 2) * s :=
    (Real.log_le_iff_le_exp hApos).mpr hAle
  have hlogA0 : 0 ≤ Real.log (mB * (U + X ^ 3 + 2)) :=
    Real.log_nonneg hA1
  have h1log : 1 + Real.log (mB * (U + X ^ 3 + 2)) ≤
      exp ((cMB + max cU (3 * cX) + 2) * s) := by
    calc
      1 + Real.log (mB * (U + X ^ 3 + 2)) ≤
          1 + (cMB + max cU (3 * cX) + 2) * s := by linarith
      _ ≤ exp ((cMB + max cU (3 * cX) + 2) * s) := by
        simpa [add_comm] using Real.add_one_le_exp ((cMB + max cU (3 * cX) + 2) * s)
  have hcube : (1 + Real.log (mB * (U + X ^ 3 + 2))) ^ 3 ≤
      exp (3 * ((cMB + max cU (3 * cX) + 2) * s)) := by
    calc
      (1 + Real.log (mB * (U + X ^ 3 + 2))) ^ 3 ≤
          (exp ((cMB + max cU (3 * cX) + 2) * s)) ^ 3 :=
        pow_le_pow_left₀ (by linarith) h1log 3
      _ = exp (3 * ((cMB + max cU (3 * cX) + 2) * s)) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hsqrt : Real.sqrt U ≤ exp ((cU / 2) * s) :=
    sqrt_le_exp_half (by linarith) hUle
  have hfirst : C * Real.sqrt U ≤ exp (cC * s) * exp ((cU / 2) * s) :=
    mul_le_mul hCle hsqrt (Real.sqrt_nonneg _) (exp_pos _).le
  calc
    C * Real.sqrt U * (1 + Real.log (mB * (U + X ^ 3 + 2))) ^ 3 ≤
        (exp (cC * s) * exp ((cU / 2) * s)) *
          exp (3 * ((cMB + max cU (3 * cX) + 2) * s)) :=
      mul_le_mul hfirst hcube (by positivity)
        (mul_nonneg (exp_pos _).le (exp_pos _).le)
    _ = exp ((cC + cU / 2 + 3 * (cMB + max cU (3 * cX) + 2)) * s) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- **The sharp-prefix envelope is polynomial on the ledger scale.**  The
asymptotic inputs are the raw growth bounds on `prefixC`, `prefixK`, `m·B`,
the bin endpoints `Uᵢ`, the cutoff `X`, and the prime-product count.  Again the
finite initial segment is handled separately by the growth structure. -/
theorem gridPrefixEnvelope_le_exp_of_growth {ι : Type} [Fintype ι] [DecidableEq ι]
    (line : DirichletLZerosOnLine)
    (m B : ℕ → ℕ) (hm : ∀ n, m n ≠ 0) (hB : ∀ n, B n ≠ 0)
    (X : ℕ → ℝ) (A U : ℕ → ι → ℕ)
    {cC cU cMB cX cK cN S : ℝ}
    (_hcC : 0 ≤ cC) (hcU : 0 ≤ cU) (hcMB : 0 ≤ cMB) (_hcX : 0 ≤ cX)
    (_hcK : 0 ≤ cK) (_hcN : 0 ≤ cN) (hS : 2 ≤ S)
    (hU : ∀ n i, 2 ≤ U n i)
    (hX : ∀ n, S ≤ scale n → 2 ≤ X n)
    (hCle : ∀ n, S ≤ scale n →
      prefixC (m n) (B n) (hm n) (hB n) line ≤ exp (cC * scale n))
    (hKle : ∀ n, S ≤ scale n →
      prefixK (m n) (B n) (hm n) (hB n) line ≤ exp (cK * scale n))
    (hMBle : ∀ n, S ≤ scale n →
      ((m n * B n : ℕ) : ℝ) ≤ exp (cMB * scale n))
    (hUle : ∀ n, S ≤ scale n → ∀ i, (U n i : ℝ) ≤ exp (cU * scale n))
    (hXle : ∀ n, S ≤ scale n → X n ≤ exp (cX * scale n))
    (hNle : ∀ n, S ≤ scale n →
      ((primeBinProducts (A n) (U n)).card : ℝ) ≤ exp (cN * scale n))
    {n : ℕ} (hn : S ≤ scale n) :
    gridPrefixEnvelope (m n) (B n)
      (prefixC (m n) (B n) (hm n) (hB n) line)
      (prefixK (m n) (B n) (hm n) (hB n) line) (X n) (A n) (U n) ≤
      exp (gridPrefixEnvelopeExponent (ι := ι) cC cU cMB cX cK cN * scale n) := by
  let s := scale n
  have hs : 2 ≤ s := hS.trans hn
  have hs0 : 0 ≤ s := by linarith
  have hs1 : 1 ≤ s := by linarith
  let card : ℝ := (Fintype.card ι : ℝ)
  let cProd : ℝ := cC + cU / 2 + 3 * (cMB + max cU (3 * cX) + 2)
  let cFirst : ℝ := card * cProd + cX + gridCoefficientExponent
  let cSecond : ℝ := cK + cN + 2
  have hmpos : 0 < m n := Nat.pos_of_ne_zero (hm n)
  have hBpos : 0 < B n := Nat.pos_of_ne_zero (hB n)
  have hmBpos : 0 < m n * B n := Nat.mul_pos hmpos hBpos
  have hmB1 : (1 : ℝ) ≤ ((m n * B n : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hmBpos.ne'
  have hB1 : (1 : ℝ) ≤ (B n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hB n)
  have hBle_mB_nat : B n ≤ m n * B n := Nat.le_mul_of_pos_left (B n) hmpos
  have hBle_mB : (B n : ℝ) ≤ ((m n * B n : ℕ) : ℝ) := by
    exact_mod_cast hBle_mB_nat
  have hBle : (B n : ℝ) ≤ exp (cMB * s) :=
    hBle_mB.trans (hMBle n hn)
  have hprodFactor : ∀ i, prefixC (m n) (B n) (hm n) (hB n) line *
      Real.sqrt (U n i) *
      (1 + Real.log (((m n * B n : ℕ) : ℝ) *
        ((U n i : ℝ) + X n ^ 3 + 2))) ^ 3 ≤ exp (cProd * s) := by
    intro i
    exact gridPrefixFactor_le_exp
      (C := prefixC (m n) (B n) (hm n) (hB n) line)
      (U := (U n i : ℝ)) (mB := ((m n * B n : ℕ) : ℝ)) (X := X n) (s := s)
      (cC := cC) (cU := cU) (cMB := cMB) (cX := cX)
      (prefixC_pos (m n) (B n) (hm n) (hB n) line) (by exact_mod_cast hU n i)
      hmB1 (hX n hn) _hcC hcU hcMB _hcX hs
      (hCle n hn) (hUle n hn i) (hMBle n hn) (hXle n hn)
  have hfactor_nonneg : ∀ i,
      0 ≤ prefixC (m n) (B n) (hm n) (hB n) line *
        Real.sqrt (U n i) *
        (1 + Real.log (((m n * B n : ℕ) : ℝ) *
          ((U n i : ℝ) + X n ^ 3 + 2))) ^ 3 := by
    intro i
    have harg : (1 : ℝ) ≤ ((m n * B n : ℕ) : ℝ) *
        ((U n i : ℝ) + X n ^ 3 + 2) := by
      have hU1 : (2 : ℝ) ≤ (U n i : ℝ) := by exact_mod_cast hU n i
      have hX0 : 0 ≤ X n := by linarith [hX n hn]
      have hpow : 0 ≤ X n ^ 3 := pow_nonneg hX0 3
      calc
        (1 : ℝ) ≤ ((m n * B n : ℕ) : ℝ) := hmB1
        _ ≤ ((m n * B n : ℕ) : ℝ) * ((U n i : ℝ) + X n ^ 3 + 2) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
    have hlog : 0 ≤ Real.log (((m n * B n : ℕ) : ℝ) *
        ((U n i : ℝ) + X n ^ 3 + 2)) := Real.log_nonneg harg
    exact mul_nonneg
      (mul_nonneg (prefixC_pos (m n) (B n) (hm n) (hB n) line).le
        (Real.sqrt_nonneg _))
      (by positivity)
  have hprod : ∏ i, prefixC (m n) (B n) (hm n) (hB n) line *
      Real.sqrt (U n i) *
      (1 + Real.log (((m n * B n : ℕ) : ℝ) *
        ((U n i : ℝ) + X n ^ 3 + 2))) ^ 3 ≤
      exp (card * cProd * s) := by
    simpa only [card] using prod_le_exp_card_mul
      (fun i => prefixC (m n) (B n) (hm n) (hB n) line *
        Real.sqrt (U n i) *
        (1 + Real.log (((m n * B n : ℕ) : ℝ) *
          ((U n i : ℝ) + X n ^ 3 + 2))) ^ 3)
      hfactor_nonneg hprodFactor
  have hprod_nonneg : 0 ≤ ∏ i, prefixC (m n) (B n) (hm n) (hB n) line *
      Real.sqrt (U n i) *
      (1 + Real.log (((m n * B n : ℕ) : ℝ) *
        ((U n i : ℝ) + X n ^ 3 + 2))) ^ 3 :=
    Finset.prod_nonneg (fun i _ => hfactor_nonneg i)
  have hlogX0 : 0 ≤ Real.log (X n) :=
    Real.log_nonneg (by linarith [hX n hn])
  have hlogX : Real.log (X n) ≤ exp (cX * s) := by
    have hXpos : 0 < X n := by linarith [hX n hn]
    have hlog_le : Real.log (X n) ≤ cX * s :=
      (Real.log_le_iff_le_exp hXpos).mpr (hXle n hn)
    calc
      Real.log (X n) ≤ cX * s := hlog_le
      _ ≤ exp (cX * s) := by
        linarith [Real.add_one_le_exp (cX * s)]
  have hcoef : 4 * Real.exp 2 / Real.pi ≤ exp (gridCoefficientExponent * s) :=
    gridCoefficient_le_exp hs1
  have hfirstInner : (4 * Real.exp 2 / Real.pi) *
      ((∏ i, prefixC (m n) (B n) (hm n) (hB n) line *
        Real.sqrt (U n i) *
        (1 + Real.log (((m n * B n : ℕ) : ℝ) *
          ((U n i : ℝ) + X n ^ 3 + 2))) ^ 3) * Real.log (X n)) ≤
      exp (cFirst * s) := by
    calc
      _ ≤ exp (gridCoefficientExponent * s) *
          (exp (card * cProd * s) * exp (cX * s)) := by
        exact mul_le_mul hcoef
          (mul_le_mul hprod hlogX hlogX0 (exp_pos _).le)
          (mul_nonneg hprod_nonneg hlogX0)
          (exp_pos _).le
      _ = exp ((gridCoefficientExponent + card * cProd + cX) * s) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ = exp (cFirst * s) := by
        congr 1
        dsimp only [cFirst]
        ring
  have hsecondInner : (2 * prefixK (m n) (B n) (hm n) (hB n) line / X n ^ 2) *
      ((primeBinProducts (A n) (U n)).card : ℝ) ≤ exp (cSecond * s) := by
    have hXpos : 0 < X n := by linarith [hX n hn]
    have hX2pos : 0 < X n ^ 2 := by positivity
    have hX2ge : (1 : ℝ) ≤ X n ^ 2 := by
      nlinarith [hX n hn, sq_nonneg (X n - 1)]
    have hKpos : 0 < prefixK (m n) (B n) (hm n) (hB n) line :=
      prefixK_pos (m n) (B n) (hm n) (hB n) line
    have hNnonneg : (0 : ℝ) ≤ ((primeBinProducts (A n) (U n)).card : ℝ) :=
      Nat.cast_nonneg _
    have hfrac : 2 * prefixK (m n) (B n) (hm n) (hB n) line / X n ^ 2 ≤
        2 * prefixK (m n) (B n) (hm n) (hB n) line := by
      rw [div_le_iff₀ hX2pos]
      nlinarith [hX2ge, hKpos.le]
    have hstep : (2 * prefixK (m n) (B n) (hm n) (hB n) line / X n ^ 2) *
        ((primeBinProducts (A n) (U n)).card : ℝ) ≤
        2 * prefixK (m n) (B n) (hm n) (hB n) line *
          ((primeBinProducts (A n) (U n)).card : ℝ) :=
      mul_le_mul_of_nonneg_right hfrac hNnonneg
    have hKle' : prefixK (m n) (B n) (hm n) (hB n) line ≤ exp (cK * s) :=
      hKle n hn
    have hNle' : ((primeBinProducts (A n) (U n)).card : ℝ) ≤ exp (cN * s) :=
      hNle n hn
    have htwo : (2 : ℝ) ≤ exp (2 * s) := by
      linarith [four_le_exp_two_mul hs]
    have htwoK : 2 * prefixK (m n) (B n) (hm n) (hB n) line ≤
        exp (2 * s) * exp (cK * s) :=
      mul_le_mul htwo hKle' hKpos.le (exp_pos _).le
    calc
        (2 * prefixK (m n) (B n) (hm n) (hB n) line / X n ^ 2) *
            ((primeBinProducts (A n) (U n)).card : ℝ) ≤
            2 * prefixK (m n) (B n) (hm n) (hB n) line *
              ((primeBinProducts (A n) (U n)).card : ℝ) := hstep
        _ ≤
            (exp (2 * s) * exp (cK * s)) * exp (cN * s) :=
          mul_le_mul htwoK hNle' hNnonneg
            (mul_nonneg (exp_pos _).le (exp_pos _).le)
        _ = exp ((cK + cN + 2) * s) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        _ = exp (cSecond * s) := by
          rfl
  have hsecondInner_nonneg :
      0 ≤ (2 * prefixK (m n) (B n) (hm n) (hB n) line / X n ^ 2) *
        ((primeBinProducts (A n) (U n)).card : ℝ) := by
    have hXpos : 0 < X n := by linarith [hX n hn]
    have hKpos : 0 < prefixK (m n) (B n) (hm n) (hB n) line :=
      prefixK_pos (m n) (B n) (hm n) (hB n) line
    have hNnonneg : (0 : ℝ) ≤ ((primeBinProducts (A n) (U n)).card : ℝ) :=
      Nat.cast_nonneg _
    positivity
  have hsqrtB : Real.sqrt (B n) ≤ exp ((cMB / 2) * s) :=
    sqrt_le_exp_half (by positivity) hBle
  have hfirstInner_nonneg :
      0 ≤ (4 * Real.exp 2 / Real.pi) *
        ((∏ i, prefixC (m n) (B n) (hm n) (hB n) line *
          Real.sqrt (U n i) *
          (1 + Real.log (((m n * B n : ℕ) : ℝ) *
            ((U n i : ℝ) + X n ^ 3 + 2))) ^ 3) * Real.log (X n)) :=
    mul_nonneg (by positivity) (mul_nonneg hprod_nonneg hlogX0)
  have hfirst : Real.sqrt (B n) * ((4 * Real.exp 2 / Real.pi) *
      ((∏ i, prefixC (m n) (B n) (hm n) (hB n) line *
        Real.sqrt (U n i) *
        (1 + Real.log (((m n * B n : ℕ) : ℝ) *
          ((U n i : ℝ) + X n ^ 3 + 2))) ^ 3) * Real.log (X n))) ≤
      exp ((cMB / 2 + cFirst) * s) := by
    calc
      _ ≤ exp ((cMB / 2) * s) * exp (cFirst * s) :=
        mul_le_mul hsqrtB hfirstInner hfirstInner_nonneg (exp_pos _).le
      _ = exp ((cMB / 2 + cFirst) * s) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hsecond : Real.sqrt (B n) *
      ((2 * prefixK (m n) (B n) (hm n) (hB n) line / X n ^ 2) *
        ((primeBinProducts (A n) (U n)).card : ℝ)) ≤
      exp ((cMB / 2 + cSecond) * s) := by
    calc
      _ ≤ exp ((cMB / 2) * s) * exp (cSecond * s) :=
        mul_le_mul hsqrtB hsecondInner hsecondInner_nonneg (exp_pos _).le
      _ = exp ((cMB / 2 + cSecond) * s) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hsum : gridPrefixEnvelope (m n) (B n)
      (prefixC (m n) (B n) (hm n) (hB n) line)
      (prefixK (m n) (B n) (hm n) (hB n) line) (X n) (A n) (U n) ≤
      exp (max (cMB / 2 + cFirst) (cMB / 2 + cSecond) * s) * 2 := by
    unfold gridPrefixEnvelope
    calc
      Real.sqrt (B n) * ((4 * Real.exp 2 / Real.pi) *
          ((∏ i, prefixC (m n) (B n) (hm n) (hB n) line *
            Real.sqrt (U n i) *
            (1 + Real.log (((m n * B n : ℕ) : ℝ) *
              ((U n i : ℝ) + X n ^ 3 + 2))) ^ 3) * Real.log (X n)) +
        (2 * prefixK (m n) (B n) (hm n) (hB n) line / X n ^ 2) *
          ((primeBinProducts (A n) (U n)).card : ℝ)) ≤
          exp ((cMB / 2 + cFirst) * s) + exp ((cMB / 2 + cSecond) * s) := by
        rw [mul_add]
        exact add_le_add hfirst hsecond
      _ ≤ exp (max (cMB / 2 + cFirst) (cMB / 2 + cSecond) * s) * 2 := by
        have hmax1 : exp ((cMB / 2 + cFirst) * s) ≤
            exp (max (cMB / 2 + cFirst) (cMB / 2 + cSecond) * s) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
        have hmax2 : exp ((cMB / 2 + cSecond) * s) ≤
            exp (max (cMB / 2 + cFirst) (cMB / 2 + cSecond) * s) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hs0
        nlinarith
  have htwo : (2 : ℝ) ≤ exp (2 * s) := by linarith [four_le_exp_two_mul hs]
  calc
    gridPrefixEnvelope (m n) (B n)
      (prefixC (m n) (B n) (hm n) (hB n) line)
      (prefixK (m n) (B n) (hm n) (hB n) line) (X n) (A n) (U n)
        ≤ exp (max (cMB / 2 + cFirst) (cMB / 2 + cSecond) * s) * 2 := hsum
    _ ≤ exp (max (cMB / 2 + cFirst) (cMB / 2 + cSecond) * s) * exp (2 * s) :=
      mul_le_mul_of_nonneg_left htwo (exp_pos _).le
    _ = exp ((max (cMB / 2 + cFirst) (cMB / 2 + cSecond) + 2) * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = exp (gridPrefixEnvelopeExponent (ι := ι) cC cU cMB cX cK cN * s) := by
      congr 1
      dsimp only [gridPrefixEnvelopeExponent, cFirst, cSecond, cProd, card]
      ring

/-! ## 4. The smallest explicit marginal-mass count -/

/-- **The marginal-mass count.**  This is the smallest explicit form of the
paper's `V ^ η ≤ mass`: a pointwise lower bound on the actual marginal count.
It is a `Prop`, not a structure, so it can be used for either marginal. -/
def MarginalMassCount (mass : ℕ → ℝ) (W : ℕ → ℝ) (η : ℝ) : Prop :=
  ∀ n, exp (η * W n) ≤ mass n

/-- **The grid-prefix marginal mass from the totient count.**  The actual
normalizer is `√φ(m) · ν`.  The paper's count is `V ^ (2η) ≤ φ(m)` plus a
positive integer reference count `ν = massCount`; taking square roots gives
`V ^ η ≤ √φ(m) · ν`. -/
theorem mass_lower_of_totient_count (m : ℕ → ℕ) (massCount : ℕ → ℕ)
    (W : ℕ → ℝ) (η : ℝ)
    (_hm : ∀ n, m n ≠ 0) (hcount : ∀ n, 0 < massCount n)
    (htotient : ∀ n, exp (2 * η * W n) ≤ ((m n).totient : ℝ)) :
    MarginalMassCount
      (fun n => Real.sqrt (((m n).totient : ℝ)) * (massCount n : ℝ)) W η := by
  intro n
  have hA : 0 < exp (η * W n) := exp_pos _
  have hsq : exp (η * W n) ^ 2 = exp (2 * η * W n) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hsqrt : exp (η * W n) ≤ Real.sqrt (((m n).totient : ℝ)) := by
    rw [← Real.sqrt_sq hA.le, hsq]
    exact Real.sqrt_le_sqrt (htotient n)
  have hcount1 : (1 : ℝ) ≤ (massCount n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (hcount n)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (((m n).totient : ℝ)) := Real.sqrt_nonneg _
  calc
    exp (η * W n) ≤ Real.sqrt (((m n).totient : ℝ)) := hsqrt
    _ = Real.sqrt (((m n).totient : ℝ)) * 1 := by ring
    _ ≤ Real.sqrt (((m n).totient : ℝ)) * (massCount n : ℝ) :=
      mul_le_mul_of_nonneg_left hcount1 hsqrt_nonneg

/-- **The Mellin marginal mass from the reduced-residue count.**  The Plancherel
sum runs over `(ZMod q)ˣ`, so the count is `φ(q)`.  The paper's
`V ^ (2η) ≤ φ(q)` gives `V ^ η ≤ √φ(q)`, the marginal mass used by the Mellin
normalization. -/
theorem mass_lower_sqrt_totient (q : ℕ → ℕ) (W : ℕ → ℝ) (η : ℝ)
    (_hq : ∀ n, q n ≠ 0)
    (htotient : ∀ n, exp (2 * η * W n) ≤ ((q n).totient : ℝ)) :
    MarginalMassCount (fun n => Real.sqrt (((q n).totient : ℝ))) W η := by
  intro n
  have hA : 0 < exp (η * W n) := exp_pos _
  have hsq : exp (η * W n) ^ 2 = exp (2 * η * W n) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hsqrt : exp (η * W n) ≤ Real.sqrt (((q n).totient : ℝ)) := by
    rw [← Real.sqrt_sq hA.le, hsq]
    exact Real.sqrt_le_sqrt (htotient n)
  simpa using hsqrt

/-! ## 5. The Mellin growth certificate -/

/-- The raw growth data behind `mellinEnvelope`.  The asymptotic fields are
bounds on the actual parameters `q`, `Bᵢ`, `|t|`; the finite initial segment is
kept separate because `scale` is negative at `n = 2` while the envelope is
positive. -/
structure MellinEnvelopeGrowth (line : DirichletLZerosOnLine) (q : ℕ → ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (B : ℕ → ι → ℕ) (t : ℕ → ℝ) where
  cB : ℝ
  cQ : ℝ
  cT : ℝ
  S : ℝ
  hcB : 0 ≤ cB
  hcQ : 0 ≤ cQ
  hcT : 0 ≤ cT
  hS : 2 ≤ S
  hq : ∀ n, q n ≠ 0
  hB : ∀ n i, 2 ≤ B n i
  hBle : ∀ n, S ≤ scale n → ∀ i, (B n i : ℝ) ≤ exp (cB * scale n)
  hQle : ∀ n, S ≤ scale n → (q n : ℝ) ≤ exp (cQ * scale n)
  hTle : ∀ n, S ≤ scale n → |t n| ≤ exp (cT * scale n)
  initial : ∀ n, scale n ≤ S →
    mellinEnvelope (q n) (mellinK line) (B n) (t n) ≤
      exp (mellinEnvelopeExponent (ι := ι) line cB cQ cT * scale n)

namespace MellinEnvelopeGrowth

variable {line : DirichletLZerosOnLine} {q : ℕ → ℕ}
  {ι : Type} [Fintype ι] [DecidableEq ι] {B : ℕ → ι → ℕ} {t : ℕ → ℝ}
  (G : MellinEnvelopeGrowth line q B t)

/-- **`envelope_poly` for the Mellin envelope.**  The eventual raw growth
bounds give the exponent `mellinEnvelopeExponent`; the finite initial segment
is the explicit field `initial`. -/
theorem envelope_poly (n : ℕ) :
    mellinEnvelope (q n) (mellinK line) (B n) (t n) ≤
      exp (mellinEnvelopeExponent (ι := ι) line G.cB G.cQ G.cT * scale n) := by
  by_cases hn : scale n ≤ G.S
  · exact G.initial n hn
  · exact mellinEnvelope_le_exp_of_growth line q B t G.hcB G.hcQ G.hcT G.hS
      G.hq G.hB G.hBle G.hQle G.hTle (le_of_lt (lt_of_not_ge hn))

end MellinEnvelopeGrowth

/-! ## 6. The sharp-prefix growth certificate -/

/-- The raw growth data behind `gridPrefixEnvelope`: bounds on `prefixC`,
`prefixK`, `m·B`, the bin endpoints `Uᵢ`, the cutoff `X`, and the product count.
-/
structure GridPrefixEnvelopeGrowth (line : DirichletLZerosOnLine)
    (m B : ℕ → ℕ) (X : ℕ → ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ℕ → ι → ℕ) where
  cC : ℝ
  cU : ℝ
  cMB : ℝ
  cX : ℝ
  cK : ℝ
  cN : ℝ
  S : ℝ
  hcC : 0 ≤ cC
  hcU : 0 ≤ cU
  hcMB : 0 ≤ cMB
  hcX : 0 ≤ cX
  hcK : 0 ≤ cK
  hcN : 0 ≤ cN
  hS : 2 ≤ S
  hm : ∀ n, m n ≠ 0
  hB : ∀ n, B n ≠ 0
  hU : ∀ n i, 2 ≤ U n i
  hX : ∀ n, S ≤ scale n → 2 ≤ X n
  hCle : ∀ n, S ≤ scale n →
    prefixC (m n) (B n) (hm n) (hB n) line ≤ exp (cC * scale n)
  hKle : ∀ n, S ≤ scale n →
    prefixK (m n) (B n) (hm n) (hB n) line ≤ exp (cK * scale n)
  hMBle : ∀ n, S ≤ scale n →
    ((m n * B n : ℕ) : ℝ) ≤ exp (cMB * scale n)
  hUle : ∀ n, S ≤ scale n → ∀ i, (U n i : ℝ) ≤ exp (cU * scale n)
  hXle : ∀ n, S ≤ scale n → X n ≤ exp (cX * scale n)
  hNle : ∀ n, S ≤ scale n →
    ((primeBinProducts (A n) (U n)).card : ℝ) ≤ exp (cN * scale n)
  initial : ∀ n, scale n ≤ S →
    gridPrefixEnvelope (m n) (B n)
      (prefixC (m n) (B n) (hm n) (hB n) line)
      (prefixK (m n) (B n) (hm n) (hB n) line) (X n) (A n) (U n) ≤
      exp (gridPrefixEnvelopeExponent (ι := ι) cC cU cMB cX cK cN * scale n)

namespace GridPrefixEnvelopeGrowth

variable {line : DirichletLZerosOnLine} {m B : ℕ → ℕ} {X : ℕ → ℝ}
  {ι : Type} [Fintype ι] [DecidableEq ι] {A U : ℕ → ι → ℕ}
  (G : GridPrefixEnvelopeGrowth line m B X A U)

/-- **`envelope_poly` for the sharp-prefix envelope.** -/
theorem envelope_poly (n : ℕ) :
    gridPrefixEnvelope (m n) (B n)
      (prefixC (m n) (B n) (G.hm n) (G.hB n) line)
      (prefixK (m n) (B n) (G.hm n) (G.hB n) line) (X n) (A n) (U n) ≤
      exp (gridPrefixEnvelopeExponent (ι := ι) G.cC G.cU G.cMB G.cX G.cK G.cN *
        scale n) := by
  by_cases hn : scale n ≤ G.S
  · exact G.initial n hn
  · exact gridPrefixEnvelope_le_exp_of_growth line m B G.hm G.hB X A U
      G.hcC G.hcU G.hcMB G.hcX G.hcK G.hcN G.hS G.hU G.hX G.hCle G.hKle
      G.hMBle G.hUle G.hXle G.hNle (le_of_lt (lt_of_not_ge hn))

end GridPrefixEnvelopeGrowth

/-! ## 7. Removing the two `EnergyScaleInputs` parameters -/

/-- **Mellin marginal certificate without `henv` / `hmass`.**  The envelope
growth comes from `MellinEnvelopeGrowth.envelope_poly`; the marginal-mass lower
bound is the explicit `MarginalMassCount`. -/
noncomputable def mellinEnergyScaleOfGrowth (line : DirichletLZerosOnLine)
    {W : ℕ → ℝ} (hW0 : ∀ n, 0 ≤ W n) (hW : DominatesScale W)
    {η : ℝ} (hη : 0 < η)
    (q : ℕ → ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ℕ → ι → ℕ) (hAB : ∀ n i, A n i ≤ B n i)
    (hdisj : ∀ n, Pairwise fun i j =>
      Disjoint (primeBin (A n i) (B n i)) (primeBin (A n j) (B n j)))
    (σ t ν : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n) (hν : ∀ n, 0 < ν n)
    (G : MellinEnvelopeGrowth line q B t)
    (M : MarginalMassCount ν W η) :
    EnergyScaleInputs W :=
  mellinEnergyScale line hW0 hW hη q G.hq A B G.hB hAB hdisj σ t ν hσ hν
    G.envelope_poly M

/-- **Mellin certificate from the reduced-residue count.**  The marginal mass is
the actual count `√φ(q)`, and its lower bound is the paper's
`V ^ (2η) ≤ φ(q)`. -/
noncomputable def mellinEnergyScaleOfTotientCount (line : DirichletLZerosOnLine)
    {W : ℕ → ℝ} (hW0 : ∀ n, 0 ≤ W n) (hW : DominatesScale W)
    {η : ℝ} (hη : 0 < η)
    (q : ℕ → ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ℕ → ι → ℕ) (hAB : ∀ n i, A n i ≤ B n i)
    (hdisj : ∀ n, Pairwise fun i j =>
      Disjoint (primeBin (A n i) (B n i)) (primeBin (A n j) (B n j)))
    (σ t : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n)
    (G : MellinEnvelopeGrowth line q B t)
    (htotient : ∀ n, exp (2 * η * W n) ≤ ((q n).totient : ℝ)) :
    EnergyScaleInputs W :=
  mellinEnergyScaleOfGrowth line hW0 hW hη q A B hAB hdisj σ t
    (fun n => Real.sqrt (((q n).totient : ℝ))) hσ
    (fun n => by
      have hqpos : 0 < q n := Nat.pos_of_ne_zero (G.hq n)
      have hφ : (0 : ℝ) < ((q n).totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hqpos
      exact Real.sqrt_pos.mpr hφ)
    G (mass_lower_sqrt_totient q W η G.hq htotient)

/-- **Sharp-prefix marginal certificate without `henv` / `hmass`.** -/
noncomputable def gridPrefixEnergyScaleOfGrowth (line : DirichletLZerosOnLine)
    {W : ℕ → ℝ} (hW0 : ∀ n, 0 ≤ W n) (hW : DominatesScale W)
    {η : ℝ} (hη : 0 < η)
    (m Bm : ℕ → ℕ) (cop : ∀ n, (m n).Coprime (Bm n))
    (X : ℕ → ℝ) (cutoffs : ℕ → Finset ℕ) (hne : ∀ n, (cutoffs n).Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ℕ → ι → ℕ)
    (hX : ∀ n, 2 ≤ X n) (heX : ∀ n, Real.exp 1 ≤ X n)
    (hcut : ∀ n j, j ∈ cutoffs n → X n ≤ (j : ℝ) + 1 / 2 ∧
      (j : ℝ) + 1 / 2 ≤ 2 * X n)
    (hP : ∀ n y, y ∈ primeBinProducts (A n) (U n) → X n ≤ (y : ℝ) ∧
      (y : ℝ) ≤ 2 * X n)
    (hAU : ∀ n i, A n i ≤ U n i)
    (hdisj : ∀ n, Pairwise fun i j =>
      Disjoint (primeBin (A n i) (U n i)) (primeBin (A n j) (U n j)))
    (ν : ℕ → ℝ) (hν : ∀ n, 0 < ν n)
    (G : GridPrefixEnvelopeGrowth line m Bm X A U)
    (M : MarginalMassCount
      (fun n => Real.sqrt (((m n).totient : ℝ)) * ν n) W η) :
    EnergyScaleInputs W :=
  gridPrefixEnergyScale line hW0 hW hη m Bm G.hm G.hB cop X cutoffs hne A U
    hX heX hcut hP G.hU hAU hdisj ν hν G.envelope_poly M

/-- **Grid-prefix certificate from the totient count.**  This is the form in
which the marginal-mass lower bound is the paper's count `V^{2η} ≤ φ(m)` rather
than the final mass inequality. -/
noncomputable def gridPrefixEnergyScaleOfTotientCount
    (line : DirichletLZerosOnLine)
    {W : ℕ → ℝ} (hW0 : ∀ n, 0 ≤ W n) (hW : DominatesScale W)
    {η : ℝ} (hη : 0 < η)
    (m Bm : ℕ → ℕ) (massCount : ℕ → ℕ)
    (cop : ∀ n, (m n).Coprime (Bm n))
    (X : ℕ → ℝ) (cutoffs : ℕ → Finset ℕ) (hne : ∀ n, (cutoffs n).Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ℕ → ι → ℕ)
    (hX : ∀ n, 2 ≤ X n) (heX : ∀ n, Real.exp 1 ≤ X n)
    (hcut : ∀ n j, j ∈ cutoffs n → X n ≤ (j : ℝ) + 1 / 2 ∧
      (j : ℝ) + 1 / 2 ≤ 2 * X n)
    (hP : ∀ n y, y ∈ primeBinProducts (A n) (U n) → X n ≤ (y : ℝ) ∧
      (y : ℝ) ≤ 2 * X n)
    (hAU : ∀ n i, A n i ≤ U n i)
    (hdisj : ∀ n, Pairwise fun i j =>
      Disjoint (primeBin (A n i) (U n i)) (primeBin (A n j) (U n j)))
    (G : GridPrefixEnvelopeGrowth line m Bm X A U)
    (hm : ∀ n, m n ≠ 0) (hcount : ∀ n, 0 < massCount n)
    (htotient : ∀ n, exp (2 * η * W n) ≤ ((m n).totient : ℝ)) :
    EnergyScaleInputs W :=
  gridPrefixEnergyScaleOfGrowth line hW0 hW hη m Bm cop X cutoffs hne A U
    hX heX hcut hP hAU hdisj (fun n => (massCount n : ℝ))
    (fun n => by
      have : 0 < (massCount n : ℝ) := by exact_mod_cast hcount n
      exact this) G
    (mass_lower_of_totient_count m massCount W η hm hcount htotient)

/-! ## 8. Axiom audit -/

#print axioms prod_le_exp_card_mul
#print axioms mellinEnvelope_le_exp_of_growth
#print axioms gridPrefixEnvelope_le_exp_of_growth
#print axioms mass_lower_of_totient_count
#print axioms mass_lower_sqrt_totient
#print axioms MellinEnvelopeGrowth.envelope_poly
#print axioms GridPrefixEnvelopeGrowth.envelope_poly
#print axioms mellinEnergyScaleOfGrowth
#print axioms mellinEnergyScaleOfTotientCount
#print axioms gridPrefixEnergyScaleOfGrowth
#print axioms gridPrefixEnergyScaleOfTotientCount

end Cogentic.RandomizedL19EnergyMass
