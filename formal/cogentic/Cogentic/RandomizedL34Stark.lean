import Cogentic.RandomizedL34ZeroFree

/-!
# L34: Stark's bound with an explicit constant and the smallest zero-free input

`Cogentic.RandomizedL34ZeroFree` isolated the paper's three analytic inputs and
proved the constant-comparison lemmas

* `starkBetaUpper_of_classical` — a classical Stark estimate with constant
  `c ≥ 1/4` gives `StarkBetaUpper`;
* `starkBetaClassical_quarter_iff_betaUpper` — the `c = 1/4` classical form is
  exactly `StarkBetaUpper`;
* `dedekindZeroFreeAboveBeta_iff_distance` — the zero-free region "above `β₀`"
  is exactly the division-free inequality
  `c_z ≤ (1 - Re ρ) log |Δ_E|`.

This file packages those equivalences into the two explicit inputs that the
paper actually quotes.

## Stark

The named constant is `starkConstant = 1/4`.  The structure
`StarkClassicalInput β F D c` is the classical estimate
`β₀ ≤ 1 - c / (F log |Δ_E|)` together with the arithmetic side conditions
`F > 0`, `log |Δ_E| > 0`, and `1/4 ≤ c`.  Its theorem
`StarkClassicalInput.toStarkBetaUpper` proves the paper's
`StarkBetaUpper β F D`, i.e.
`β₀ ≤ 1 - (4 F log |Δ_E|)⁻¹`.  The exact equivalence with the paper's form is
`starkBetaUpper_iff_classicalInput_quarter`, and the division-free product form
`StarkBetaProduct` is exposed as the alternative smallest input
`StarkProductInput` with
`starkClassicalInput_iff_productInput`.

## Zero-free region

The structure `DedekindZeroFreeDistanceInput β R c_z D` carries positivity of
`c_z` and `log |Δ_E|` together with the single division-free inequality
`∀ n, β₀ n < R n → c_z ≤ (1 - R n) * log |Δ_E|`.  The theorem
`DedekindZeroFreeDistanceInput.toDedekindZeroFreeAboveBeta` recovers the paper's
`DedekindZeroFreeAboveBeta`, and
`dedekindZeroFreeAboveBeta_iff_distanceInput` is the exact equivalence for
`c_z > 0` and `log |Δ_E| > 0`.  The no-double-exceedance form is available as
`DedekindZeroFreeDistanceInput.toNoAboveBoth`.

## The combined reduction

`StarkZeroFreeInputs` bundles the two inputs.  Its
`toZeroFreeAnalyticInputs` and `toDedekindAnalyticInputs` compose them with the
range threshold and the two-sided Chebotarev count, giving the existing
`ZeroFreeAnalyticInputs` and `DedekindAnalyticInputs` without any further
analytic hypothesis.  No `sorry`, `admit`, `axiom`, `native_decide`, or
zero-free claim is used; the zero-free region remains an explicit hypothesis.
-/

namespace Cogentic.RandomizedL34Stark

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree

noncomputable section

/-! ## 1. Stark's bound from the classical estimate -/

/-- The explicit Stark constant used by the paper: `1/4`. -/
def starkConstant : ℝ := 1 / 4

/-- `starkConstant` is literally `1/4`. -/
theorem starkConstant_eq : starkConstant = 1 / 4 := rfl

/-- **The explicit classical Stark estimate.**  The literature statement
`β₀ ≤ 1 - c / (F log |Δ_E|)`, with the constant `c` kept explicit and compared
with the paper's `1/4`.  The positivity fields are exactly the denominators
needed by the comparison. -/
structure StarkClassicalInput (beta0 F discLog : ℕ → ℝ) (c : ℝ) : Prop where
  /-- The factorial factor is positive. -/
  F_pos : ∀ n, 0 < F n
  /-- `log |Δ_E|` is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- The literature constant is at least the paper's `1/4`. -/
  c_ge : starkConstant ≤ c
  /-- The classical Stark bound. -/
  classical : StarkBetaClassical beta0 F discLog c

/-- **A classical Stark bound with an explicit constant `c ≥ 1/4` proves the
paper's `StarkBetaUpper`.** -/
theorem starkBetaUpper_of_classical_explicit
    {beta0 F discLog : ℕ → ℝ} {c : ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n)
    (hc : starkConstant ≤ c)
    (h : StarkBetaClassical beta0 F discLog c) :
    StarkBetaUpper beta0 F discLog :=
  starkBetaUpper_of_classical hF hd (by simpa [starkConstant] using hc) h

/-- The packaged classical Stark input proves `StarkBetaUpper`. -/
theorem StarkClassicalInput.toStarkBetaUpper
    {beta0 F discLog : ℕ → ℝ} {c : ℝ}
    (S : StarkClassicalInput beta0 F discLog c) :
    StarkBetaUpper beta0 F discLog :=
  starkBetaUpper_of_classical_explicit S.F_pos S.discLog_pos S.c_ge S.classical

/-- The packaged classical Stark input proves the smallest `StarkInput`. -/
theorem StarkClassicalInput.toStarkInput
    {beta0 F discLog : ℕ → ℝ} {c : ℝ}
    (S : StarkClassicalInput beta0 F discLog c) :
    StarkInput beta0 F discLog where
  gap := starkGap_of_betaUpper S.toStarkBetaUpper

/-- **The `c = 1/4` classical input is exactly the paper's `StarkBetaUpper`.**
This is the lossless form of the Stark reduction; the only hypotheses are the
positivity conditions that the classical statement already needs. -/
theorem starkBetaUpper_iff_classicalInput_quarter
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n) :
    StarkBetaUpper beta0 F discLog ↔
      StarkClassicalInput beta0 F discLog starkConstant := by
  constructor
  · intro h
    exact
      { F_pos := hF
        discLog_pos := hd
        c_ge := le_rfl
        classical :=
          (starkBetaClassical_quarter_iff_betaUpper hF hd).mpr h }
  · intro S
    exact S.toStarkBetaUpper

/-- **The smallest division-free Stark input.**  Stark's bound written as
`1 ≤ 4 F log |Δ_E| (1 - β₀)`, with no division. -/
structure StarkProductInput (beta0 F discLog : ℕ → ℝ) : Prop where
  /-- The factorial factor is positive. -/
  F_pos : ∀ n, 0 < F n
  /-- `log |Δ_E|` is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- The division-free product form of Stark's bound. -/
  product : StarkBetaProduct beta0 F discLog

/-- The product input proves `StarkBetaUpper`. -/
theorem StarkProductInput.toStarkBetaUpper
    {beta0 F discLog : ℕ → ℝ}
    (S : StarkProductInput beta0 F discLog) :
    StarkBetaUpper beta0 F discLog :=
  starkBetaUpper_of_product S.F_pos S.discLog_pos S.product

/-- The product input proves the smallest `StarkInput`. -/
theorem StarkProductInput.toStarkInput
    {beta0 F discLog : ℕ → ℝ}
    (S : StarkProductInput beta0 F discLog) :
    StarkInput beta0 F discLog where
  gap := starkGap_of_betaUpper S.toStarkBetaUpper

/-- **The product input is exactly `StarkBetaUpper`.** -/
theorem starkBetaUpper_iff_productInput
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n) :
    StarkBetaUpper beta0 F discLog ↔ StarkProductInput beta0 F discLog := by
  constructor
  · intro h
    exact
      { F_pos := hF
        discLog_pos := hd
        product := starkBetaProduct_of_betaUpper hF hd h }
  · intro S
    exact S.toStarkBetaUpper

/-- The classical `c = 1/4` input and the division-free product input are
equivalent.  This records that the explicit constant only changes the position
of the factor `4`. -/
theorem starkClassicalInput_iff_productInput
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n) :
    StarkClassicalInput beta0 F discLog starkConstant ↔
      StarkProductInput beta0 F discLog := by
  constructor
  · intro S
    exact
      { F_pos := S.F_pos
        discLog_pos := S.discLog_pos
        product := starkBetaProduct_of_betaUpper S.F_pos S.discLog_pos
          S.toStarkBetaUpper }
  · intro S
    exact
      { F_pos := hF
        discLog_pos := hd
        c_ge := le_rfl
        classical :=
          (starkBetaClassical_quarter_iff_betaUpper hF hd).mpr
            S.toStarkBetaUpper }

/-! ## 2. The smallest explicit zero-free region input -/

/-- **The smallest explicit zero-free region input.**  Above `β₀`, the gap to
`1` satisfies the division-free inequality
`c_z ≤ (1 - Re ρ) log |Δ_E|`.  The fields `cz_pos` and `discLog_pos` are the
positivity conditions already required by the paper-level region. -/
structure DedekindZeroFreeDistanceInput
    (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) : Prop where
  /-- The zero-free-region constant is positive. -/
  cz_pos : 0 < cz
  /-- `log |Δ_E|` is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- The division-free gap inequality. -/
  distance : DedekindZeroFreeDistance beta0 zeroRealPart cz discLog

/-- The division-free input gives the paper's `DedekindZeroFreeAboveBeta`. -/
theorem DedekindZeroFreeDistanceInput.toDedekindZeroFreeAboveBeta
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (Z : DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_distance Z.discLog_pos Z.distance

/-- The division-free input gives the smallest `DedekindZeroFreeInput`. -/
theorem DedekindZeroFreeDistanceInput.toDedekindZeroFreeInput
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (Z : DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeInput beta0 zeroRealPart cz discLog where
  cz_pos := Z.cz_pos
  above_beta := Z.toDedekindZeroFreeAboveBeta

/-- The division-free input gives the core region of `AnalyticSubProps`. -/
theorem DedekindZeroFreeDistanceInput.toDedekindZeroFreeCore
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (Z : DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeCore beta0 zeroRealPart cz discLog :=
  dedekindZeroFreeCore_of_aboveBeta Z.toDedekindZeroFreeAboveBeta

/-- The division-free input gives the no-double-exceedance form. -/
theorem DedekindZeroFreeDistanceInput.toNoAboveBoth
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (Z : DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeNoAboveBoth beta0 zeroRealPart cz discLog :=
  dedekindZeroFreeNoAboveBoth_of_aboveBeta Z.toDedekindZeroFreeAboveBeta

/-- The smallest `DedekindZeroFreeInput` gives the division-free input once
`log |Δ_E|` is positive. -/
theorem DedekindZeroFreeInput.toDedekindZeroFreeDistanceInput
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (Z : DedekindZeroFreeInput beta0 zeroRealPart cz discLog)
    (hd : ∀ n, 0 < discLog n) :
    DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog where
  cz_pos := Z.cz_pos
  discLog_pos := hd
  distance := dedekindZeroFreeDistance_of_aboveBeta hd Z.above_beta

/-- **The zero-free region in its smallest explicit form is exactly the region
above `β₀`.** -/
theorem dedekindZeroFreeInput_iff_distanceInput
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n) :
    DedekindZeroFreeInput beta0 zeroRealPart cz discLog ↔
      DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog :=
  ⟨fun Z =>
      Cogentic.RandomizedL34Stark.DedekindZeroFreeInput.toDedekindZeroFreeDistanceInput
        Z hd,
    fun Z => Z.toDedekindZeroFreeInput⟩

/-- **`DedekindZeroFreeAboveBeta` is exactly the division-free input** when
`c_z > 0` and `log |Δ_E| > 0`. -/
theorem dedekindZeroFreeAboveBeta_iff_distanceInput
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hcz : 0 < cz) (hd : ∀ n, 0 < discLog n) :
    DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog ↔
      DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog := by
  constructor
  · intro h
    exact
      { cz_pos := hcz
        discLog_pos := hd
        distance := dedekindZeroFreeDistance_of_aboveBeta hd h }
  · intro Z
    exact Z.toDedekindZeroFreeAboveBeta

/-! ## 3. The combined zero-free/Stark reduction -/

/-- **The combined smallest input.**  The zero-free part is the division-free
distance input; the Stark part is the classical estimate with its explicit
constant `c ≥ 1/4`. -/
structure StarkZeroFreeInputs (beta0 zeroRealPart F discLog : ℕ → ℝ)
    (cz c : ℝ) : Prop where
  /-- The smallest explicit zero-free region. -/
  zeroFree : DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog
  /-- The classical Stark estimate with an explicit constant. -/
  stark : StarkClassicalInput beta0 F discLog c

namespace StarkZeroFreeInputs

/-- The zero-free component in paper form. -/
theorem zeroFreeAboveBeta
    {beta0 zeroRealPart F discLog : ℕ → ℝ} {cz c : ℝ}
    (A : StarkZeroFreeInputs beta0 zeroRealPart F discLog cz c) :
    DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog :=
  A.zeroFree.toDedekindZeroFreeAboveBeta

/-- The Stark component in paper form. -/
theorem starkBetaUpper
    {beta0 zeroRealPart F discLog : ℕ → ℝ} {cz c : ℝ}
    (A : StarkZeroFreeInputs beta0 zeroRealPart F discLog cz c) :
    StarkBetaUpper beta0 F discLog :=
  A.stark.toStarkBetaUpper

/-- **The combined input gives `ZeroFreeAnalyticInputs`.**  The range and the
two-sided Chebotarev count are passed separately; the zero-free and Stark fields
are exactly the reduced inputs of this file. -/
theorem toZeroFreeAnalyticInputs
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz c K C cZ : ℝ}
    (A : StarkZeroFreeInputs beta0 zeroRealPart F discLog cz c)
    (hK : 0 < K)
    (hr : ChebotarevRangeThreshold K x degree discLog)
    (hx : ∀ n, 0 < x n)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hcheb : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    ZeroFreeAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 where
  cz_pos := A.zeroFree.cz_pos
  zeroFree := A.zeroFreeAboveBeta
  stark := A.starkBetaUpper
  K_pos := hK
  range := hr
  x_pos := hx
  C_pos := hC
  cZ_pos := hcZ
  cheb := hcheb

/-- **The combined input gives `DedekindAnalyticInputs`.**  This is the final
reduction: no analytic statement other than the explicit division-free
zero-free region and the classical Stark estimate remains. -/
theorem toDedekindAnalyticInputs
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz c K C cZ : ℝ}
    (A : StarkZeroFreeInputs beta0 zeroRealPart F discLog cz c)
    (hK : 0 < K)
    (hr : ChebotarevRangeThreshold K x degree discLog)
    (hx : ∀ n, 0 < x n)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hcheb : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 :=
  (A.toZeroFreeAnalyticInputs hK hr hx hC hcZ hcheb).toDedekindAnalyticInputs

end StarkZeroFreeInputs

/-- **Direct reduction from the two explicit inputs.**  The smallest zero-free
input and the classical Stark input, together with the range and the two-sided
count, give `DedekindAnalyticInputs`. -/
theorem dedekindAnalyticInputs_of_starkClassical_and_distance
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz c K C cZ : ℝ}
    (Z : DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog)
    (S : StarkClassicalInput beta0 F discLog c)
    (hK : 0 < K)
    (hr : ChebotarevRangeThreshold K x degree discLog)
    (hx : ∀ n, 0 < x n)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hcheb : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 :=
  (StarkZeroFreeInputs.mk Z S).toDedekindAnalyticInputs hK hr hx hC hcZ hcheb

/-- **Direct reduction with the paper's `c = 1/4` Stark constant.** -/
theorem dedekindAnalyticInputs_of_starkQuarter_and_distance
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (Z : DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog)
    (S : StarkClassicalInput beta0 F discLog starkConstant)
    (hK : 0 < K)
    (hr : ChebotarevRangeThreshold K x degree discLog)
    (hx : ∀ n, 0 < x n)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hcheb : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 :=
  dedekindAnalyticInputs_of_starkClassical_and_distance Z S hK hr hx hC hcZ hcheb

/-! ## Axiom audit -/

#print axioms starkBetaUpper_of_classical_explicit
#print axioms StarkClassicalInput.toStarkBetaUpper
#print axioms StarkClassicalInput.toStarkInput
#print axioms starkBetaUpper_iff_classicalInput_quarter
#print axioms StarkProductInput.toStarkBetaUpper
#print axioms starkBetaUpper_iff_productInput
#print axioms starkClassicalInput_iff_productInput
#print axioms DedekindZeroFreeDistanceInput.toDedekindZeroFreeAboveBeta
#print axioms DedekindZeroFreeDistanceInput.toDedekindZeroFreeInput
#print axioms DedekindZeroFreeDistanceInput.toDedekindZeroFreeCore
#print axioms DedekindZeroFreeDistanceInput.toNoAboveBoth
#print axioms DedekindZeroFreeInput.toDedekindZeroFreeDistanceInput
#print axioms dedekindZeroFreeInput_iff_distanceInput
#print axioms dedekindZeroFreeAboveBeta_iff_distanceInput
#print axioms StarkZeroFreeInputs.zeroFreeAboveBeta
#print axioms StarkZeroFreeInputs.starkBetaUpper
#print axioms StarkZeroFreeInputs.toZeroFreeAnalyticInputs
#print axioms StarkZeroFreeInputs.toDedekindAnalyticInputs
#print axioms dedekindAnalyticInputs_of_starkClassical_and_distance
#print axioms dedekindAnalyticInputs_of_starkQuarter_and_distance

end

end Cogentic.RandomizedL34Stark
