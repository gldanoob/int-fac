import Cogentic.RandomizedL34Stark

/-!
# L34: the classical Stark exceptional-zero lemma and `StarkClassicalInput`

`Cogentic.RandomizedL34Stark` packaged the paper's Stark input as

* `StarkClassicalInput β F D c` — the literature estimate
  `β₀ ≤ 1 - c / (F log |Δ_E|)` with `c ≥ 1/4`;
* `StarkBetaUpper β F D` — the paper's `β₀ ≤ 1 - (4 F log |Δ_E|)⁻¹`;
* `StarkProductInput β F D` — the division-free product form.

The present file closes the remaining interface gap.  It states the **classical
Stark exceptional-zero lemma** — the real-zero exclusion supplied by Stark's
lemma — in the form in which it is actually quoted, and proves that it gives
`StarkClassicalInput` at the paper's constant `1/4`.

## The smallest exceptional-zero input

The classical lemma is not a zero-free region.  It says only that the
exceptional real zero `β₀` cannot lie strictly above the Stark line
`1 - (4 F log |Δ_E|)⁻¹`.  Written without division this is the single
predicate

`StarkExceptionalZeroInput β F D`:
`F n > 0`, `log |Δ_E| n > 0`, and `¬ (starkLine F D n < β₀ n)`.

No auxiliary constant and no separate region statement is stored:
`StarkExceptionalZeroInput.toStarkClassicalInput` supplies the `c = 1/4`
packaging, and `starkExceptionalZeroInput_iff_classicalInput` shows the
reduction is lossless.

## The factorial scale

Stark's lemma is usually quoted with the degree factorial.  The structure
`StarkFactorialExceptionalZeroInput β d D` states the same exclusion at the
literal line `1 - (4 d! log |Δ_E|)⁻¹`.  The paper's field `E = K(√γ)` has
absolute degree `2d`, hence the factor `F = (2d)!`; the theorem
`StarkFactorialExceptionalZeroInput.toStarkBetaUpper_absolute` derives the
paper's bound from `d! ≤ (2d)!`.  This is the only place where the factorial
enlargement is used, and it is monotonicity of the Stark line in `F`.

## What is and is not proved

The classical exceptional-zero lemma is an explicit hypothesis.  Nothing here
claims a zero-free region, a Dedekind zeta zero theory, or Stark's theorem
itself.  The zero-free side remains the separate input
`DedekindZeroFreeDistanceInput` of `Cogentic.RandomizedL34Stark`.  No `sorry`,
`admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedL34ClassicalStark

open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34Stark

noncomputable section

/-! ## 1. The smallest explicit exceptional-zero input -/

/-- The explicit Stark line `1 - (4 F log |Δ_E|)⁻¹`. -/
noncomputable def starkLine (F discLog : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - 1 / (4 * F n * discLog n)

/-- **The classical Stark exceptional-zero lemma, in its smallest explicit
form.**  The exceptional zero does not lie strictly above the Stark line.  This
is the real-zero exclusion of Stark's lemma, kept as a single inequality with
only the two positivity side conditions needed to read the line as a genuine
upper bound. -/
structure StarkExceptionalZeroInput (beta0 F discLog : ℕ → ℝ) : Prop where
  /-- The factorial factor is positive. -/
  F_pos : ∀ n, 0 < F n
  /-- `log |Δ_E|` is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- No exceptional zero lies strictly above the Stark line. -/
  no_exceptional_above : ∀ n, ¬ (starkLine F discLog n < beta0 n)

/-- The smallest input is exactly Stark's upper-bound form. -/
theorem StarkExceptionalZeroInput.toStarkBetaUpper
    {beta0 F discLog : ℕ → ℝ}
    (S : StarkExceptionalZeroInput beta0 F discLog) :
    StarkBetaUpper beta0 F discLog := by
  intro n
  simpa [starkLine] using not_lt.mp (S.no_exceptional_above n)

/-- The smallest input gives the division-free product form. -/
theorem StarkExceptionalZeroInput.toStarkProductInput
    {beta0 F discLog : ℕ → ℝ}
    (S : StarkExceptionalZeroInput beta0 F discLog) :
    StarkProductInput beta0 F discLog where
  F_pos := S.F_pos
  discLog_pos := S.discLog_pos
  product :=
    starkBetaProduct_of_betaUpper S.F_pos S.discLog_pos S.toStarkBetaUpper

/-- **The classical exceptional-zero lemma proves `StarkClassicalInput` at the
paper's constant `1/4`.**  This is the reduction requested by the L34 ledger:
the only analytic content is the real-zero exclusion, and the classical
constant `c = 1/4` is definitional. -/
theorem StarkExceptionalZeroInput.toStarkClassicalInput
    {beta0 F discLog : ℕ → ℝ}
    (S : StarkExceptionalZeroInput beta0 F discLog) :
    StarkClassicalInput beta0 F discLog starkConstant :=
  { F_pos := S.F_pos
    discLog_pos := S.discLog_pos
    c_ge := le_rfl
    classical :=
      (starkBetaClassical_quarter_iff_betaUpper S.F_pos S.discLog_pos).mpr
        S.toStarkBetaUpper }

/-- The smallest input also gives the minimal `StarkInput`. -/
theorem StarkExceptionalZeroInput.toStarkInput
    {beta0 F discLog : ℕ → ℝ}
    (S : StarkExceptionalZeroInput beta0 F discLog) :
    StarkInput beta0 F discLog :=
  S.toStarkClassicalInput.toStarkInput

/-- Stark's upper-bound form repackages as the smallest exceptional-zero
input. -/
theorem StarkExceptionalZeroInput.ofStarkBetaUpper
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n)
    (h : StarkBetaUpper beta0 F discLog) :
    StarkExceptionalZeroInput beta0 F discLog where
  F_pos := hF
  discLog_pos := hd
  no_exceptional_above := by
    intro n
    simpa [starkLine] using not_lt.mpr (h n)

/-- The packaged classical input gives the smallest exceptional-zero input. -/
theorem StarkExceptionalZeroInput.ofStarkClassicalInput
    {beta0 F discLog : ℕ → ℝ}
    (S : StarkClassicalInput beta0 F discLog starkConstant) :
    StarkExceptionalZeroInput beta0 F discLog :=
  StarkExceptionalZeroInput.ofStarkBetaUpper S.F_pos S.discLog_pos
    S.toStarkBetaUpper

/-- **The smallest exceptional-zero input is exactly Stark's upper bound.** -/
theorem starkExceptionalZeroInput_iff_betaUpper
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n) :
    StarkExceptionalZeroInput beta0 F discLog ↔
      StarkBetaUpper beta0 F discLog :=
  ⟨StarkExceptionalZeroInput.toStarkBetaUpper,
    StarkExceptionalZeroInput.ofStarkBetaUpper hF hd⟩

/-- **The smallest exceptional-zero input is exactly the classical input at
`c = 1/4`.**  The reduction above is lossless: no positivity is lost, and the
constant is forced to be the paper's. -/
theorem starkExceptionalZeroInput_iff_classicalInput
    {beta0 F discLog : ℕ → ℝ} :
    StarkExceptionalZeroInput beta0 F discLog ↔
      StarkClassicalInput beta0 F discLog starkConstant :=
  ⟨StarkExceptionalZeroInput.toStarkClassicalInput,
    StarkExceptionalZeroInput.ofStarkClassicalInput⟩

/-- **The smallest exceptional-zero input is exactly the division-free product
input.** -/
theorem starkExceptionalZeroInput_iff_productInput
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n) :
    StarkExceptionalZeroInput beta0 F discLog ↔
      StarkProductInput beta0 F discLog :=
  ⟨StarkExceptionalZeroInput.toStarkProductInput,
    fun S => StarkExceptionalZeroInput.ofStarkBetaUpper hF hd S.toStarkBetaUpper⟩

/-! ## 2. The literature form with an explicit constant -/

/-- **The classical exceptional-zero lemma with a literature constant `c`.**
The same real-zero exclusion at the line `1 - c / (F log |Δ_E|)`, with
`c ≥ 1/4`.  This is the shape in which an estimate carrying its own constant is
quoted; the theorem `toStarkClassicalInput` unwraps it. -/
structure StarkClassicalExceptionalZero (beta0 F discLog : ℕ → ℝ) (c : ℝ) : Prop where
  /-- The factorial factor is positive. -/
  F_pos : ∀ n, 0 < F n
  /-- `log |Δ_E|` is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- The literature constant is at least the paper's `1/4`. -/
  c_ge : starkConstant ≤ c
  /-- No exceptional zero lies strictly above the classical Stark line. -/
  no_exceptional_above : ∀ n, ¬ (1 - c / (F n * discLog n) < beta0 n)

/-- The classical real-zero form is exactly `StarkClassicalInput`. -/
theorem starkClassicalExceptionalZero_iff_classicalInput
    {beta0 F discLog : ℕ → ℝ} {c : ℝ} :
    StarkClassicalExceptionalZero beta0 F discLog c ↔
      StarkClassicalInput beta0 F discLog c :=
  ⟨fun S =>
      { F_pos := S.F_pos
        discLog_pos := S.discLog_pos
        c_ge := S.c_ge
        classical := fun n => not_lt.mp (S.no_exceptional_above n) },
    fun S =>
      { F_pos := S.F_pos
        discLog_pos := S.discLog_pos
        c_ge := S.c_ge
        no_exceptional_above := fun n => not_lt.mpr (S.classical n) }⟩

/-- The literature form proves `StarkClassicalInput`. -/
theorem StarkClassicalExceptionalZero.toStarkClassicalInput
    {beta0 F discLog : ℕ → ℝ} {c : ℝ}
    (S : StarkClassicalExceptionalZero beta0 F discLog c) :
    StarkClassicalInput beta0 F discLog c :=
  starkClassicalExceptionalZero_iff_classicalInput.mp S

/-- The literature form proves the paper's Stark bound. -/
theorem StarkClassicalExceptionalZero.toStarkBetaUpper
    {beta0 F discLog : ℕ → ℝ} {c : ℝ}
    (S : StarkClassicalExceptionalZero beta0 F discLog c) :
    StarkBetaUpper beta0 F discLog :=
  S.toStarkClassicalInput.toStarkBetaUpper

/-- A **strict** classical estimate, as usually printed: the exceptional zero is
strictly below the Stark line. -/
structure StarkStrictExceptionalZero (beta0 F discLog : ℕ → ℝ) (c : ℝ) : Prop where
  /-- The factorial factor is positive. -/
  F_pos : ∀ n, 0 < F n
  /-- `log |Δ_E|` is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- The literature constant is at least the paper's `1/4`. -/
  c_ge : starkConstant ≤ c
  /-- The exceptional zero is strictly below the classical Stark line. -/
  strict_above : ∀ n, beta0 n < 1 - c / (F n * discLog n)

/-- Strict to non-strict: the printed strict estimate gives the classical
real-zero exclusion. -/
theorem StarkStrictExceptionalZero.toStarkClassicalExceptionalZero
    {beta0 F discLog : ℕ → ℝ} {c : ℝ}
    (S : StarkStrictExceptionalZero beta0 F discLog c) :
    StarkClassicalExceptionalZero beta0 F discLog c where
  F_pos := S.F_pos
  discLog_pos := S.discLog_pos
  c_ge := S.c_ge
  no_exceptional_above := fun n => not_lt.mpr (le_of_lt (S.strict_above n))

/-- The strict classical estimate proves `StarkClassicalInput`. -/
theorem StarkStrictExceptionalZero.toStarkClassicalInput
    {beta0 F discLog : ℕ → ℝ} {c : ℝ}
    (S : StarkStrictExceptionalZero beta0 F discLog c) :
    StarkClassicalInput beta0 F discLog c :=
  S.toStarkClassicalExceptionalZero.toStarkClassicalInput

/-! ## 3. The literal factorial scale -/

/-- The factorial factor `d!` as a real sequence. -/
noncomputable def factorialFactor (degree : ℕ → ℕ) : ℕ → ℝ :=
  fun n => ((degree n).factorial : ℝ)

/-- The paper's absolute-degree factor `(2d)!`. -/
noncomputable def absoluteFactorialFactor (degree : ℕ → ℕ) : ℕ → ℝ :=
  fun n => ((2 * degree n).factorial : ℝ)

/-- `d!` is positive. -/
theorem factorialFactor_pos (degree : ℕ → ℕ) (n : ℕ) :
    0 < factorialFactor degree n := by
  unfold factorialFactor
  exact_mod_cast Nat.factorial_pos (degree n)

/-- `(2d)!` is positive. -/
theorem absoluteFactorialFactor_pos (degree : ℕ → ℕ) (n : ℕ) :
    0 < absoluteFactorialFactor degree n := by
  unfold absoluteFactorialFactor
  exact_mod_cast Nat.factorial_pos (2 * degree n)

/-- **Stark's exceptional-zero lemma at the literal factorial scale.**  No
exceptional zero lies above `1 - (4 d! log |Δ_E|)⁻¹`. -/
structure StarkFactorialExceptionalZeroInput
    (beta0 : ℕ → ℝ) (degree : ℕ → ℕ) (discLog : ℕ → ℝ) : Prop where
  /-- The degree is positive. -/
  degree_pos : ∀ n, 0 < degree n
  /-- `log |Δ_E|` is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- No exceptional zero lies strictly above the factorial Stark line. -/
  no_exceptional_above :
    ∀ n, ¬ (starkLine (factorialFactor degree) discLog n < beta0 n)

/-- The factorial form is an instance of the smallest exceptional-zero input,
with `F = d!`. -/
theorem StarkFactorialExceptionalZeroInput.toStarkExceptionalZeroInput
    {beta0 : ℕ → ℝ} {degree : ℕ → ℕ} {discLog : ℕ → ℝ}
    (S : StarkFactorialExceptionalZeroInput beta0 degree discLog) :
    StarkExceptionalZeroInput beta0 (factorialFactor degree) discLog where
  F_pos := factorialFactor_pos degree
  discLog_pos := S.discLog_pos
  no_exceptional_above := S.no_exceptional_above

/-- The factorial form proves Stark's upper bound with `F = d!`. -/
theorem StarkFactorialExceptionalZeroInput.toStarkBetaUpper
    {beta0 : ℕ → ℝ} {degree : ℕ → ℕ} {discLog : ℕ → ℝ}
    (S : StarkFactorialExceptionalZeroInput beta0 degree discLog) :
    StarkBetaUpper beta0 (factorialFactor degree) discLog :=
  S.toStarkExceptionalZeroInput.toStarkBetaUpper

/-- The factorial form proves `StarkClassicalInput` with `F = d!` at
`c = 1/4`. -/
theorem StarkFactorialExceptionalZeroInput.toStarkClassicalInput
    {beta0 : ℕ → ℝ} {degree : ℕ → ℕ} {discLog : ℕ → ℝ}
    (S : StarkFactorialExceptionalZeroInput beta0 degree discLog) :
    StarkClassicalInput beta0 (factorialFactor degree) discLog starkConstant :=
  S.toStarkExceptionalZeroInput.toStarkClassicalInput

/-- **Monotonicity of the Stark line in the factorial factor.**  If `F ≤ F'`
pointwise, then a Stark bound at `F` implies the weaker bound at `F'`. -/
theorem starkBetaUpper_of_factor_le
    {beta0 F F' discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n)
    (hFF' : ∀ n, F n ≤ F' n)
    (h : StarkBetaUpper beta0 F discLog) :
    StarkBetaUpper beta0 F' discLog := by
  intro n
  have hden : 0 < 4 * F n * discLog n :=
    mul_pos (mul_pos (by norm_num) (hF n)) (hd n)
  have hle : 1 / (4 * F' n * discLog n) ≤ 1 / (4 * F n * discLog n) := by
    apply one_div_le_one_div_of_le hden
    have hmul : 4 * F n ≤ 4 * F' n := by linarith [hFF' n]
    exact mul_le_mul_of_nonneg_right hmul (le_of_lt (hd n))
  linarith [h n, hle]

/-- The factorial form gives the paper's bound for every factor sequence `F`
dominating `d!`. -/
theorem StarkFactorialExceptionalZeroInput.toStarkBetaUpper_of_le
    {beta0 : ℕ → ℝ} {degree : ℕ → ℕ} {discLog F : ℕ → ℝ}
    (S : StarkFactorialExceptionalZeroInput beta0 degree discLog)
    (hle : ∀ n, factorialFactor degree n ≤ F n) :
    StarkBetaUpper beta0 F discLog :=
  starkBetaUpper_of_factor_le (factorialFactor_pos degree) S.discLog_pos hle
    S.toStarkBetaUpper

/-- `d! ≤ (2d)!`. -/
theorem factorial_le_two_mul_factorial (d : ℕ) :
    d.factorial ≤ (2 * d).factorial :=
  Nat.factorial_le (by omega)

/-- `d! ≤ (2d)!` as real sequences. -/
theorem factorialFactor_le_absoluteFactorialFactor
    (degree : ℕ → ℕ) (n : ℕ) :
    factorialFactor degree n ≤ absoluteFactorialFactor degree n := by
  unfold factorialFactor absoluteFactorialFactor
  exact_mod_cast factorial_le_two_mul_factorial (degree n)

/-- **The paper's absolute-degree instance `F = (2d)!`.**  The field
`E = K(√γ)` has absolute degree `2d`, so the factorial-scale lemma gives the
bound with `F = (2d)!` once `d! ≤ (2d)!` is used. -/
theorem StarkFactorialExceptionalZeroInput.toStarkBetaUpper_absolute
    {beta0 : ℕ → ℝ} {degree : ℕ → ℕ} {discLog : ℕ → ℝ}
    (S : StarkFactorialExceptionalZeroInput beta0 degree discLog) :
    StarkBetaUpper beta0 (absoluteFactorialFactor degree) discLog :=
  S.toStarkBetaUpper_of_le (factorialFactor_le_absoluteFactorialFactor degree)

/-- The paper's `F = (2d)!` instance of `StarkClassicalInput` at `c = 1/4`. -/
theorem StarkFactorialExceptionalZeroInput.toStarkClassicalInput_absolute
    {beta0 : ℕ → ℝ} {degree : ℕ → ℕ} {discLog : ℕ → ℝ}
    (S : StarkFactorialExceptionalZeroInput beta0 degree discLog) :
    StarkClassicalInput beta0 (absoluteFactorialFactor degree) discLog
      starkConstant :=
  (starkBetaUpper_iff_classicalInput_quarter
    (absoluteFactorialFactor_pos degree) S.discLog_pos).mp
    S.toStarkBetaUpper_absolute

/-! ## 4. Composition with the zero-free distance input -/

/-- The smallest exceptional-zero input and the explicit zero-free distance
input assemble the combined `StarkZeroFreeInputs` at `c = 1/4`. -/
theorem starkZeroFreeInputs_of_exceptionalZero
    {beta0 zeroRealPart F discLog : ℕ → ℝ} {cz : ℝ}
    (Z : DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog)
    (S : StarkExceptionalZeroInput beta0 F discLog) :
    StarkZeroFreeInputs beta0 zeroRealPart F discLog cz starkConstant :=
  StarkZeroFreeInputs.mk Z S.toStarkClassicalInput

/-- **The classical exceptional-zero lemma reduces directly to
`DedekindAnalyticInputs`.**  The zero-free and range inputs are passed
separately; the Stark component is the reduction of this file. -/
theorem dedekindAnalyticInputs_of_exceptionalZero
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (Z : DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog)
    (S : StarkExceptionalZeroInput beta0 F discLog)
    (hK : 0 < K)
    (hr : ChebotarevRangeThreshold K x degree discLog)
    (hx : ∀ n, 0 < x n)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hcheb : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 :=
  dedekindAnalyticInputs_of_starkQuarter_and_distance Z
    S.toStarkClassicalInput hK hr hx hC hcZ hcheb

/-- **The factorial-scale exceptional-zero lemma reduces directly to
`DedekindAnalyticInputs` with the paper's `F = (2d)!`.** -/
theorem dedekindAnalyticInputs_of_factorialExceptionalZero
    {beta0 zeroRealPart : ℕ → ℝ} {degree : ℕ → ℕ}
    {discLog x absDegree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (Z : DedekindZeroFreeDistanceInput beta0 zeroRealPart cz discLog)
    (S : StarkFactorialExceptionalZeroInput beta0 degree discLog)
    (hK : 0 < K)
    (hr : ChebotarevRangeThreshold K x absDegree discLog)
    (hx : ∀ n, 0 < x n)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hcheb : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x absDegree)) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog
      (absoluteFactorialFactor degree) K x absDegree C cZ count liX liBeta0 :=
  dedekindAnalyticInputs_of_starkQuarter_and_distance Z
    S.toStarkClassicalInput_absolute hK hr hx hC hcZ hcheb

/-! ## Axiom audit -/

#print axioms StarkExceptionalZeroInput.toStarkBetaUpper
#print axioms StarkExceptionalZeroInput.toStarkProductInput
#print axioms StarkExceptionalZeroInput.toStarkClassicalInput
#print axioms StarkExceptionalZeroInput.toStarkInput
#print axioms StarkExceptionalZeroInput.ofStarkBetaUpper
#print axioms StarkExceptionalZeroInput.ofStarkClassicalInput
#print axioms starkExceptionalZeroInput_iff_betaUpper
#print axioms starkExceptionalZeroInput_iff_classicalInput
#print axioms starkExceptionalZeroInput_iff_productInput
#print axioms starkClassicalExceptionalZero_iff_classicalInput
#print axioms StarkClassicalExceptionalZero.toStarkClassicalInput
#print axioms StarkClassicalExceptionalZero.toStarkBetaUpper
#print axioms StarkStrictExceptionalZero.toStarkClassicalExceptionalZero
#print axioms StarkStrictExceptionalZero.toStarkClassicalInput
#print axioms factorialFactor_pos
#print axioms absoluteFactorialFactor_pos
#print axioms StarkFactorialExceptionalZeroInput.toStarkExceptionalZeroInput
#print axioms StarkFactorialExceptionalZeroInput.toStarkBetaUpper
#print axioms StarkFactorialExceptionalZeroInput.toStarkClassicalInput
#print axioms starkBetaUpper_of_factor_le
#print axioms StarkFactorialExceptionalZeroInput.toStarkBetaUpper_of_le
#print axioms factorial_le_two_mul_factorial
#print axioms factorialFactor_le_absoluteFactorialFactor
#print axioms StarkFactorialExceptionalZeroInput.toStarkBetaUpper_absolute
#print axioms StarkFactorialExceptionalZeroInput.toStarkClassicalInput_absolute
#print axioms starkZeroFreeInputs_of_exceptionalZero
#print axioms dedekindAnalyticInputs_of_exceptionalZero
#print axioms dedekindAnalyticInputs_of_factorialExceptionalZero

end

end Cogentic.RandomizedL34ClassicalStark
