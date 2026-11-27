import Cogentic.RandomizedL34

/-!
# L34: elementary sub-lemmas

This file splits the arithmetic and counting content out of
`Cogentic.RandomizedL34.EffectiveChebotarevInputs`.  Every paper-level analytic
input -- the Dedekind zero-free region, Stark's exceptional-zero bound, the
Lagarias-Odlyzko range and error, and the effective Chebotarev count -- remains
an explicit `Prop` hypothesis (the same `Prop`s defined in
`Cogentic.RandomizedL34`).  Nothing here asserts a theorem of analytic number
theory.

The four groups of elementary sub-lemmas are:

1. **Probe budget arithmetic.**  `R = F T¹⁰` gives `R > 0`, the exact multiplier
   identity for a per-ideal probability `c/(d F T⁶)`, and the cubic lower bound
   `R · c/(d F T⁶) ≥ c T³` when `d ≤ T`.
2. **Class-count polynomial bound.**  `h* ≤ Ch T³` and
   `classCount ≤ 2^{h*}` give `classCount ≤ 2^{Ch T³}` and
   `log classCount ≤ Ch T³ log 2`.
3. **Mask compression.**  `h* + 7 ≤ m` gives `2^{h*-m} ≤ 1/128`; exact
   `m = h* + 7` gives equality `2^{h*-m} = 1/128`.
4. **Error negligibility.**  The Chebotarev error and the discarded small /
   higher-degree ideals are each at most one eighth of the logarithmic-integral
   gap.  Combined with the cumulative Chebotarev count, this yields the
   `bracketTerm (cbr/4)` lower bound for the degree-one inert count and then the
   per-trial probe lower bound.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no loss, mass,
count, or error is set to zero.
-/

namespace Cogentic.RandomizedL34Sub

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## 0. The paper-level boundary

The five analytic statements below are kept verbatim as explicit `Prop`
fields.  They are Lagarias-Odlyzko's Dedekind zero-free region and effective
Chebotarev theorem, and Stark's exceptional-zero bound.  No proof of any of
them appears in this file. -/

/-- **Paper-level analytic inputs**, bundled for reference.  The elementary
sub-lemmas in the rest of the file never prove, weaken, or eliminate these
fields; they are hypotheses throughout. -/
structure PaperLevelInputs
    (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ)
    (F : ℕ → ℝ) (K : ℝ) (x degree : ℕ → ℝ)
    (C cZ : ℝ) (error count main : ℕ → ℝ) : Prop where
  /-- Lagarias-Odlyzko: the Dedekind zero-free region away from `β₀`. -/
  zeroFree : DedekindZeroFreeRegion beta0 zeroRealPart cz discLog
  /-- Stark: the exceptional real zero is bounded away from `1`. -/
  stark : StarkExceptionalZeroBound beta0 F discLog
  /-- Lagarias-Odlyzko: the Chebotarev range condition. -/
  chebRange : EffectiveChebotarevRange K x degree discLog
  /-- Lagarias-Odlyzko: the explicit error term. -/
  chebError : LagariasOdlyzkoError C cZ x degree error
  /-- Lagarias-Odlyzko: the effective Chebotarev count. -/
  chebCount : EffectiveChebotarev count main error

/-- Every `EffectiveChebotarevInputs` bundle carries its paper-level content
in the `PaperLevelInputs` structure. -/
theorem EffectiveChebotarevInputs.toPaperLevel
    (I : EffectiveChebotarevInputs) :
    PaperLevelInputs I.beta0 I.zeroRealPart I.cz I.discLog I.F I.K I.x
      I.degree I.C I.cZ I.error I.count I.main :=
  { zeroFree := I.zero_free
    stark := I.stark
    chebRange := I.cheb_range
    chebError := I.cheb_error
    chebCount := I.cheb_count }

/-! ## 1. Probe budget arithmetic -/

/-- The paper's budget `R = F T¹⁰` is positive whenever `F` and `T` are. -/
theorem probeBudget_pos {R : ℕ → ℕ} {F T : ℕ → ℝ}
    (hR : ProbeBudget R F T) (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n)
    (n : ℕ) : 0 < R n := by
  have hpos : 0 < F n * T n ^ 10 := mul_pos (hF n) (pow_pos (hT n) 10)
  rw [← hR n] at hpos
  exact_mod_cast hpos

/-- **Budget multiplier identity.**  Multiplying the budget `R = F T¹⁰` by a
per-ideal probability `c/(d F T⁶)` cancels `F` and six powers of `T`, leaving
`c T⁴ / d`.  This is the arithmetic content of the `T⁴/T⁶ = T⁻²` cancellation
in the probe-count estimate. -/
theorem probeBudget_mul_selection {R : ℕ → ℕ} {F T : ℕ → ℝ}
    (hR : ProbeBudget R F T) {c degree : ℕ → ℝ}
    (hF : ∀ n, F n ≠ 0) (hT : ∀ n, T n ≠ 0) (hd : ∀ n, degree n ≠ 0)
    (n : ℕ) :
    (R n : ℝ) * (c n / (degree n * F n * T n ^ 6)) =
      c n * T n ^ 4 / degree n := by
  rw [hR n]
  field_simp [hF n, hT n, hd n]

/-- **Budget cubic lower bound.**  Since `d ≤ T` and `T > 0`, the exact
multiplier identity gives `R · c/(d F T⁶) ≥ c T³` for `c ≥ 0`.  This is the
step that converts the `R = F T¹⁰` budget into the `T³` exponent used by the
class-count polynomial bound. -/
theorem probeBudget_cubic_lower {R : ℕ → ℕ} {F T : ℕ → ℝ}
    (hR : ProbeBudget R F T) {c degree : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) (hF : ∀ n, 0 < F n) (hT : ∀ n, 1 ≤ T n)
    (hd : ∀ n, 0 < degree n) (hdegT : ∀ n, degree n ≤ T n) (n : ℕ) :
    c n * T n ^ 3 ≤
      (R n : ℝ) * (c n / (degree n * F n * T n ^ 6)) := by
  rw [probeBudget_mul_selection hR (fun m => (hF m).ne')
    (fun m => (lt_of_lt_of_le zero_lt_one (hT m)).ne') (fun m => (hd m).ne') n]
  have hTpos : 0 < T n := lt_of_lt_of_le zero_lt_one (hT n)
  have hT4 : c n * T n ^ 3 = c n * T n ^ 4 / T n := by
    field_simp [hTpos.ne']
  rw [hT4]
  exact div_le_div_of_nonneg_left (mul_nonneg (hc n) (by positivity)) (hd n) (hdegT n)

/-- The paper's budget divided by `F T¹⁰` recovers one; a sanity identity used
to keep the exact budget visible in downstream arithmetic. -/
theorem probeBudget_div_budget {R : ℕ → ℕ} {F T : ℕ → ℝ}
    (hR : ProbeBudget R F T) (hF : ∀ n, F n ≠ 0) (hT : ∀ n, T n ≠ 0) (n : ℕ) :
    (R n : ℝ) / (F n * T n ^ 10) = 1 := by
  rw [hR n]
  field_simp [hF n, hT n]

/-! ## 2. Class-count polynomial bound -/

/-- **Class count against the cubic exponent.**  Lemma E.2 (`classCount ≤ 2^{h*}`)
and `h* ≤ Ch T³` combine to `classCount ≤ 2^{Ch T³}`. -/
theorem classCount_le_two_rpow {classCount hstar T : ℕ → ℝ} {Ch : ℝ}
    (hclass : ClassCountBound classCount hstar)
    (hpoly : ClassCountPolynomial Ch hstar T) (n : ℕ) :
    classCount n ≤ (2 : ℝ) ^ (Ch * T n ^ 3) := by
  calc
    classCount n ≤ (2 : ℝ) ^ (hstar n) := hclass n
    _ ≤ (2 : ℝ) ^ (Ch * T n ^ 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (hpoly.2 n)

/-- **Entropy form of the class count.**  Taking logarithms of Lemma E.2 gives
`log classCount ≤ h* log 2`. -/
theorem log_classCount_le {classCount hstar : ℕ → ℝ}
    (hclass : ClassCountBound classCount hstar)
    (hpos : ∀ n, 0 < classCount n) (n : ℕ) :
    Real.log (classCount n) ≤ hstar n * Real.log 2 := by
  calc
    Real.log (classCount n) ≤ Real.log ((2 : ℝ) ^ (hstar n)) :=
      Real.log_le_log (hpos n) (hclass n)
    _ = hstar n * Real.log 2 := by
      rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]

/-- **Cubic entropy bound.**  Composing the entropy form with `h* ≤ Ch T³`
gives `log classCount ≤ Ch T³ log 2`, the bound consumed by the probe-miss
exponential estimate. -/
theorem log_classCount_le_cubic {classCount hstar T : ℕ → ℝ} {Ch : ℝ}
    (hclass : ClassCountBound classCount hstar)
    (hpoly : ClassCountPolynomial Ch hstar T)
    (hpos : ∀ n, 0 < classCount n) (n : ℕ) :
    Real.log (classCount n) ≤ Ch * T n ^ 3 * Real.log 2 := by
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  calc
    Real.log (classCount n) ≤ hstar n * Real.log 2 :=
      log_classCount_le hclass hpos n
    _ ≤ (Ch * T n ^ 3) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (hpoly.2 n) hlog2

/-- **Exponential form of the class count.**  The previous bound is exactly
`classCount ≤ exp (Ch T³ log 2)`, the form used when multiplying by the
per-trial miss exponential. -/
theorem classCount_le_exp_cubic {classCount hstar T : ℕ → ℝ} {Ch : ℝ}
    (hclass : ClassCountBound classCount hstar)
    (hpoly : ClassCountPolynomial Ch hstar T)
    (_hpos : ∀ n, 0 < classCount n) (n : ℕ) :
    classCount n ≤ Real.exp (Ch * T n ^ 3 * Real.log 2) := by
  calc
    classCount n ≤ (2 : ℝ) ^ (Ch * T n ^ 3) :=
      classCount_le_two_rpow hclass hpoly n
    _ = Real.exp (Ch * T n ^ 3 * Real.log 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring_nf

/-! ## 3. Mask compression -/

/-- The mask bit budget `h* + 7 ≤ m` is equivalently a gap of at least seven
bits. -/
theorem mask_gap_ge_seven {hstar m : ℕ → ℝ}
    (h : MaskCompressionBits hstar m) (n : ℕ) :
    7 ≤ m n - hstar n := by
  linarith [h n]

/-- **Mask failure is at most `1/128`.**  The compressed coordinates of
`m = h* + 7` bits fail simultaneously with probability at most `2^{-7}`. -/
theorem maskFailure_le_inv128 {hstar m : ℕ → ℝ}
    (h : MaskCompressionBits hstar m) (n : ℕ) :
    maskFailure hstar m n ≤ 1 / 128 := by
  unfold maskFailure
  have hbits : hstar n - m n ≤ (-7 : ℝ) := by
    linarith [h n]
  calc
    (2 : ℝ) ^ (hstar n - m n) ≤ (2 : ℝ) ^ (-7 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hbits
    _ = 1 / 128 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

/-- **Exact mask compression.**  When the compressed length is exactly
`m = h* + 7`, the mask failure is exactly the paper's `1/128` slack. -/
theorem maskFailure_eq_inv128 {hstar m : ℕ → ℝ}
    (h : ∀ n, m n = hstar n + 7) (n : ℕ) :
    maskFailure hstar m n = 1 / 128 := by
  unfold maskFailure
  have hgap : hstar n - m n = (-7 : ℝ) := by
    rw [h n]
    ring
  rw [hgap, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The mask failure is nonnegative. -/
theorem maskFailure_nonneg' {hstar m : ℕ → ℝ} (n : ℕ) :
    0 ≤ maskFailure hstar m n := by
  unfold maskFailure
  exact Real.rpow_nonneg (by norm_num) _

/-- **The exact slack identity for the ledger.**  If the mask uses exactly
`h* + 7` bits, then the excess loss over the `1/128` slack is the positive part
of the probe miss, not of the probe miss plus a mask contribution. -/
theorem excessLoss_mask_exact {probe m hstar : ℕ → ℝ}
    (h : ∀ n, m n = hstar n + 7) (probeNonneg : ∀ n, 0 ≤ probe n) (n : ℕ) :
    excessLoss probe (maskFailure hstar m) allowedFailure n = probe n := by
  unfold excessLoss allowedFailure
  rw [maskFailure_eq_inv128 h n]
  have hz : probe n + 1 / 128 - 1 / 128 = probe n := by ring
  rw [hz, max_eq_right (probeNonneg n)]

/-! ## 4. Error negligibility -/

/-- **Chebotarev error is at most one eighth of the bracket.**  The
Lagarias-Odlyzko error estimate, measured against `bracketTerm (cbr/8)`, is the
same as one eighth of the full bracket term. -/
theorem error_le_eighth_bracket {cbr : ℝ} {x F T error : ℕ → ℝ}
    (hnegl : ChebotarevErrorNegligible cbr x F T error) (n : ℕ) :
    error n ≤ bracketTerm cbr x F T n / 8 := by
  have h := hnegl n
  have h8 : bracketTerm (cbr / 8) x F T n = bracketTerm cbr x F T n / 8 := by
    unfold bracketTerm
    ring
  rwa [h8] at h

/-- **Chebotarev error is at most one eighth of the log-integral gap.**  This
combines the error negligibility with the Stark/dyadic bracket
`B ≤ Li x - Li x^{β₀}`. -/
theorem error_le_eighth_gap {cbr : ℝ} {x F T error liX liBeta0 : ℕ → ℝ}
    (hbracket : LogIntegralBracket cbr x F T liX liBeta0)
    (hnegl : ChebotarevErrorNegligible cbr x F T error) (n : ℕ) :
    error n ≤ (liX n - liBeta0 n) / 8 := by
  have h1 : error n ≤ bracketTerm cbr x F T n / 8 :=
    error_le_eighth_bracket hnegl n
  have h2 : bracketTerm cbr x F T n / 8 ≤ (liX n - liBeta0 n) / 8 :=
    div_le_div_of_nonneg_right (hbracket.2 n) (by norm_num)
  exact h1.trans h2

/-- **Discarded ideals are at most one eighth of the gap.**  The `d sqrt x`
small / higher-degree ideals lost by the degree-one reduction are bounded by
`bracketTerm (cbr/8)` and hence by one eighth of the log-integral gap. -/
theorem degreeLoss_le_eighth_gap {cbr : ℝ} {x degree F T liX liBeta0 : ℕ → ℝ}
    (hbracket : LogIntegralBracket cbr x F T liX liBeta0)
    (hloss : DegreeOneLossNegligible cbr x degree F T) (n : ℕ) :
    degree n * Real.sqrt (x n) ≤ (liX n - liBeta0 n) / 8 := by
  have h1 : degree n * Real.sqrt (x n) ≤ bracketTerm cbr x F T n / 8 := by
    have h := hloss n
    have h8 : bracketTerm (cbr / 8) x F T n = bracketTerm cbr x F T n / 8 := by
      unfold bracketTerm
      ring
    rwa [h8] at h
  have h2 : bracketTerm cbr x F T n / 8 ≤ (liX n - liBeta0 n) / 8 :=
    div_le_div_of_nonneg_right (hbracket.2 n) (by norm_num)
  exact h1.trans h2

/-- **Cumulative inert lower bound from effective Chebotarev.**  The Chebotarev
count lies within `error` of its main term `½ (Li x - Li x^{β₀})`, and the inert
count contains it.  This is the elementary triangle-inequality step; the
paper-level `EffectiveChebotarev` remains an explicit hypothesis. -/
theorem inert_lower_of_props {count main error inertCount liX liBeta0 : ℕ → ℝ}
    (hcheb : EffectiveChebotarev count main error)
    (hmain : ∀ n, main n = (1 / 2) * (liX n - liBeta0 n))
    (hge : ∀ n, count n ≤ inertCount n) (n : ℕ) :
    (1 / 2) * (liX n - liBeta0 n) - error n ≤ inertCount n := by
  have hcount := (abs_le.mp (hcheb n)).1
  rw [hmain n] at hcount
  have hge' := hge n
  linarith

/-- **Degree-one inert lower bound from the four elementary estimates.**  The
full inert count is at least `½(Li x - Li x^{β₀}) - error`; the error and the
discarded ideals each cost at most one eighth of the gap; hence the degree-one
inert count still contains `bracketTerm (cbr/4)`. -/
theorem degreeOneInert_lower_of_props {cbr : ℝ}
    {x degree F T : ℕ → ℝ}
    {error inertCount degreeOneInert liX liBeta0 : ℕ → ℝ}
    (hbracket : LogIntegralBracket cbr x F T liX liBeta0)
    (hnegl : ChebotarevErrorNegligible cbr x F T error)
    (hloss : DegreeOneLossNegligible cbr x degree F T)
    (hred : DegreeOneInertReduction inertCount degreeOneInert degree x)
    (hinert : ∀ n, (1 / 2) * (liX n - liBeta0 n) - error n ≤ inertCount n)
    (n : ℕ) :
    bracketTerm (cbr / 4) x F T n ≤ degreeOneInert n := by
  let B := bracketTerm cbr x F T n
  have hbracket' : B ≤ liX n - liBeta0 n := hbracket.2 n
  have herror : error n ≤ B / 8 := by
    have := hnegl n
    have h8 : bracketTerm (cbr / 8) x F T n = B / 8 := by
      unfold B bracketTerm
      ring
    rwa [h8] at this
  have hloss' : degree n * Real.sqrt (x n) ≤ B / 8 := by
    have := hloss n
    have h8 : bracketTerm (cbr / 8) x F T n = B / 8 := by
      unfold B bracketTerm
      ring
    rwa [h8] at this
  have hred' : inertCount n - degree n * Real.sqrt (x n) ≤ degreeOneInert n :=
    hred n
  have hinert' := hinert n
  have hquarter : bracketTerm (cbr / 4) x F T n = B / 4 := by
    unfold B bracketTerm
    ring
  rw [hquarter]
  nlinarith

/-- **Per-trial probe lower bound from the elementary estimates.**  Composing
the degree-one inert lower bound with the per-ideal selection probability
`csel/(d x)` gives `(csel cbr/4)/(d F T⁶) ≤ pTrial`. -/
theorem probe_lower_of_props {cbr csel : ℝ}
    {x degree F T : ℕ → ℝ}
    {error inertCount degreeOneInert liX liBeta0 pTrial : ℕ → ℝ}
    (hbracket : LogIntegralBracket cbr x F T liX liBeta0)
    (hnegl : ChebotarevErrorNegligible cbr x F T error)
    (hloss : DegreeOneLossNegligible cbr x degree F T)
    (hred : DegreeOneInertReduction inertCount degreeOneInert degree x)
    (hinert : ∀ n, (1 / 2) * (liX n - liBeta0 n) - error n ≤ inertCount n)
    (hsel : ProbeSelectionLowerBound csel x degree degreeOneInert pTrial)
    (hx : ∀ n, 0 < x n) (hd : ∀ n, 0 < degree n)
    (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n) (n : ℕ) :
    csel * cbr / 4 / (degree n * F n * T n ^ 6) ≤ pTrial n := by
  have hdeg := degreeOneInert_lower_of_props hbracket hnegl hloss hred hinert n
  have hsel' := hsel.2 n
  have hcsel : 0 ≤ csel := hsel.1.le
  have hnum : csel * bracketTerm (cbr / 4) x F T n ≤
      csel * degreeOneInert n :=
    mul_le_mul_of_nonneg_left hdeg hcsel
  have hfrac :
      csel * bracketTerm (cbr / 4) x F T n / (degree n * x n) ≤
        csel * degreeOneInert n / (degree n * x n) :=
    (div_le_div_iff_of_pos_right (mul_pos (hd n) (hx n))).mpr hnum
  have heq :
      csel * bracketTerm (cbr / 4) x F T n / (degree n * x n) =
        csel * cbr / 4 / (degree n * F n * T n ^ 6) := by
    unfold bracketTerm
    field_simp [(hx n).ne', (hd n).ne', (hF n).ne', (hT n).ne']
  calc
    csel * cbr / 4 / (degree n * F n * T n ^ 6)
        = csel * bracketTerm (cbr / 4) x F T n / (degree n * x n) := heq.symm
    _ ≤ csel * degreeOneInert n / (degree n * x n) := hfrac
    _ ≤ pTrial n := hsel'

/-! ## 5. Combined probe-miss reduction -/

/-- **Probe miss is exponentially small.**  This assembles the budget
arithmetic (`R p ≥ cProbe T³`), the class-count polynomial bound
(`log classCount ≤ Ch T³ log 2`), and the eventual cubic domination
`2H ≤ (cProbe - Ch log 2) T³`, where `cProbe = csel cbr/4`.  All analytic
content is in the explicit hypotheses; the proof is the elementary exponent
comparison. -/
theorem probeMiss_le_exp_of_estimates
    {classCount hstar T F degree pTrial : ℕ → ℝ} {R : ℕ → ℕ}
    {Ch csel cbr : ℝ}
    (hbudget : ProbeBudget R F T)
    (hcsel : 0 < csel) (hcbr : 0 < cbr)
    (hprobe : ∀ n, csel * cbr / 4 / (degree n * F n * T n ^ 6) ≤ pTrial n)
    (hclass : ClassCountBound classCount hstar)
    (hpoly : ClassCountPolynomial Ch hstar T)
    (hclasspos : ∀ n, 0 < classCount n)
    (hd : ∀ n, 0 < degree n) (hdT : ∀ n, degree n ≤ T n)
    (hF : ∀ n, 0 < F n) (hT : ∀ n, 1 ≤ T n)
    (hmargin : Ch * Real.log 2 < csel * cbr / 4)
    (hcubic : ∀ᶠ n : ℕ in atTop,
      2 * scale n ≤ (csel * cbr / 4 - Ch * Real.log 2) * T n ^ 3) :
    ∀ᶠ n : ℕ in atTop,
      probeMiss classCount pTrial R n ≤ Real.exp (-(2 : ℝ) * scale n) := by
  filter_upwards [hcubic] with n hcubic
  have hTpos : 0 < T n := lt_of_lt_of_le zero_lt_one (hT n)
  have hFpos : 0 < F n := hF n
  have hdpos : 0 < degree n := hd n
  have hcProbe : 0 < csel * cbr / 4 := by positivity
  -- `R p ≥ (csel cbr/4) T⁴ / d`
  have hRp1 : csel * cbr / 4 * T n ^ 4 / degree n ≤
      (R n : ℝ) * pTrial n := by
    rw [hbudget n]
    have hEq :
        csel * cbr / 4 * T n ^ 4 / degree n =
          (F n * T n ^ 10) *
            (csel * cbr / 4 / (degree n * F n * T n ^ 6)) := by
      field_simp [hTpos.ne', hFpos.ne', hdpos.ne']
    rw [hEq]
    exact mul_le_mul_of_nonneg_left (hprobe n) (by positivity)
  -- `(csel cbr/4) T³ ≤ R p`, since `d ≤ T`
  have hRp : csel * cbr / 4 * T n ^ 3 ≤ (R n : ℝ) * pTrial n := by
    have hT4 : csel * cbr / 4 * T n ^ 3 = csel * cbr / 4 * T n ^ 4 / T n := by
      field_simp [hTpos.ne']
    have hmono : csel * cbr / 4 * T n ^ 4 / T n ≤
        csel * cbr / 4 * T n ^ 4 / degree n :=
      div_le_div_of_nonneg_left (by positivity) hdpos (hdT n)
    exact hT4.trans_le (hmono.trans hRp1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hstar_le : hstar n ≤ Ch * T n ^ 3 := hpoly.2 n
  have h1 : hstar n * Real.log 2 ≤ (Ch * T n ^ 3) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hstar_le hlog2.le
  have h2 : (Ch * T n ^ 3) * Real.log 2 ≤ csel * cbr / 4 * T n ^ 3 := by
    have hT3 : 0 ≤ T n ^ 3 := by positivity
    nlinarith [hmargin]
  have hExp : hstar n * Real.log 2 + 2 * scale n ≤
      (R n : ℝ) * pTrial n := by
    calc
      hstar n * Real.log 2 + 2 * scale n
          ≤ (Ch * T n ^ 3) * Real.log 2 +
              (csel * cbr / 4 - Ch * Real.log 2) * T n ^ 3 :=
            add_le_add h1 hcubic
      _ = csel * cbr / 4 * T n ^ 3 := by ring
      _ ≤ (R n : ℝ) * pTrial n := hRp
  have hlogclass : Real.log (classCount n) ≤ hstar n * Real.log 2 :=
    log_classCount_le hclass hclasspos n
  calc
    probeMiss classCount pTrial R n
        = classCount n * Real.exp (-((R n : ℝ) * pTrial n)) := rfl
    _ ≤ Real.exp (hstar n * Real.log 2) *
          Real.exp (-((R n : ℝ) * pTrial n)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        rw [← Real.exp_log (hclasspos n)]
        exact Real.exp_le_exp.mpr hlogclass
    _ = Real.exp (hstar n * Real.log 2 - (R n : ℝ) * pTrial n) := by
        rw [← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(2 : ℝ) * scale n) :=
        Real.exp_le_exp.mpr (by linarith)

/-- **End-to-end elementary reduction.**  From the explicit paper-level
bracket, error-negligibility, and degree-one-reduction hypotheses together with
the elementary class-count and budget estimates, the probe miss is eventually
at most `exp (-2H)`.  This is the L34 ledger estimate with all genuinely
analytic content still in hypotheses. -/
theorem probeMiss_le_exp_of_paper_props
    {classCount hstar T F degree pTrial : ℕ → ℝ}
    {R : ℕ → ℕ} {Ch csel cbr : ℝ}
    {x error inertCount degreeOneInert liX liBeta0 : ℕ → ℝ}
    (hbudget : ProbeBudget R F T)
    (hbracket : LogIntegralBracket cbr x F T liX liBeta0)
    (hnegl : ChebotarevErrorNegligible cbr x F T error)
    (hloss : DegreeOneLossNegligible cbr x degree F T)
    (hred : DegreeOneInertReduction inertCount degreeOneInert degree x)
    (hinert : ∀ n, (1 / 2) * (liX n - liBeta0 n) - error n ≤ inertCount n)
    (hsel : ProbeSelectionLowerBound csel x degree degreeOneInert pTrial)
    (hx : ∀ n, 0 < x n) (hd : ∀ n, 0 < degree n)
    (hF : ∀ n, 0 < F n) (hT : ∀ n, 1 ≤ T n)
    (hdT : ∀ n, degree n ≤ T n)
    (hclass : ClassCountBound classCount hstar)
    (hpoly : ClassCountPolynomial Ch hstar T)
    (hclasspos : ∀ n, 0 < classCount n)
    (hmargin : Ch * Real.log 2 < csel * cbr / 4)
    (hcubic : ∀ᶠ n : ℕ in atTop,
      2 * scale n ≤ (csel * cbr / 4 - Ch * Real.log 2) * T n ^ 3) :
    ∀ᶠ n : ℕ in atTop,
      probeMiss classCount pTrial R n ≤ Real.exp (-(2 : ℝ) * scale n) := by
  refine probeMiss_le_exp_of_estimates hbudget hsel.1 hbracket.1 ?_ hclass hpoly
    hclasspos hd hdT hF hT hmargin hcubic
  intro n
  exact probe_lower_of_props hbracket hnegl hloss hred hinert hsel hx hd hF
    (fun m => lt_of_lt_of_le zero_lt_one (hT m)) n

/-! ## Axiom audit -/

#print axioms probeBudget_pos
#print axioms probeBudget_mul_selection
#print axioms probeBudget_cubic_lower
#print axioms probeBudget_div_budget
#print axioms classCount_le_two_rpow
#print axioms log_classCount_le
#print axioms log_classCount_le_cubic
#print axioms classCount_le_exp_cubic
#print axioms mask_gap_ge_seven
#print axioms maskFailure_le_inv128
#print axioms maskFailure_eq_inv128
#print axioms maskFailure_nonneg'
#print axioms excessLoss_mask_exact
#print axioms error_le_eighth_bracket
#print axioms error_le_eighth_gap
#print axioms degreeLoss_le_eighth_gap
#print axioms inert_lower_of_props
#print axioms degreeOneInert_lower_of_props
#print axioms probe_lower_of_props
#print axioms probeMiss_le_exp_of_estimates
#print axioms probeMiss_le_exp_of_paper_props
#print axioms EffectiveChebotarevInputs.toPaperLevel

end Cogentic.RandomizedL34Sub
