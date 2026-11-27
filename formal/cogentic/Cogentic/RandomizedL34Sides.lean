import Cogentic.RandomizedL34Dedekind

/-!
# L34: the one-sided Chebotarev sides and the removal of the error residual

`Cogentic.RandomizedL34Dedekind` reduced the cumulative Chebotarev theorem to
the two-sided structure

* `ChebotarevSides count main error`, with the one-sided fields `lower` and
  `upper`, and
* `ChebotarevErrorSlack C cZ x degree count main`, whose `exists_err` field
  carries a *residual* error sequence `err` bounded by the explicit
  Lagarias–Odlyzko envelope.

The L34 ledger itself uses only the lower side of the count: the inert count
contains the counted class, and the effective-Chebotarev envelope plus the
log-integral bracket turn `main - error` into `bracketTerm (cbr/4)`.
Consequently the upper side is a residual hypothesis, and the existential
`err` is a residual witness.

This file removes both residuals.

## The canonical residual

`countResidual count main n = |count n - main n|` is the canonical error
sequence.  The main theorem `chebotarevErrorSlack_iff_residual_le` proves that
`ChebotarevErrorSlack` is *exactly* the statement that this canonical residual
is pointwise bounded by `lagariasOdlyzkoError`.  Thus the existential field
`exists_err` adds no content: it can always be instantiated by
`countResidual`, and conversely every slack witness is dominated by it.  With
the positivity of `C` and `cZ`, this is equivalent to the effective-Chebotarev
envelope (`chebotarevErrorSlack_iff_effective`).

## The one-sided bounds

`lower_iff_residual_lower` and `upper_iff_residual_upper` identify the two
one-sided bounds with the two halves of the absolute-value envelope, and
`effective_iff_sides` shows that the effective envelope is exactly their
conjunction.  Hence both `ChebotarevSides` and `ChebotarevErrorSlack` are
inter-derivable with a single absolute-value envelope; neither introduces an
extra one-sided error.

## The bracket

`bracketQuarter_le_main_sub_error` combines the error negligibility
`error ≤ bracketTerm (cbr/8)` with `bracketTerm cbr ≤ Li x - Li x^{β₀}` to
prove `bracketTerm (cbr/4) ≤ main - error`.  Consequently
`count_lower_of_bracket_of_effective` gives the one-sided lower bound
`bracketTerm (cbr/4) ≤ count` using only the lower side of the effective
envelope, and `inert_lower_of_bracket` propagates it to the inert count.  The
upper side is never needed: `count_upper_of_bracket` records the (weaker)
upper bracket consequence for completeness, but the ledger reduction below
does not use it.

## The one-sided L34 core

`ChebotarevLowerInput` drops the `upper` field.  `DedekindSidesInputs` is
`DedekindAnalyticInputs` with only this one-sided count field, and
`L34SidesCore` is `L34DedekindCore` with `dedekind` replaced by
`DedekindSidesInputs`.  The theorem `L34SidesCore.probeMiss_le_ledger` proves
the same L34 probe-miss bound directly from the lower side, and
`L34SidesCore.loss_le_ledger` / `loss_le_paper` / `ratedLeaf` re-export the
ledger.  Conversely, `L34SidesCore.toL34DedekindCore_of_upper` rebuilds the
old core whenever an upper side is supplied, so the reduction is lossless and
the removed upper side is genuinely a residual.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no error, count,
loss or mass is set to zero.
-/

namespace Cogentic.RandomizedL34Sides

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The canonical error residual -/

/-- The canonical pointwise residual `|count - main|`.  This is the error that
`EffectiveChebotarev` controls directly; it makes the existential witness of
`ChebotarevErrorSlack` explicit. -/
def countResidual (count main : ℕ → ℝ) (n : ℕ) : ℝ :=
  |count n - main n|

/-- The canonical residual is nonnegative. -/
theorem countResidual_nonneg (count main : ℕ → ℝ) (n : ℕ) :
    0 ≤ countResidual count main n :=
  abs_nonneg _

/-- The canonical residual is exactly the absolute deviation. -/
theorem countResidual_eq_abs (count main : ℕ → ℝ) (n : ℕ) :
    countResidual count main n = |count n - main n| :=
  rfl

/-- A pointwise bound on the canonical residual is exactly the effective
Chebotarev envelope. -/
theorem countResidual_le_iff_effective {count main error : ℕ → ℝ} :
    (∀ n, countResidual count main n ≤ error n) ↔
      EffectiveChebotarev count main error :=
  Iff.rfl

/-- **The slack error has no residual content.**  `ChebotarevErrorSlack` is
equivalent to the positivity of its two constants together with the canonical
residual being bounded by the explicit Lagarias–Odlyzko envelope.  The
existential `err` is therefore not an extra hypothesis: `countResidual` is a
canonical witness and it dominates every other witness. -/
theorem chebotarevErrorSlack_iff_residual_le {C cZ : ℝ}
    {x degree count main : ℕ → ℝ} :
    ChebotarevErrorSlack C cZ x degree count main ↔
      0 < C ∧ 0 < cZ ∧
        ∀ n, countResidual count main n ≤
          lagariasOdlyzkoError C cZ x degree n := by
  constructor
  · intro E
    obtain ⟨err, _herr_nonneg, herr_le, hclose⟩ := E.exists_err
    refine ⟨E.C_pos, E.cZ_pos, fun n => ?_⟩
    exact (hclose n).trans (herr_le n)
  · rintro ⟨hC, hcZ, hres⟩
    refine ⟨hC, hcZ, countResidual count main, ?_, hres, ?_⟩
    · exact countResidual_nonneg count main
    · intro n
      exact le_rfl

/-- **The slack bundle is the effective envelope.**  With the two constants
positive, `ChebotarevErrorSlack` is inter-derivable with the effective
Chebotarev count for the explicit envelope. -/
theorem chebotarevErrorSlack_iff_effective {C cZ : ℝ} (hC : 0 < C) (hcZ : 0 < cZ)
    {x degree count main : ℕ → ℝ} :
    ChebotarevErrorSlack C cZ x degree count main ↔
      EffectiveChebotarev count main (lagariasOdlyzkoError C cZ x degree) := by
  rw [chebotarevErrorSlack_iff_residual_le]
  constructor
  · rintro ⟨_, _, hres⟩
    exact countResidual_le_iff_effective.mp hres
  · intro h
    exact ⟨hC, hcZ, countResidual_le_iff_effective.mpr h⟩

/-- The canonical residual is the tight witness: any error that controls the
absolute deviation also controls `countResidual`. -/
theorem countResidual_le_of_close {count main err : ℕ → ℝ}
    (hclose : ∀ n, |count n - main n| ≤ err n) (n : ℕ) :
    countResidual count main n ≤ err n :=
  hclose n

/-- The canonical residual is bounded by every slack witness. -/
theorem countResidual_le_of_exists_err {C cZ : ℝ}
    {x degree count main : ℕ → ℝ}
    (E : ChebotarevErrorSlack C cZ x degree count main) (n : ℕ) :
    countResidual count main n ≤ lagariasOdlyzkoError C cZ x degree n := by
  obtain ⟨err, _herr_nonneg, herr_le, hclose⟩ := E.exists_err
  exact (hclose n).trans (herr_le n)

/-! ## 2. The one-sided bounds and the effective envelope -/

/-- The lower side of the count is the lower half of the absolute-value
envelope. -/
theorem lower_iff_residual_lower {count main error : ℕ → ℝ} :
    ChebotarevLowerBound count main error ↔
      ∀ n, main n - error n ≤ count n :=
  Iff.rfl

/-- The upper side of the count is the upper half of the absolute-value
envelope. -/
theorem upper_iff_residual_upper {count main error : ℕ → ℝ} :
    ChebotarevUpperBound count main error ↔
      ∀ n, count n ≤ main n + error n :=
  Iff.rfl

/-- The lower side in additive-residual form. -/
theorem lower_iff_residual_lower_add {count main error : ℕ → ℝ} :
    ChebotarevLowerBound count main error ↔
      ∀ n, -error n ≤ count n - main n := by
  constructor <;> intro h n <;> linarith [h n]

/-- The upper side in additive-residual form. -/
theorem upper_iff_residual_upper_add {count main error : ℕ → ℝ} :
    ChebotarevUpperBound count main error ↔
      ∀ n, count n - main n ≤ error n := by
  constructor <;> intro h n <;> linarith [h n]

/-- **The effective envelope is exactly the conjunction of the two one-sided
bounds.**  This is the two-sided form of `chebotarevSides_iff_effective`,
written so that each half is visible. -/
theorem effective_iff_sides {count main error : ℕ → ℝ} :
    EffectiveChebotarev count main error ↔
      ChebotarevLowerBound count main error ∧
        ChebotarevUpperBound count main error := by
  constructor
  · intro h
    exact ⟨chebotarevLowerBound_of_effective h,
      chebotarevUpperBound_of_effective h⟩
  · rintro ⟨hlow, hhigh⟩
    exact effectiveChebotarev_of_sides hlow hhigh

/-- The effective envelope gives the lower side. -/
theorem lower_of_effective {count main error : ℕ → ℝ}
    (h : EffectiveChebotarev count main error) :
    ChebotarevLowerBound count main error :=
  chebotarevLowerBound_of_effective h

/-- The effective envelope gives the upper side. -/
theorem upper_of_effective {count main error : ℕ → ℝ}
    (h : EffectiveChebotarev count main error) :
    ChebotarevUpperBound count main error :=
  chebotarevUpperBound_of_effective h

/-- The two sides rebuild the effective envelope. -/
theorem effective_of_sides {count main error : ℕ → ℝ}
    (hlow : ChebotarevLowerBound count main error)
    (hhigh : ChebotarevUpperBound count main error) :
    EffectiveChebotarev count main error :=
  effectiveChebotarev_of_sides hlow hhigh

/-- The effective profile gives both sides at once. -/
theorem sides_of_effective {count main error : ℕ → ℝ}
    (h : EffectiveChebotarev count main error) :
    ChebotarevSides count main error :=
  chebotarevSides_of_effective h

/-- The slack error gives both sides for the explicit envelope. -/
theorem sides_of_slack {C cZ : ℝ} {x degree count main : ℕ → ℝ}
    (E : ChebotarevErrorSlack C cZ x degree count main) :
    ChebotarevSides count main (lagariasOdlyzkoError C cZ x degree) :=
  ⟨ChebotarevErrorSlack.lower E, ChebotarevErrorSlack.upper E⟩

/-- **The effective envelope gives the slack bundle.**  This is the converse
of `chebotarevErrorSlack_iff_effective`: once the count satisfies the exact
envelope, the slack residual can be taken to be the envelope itself. -/
theorem chebotarevErrorSlack_of_effective {C cZ : ℝ} (hC : 0 < C) (hcZ : 0 < cZ)
    {x degree count main : ℕ → ℝ} (hx : ∀ n, 0 ≤ x n)
    (h : EffectiveChebotarev count main (lagariasOdlyzkoError C cZ x degree)) :
    ChebotarevErrorSlack C cZ x degree count main :=
  ChebotarevErrorSlack.ofExact hC hcZ hx h

/-- A slack error transfers to an arbitrary larger envelope.  This is the
one-sided absorption of the residual `err` into the envelope. -/
theorem lower_of_slack_of_le {C cZ : ℝ} {x degree count main : ℕ → ℝ}
    (E : ChebotarevErrorSlack C cZ x degree count main)
    {err : ℕ → ℝ}
    (hle : ∀ n, lagariasOdlyzkoError C cZ x degree n ≤ err n) :
    ChebotarevLowerBound count main err := by
  obtain ⟨e, _he_nonneg, he_le, hclose⟩ := E.exists_err
  intro n
  have hlow := (abs_le.mp (hclose n)).1
  linarith [hlow, he_le n, hle n]

/-- A slack error transfers to an arbitrary larger envelope, upper side. -/
theorem upper_of_slack_of_le {C cZ : ℝ} {x degree count main : ℕ → ℝ}
    (E : ChebotarevErrorSlack C cZ x degree count main)
    {err : ℕ → ℝ}
    (hle : ∀ n, lagariasOdlyzkoError C cZ x degree n ≤ err n) :
    ChebotarevUpperBound count main err := by
  obtain ⟨e, _he_nonneg, he_le, hclose⟩ := E.exists_err
  intro n
  have hhigh := (abs_le.mp (hclose n)).2
  linarith [hhigh, he_le n, hle n]

/-- A slack error transfers to two-sided sides for any larger envelope. -/
theorem sides_of_slack_of_le {C cZ : ℝ} {x degree count main : ℕ → ℝ}
    (E : ChebotarevErrorSlack C cZ x degree count main)
    {err : ℕ → ℝ}
    (hle : ∀ n, lagariasOdlyzkoError C cZ x degree n ≤ err n) :
    ChebotarevSides count main err :=
  ⟨lower_of_slack_of_le E hle, upper_of_slack_of_le E hle⟩

/-! ## 3. The log-integral bracket and the one-sided count -/

/-- The bracket term is positive when `cbr`, `x`, `F` and `T` are positive. -/
theorem bracketTerm_pos {cbr : ℝ} {x F T : ℕ → ℝ}
    (hcbr : 0 < cbr) (hx : ∀ n, 0 < x n) (hF : ∀ n, 0 < F n)
    (hT : ∀ n, 0 < T n) (n : ℕ) :
    0 < bracketTerm cbr x F T n := by
  unfold bracketTerm
  exact div_pos (mul_pos hcbr (hx n)) (mul_pos (hF n) (pow_pos (hT n) 6))

/-- **The main term minus the error contains one quarter of the bracket.**
The bracket is at most the log-integral gap, while the error is at most one
eighth of the bracket; hence `bracket/4 ≤ gap/2 - error`. -/
theorem bracketQuarter_le_main_sub_error {cbr : ℝ}
    {x F T liX liBeta0 error : ℕ → ℝ}
    (hbracket : LogIntegralBracket cbr x F T liX liBeta0)
    (hnegl : ChebotarevErrorNegligible cbr x F T error)
    (hx : ∀ n, 0 < x n) (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n)
    (n : ℕ) :
    bracketTerm (cbr / 4) x F T n ≤ mainOf liX liBeta0 n - error n := by
  let B := bracketTerm cbr x F T n
  have hBpos : 0 < B := bracketTerm_pos hbracket.1 hx hF hT n
  have hBle : B ≤ liX n - liBeta0 n := hbracket.2 n
  have herr : error n ≤ B / 8 := by
    have h8 : bracketTerm (cbr / 8) x F T n = B / 8 := by
      unfold B bracketTerm
      ring
    simpa [h8] using hnegl n
  have hquarter : bracketTerm (cbr / 4) x F T n = B / 4 := by
    unfold B bracketTerm
    ring
  have hgap0 : 0 ≤ liX n - liBeta0 n := le_trans hBpos.le hBle
  have herrGap : error n ≤ (liX n - liBeta0 n) / 8 := by linarith
  have hB4 : B / 4 ≤ (liX n - liBeta0 n) / 4 := by linarith
  have hgap4 : (liX n - liBeta0 n) / 4 ≤
      (1 / 2 : ℝ) * (liX n - liBeta0 n) - error n := by linarith
  rw [mainOf, hquarter]
  exact hB4.trans hgap4

/-- **The lower side of the count contains one quarter of the bracket.**
Only the lower Chebotarev inequality is used. -/
theorem count_lower_of_bracket {cbr : ℝ}
    {x F T count liX liBeta0 error : ℕ → ℝ}
    (hbracket : LogIntegralBracket cbr x F T liX liBeta0)
    (hnegl : ChebotarevErrorNegligible cbr x F T error)
    (hlower : ChebotarevLowerBound count (mainOf liX liBeta0) error)
    (hx : ∀ n, 0 < x n) (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n)
    (n : ℕ) :
    bracketTerm (cbr / 4) x F T n ≤ count n :=
  (bracketQuarter_le_main_sub_error hbracket hnegl hx hF hT n).trans
    (hlower n)

/-- **The one-sided lower bound from the effective error envelope.**  The
absolute-value hypothesis `EffectiveChebotarev` is used only through its lower
half. -/
theorem count_lower_of_bracket_of_effective {cbr : ℝ}
    {x F T count liX liBeta0 error : ℕ → ℝ}
    (hbracket : LogIntegralBracket cbr x F T liX liBeta0)
    (hnegl : ChebotarevErrorNegligible cbr x F T error)
    (hcheb : EffectiveChebotarev count (mainOf liX liBeta0) error)
    (hx : ∀ n, 0 < x n) (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n)
    (n : ℕ) :
    bracketTerm (cbr / 4) x F T n ≤ count n :=
  count_lower_of_bracket hbracket hnegl
    (chebotarevLowerBound_of_effective hcheb) hx hF hT n

/-- **The one-sided lower bound from a slack error.** -/
theorem count_lower_of_bracket_of_slack {C cZ cbr : ℝ}
    {x F T count liX liBeta0 : ℕ → ℝ}
    (hbracket : LogIntegralBracket cbr x F T liX liBeta0)
    (hnegl : ChebotarevErrorNegligible cbr x F T
      (lagariasOdlyzkoError C cZ x degree))
    (E : ChebotarevErrorSlack C cZ x degree count (mainOf liX liBeta0))
    (hx : ∀ n, 0 < x n) (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n)
    (n : ℕ) :
    bracketTerm (cbr / 4) x F T n ≤ count n :=
  count_lower_of_bracket hbracket hnegl
    (ChebotarevErrorSlack.lower E) hx hF hT n

/-- **The lower bound propagates to the inert count.** -/
theorem inert_lower_of_bracket {cbr : ℝ}
    {x F T count inertCount liX liBeta0 error : ℕ → ℝ}
    (hbracket : LogIntegralBracket cbr x F T liX liBeta0)
    (hnegl : ChebotarevErrorNegligible cbr x F T error)
    (hlower : ChebotarevLowerBound count (mainOf liX liBeta0) error)
    (hge : ∀ n, count n ≤ inertCount n)
    (hx : ∀ n, 0 < x n) (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n)
    (n : ℕ) :
    bracketTerm (cbr / 4) x F T n ≤ inertCount n :=
  (count_lower_of_bracket hbracket hnegl hlower hx hF hT n).trans (hge n)

/-- The upper side gives the complementary (weaker) bracket consequence
`count ≤ Li x - Li x^{β₀}`.  This is recorded for completeness; the ledger
does not use it. -/
theorem count_upper_of_bracket {cbr : ℝ}
    {x F T count liX liBeta0 error : ℕ → ℝ}
    (hbracket : LogIntegralBracket cbr x F T liX liBeta0)
    (hnegl : ChebotarevErrorNegligible cbr x F T error)
    (hupper : ChebotarevUpperBound count (mainOf liX liBeta0) error)
    (hx : ∀ n, 0 < x n) (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n)
    (n : ℕ) :
    count n ≤ liX n - liBeta0 n := by
  let B := bracketTerm cbr x F T n
  have hBpos : 0 < B := bracketTerm_pos hbracket.1 hx hF hT n
  have hBle : B ≤ liX n - liBeta0 n := hbracket.2 n
  have herr : error n ≤ B / 8 := by
    have h8 : bracketTerm (cbr / 8) x F T n = B / 8 := by
      unfold B bracketTerm
      ring
    simpa [h8] using hnegl n
  have hgap0 : 0 ≤ liX n - liBeta0 n := le_trans hBpos.le hBle
  have herrGap : error n ≤ (liX n - liBeta0 n) / 8 := by linarith
  have hmain : mainOf liX liBeta0 n = (1 / 2 : ℝ) * (liX n - liBeta0 n) := rfl
  have hu := hupper n
  rw [hmain] at hu
  linarith [hu]

/-! ## 4. The one-sided bundles -/

/-- **The one-sided Chebotarev input.**  This is the smallest count input: the
lower side of the count against the explicit envelope, with the two positivity
constants.  There is no upper side and no existential residual. -/
structure ChebotarevLowerInput (C cZ : ℝ) (x degree : ℕ → ℝ)
    (count liX liBeta0 : ℕ → ℝ) : Prop where
  /-- The error constant is positive. -/
  C_pos : 0 < C
  /-- The error exponent is positive. -/
  cZ_pos : 0 < cZ
  /-- `main - error ≤ count`. -/
  lower : ChebotarevLowerBound count (mainOf liX liBeta0)
    (lagariasOdlyzkoError C cZ x degree)

/-- The one-sided input is the lower half of `ChebotarevSides`. -/
theorem ChebotarevLowerInput.ofSides {C cZ : ℝ} {x degree count liX liBeta0 : ℕ → ℝ}
    (hC : 0 < C) (hcZ : 0 < cZ)
    (S : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    ChebotarevLowerInput C cZ x degree count liX liBeta0 where
  C_pos := hC
  cZ_pos := hcZ
  lower := S.lower

/-- Adding the upper side rebuilds the two-sided structure. -/
theorem ChebotarevLowerInput.toSides {C cZ : ℝ} {x degree count liX liBeta0 : ℕ → ℝ}
    (L : ChebotarevLowerInput C cZ x degree count liX liBeta0)
    (upper : ChebotarevUpperBound count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree) where
  lower := L.lower
  upper := upper

/-- Adding the upper side rebuilds the two-sided count input. -/
theorem ChebotarevLowerInput.toChebotarevCountInput {C cZ : ℝ}
    {x degree count liX liBeta0 : ℕ → ℝ}
    (L : ChebotarevLowerInput C cZ x degree count liX liBeta0)
    (upper : ChebotarevUpperBound count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    ChebotarevCountInput C cZ x degree count liX liBeta0 where
  C_pos := L.C_pos
  cZ_pos := L.cZ_pos
  lower := L.lower
  upper := upper

/-- The two-sided count input drops to the one-sided input. -/
theorem ChebotarevLowerInput.ofCountInput {C cZ : ℝ}
    {x degree count liX liBeta0 : ℕ → ℝ}
    (Q : ChebotarevCountInput C cZ x degree count liX liBeta0) :
    ChebotarevLowerInput C cZ x degree count liX liBeta0 where
  C_pos := Q.C_pos
  cZ_pos := Q.cZ_pos
  lower := Q.lower

/-- A slack error also gives the one-sided input. -/
theorem ChebotarevLowerInput.ofSlack {C cZ : ℝ}
    {x degree count liX liBeta0 : ℕ → ℝ}
    (E : ChebotarevErrorSlack C cZ x degree count (mainOf liX liBeta0)) :
    ChebotarevLowerInput C cZ x degree count liX liBeta0 where
  C_pos := E.C_pos
  cZ_pos := E.cZ_pos
  lower := ChebotarevErrorSlack.lower E

/-- **The reduced Dedekind/Stark/Chebotarev inputs with a one-sided count.**
This is `DedekindAnalyticInputs` with the two-sided `ChebotarevCountInput`
replaced by `ChebotarevLowerInput`. -/
structure DedekindSidesInputs
    (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ)
    (F : ℕ → ℝ) (K : ℝ) (x degree : ℕ → ℝ)
    (C cZ : ℝ) (count : ℕ → ℝ) (liX liBeta0 : ℕ → ℝ) : Prop where
  /-- The Dedekind zero-free region in its smallest form. -/
  zeroFree : DedekindZeroFreeInput beta0 zeroRealPart cz discLog
  /-- Stark's exceptional-zero gap. -/
  stark : StarkInput beta0 F discLog
  /-- The Lagarias–Odlyzko range inequality. -/
  range : ChebotarevRangeInput K x degree discLog
  /-- The cumulative Chebotarev count, one-sided. -/
  cheb : ChebotarevLowerInput C cZ x degree count liX liBeta0

/-- The two-sided bundle drops to the one-sided bundle. -/
theorem DedekindAnalyticInputs.toDedekindSidesInputs
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0) :
    DedekindSidesInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 where
  zeroFree := A.zeroFree
  stark := A.stark
  range := A.range
  cheb := ChebotarevLowerInput.ofCountInput A.cheb

/-- Adding the upper side rebuilds the two-sided bundle. -/
theorem DedekindSidesInputs.toDedekindAnalyticInputs
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (B : DedekindSidesInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0)
    (upper : ChebotarevUpperBound count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0 where
  zeroFree := B.zeroFree
  stark := B.stark
  range := B.range
  cheb := B.cheb.toChebotarevCountInput upper

/-- A slack Chebotarev error gives the one-sided bundle. -/
theorem DedekindSidesInputs.ofSlack
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (Z : DedekindZeroFreeInput beta0 zeroRealPart cz discLog)
    (St : StarkInput beta0 F discLog)
    (R : ChebotarevRangeInput K x degree discLog)
    (E : ChebotarevErrorSlack C cZ x degree count (mainOf liX liBeta0)) :
    DedekindSidesInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 where
  zeroFree := Z
  stark := St
  range := R
  cheb := ChebotarevLowerInput.ofSlack E

/-- The one-sided bundle gives the lower side of the cumulative count. -/
theorem DedekindSidesInputs.chebotarevLowerBound
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (B : DedekindSidesInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0) :
    ChebotarevLowerBound count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree) :=
  B.cheb.lower

/-! ## 5. The one-sided L34 core -/

/-- **`L34DedekindCore` with only the one-sided Chebotarev input.**  Every
field except `dedekind` is copied from `L34DedekindCore`; the analytic bundle
`dedekind` is replaced by `DedekindSidesInputs`, which keeps only the lower
side of the count. -/
structure L34SidesCore where
  /-- The Chebotarev cutoff `x`. -/
  x : ℕ → ℝ
  /-- The absolute degree `2d` of `E = K(√γ)`. -/
  degree : ℕ → ℝ
  /-- `log |Δ_E|`. -/
  discLog : ℕ → ℝ
  /-- The factorial factor `F = (2d)!`. -/
  F : ℕ → ℝ
  /-- The polynomial input parameter `T`. -/
  T : ℕ → ℝ
  /-- The class-group logarithm `h*`. -/
  hstar : ℕ → ℝ
  /-- The compressed bit length `m = h* + 7`. -/
  m : ℕ → ℝ
  /-- The number of probes `R`. -/
  R : ℕ → ℕ
  /-- The number of nonrational classes. -/
  classCount : ℕ → ℝ
  /-- The per-trial detection probability. -/
  pTrial : ℕ → ℝ
  /-- The possible exceptional real zero `β₀`. -/
  beta0 : ℕ → ℝ
  /-- The real part of a generic zero of `ζ_E`. -/
  zeroRealPart : ℕ → ℝ
  /-- A cumulative Chebotarev count. -/
  count : ℕ → ℝ
  /-- The cumulative inert count. -/
  inertCount : ℕ → ℝ
  /-- The degree-one inert count after discarding small / higher-degree ideals. -/
  degreeOneInert : ℕ → ℝ
  /-- `Li x`. -/
  liX : ℕ → ℝ
  /-- `Li x^{β₀}`. -/
  liBeta0 : ℕ → ℝ
  /-- The range constant. -/
  K : ℝ
  /-- The constant `C` in the effective error. -/
  C : ℝ
  /-- The constant `c` in the effective error. -/
  cZ : ℝ
  /-- The zero-free-region constant `c_z`. -/
  cz : ℝ
  /-- The bracket constant. -/
  cbr : ℝ
  /-- The per-ideal selection constant. -/
  csel : ℝ
  /-- The polynomial constant in `h* ≤ Ch T³`. -/
  Ch : ℝ
  /-- The cutoff is positive. -/
  x_pos : ∀ n, 0 < x n
  /-- The extension degree is positive. -/
  degree_pos : ∀ n, 0 < degree n
  /-- The discriminant logarithm is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- The factorial factor is positive. -/
  F_pos : ∀ n, 0 < F n
  /-- The polynomial parameter is positive. -/
  T_pos : ∀ n, 0 < T n
  /-- The polynomial parameter is at least one. -/
  T_ge_one : ∀ n, 1 ≤ T n
  /-- There is at least one nonrational class. -/
  classCount_pos : ∀ n, 0 < classCount n
  /-- The per-trial probability is nonnegative. -/
  pTrial_nonneg : ∀ n, 0 ≤ pTrial n
  /-- The per-trial probability is at most one. -/
  pTrial_le_one : ∀ n, pTrial n ≤ 1
  /-- The actual failure probability of the probe stage. -/
  actualMiss : ℕ → ℝ
  /-- The actual failure probability is nonnegative. -/
  actualMiss_nonneg : ∀ n, 0 ≤ actualMiss n
  /-- The probe union bound. -/
  union_bound : ProbeMissUnionBound actualMiss pTrial classCount R
  /-- The degree is bounded by the polynomial parameter. -/
  degree_le_T : ∀ n, degree n ≤ T n
  /-- **The one-sided analytic bundle.** -/
  sides : DedekindSidesInputs beta0 zeroRealPart cz discLog F K x degree
    C cZ count liX liBeta0
  /-- The inert count contains the counted nonidentity class. -/
  inert_ge_count : ∀ n, count n ≤ inertCount n
  /-- Stark's bound converted to the dyadic bracket. -/
  bracket : LogIntegralBracket cbr x F T liX liBeta0
  /-- The Chebotarev error is negligible against the bracket. -/
  error_negligible : ChebotarevErrorNegligible cbr x F T
    (lagariasOdlyzkoError C cZ x degree)
  /-- Discarding small / higher-degree ideals is negligible. -/
  degree_one_loss : DegreeOneLossNegligible cbr x degree F T
  /-- The degree-one reduction. -/
  degree_one_reduction : DegreeOneInertReduction inertCount degreeOneInert degree x
  /-- Probe selection at `1/(d x)` per eligible ideal. -/
  selection : ProbeSelectionLowerBound csel x degree degreeOneInert pTrial
  /-- The paper's budget `R = F T¹⁰`. -/
  budget : ProbeBudget R F T
  /-- Lemma E.2: at most `2^{h*}` nonrational classes. -/
  class_le : ClassCountBound classCount hstar
  /-- The polynomial bound `h* = O(T³)`. -/
  hstar_poly : ClassCountPolynomial Ch hstar T
  /-- The mask-compression bit budget. -/
  mask_bits : MaskCompressionBits hstar m
  /-- The probe constant beats the class-count entropy constant. -/
  constant_margin : Ch * Real.log 2 < csel * cbr / 4
  /-- The probe exponent `T³` eventually dominates the ledger scale. -/
  scale_cubic : ∀ᶠ n : ℕ in atTop,
    2 * scale n ≤ (csel * cbr / 4 - Ch * Real.log 2) * T n ^ 3

namespace L34SidesCore

/-- The L34 loss charged to the C5 ledger, exactly as in `L34DedekindCore`. -/
noncomputable def loss (S : L34SidesCore) : ℕ → ℝ :=
  excessLoss S.actualMiss (maskFailure S.hstar S.m) allowedFailure

/-- The loss is nonnegative. -/
theorem loss_nonneg (S : L34SidesCore) (n : ℕ) : 0 ≤ S.loss n := by
  unfold loss excessLoss
  exact le_max_left 0 _

/-- The compressed mask failure is at most `2^{-7} = 1/128`. -/
theorem maskFailure_le_allowed (S : L34SidesCore) (n : ℕ) :
    maskFailure S.hstar S.m n ≤ 1 / 128 := by
  have hbits : S.hstar n - S.m n ≤ (-7 : ℝ) := by
    have := S.mask_bits n
    linarith
  calc
    maskFailure S.hstar S.m n = (2 : ℝ) ^ (S.hstar n - S.m n) := rfl
    _ ≤ (2 : ℝ) ^ (-7 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hbits
    _ = 1 / 128 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

/-- The mask failure is nonnegative. -/
theorem maskFailure_nonneg (S : L34SidesCore) (n : ℕ) :
    0 ≤ maskFailure S.hstar S.m n := by
  unfold maskFailure
  exact Real.rpow_nonneg (by norm_num) _

/-- The probe miss is nonnegative. -/
theorem probeMiss_nonneg (S : L34SidesCore) (n : ℕ) :
    0 ≤ probeMiss S.classCount S.pTrial S.R n := by
  unfold probeMiss
  exact mul_nonneg (S.classCount_pos n).le (Real.exp_pos _).le

/-- The actual miss is at most the probe miss (the union bound in exponential
form). -/
theorem actualMiss_le_probeMiss (S : L34SidesCore) (n : ℕ) :
    S.actualMiss n ≤ probeMiss S.classCount S.pTrial S.R n := by
  have hpow := one_sub_pow_le_exp_neg (S.pTrial n) (S.pTrial_nonneg n)
    (S.pTrial_le_one n) (S.R n)
  calc
    S.actualMiss n ≤ S.classCount n * (1 - S.pTrial n) ^ (S.R n) :=
      S.union_bound n
    _ ≤ S.classCount n * Real.exp (-((S.R n : ℝ) * S.pTrial n)) :=
      mul_le_mul_of_nonneg_left hpow (S.classCount_pos n).le
    _ = probeMiss S.classCount S.pTrial S.R n := rfl

/-- The loss is at most the probe miss. -/
theorem loss_le_probeMiss (S : L34SidesCore) (n : ℕ) :
    S.loss n ≤ probeMiss S.classCount S.pTrial S.R n := by
  have hmask := S.maskFailure_le_allowed n
  have hprobe := S.probeMiss_nonneg n
  have hactual := S.actualMiss_le_probeMiss n
  unfold loss excessLoss allowedFailure
  apply max_le hprobe
  linarith

/-- The lower side of the Chebotarev count gives the cumulative inert lower
bound.  This is the point where the upper side would have been used by the
two-sided route; here only `sides.cheb.lower` is consumed. -/
theorem inert_lower (S : L34SidesCore) (n : ℕ) :
    (1 / 2) * (S.liX n - S.liBeta0 n) -
        lagariasOdlyzkoError S.C S.cZ S.x S.degree n ≤ S.inertCount n := by
  have hlower := S.sides.cheb.lower n
  have hge := S.inert_ge_count n
  unfold mainOf at hlower
  linarith

/-- **The L34 probe-miss bound from the one-sided count.**  This is
`probeMiss_le_exp_of_paper_props` with `hinert` supplied by the lower side and
`inert_ge_count`; no upper Chebotarev side appears. -/
theorem probeMiss_le_ledger (S : L34SidesCore) :
    ∀ᶠ n : ℕ in atTop,
      probeMiss S.classCount S.pTrial S.R n ≤ exp (-(2 : ℝ) * scale n) := by
  refine probeMiss_le_exp_of_paper_props S.budget S.bracket S.error_negligible
    S.degree_one_loss S.degree_one_reduction ?_ S.selection S.x_pos S.degree_pos
    S.F_pos S.T_ge_one S.degree_le_T S.class_le S.hstar_poly S.classCount_pos
    S.constant_margin S.scale_cubic
  intro n
  exact S.inert_lower n

/-- **The L34 ledger slot from the one-sided count.** -/
theorem loss_le_ledger (S : L34SidesCore) :
    ∀ᶠ n : ℕ in atTop, S.loss n ≤ exp (-(2 : ℝ) * scale n) := by
  filter_upwards [S.probeMiss_le_ledger] with n hprobe
  exact (S.loss_le_probeMiss n).trans hprobe

/-- The manuscript's slower `exp (-H / log H)` rate, from the one-sided
count. -/
theorem loss_le_paper (S : L34SidesCore) :
    ∀ᶠ n : ℕ in atTop, S.loss n ≤ exp (-(1 * paperRate n)) := by
  filter_upwards [S.loss_le_ledger, scale_grows.eventually_ge_atTop (Real.exp 1)]
    with n hledger hs
  have hs0 : 0 < scale n := lt_of_lt_of_le (Real.exp_pos 1) hs
  have hlog1 : 1 ≤ Real.log (scale n) := by
    have h := Real.log_le_log (Real.exp_pos 1) hs
    simpa [Real.log_exp] using h
  have hlogpos : 0 < Real.log (scale n) := lt_of_lt_of_le zero_lt_one hlog1
  have hrate : paperRate n ≤ 2 * scale n := by
    unfold paperRate
    rw [div_le_iff₀ hlogpos]
    nlinarith [hs0, hlog1]
  exact hledger.trans (Real.exp_le_exp.mpr (by nlinarith))

/-- The literal `RatedLeaf` of the one-sided core. -/
noncomputable def ratedLeaf (S : L34SidesCore) :
    Cogentic.RandomizedPaperLeafStatements.RatedLeaf where
  loss := S.loss
  loss_nonneg := S.loss_nonneg
  rate := paperRate
  c := 1
  c_pos := by norm_num
  paper := S.loss_le_paper
  ledger := S.loss_le_ledger

/-- The leaf's ledger slot is the proved one-sided ledger. -/
theorem ratedLeaf_slot (S : L34SidesCore) :
    ∀ᶠ n : ℕ in atTop, S.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.ratedLeaf.slot

/-- **Rebuild the old core when the upper side is supplied.**  This proves
that dropping the upper side loses nothing: the one-sided core plus the upper
Chebotarev inequality is exactly the old two-sided core. -/
def toL34DedekindCore_of_upper (S : L34SidesCore)
    (upper : ChebotarevUpperBound S.count (mainOf S.liX S.liBeta0)
      (lagariasOdlyzkoError S.C S.cZ S.x S.degree)) : L34DedekindCore where
  x := S.x
  degree := S.degree
  discLog := S.discLog
  F := S.F
  T := S.T
  hstar := S.hstar
  m := S.m
  R := S.R
  classCount := S.classCount
  pTrial := S.pTrial
  beta0 := S.beta0
  zeroRealPart := S.zeroRealPart
  count := S.count
  inertCount := S.inertCount
  degreeOneInert := S.degreeOneInert
  liX := S.liX
  liBeta0 := S.liBeta0
  K := S.K
  C := S.C
  cZ := S.cZ
  cz := S.cz
  cbr := S.cbr
  csel := S.csel
  Ch := S.Ch
  x_pos := S.x_pos
  degree_pos := S.degree_pos
  discLog_pos := S.discLog_pos
  F_pos := S.F_pos
  T_pos := S.T_pos
  T_ge_one := S.T_ge_one
  classCount_pos := S.classCount_pos
  pTrial_nonneg := S.pTrial_nonneg
  pTrial_le_one := S.pTrial_le_one
  actualMiss := S.actualMiss
  actualMiss_nonneg := S.actualMiss_nonneg
  union_bound := S.union_bound
  degree_le_T := S.degree_le_T
  dedekind := S.sides.toDedekindAnalyticInputs upper
  inert_ge_count := S.inert_ge_count
  bracket := S.bracket
  error_negligible := S.error_negligible
  degree_one_loss := S.degree_one_loss
  degree_one_reduction := S.degree_one_reduction
  selection := S.selection
  budget := S.budget
  class_le := S.class_le
  hstar_poly := S.hstar_poly
  mask_bits := S.mask_bits
  constant_margin := S.constant_margin
  scale_cubic := S.scale_cubic

/-- Every old two-sided core yields a one-sided core by forgetting the upper
side. -/
def ofL34DedekindCore (S : L34DedekindCore) : L34SidesCore where
  x := S.x
  degree := S.degree
  discLog := S.discLog
  F := S.F
  T := S.T
  hstar := S.hstar
  m := S.m
  R := S.R
  classCount := S.classCount
  pTrial := S.pTrial
  beta0 := S.beta0
  zeroRealPart := S.zeroRealPart
  count := S.count
  inertCount := S.inertCount
  degreeOneInert := S.degreeOneInert
  liX := S.liX
  liBeta0 := S.liBeta0
  K := S.K
  C := S.C
  cZ := S.cZ
  cz := S.cz
  cbr := S.cbr
  csel := S.csel
  Ch := S.Ch
  x_pos := S.x_pos
  degree_pos := S.degree_pos
  discLog_pos := S.discLog_pos
  F_pos := S.F_pos
  T_pos := S.T_pos
  T_ge_one := S.T_ge_one
  classCount_pos := S.classCount_pos
  pTrial_nonneg := S.pTrial_nonneg
  pTrial_le_one := S.pTrial_le_one
  actualMiss := S.actualMiss
  actualMiss_nonneg := S.actualMiss_nonneg
  union_bound := S.union_bound
  degree_le_T := S.degree_le_T
  sides := DedekindAnalyticInputs.toDedekindSidesInputs S.dedekind
  inert_ge_count := S.inert_ge_count
  bracket := S.bracket
  error_negligible := S.error_negligible
  degree_one_loss := S.degree_one_loss
  degree_one_reduction := S.degree_one_reduction
  selection := S.selection
  budget := S.budget
  class_le := S.class_le
  hstar_poly := S.hstar_poly
  mask_bits := S.mask_bits
  constant_margin := S.constant_margin
  scale_cubic := S.scale_cubic

/-- The ledger slot of the rebuilt old core is the one-sided ledger.  This
records that the upper side never enters the ledger estimate. -/
theorem toCore_probeMiss_le_ledger (S : L34SidesCore)
    (upper : ChebotarevUpperBound S.count (mainOf S.liX S.liBeta0)
      (lagariasOdlyzkoError S.C S.cZ S.x S.degree)) :
    ∀ᶠ n : ℕ in atTop,
      probeMiss S.classCount S.pTrial S.R n ≤ exp (-(2 : ℝ) * scale n) :=
  (S.toL34DedekindCore_of_upper upper).toL34AnalyticCore.probeMiss_le_ledger

end L34SidesCore

/-! ## Axiom audit -/

#print axioms countResidual_nonneg
#print axioms countResidual_le_iff_effective
#print axioms chebotarevErrorSlack_iff_residual_le
#print axioms chebotarevErrorSlack_iff_effective
#print axioms countResidual_le_of_close
#print axioms countResidual_le_of_exists_err
#print axioms lower_iff_residual_lower
#print axioms upper_iff_residual_upper
#print axioms lower_iff_residual_lower_add
#print axioms upper_iff_residual_upper_add
#print axioms effective_iff_sides
#print axioms lower_of_effective
#print axioms upper_of_effective
#print axioms effective_of_sides
#print axioms sides_of_effective
#print axioms sides_of_slack
#print axioms chebotarevErrorSlack_of_effective
#print axioms lower_of_slack_of_le
#print axioms upper_of_slack_of_le
#print axioms sides_of_slack_of_le
#print axioms bracketTerm_pos
#print axioms bracketQuarter_le_main_sub_error
#print axioms count_lower_of_bracket
#print axioms count_lower_of_bracket_of_effective
#print axioms count_lower_of_bracket_of_slack
#print axioms inert_lower_of_bracket
#print axioms count_upper_of_bracket
#print axioms ChebotarevLowerInput.ofSides
#print axioms ChebotarevLowerInput.toSides
#print axioms ChebotarevLowerInput.toChebotarevCountInput
#print axioms ChebotarevLowerInput.ofCountInput
#print axioms ChebotarevLowerInput.ofSlack
#print axioms DedekindAnalyticInputs.toDedekindSidesInputs
#print axioms DedekindSidesInputs.toDedekindAnalyticInputs
#print axioms DedekindSidesInputs.ofSlack
#print axioms DedekindSidesInputs.chebotarevLowerBound
#print axioms L34SidesCore.loss_nonneg
#print axioms L34SidesCore.maskFailure_le_allowed
#print axioms L34SidesCore.maskFailure_nonneg
#print axioms L34SidesCore.probeMiss_nonneg
#print axioms L34SidesCore.actualMiss_le_probeMiss
#print axioms L34SidesCore.loss_le_probeMiss
#print axioms L34SidesCore.inert_lower
#print axioms L34SidesCore.probeMiss_le_ledger
#print axioms L34SidesCore.loss_le_ledger
#print axioms L34SidesCore.loss_le_paper
#print axioms L34SidesCore.ratedLeaf
#print axioms L34SidesCore.ratedLeaf_slot
#print axioms L34SidesCore.toL34DedekindCore_of_upper
#print axioms L34SidesCore.ofL34DedekindCore
#print axioms L34SidesCore.toCore_probeMiss_le_ledger

end

end Cogentic.RandomizedL34Sides
