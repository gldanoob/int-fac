import Cogentic.RandomizedL30Younis

/-!
# L30: the raw analytic layer

`Cogentic/RandomizedL30Younis.lean` reduces KeyBreak Proposition H.3 to the
structure `YounisLPPInputs`, whose two analytic halves are

* `YounisOddRelativeShortInterval A` plus `YounisOddGlobalLower B`, which
  together give `YounisOddCentralCount` and hence `YounisShortIntervalCount`;
* `LPPRawModelCount` plus `LPPNormalization`, which together give
  `LPPOrderFibreCount`.

This file pushes the second half one layer further down and records the
resulting smallest explicit LPP input.

## The LPP loss

`LPPNormalization p t err Q` is not an analytic theorem: it is the elementary
statement that the polylogarithmic loss `Q` is dominated by
`p · exp ((1 + ε) t_p)`.  The paper's loss is a fixed power of `log p`; this
file fixes the explicit choice

`lppLogLoss p n = log (p n) + 1`.

For `p ≥ 2`, `log p + 1 ≤ p` (from `log x ≤ x - 1`), so the normalization is
proved outright for this `Q`, with no analytic input and no zero count:

* `lppNormalization_logLoss : LPPNormalization p t err (lppLogLoss p)`.

The only remaining LPP analytic statement is therefore the raw model count
with this explicit loss,

* `LPPRawLogModelCount p t err fibreModels =
     LPPRawModelCount p t err fibreModels (lppLogLoss p)`,

which is `|fibreModels n m| ≥ p^{9/2} / (log p + 1)` on the eligible orders.
`lppOrderFibreCount_of_rawLog` performs the normalization arithmetic and
produces the paper's `p^{7/2} exp (-(1+ε) t_p)` per-order count.

## The canonical loss and the reduction from the existing fibre count

If one is willing to let the loss be as large as the whole normalization
budget, `Q = p · exp ((1+ε) t_p)`, then the raw count and the normalization are
*equivalent* to the already formalised per-order count:

* `lppNormalization_canonical` proves the normalization by reflexivity;
* `lppRawModelCount_canonical_of_orderFibreCount` proves the raw count from
  `LPPOrderFibreCount`, reversing the algebra of `lppOrderFibreCount_of_raw`.

Consequently `younisLPPInputs_of_orderFibreCount` constructs `YounisLPPInputs`
from the existing `LPPOrderFibreCount` alone (plus the Younis density inputs),
so `LPPRawModelCount` and `LPPNormalization` add no analytic content beyond that
count.

## The Younis half

The odd-order count is genuinely stronger than the unrestricted central count:
the central interval is one-sided and the parity condition `n ≡ 2 (mod 4)` is
exactly what the LPP model construction uses.  It is therefore retained in the
two paper-level halves already isolated in `RandomizedL30Younis`:

* `YounisOddRelativeShortInterval A` — relative short-interval density;
* `YounisOddGlobalLower B` — the global odd smooth lower bound.

`RawInputs.younisOddCentralCount` reproves the reduction
`A B ≥ 4 ⟹ YounisOddCentralCount`, and `RawInputs.younisShortIntervalCount`
passes to the unrestricted count.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no count or error
is set to zero.
-/

namespace Cogentic.RandomizedL30Raw

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis

noncomputable section

/-! ## The explicit polylogarithmic LPP loss -/

/-- The paper's polylogarithmic loss in the raw LPP count, made explicit:
`Q (p) = log p + 1`.  This is the smallest loss for which the normalization
`Q ≤ p · exp ((1+ε) t_p)` is elementary. -/
def lppLogLoss (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.log (p n) + 1

/-- The explicit loss is positive for `p ≥ 2`. -/
theorem lppLogLoss_pos {p : ℕ → ℝ} {n : ℕ} (hp : 2 ≤ p n) :
    0 < lppLogLoss p n := by
  unfold lppLogLoss
  have hp1 : (1 : ℝ) < p n := by linarith
  have hlog : 0 < Real.log (p n) := Real.log_pos hp1
  linarith

/-- For `p ≥ 2`, `log p + 1 ≤ p`.  This is the only numerical fact behind the
normalization of the explicit loss. -/
theorem lppLogLoss_le_p {p : ℕ → ℝ} {n : ℕ} (hp : 2 ≤ p n) :
    lppLogLoss p n ≤ p n := by
  unfold lppLogLoss
  have hp0 : (0 : ℝ) < p n := by linarith
  have hlog : Real.log (p n) ≤ p n - 1 := Real.log_le_sub_one_of_pos hp0
  linarith

/-- **The LPP normalization for the explicit polylog loss.**  If `p ≥ 2`,
`t ≥ 0`, and `ε ≥ -1`, then `log p + 1 ≤ p exp ((1+ε) t)`.  No analytic input
is used; the paper's `1 + o(1)` loss is absorbed by `exp ((1+ε) t) ≥ 1`. -/
theorem lppNormalization_logLoss {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) (ht : ∀ n, 0 ≤ t n) (he : ∀ n, -1 ≤ err n) :
    LPPNormalization p t err (lppLogLoss p) := by
  intro n
  refine ⟨lppLogLoss_pos (hp n), ?_⟩
  have hp0 : (0 : ℝ) < p n := by linarith [hp n]
  have hexp1 : (1 : ℝ) ≤ Real.exp ((1 + err n) * t n) := by
    calc
      (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp ((1 + err n) * t n) :=
          Real.exp_le_exp.mpr (mul_nonneg (by linarith [he n]) (ht n))
  calc
    lppLogLoss p n ≤ p n := lppLogLoss_le_p (hp n)
    _ = p n * 1 := by ring
    _ ≤ p n * Real.exp ((1 + err n) * t n) :=
          mul_le_mul_of_nonneg_left hexp1 hp0.le

/-- **The smallest explicit raw LPP input.**  Every eligible smooth order
carries at least `p^{9/2} / (log p + 1)` nonsingular quintic models.  The only
difference from the paper's raw theorem is that the unspecified polylogarithmic
loss has been fixed to `log p + 1`; the normalization is proved above rather
than assumed. -/
def LPPRawLogModelCount (p t err : ℕ → ℝ)
    (fibreModels : ℕ → ℕ → Finset ℕ) : Prop :=
  LPPRawModelCount p t err fibreModels (lppLogLoss p)

/-- **LPP after the explicit raw loss.**  The raw count with loss `log p + 1`
and the proved normalization give the paper's normalized per-order fibre
count. -/
theorem lppOrderFibreCount_of_rawLog {p t err : ℕ → ℝ}
    {fibreModels : ℕ → ℕ → Finset ℕ}
    (hp : ∀ n, 2 ≤ p n) (ht : ∀ n, 0 ≤ t n) (he : ∀ n, -1 ≤ err n)
    (hraw : LPPRawLogModelCount p t err fibreModels) :
    LPPOrderFibreCount p t err fibreModels :=
  lppOrderFibreCount_of_raw hp (lppNormalization_logLoss hp ht he) hraw

/-! ## The canonical loss and the equivalence with the existing fibre count -/

/-- The maximal admissible loss: the whole normalization budget
`Q = p · exp ((1+ε) t_p)`.  With this choice the raw model count is exactly
the already formalised per-order count. -/
def lppCanonicalLoss (p t err : ℕ → ℝ) (n : ℕ) : ℝ :=
  p n * Real.exp ((1 + err n) * t n)

/-- The canonical loss is positive. -/
theorem lppCanonicalLoss_pos {p t err : ℕ → ℝ} {n : ℕ} (hp : 0 < p n) :
    0 < lppCanonicalLoss p t err n :=
  mul_pos hp (Real.exp_pos _)

/-- **The canonical loss satisfies the normalization by reflexivity.** -/
theorem lppNormalization_canonical {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) :
    LPPNormalization p t err (lppCanonicalLoss p t err) := by
  intro n
  have hp0 : (0 : ℝ) < p n := by linarith [hp n]
  exact ⟨lppCanonicalLoss_pos hp0, le_rfl⟩

/-- The exponent arithmetic of the LPP normalization, stated separately:
`p^{9/2} / (p exp a) = p^{7/2} exp (-a)`. -/
theorem rpow_nine_div_exp_eq {p : ℝ} (hp : 0 < p) (a : ℝ) :
    p ^ ((9 : ℝ) / 2) / (p * Real.exp a) =
      p ^ ((7 : ℝ) / 2) * Real.exp (-a) := by
  have hsplit : p ^ ((9 : ℝ) / 2) = p ^ ((7 : ℝ) / 2) * p := by
    rw [show ((9 : ℝ) / 2) = (7 : ℝ) / 2 + 1 by norm_num,
      Real.rpow_add hp, Real.rpow_one]
  rw [hsplit, div_eq_mul_inv, mul_inv, Real.exp_neg]
  field_simp

/-- **The raw count from the existing per-order fibre count**, with the
canonical loss.  This is the converse of `lppOrderFibreCount_of_raw` for the
choice `Q = p exp ((1+ε) t)`: the raw count then contains exactly the
normalized per-order count. -/
theorem lppRawModelCount_canonical_of_orderFibreCount {p t err : ℕ → ℝ}
    {fibreModels : ℕ → ℕ → Finset ℕ}
    (hp : ∀ n, 2 ≤ p n)
    (h : LPPOrderFibreCount p t err fibreModels) :
    LPPRawModelCount p t err fibreModels (lppCanonicalLoss p t err) := by
  intro n m hm
  have hp0 : (0 : ℝ) < p n := by linarith [hp n]
  have heq : p n ^ ((9 : ℝ) / 2) / lppCanonicalLoss p t err n =
      p n ^ ((7 : ℝ) / 2) * Real.exp (-(1 + err n) * t n) := by
    unfold lppCanonicalLoss
    rw [rpow_nine_div_exp_eq hp0 ((1 + err n) * t n)]
    have harg : -((1 + err n) * t n) = -(1 + err n) * t n := by ring
    rw [harg]
  rw [heq]
  exact h n m hm

/-- **Raw model count and normalization are equivalent to the existing
per-order fibre count.**  Given `LPPOrderFibreCount`, the raw count with the
canonical loss and the corresponding normalization both hold; conversely
`lppOrderFibreCount_of_raw` recovers the per-order count. -/
theorem lppRaw_and_normalization_canonical_iff_orderFibreCount {p t err : ℕ → ℝ}
    {fibreModels : ℕ → ℕ → Finset ℕ} (hp : ∀ n, 2 ≤ p n) :
    LPPRawModelCount p t err fibreModels (lppCanonicalLoss p t err) ∧
        LPPNormalization p t err (lppCanonicalLoss p t err) ↔
      LPPOrderFibreCount p t err fibreModels := by
  constructor
  · rintro ⟨hraw, hnorm⟩
    exact lppOrderFibreCount_of_raw hp hnorm hraw
  · intro h
    exact ⟨lppRawModelCount_canonical_of_orderFibreCount hp h,
      lppNormalization_canonical hp⟩

/-! ## The Younis half -/

/-- **`YounisOddCentralCount` from the two paper-level halves.**  This is the
reduction of `RandomizedL30Younis`, restated as the raw layer's Younis
interface: relative short-interval density and the global odd lower bound
suffice once `A B ≥ 4`, the interval-cardinality loss. -/
theorem younisOddCentralCount_of_relative_global {p t err : ℕ → ℝ} {A B : ℝ}
    (hp : ∀ n, 2 ≤ p n) (hA : 0 < A) (hB : 0 < B) (hAB : 4 ≤ A * B)
    (hrel : YounisOddRelativeShortInterval A p t err)
    (hglob : YounisOddGlobalLower B p t err) :
    YounisOddCentralCount p t err :=
  younisOddCentralCount_of_density hp hA hB hAB hrel hglob

/-- **`YounisShortIntervalCount` from the odd central count.**  The odd orders
are a subset of the central smooth orders. -/
theorem younisShortIntervalCount_of_oddCount {p t err : ℕ → ℝ}
    (h : YounisOddCentralCount p t err) :
    YounisShortIntervalCount p t err :=
  younisShortIntervalCount_of_odd h

/-! ## The raw input structure -/

/-- The smallest explicit analytic inputs of the L30 reduction.

The Younis half keeps the two paper-level halves already isolated by
`RandomizedL30Younis`.  The LPP half keeps only `LPPRawLogModelCount`; the
normalization is no longer a field, because `lppNormalization_logLoss` proves it
for the explicit loss `log p + 1`.

The elementary side conditions `p ≥ 2`, `t ≥ 0`, `ε ≥ -1` are the natural
regime of `t_p = √(log p log log p)` and of the `1 + o(1)` error. -/
structure RawInputs where
  /-- The prime whose genus-two order is counted at scale `n`. -/
  p : ℕ → ℝ
  /-- The paper's `t_p = √(log p · log log p)`. -/
  t : ℕ → ℝ
  /-- The explicit `1 + o(1)` relative error. -/
  err : ℕ → ℝ
  /-- The prime is at least `2`. -/
  p_ge_two : ∀ n, 2 ≤ p n
  /-- `t_p ≥ 0`. -/
  t_nonneg : ∀ n, 0 ≤ t n
  /-- The relative error satisfies `ε ≥ -1`; for the paper's `ε → 0` this is
  automatic eventually, and it makes `exp ((1+ε) t_p) ≥ 1`. -/
  err_ge_neg_one : ∀ n, -1 ≤ err n
  /-- The finite set of quintic models attached to order `m`. -/
  fibreModels : ℕ → ℕ → Finset ℕ
  /-- Relative short-interval density constant. -/
  A : ℝ
  /-- Global odd smooth lower-bound constant. -/
  B : ℝ
  /-- `A > 0`. -/
  A_pos : 0 < A
  /-- `B > 0`. -/
  B_pos : 0 < B
  /-- The interval-cardinality relation `A B ≥ 4`. -/
  AB_ge_four : 4 ≤ A * B
  /-- Younis's relative short-interval density for odd smooth orders. -/
  younis_relative : YounisOddRelativeShortInterval A p t err
  /-- The global odd smooth lower bound. -/
  younis_global : YounisOddGlobalLower B p t err
  /-- The raw LPP model count with the explicit loss `log p + 1`. -/
  lpp_raw_log : LPPRawLogModelCount p t err fibreModels

namespace RawInputs

variable (S : RawInputs)

/-- **The explicit LPP normalization**, now a theorem rather than an input. -/
theorem lpp_normalization :
    LPPNormalization S.p S.t S.err (lppLogLoss S.p) :=
  lppNormalization_logLoss S.p_ge_two S.t_nonneg S.err_ge_neg_one

/-- **The raw LPP count** with the explicit loss, restated under the
`LPPRawModelCount` name used by `YounisLPPInputs`. -/
theorem lpp_raw :
    LPPRawModelCount S.p S.t S.err S.fibreModels (lppLogLoss S.p) :=
  S.lpp_raw_log

/-- **The Younis odd central count** from the two analytic halves. -/
theorem younisOddCentralCount : YounisOddCentralCount S.p S.t S.err :=
  younisOddCentralCount_of_relative_global S.p_ge_two S.A_pos S.B_pos
    S.AB_ge_four S.younis_relative S.younis_global

/-- **The unrestricted Younis central count.** -/
theorem younisShortIntervalCount : YounisShortIntervalCount S.p S.t S.err :=
  younisShortIntervalCount_of_oddCount S.younisOddCentralCount

/-- **The LPP per-order fibre count** from the raw log count and the proved
normalization. -/
theorem lppOrderFibreCount : LPPOrderFibreCount S.p S.t S.err S.fibreModels :=
  lppOrderFibreCount_of_rawLog S.p_ge_two S.t_nonneg S.err_ge_neg_one S.lpp_raw_log

/-- **The reduction to `YounisLPPInputs`.**  Every analytic field is either one
of the two Younis halves or the raw LPP log count; the normalization field is
discharged by `lppNormalization_logLoss`. -/
noncomputable def toYounisLPPInputs : YounisLPPInputs where
  p := S.p
  t := S.t
  err := S.err
  p_ge_two := S.p_ge_two
  fibreModels := S.fibreModels
  Q := lppLogLoss S.p
  A := S.A
  B := S.B
  A_pos := S.A_pos
  B_pos := S.B_pos
  AB_ge_four := S.AB_ge_four
  younis_relative := S.younis_relative
  younis_global := S.younis_global
  lpp_normalization := S.lpp_normalization
  lpp_raw := S.lpp_raw

/-- **The reduction to `AnalyticInputs`**, reusing the Cantor/H.5 data. -/
noncomputable def toAnalyticInputs (C : CantorCostInputs) : AnalyticInputs :=
  S.toYounisLPPInputs.toAnalyticInputs C

/-- **The reduction to `PaperInputs`**. -/
noncomputable def toPaperInputs (C : CantorCostInputs) : PaperInputs :=
  S.toYounisLPPInputs.toPaperInputs C

end RawInputs

/-! ## The reduction from the existing order-fibre count -/

/-- **`YounisLPPInputs` from the existing `LPPOrderFibreCount`.**  With the
canonical loss `Q = p exp ((1+ε) t)`, the raw LPP count and the normalization
are derived from the per-order fibre count, so the LPP analytic content of
`YounisLPPInputs` is exactly the already formalised order-fibre estimate. -/
noncomputable def younisLPPInputs_of_orderFibreCount
    (p t err : ℕ → ℝ) (hp : ∀ n, 2 ≤ p n)
    (fibreModels : ℕ → ℕ → Finset ℕ)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (hAB : 4 ≤ A * B)
    (hrel : YounisOddRelativeShortInterval A p t err)
    (hglob : YounisOddGlobalLower B p t err)
    (h : LPPOrderFibreCount p t err fibreModels) :
    YounisLPPInputs where
  p := p
  t := t
  err := err
  p_ge_two := hp
  fibreModels := fibreModels
  Q := lppCanonicalLoss p t err
  A := A
  B := B
  A_pos := hA
  B_pos := hB
  AB_ge_four := hAB
  younis_relative := hrel
  younis_global := hglob
  lpp_normalization := lppNormalization_canonical hp
  lpp_raw := lppRawModelCount_canonical_of_orderFibreCount hp h

/-- The per-order fibre count read back from the constructed inputs is the
original one. -/
theorem younisLPPInputs_of_orderFibreCount_lpp
    (p t err : ℕ → ℝ) (hp : ∀ n, 2 ≤ p n)
    (fibreModels : ℕ → ℕ → Finset ℕ)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (hAB : 4 ≤ A * B)
    (hrel : YounisOddRelativeShortInterval A p t err)
    (hglob : YounisOddGlobalLower B p t err)
    (h : LPPOrderFibreCount p t err fibreModels) :
    LPPOrderFibreCount p t err fibreModels :=
  (younisLPPInputs_of_orderFibreCount p t err hp fibreModels A B hA hB hAB hrel hglob h)
    |>.lppOrderFibreCount

/-! ## Axiom audit -/

#print axioms lppLogLoss_pos
#print axioms lppLogLoss_le_p
#print axioms lppNormalization_logLoss
#print axioms lppOrderFibreCount_of_rawLog
#print axioms lppCanonicalLoss_pos
#print axioms lppNormalization_canonical
#print axioms rpow_nine_div_exp_eq
#print axioms lppRawModelCount_canonical_of_orderFibreCount
#print axioms lppRaw_and_normalization_canonical_iff_orderFibreCount
#print axioms younisOddCentralCount_of_relative_global
#print axioms younisShortIntervalCount_of_oddCount
#print axioms RawInputs.lpp_normalization
#print axioms RawInputs.lpp_raw
#print axioms RawInputs.younisOddCentralCount
#print axioms RawInputs.younisShortIntervalCount
#print axioms RawInputs.lppOrderFibreCount
#print axioms RawInputs.toYounisLPPInputs
#print axioms RawInputs.toAnalyticInputs
#print axioms RawInputs.toPaperInputs
#print axioms younisLPPInputs_of_orderFibreCount
#print axioms younisLPPInputs_of_orderFibreCount_lpp

end

end Cogentic.RandomizedL30Raw
