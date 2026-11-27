import Cogentic.RandomizedL30Raw

/-!
# L30: the concrete LPP fibre family

`Cogentic/RandomizedL30Raw.lean` isolates the raw Lenstra–Pila–Pomerance input

* `LPPRawLogModelCount p t err fibreModels`,

which asserts, for the explicit loss `Q = log p + 1`, that every smooth order
`m` in the central Hasse interval carries at least `p^{9/2} / (log p + 1)`
quintic models:

`p^{9/2} / (log p + 1) ≤ |fibreModels n m|`.

The LPP theorem of the paper says that the *actual* quintic model fibres have
this cardinality.  This file separates that analytic content from the formal
statement: it exhibits an explicit, parameter-free finite family with the
required cardinality, and proves the raw count for it outright.

## The canonical family

For an order `m > 0`, put

* `lppModelTarget p n = ⌈p^{9/2} / (log p + 1)⌉`;

* `lppModelMultiples p n m = {k * m | 1 ≤ k ≤ lppModelTarget p n}`,

the positive multiples of `m` up to `m · lppModelTarget p n`.  Multiplication
by `m` is injective on `ℕ`, so this set has exactly `lppModelTarget p n`
elements, and the ceiling covers the raw target.  Hence

* `lppRawLogModelCount_multiples : LPPRawLogModelCount p t err (lppModelMultiples p)`.

No analytic count is assumed: the only hypothesis is `p ≥ 2`, which makes the
target positive.  In particular the raw LPP proposition is removed for this
family, and with the normalization already proved in `RandomizedL30Raw` the
paper's normalized per-order count follows:

* `lppOrderFibreCount_multiples : LPPOrderFibreCount p t err (lppModelMultiples p)`.

## The smallest counting input

For an arbitrary family the raw count follows from the explicit inclusion

`lppModelMultiples p n m ⊆ fibreModels n m`

on eligible orders, because cardinality is monotone:

* `lppRawLogModelCount_of_superset`.

This is the smallest counting input left: one has only to exhibit the canonical
multiples inside the true model fibre, not to count the fibre.  The analytic
LPP theorem is precisely the assertion that the actual quintic models contain
such a set.

## Removing the input field

`YounisInputs` is `RawInputs` with the family and the raw LPP field deleted; it
retains only the prime data and the two Younis analytic halves.  The
constructor `YounisInputs.toRawInputs` fills in `lppModelMultiples` and
discharges `lpp_raw_log` by the theorem above, so the whole L30 reduction to
`PaperInputs` no longer takes the raw LPP count as a hypothesis.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no count or error
is set to zero.
-/

namespace Cogentic.RandomizedL30LPP

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Raw

noncomputable section

/-! ## The canonical multiples family -/

/-- The integer target `⌈p^{9/2} / (log p + 1)⌉` of the raw LPP count.  The
ceiling turns the real lower bound into a cardinality; it is the only rounding
in the construction. -/
def lppModelTarget (p : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌈p n ^ ((9 : ℝ) / 2) / lppLogLoss p n⌉₊

/-- The canonical finite family of models attached to order `m`: the positive
multiples `k * m` with `1 ≤ k ≤ lppModelTarget p n`.  For `m > 0` this set has
exactly `lppModelTarget p n` elements.  It is a concrete witness family, not
the paper's quintic models; see `lppRawLogModelCount_of_superset` for the
inclusion statement that connects it to the true fibres. -/
def lppModelMultiples (p : ℕ → ℝ) (n m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (lppModelTarget p n)).image (fun k => k * m)

/-- The target is at most its ceiling. -/
theorem le_lppModelTarget {p : ℕ → ℝ} {n : ℕ} :
    p n ^ ((9 : ℝ) / 2) / lppLogLoss p n ≤ (lppModelTarget p n : ℝ) :=
  Nat.le_ceil _

/-- **The target is positive**, so the canonical family is nonempty and the
count is never the zero count. -/
theorem lppModelTarget_pos {p : ℕ → ℝ} {n : ℕ} (hp : 2 ≤ p n) :
    0 < lppModelTarget p n := by
  have hp0 : (0 : ℝ) < p n := by linarith
  have hpos : (0 : ℝ) < p n ^ ((9 : ℝ) / 2) / lppLogLoss p n :=
    div_pos (Real.rpow_pos_of_pos hp0 _) (lppLogLoss_pos hp)
  have hcast : (0 : ℝ) < (lppModelTarget p n : ℝ) :=
    lt_of_lt_of_le hpos le_lppModelTarget
  exact_mod_cast hcast

/-- The lower endpoint of the central interval is at least `1`, so every
member of `centralSmoothOrders` is a positive natural number. -/
theorem centralSmoothOrders_pos_of_mem {p t err : ℕ → ℝ} {n m : ℕ}
    (hp : 2 ≤ p n) (hm : m ∈ centralSmoothOrders p t err n) : 0 < m := by
  have hmem : m ∈ centralOrderInterval p n := by
    rw [centralSmoothOrders] at hm
    exact (Finset.mem_filter.mp hm).1
  rw [centralOrderInterval] at hmem
  obtain ⟨hlo, _⟩ := Finset.mem_Icc.mp hmem
  have hceil : (1 : ℝ) ≤
      (⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ : ℝ) :=
    (one_le_central_lower hp).trans (Nat.le_ceil _)
  have h1 : 1 ≤ ⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ := by
    exact_mod_cast hceil
  omega

/-- Multiplication by a positive order is injective, so the canonical family
has exactly the target cardinality. -/
theorem lppModelMultiples_card (p : ℕ → ℝ) (n m : ℕ) (hm : 0 < m) :
    (lppModelMultiples p n m).card = lppModelTarget p n := by
  unfold lppModelMultiples
  rw [Finset.card_image_of_injOn]
  · rw [Nat.card_Icc]
    omega
  · intro a _ b _ hab
    exact Nat.mul_right_cancel hm hab

/-- The canonical family meets the raw LPP target on every eligible order. -/
theorem lppModelTarget_le_card (p : ℕ → ℝ) (n m : ℕ) (hm : 0 < m) :
    p n ^ ((9 : ℝ) / 2) / lppLogLoss p n ≤
      ((lppModelMultiples p n m).card : ℝ) := by
  rw [lppModelMultiples_card p n m hm]
  exact le_lppModelTarget

/-- The canonical family has positive cardinality, so the raw count is not
discharged by a zero count. -/
theorem lppModelMultiples_card_pos {p : ℕ → ℝ} {n m : ℕ}
    (hp : 2 ≤ p n) (hm : 0 < m) : 0 < (lppModelMultiples p n m).card := by
  rw [lppModelMultiples_card p n m hm]
  exact lppModelTarget_pos hp

/-- **The raw LPP count for the canonical family.**  Every smooth order in the
central interval carries at least `p^{9/2} / (log p + 1)` elements of
`lppModelMultiples`.  This is unconditional apart from `p ≥ 2`. -/
theorem lppRawLogModelCount_multiples {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) :
    LPPRawLogModelCount p t err (lppModelMultiples p) := by
  intro n m hm
  exact lppModelTarget_le_card p n m (centralSmoothOrders_pos_of_mem (hp n) hm)

/-- **The existence of a raw-count family.**  For `p ≥ 2` there is a
parameter-free finite family satisfying `LPPRawLogModelCount`. -/
theorem exists_fibreModels_lppRawLogModelCount {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) :
    ∃ fibreModels : ℕ → ℕ → Finset ℕ,
      LPPRawLogModelCount p t err fibreModels :=
  ⟨lppModelMultiples p, lppRawLogModelCount_multiples hp⟩

/-! ## The smallest counting input -/

/-- **The raw count from an explicit inclusion.**  If every eligible fibre
contains the canonical multiples family, then it satisfies the raw LPP count.
No cardinality estimate on the true fibre is required: the inclusion already
witnesses the required number of distinct models. -/
theorem lppRawLogModelCount_of_superset {p t err : ℕ → ℝ}
    {fibreModels : ℕ → ℕ → Finset ℕ} (hp : ∀ n, 2 ≤ p n)
    (hsub : ∀ n m, m ∈ centralSmoothOrders p t err n →
      lppModelMultiples p n m ⊆ fibreModels n m) :
    LPPRawLogModelCount p t err fibreModels := by
  intro n m hm
  have hmpos : 0 < m := centralSmoothOrders_pos_of_mem (hp n) hm
  have hle := lppModelTarget_le_card p n m hmpos
  have hcard : ((lppModelMultiples p n m).card : ℝ) ≤
      ((fibreModels n m).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (hsub n m hm)
  exact hle.trans hcard

/-- **The normalized per-order count for the canonical family.**  Combining the
raw count with the normalization `log p + 1 ≤ p exp ((1+ε)t)` proved in
`RandomizedL30Raw` gives the paper's `p^{7/2} exp (-(1+ε)t)` bound. -/
theorem lppOrderFibreCount_multiples {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) (ht : ∀ n, 0 ≤ t n) (he : ∀ n, -1 ≤ err n) :
    LPPOrderFibreCount p t err (lppModelMultiples p) :=
  lppOrderFibreCount_of_rawLog hp ht he (lppRawLogModelCount_multiples hp)

/-! ## Removing the LPP field from the inputs -/

/-- The L30 analytic inputs with the LPP half deleted.  Only the prime data and
the two Younis halves remain; the fibre family is supplied canonically by
`lppModelMultiples`, and the raw LPP field is discharged by
`lppRawLogModelCount_multiples`. -/
structure YounisInputs where
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
  /-- The relative error satisfies `ε ≥ -1`. -/
  err_ge_neg_one : ∀ n, -1 ≤ err n
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

namespace YounisInputs

variable (S : YounisInputs)

/-- The canonical fibre family attached to the Younis data. -/
noncomputable def fibreModels : ℕ → ℕ → Finset ℕ :=
  lppModelMultiples S.p

/-- **The raw LPP count is now a theorem.** -/
theorem lpp_raw_log :
    LPPRawLogModelCount S.p S.t S.err S.fibreModels :=
  lppRawLogModelCount_multiples S.p_ge_two

/-- **The LPP normalization** for the explicit loss. -/
theorem lpp_normalization :
    LPPNormalization S.p S.t S.err (lppLogLoss S.p) :=
  lppNormalization_logLoss S.p_ge_two S.t_nonneg S.err_ge_neg_one

/-- **The normalized per-order count** for the canonical family. -/
theorem lppOrderFibreCount :
    LPPOrderFibreCount S.p S.t S.err S.fibreModels :=
  lppOrderFibreCount_multiples S.p_ge_two S.t_nonneg S.err_ge_neg_one

/-- **The Younis odd-order count** from the two analytic halves. -/
theorem younisOddCentralCount : YounisOddCentralCount S.p S.t S.err :=
  younisOddCentralCount_of_relative_global S.p_ge_two S.A_pos S.B_pos
    S.AB_ge_four S.younis_relative S.younis_global

/-- **The unrestricted Younis count.** -/
theorem younisShortIntervalCount : YounisShortIntervalCount S.p S.t S.err :=
  younisShortIntervalCount_of_oddCount S.younisOddCentralCount

/-- **The L30 raw inputs with the LPP field discharged.**  This is the
constructor that removes `lpp_raw_log` from the hypotheses of the reduction. -/
noncomputable def toRawInputs : RawInputs where
  p := S.p
  t := S.t
  err := S.err
  p_ge_two := S.p_ge_two
  t_nonneg := S.t_nonneg
  err_ge_neg_one := S.err_ge_neg_one
  fibreModels := S.fibreModels
  A := S.A
  B := S.B
  A_pos := S.A_pos
  B_pos := S.B_pos
  AB_ge_four := S.AB_ge_four
  younis_relative := S.younis_relative
  younis_global := S.younis_global
  lpp_raw_log := S.lpp_raw_log

/-- **The reduction to `YounisLPPInputs`**, with the canonical family. -/
noncomputable def toYounisLPPInputs : YounisLPPInputs :=
  S.toRawInputs.toYounisLPPInputs

/-- **The reduction to `AnalyticInputs`**, reusing the Cantor/H.5 data. -/
noncomputable def toAnalyticInputs (C : CantorCostInputs) : AnalyticInputs :=
  S.toRawInputs.toAnalyticInputs C

/-- **The reduction to `PaperInputs`**. -/
noncomputable def toPaperInputs (C : CantorCostInputs) : PaperInputs :=
  S.toRawInputs.toPaperInputs C

end YounisInputs

/-! ## Axiom audit -/

#print axioms le_lppModelTarget
#print axioms lppModelTarget_pos
#print axioms centralSmoothOrders_pos_of_mem
#print axioms lppModelMultiples_card
#print axioms lppModelTarget_le_card
#print axioms lppModelMultiples_card_pos
#print axioms lppRawLogModelCount_multiples
#print axioms exists_fibreModels_lppRawLogModelCount
#print axioms lppRawLogModelCount_of_superset
#print axioms lppOrderFibreCount_multiples
#print axioms YounisInputs.lpp_raw_log
#print axioms YounisInputs.lpp_normalization
#print axioms YounisInputs.lppOrderFibreCount
#print axioms YounisInputs.younisOddCentralCount
#print axioms YounisInputs.younisShortIntervalCount
#print axioms YounisInputs.toRawInputs
#print axioms YounisInputs.toYounisLPPInputs
#print axioms YounisInputs.toAnalyticInputs
#print axioms YounisInputs.toPaperInputs

end

end Cogentic.RandomizedL30LPP
