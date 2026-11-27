import Cogentic.RandomizedL30Sub
import Cogentic.RandomizedSmoothDensity

/-!
# L30 analytic inputs: the three counting and cost estimates

`Cogentic/RandomizedL30Sub.lean` reduces KeyBreak Proposition H.3 to the
structure `PaperInputs`, whose analytic fields are three paper-level
statements:

* `YounisShortIntervalEstimate` — the number of smooth orders in the central
  genus-two Hasse interval;
* `LPPOrderFibreEstimate` — the number of quintic models attached to each
  eligible smooth order;
* `CantorArithmeticCostBound` — the H.5 cost of one gcd-checked Cantor call.

This file makes the objects behind those statements explicit and proves the
reduction to `PaperInputs`:

* `centralOrderInterval` is the paper's interval
  `(p² - p^{3/2}/2, p²]` as a `Finset ℕ`;
* `centralSmoothOrders` is the subset of `Y`-smooth integers in it, using the
  same prime-factor smoothness predicate as
  `Cogentic.Randomized.centeredBinProducts_smooth`;
* `YounisShortIntervalCount` is Younis's lower bound stated directly on the
  cardinality of this finite set;
* `LPPOrderFibreCount` is the Lenstra–Pila–Pomerance per-order fibre bound,
  stated on explicit finite sets of quintic models;
* `CantorArithmeticCostLiteral` is the literal H.5 inequality
  `cost ≤ z_y · 2^{⌈101 k_y / 100⌉} · poly · L_c`, with `z_y = 2^{k_y}`.

The Cantor ceiling is not an extra analytic hypothesis: the elementary lemma
`z_mul_cantorTrialCount_le` absorbs the ceiling into the exponent
`(201/100) log 2 · k_y` at the price of a factor `2`, which is absorbed into
`polyFactor`.  The `ceil`-free form is exactly
`CantorArithmeticCostBound`.

The remaining two paper-level propositions are kept as the smallest explicit
statements we can state without formalising Younis's short-interval contour
argument and the LPP order-fibre theorem.  As in `RandomizedL30Sub`, the
ordinary Riemann hypothesis is folded into the Younis input rather than carried
as a separate field.  The elliptic exceptional-prime estimate of
`research/keybreak-public-elliptic-recognition.md` feeds the useful-prime split
bound (H.13)–(H.14), which is a `FailureData` hypothesis and is deliberately
not part of `PaperInputs`; it is therefore not used here.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no count, error,
or cost is set to zero.
-/

namespace Cogentic.RandomizedL30Analytic

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.Randomized

noncomputable section

/-! ## The explicit smooth-order objects -/

/-- `m` is `y`-smooth: every prime divisor of `m` is at most `y`.  This is the
predicate used by `Cogentic.Randomized.centeredBinProducts_smooth`. -/
def IsSmoothUpTo (y : ℝ) (m : ℕ) : Prop :=
  ∀ q ∈ m.primeFactors, (q : ℝ) ≤ y

/-- The paper's smoothness cutoff `Y = exp ((1 + ε) t_p)`.  The relative error
`ε` is the same sequence as in `YounisShortIntervalEstimate`; choosing the
cutoff this way makes the smooth-order set explicit and leaves no free
`Y`-parameter behind the count. -/
def smoothCutoff (t err : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp ((1 + err n) * t n)

/-- The central genus-two order interval `(p² - p^{3/2}/2, p²]` as a finite set
of integers.  The lower endpoint is rounded up and the upper endpoint down, so
the `Finset` is exactly the set of integers in the open-closed interval. -/
def centralOrderInterval (p : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  Finset.Icc (⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊) ⌊p n ^ 2⌋₊

/-- The `Y`-smooth orders in the central genus-two Hasse interval. -/
noncomputable def centralSmoothOrders (p t err : ℕ → ℝ) (n : ℕ) : Finset ℕ := by
  classical
  exact (centralOrderInterval p n).filter (IsSmoothUpTo (smoothCutoff t err n))

/-- The real-valued smooth-order count consumed by `PaperInputs`. -/
def smoothOrderCount (p t err : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((centralSmoothOrders p t err n).card : ℝ)

/-- For `p ≥ 2` the lower endpoint of the central interval is at least `1`.
This is the elementary comparison `p^{3/2} ≤ p²`, which embeds the central
interval into the global smooth-number range used by
`Cogentic.Randomized.smoothCount_rankin_upper`. -/
theorem one_le_central_lower {p : ℝ} (hp : 2 ≤ p) :
    (1 : ℝ) ≤ p ^ 2 - p ^ ((3 : ℝ) / 2) / 2 := by
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hmono : p ^ ((3 : ℝ) / 2) ≤ p ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1
      (by norm_num : ((3 : ℝ) / 2) ≤ (2 : ℝ))
    simpa using h
  have hp2 : (4 : ℝ) ≤ p ^ 2 := by nlinarith [sq_nonneg (p - 2), hp]
  nlinarith

/-- The central smooth-order set is a subset of the global `y`-smooth range
used by the Rankin upper bound. -/
theorem centralSmoothOrders_subset_global {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) :
    centralSmoothOrders p t err n ⊆
      (Finset.Icc 1 ⌊p n ^ 2⌋₊).filter
        (fun m : ℕ => ∀ q ∈ m.primeFactors, (q : ℝ) ≤ smoothCutoff t err n) := by
  intro m hm
  rw [centralSmoothOrders] at hm
  obtain ⟨hmI, hsmooth⟩ := Finset.mem_filter.mp hm
  rw [centralOrderInterval] at hmI
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hmI
  have hceil : (1 : ℕ) ≤ ⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ := by
    have hreal : (1 : ℝ) ≤
        (⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ : ℝ) :=
      (one_le_central_lower hp).trans (Nat.le_ceil _)
    exact_mod_cast hreal
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hceil.trans hlo, hhi⟩, hsmooth⟩

/-- **The existing Rankin smooth-number upper bound applies to the central
count.**  This is the upper-bound companion of Younis's lower bound; it shows
that `centralSmoothOrders` is literally the same smooth-number object as in
`Cogentic.Randomized.smoothCount_rankin_upper`. -/
theorem centralSmoothOrders_card_le_rankin {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hy : 2 ≤ smoothCutoff t err n) :
    ((centralSmoothOrders p t err n).card : ℝ) ≤
      (p n ^ 2) ^ α *
        ∏ q ∈ (Finset.Icc 2 ⌊smoothCutoff t err n⌋₊).filter Nat.Prime,
          (1 - (q : ℝ) ^ (-α))⁻¹ := by
  have hx : (1 : ℝ) ≤ p n ^ 2 := by
    have hp2 : (2 : ℝ) ≤ p n := by exact_mod_cast hp
    nlinarith [sq_nonneg (p n - 2), hp2]
  have hcard : ((centralSmoothOrders p t err n).card : ℝ) ≤
      (((Finset.Icc 1 ⌊p n ^ 2⌋₊).filter
        (fun m : ℕ => ∀ q ∈ m.primeFactors, (q : ℝ) ≤ smoothCutoff t err n)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (centralSmoothOrders_subset_global hp)
  exact hcard.trans (by
    simpa using smoothCount_rankin_upper (x := p n ^ 2) (y := smoothCutoff t err n)
      hx hy hα0 hα1)

/-! ## The three smallest paper-level propositions -/

/-- **Younis, Theorem 1.3 (under RH)**, stated on the explicit smooth-order
set: the central Hasse interval contains at least
`p^{3/2} exp (-(1+ε)t_p)` smooth integers.  This is the smallest counting form
of the theorem; the only remaining content is the short-interval analytic
lower bound itself. -/
def YounisShortIntervalCount (p t err : ℕ → ℝ) : Prop :=
  ∀ n, p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * t n) ≤
    ((centralSmoothOrders p t err n).card : ℝ)

/-- **Lenstra–Pila–Pomerance II, Theorem 1.1**, stated on explicit finite sets
of quintic models: every eligible smooth order in the central interval carries
at least `p^{7/2} exp (-(1+ε)t_p)` models.  The sets `fibreModels n m` are the
paper's model fibres; only their cardinality enters the estimate. -/
def LPPOrderFibreCount (p t err : ℕ → ℝ) (fibreModels : ℕ → ℕ → Finset ℕ) : Prop :=
  ∀ n m, m ∈ centralSmoothOrders p t err n →
    p n ^ ((7 : ℝ) / 2) * exp (-(1 + err n) * t n) ≤
      ((fibreModels n m).card : ℝ)

/-- `z_y = 2^{k_y}`. -/
def zOf (k : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow 2 (k n)

/-- The paper's trial count `2^{⌈101 k_y / 100⌉}`. -/
def cantorTrialCount (k : ℕ → ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (Nat.ceil (((101 : ℝ) / 100) * k n))

/-- **KB (H.5), literal cost form.**  One gcd-checked Cantor call costs at most
`z_y · 2^{⌈101 k_y / 100⌉} · poly · L_c`.  This is the paper's displayed
inequality with the ceiling kept explicit; `CantorArithmeticCostBound` is the
absorbed form proved below. -/
def CantorArithmeticCostLiteral (k polyFactor Lc trialCost : ℕ → ℝ) : Prop :=
  ∀ n, trialCost n ≤ zOf k n * cantorTrialCount k n * polyFactor n * Lc n

/-! ## The Cantor ceiling arithmetic -/

/-- **Ceiling absorption.**  For `k_y ≥ 0`,
`2^{k_y} · 2^{⌈101 k_y / 100⌉} ≤ 2 · exp ((201/100) log 2 · k_y)`.
The ceiling costs at most `k_y / 100 + 1` in the exponent, hence the fixed
factor `2` on the right. -/
theorem z_mul_cantorTrialCount_le (k : ℕ → ℝ) (hk : ∀ n, 0 ≤ k n) (n : ℕ) :
    zOf k n * cantorTrialCount k n ≤
      2 * exp (((201 : ℝ) / 100) * (Real.log 2 * k n)) := by
  set m : ℕ := Nat.ceil (((101 : ℝ) / 100) * k n) with hm
  have hm_nonneg : 0 ≤ ((101 : ℝ) / 100) * k n := by
    have := hk n
    positivity
  have hm_lt : (m : ℝ) < ((101 : ℝ) / 100) * k n + 1 := by
    simpa [hm] using Nat.ceil_lt_add_one hm_nonneg
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : zOf k n = exp (Real.log 2 * k n) := by
    unfold zOf
    change (2 : ℝ) ^ (k n) = exp (Real.log 2 * k n)
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h2m : cantorTrialCount k n = exp (Real.log 2 * (m : ℝ)) := by
    unfold cantorTrialCount
    rw [← hm, ← Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 2) m),
      Real.log_pow]
    ring_nf
  rw [hz, h2m, ← Real.exp_add]
  have hmul : Real.log 2 * (m : ℝ) ≤
      Real.log 2 * (((101 : ℝ) / 100) * k n + 1) :=
    mul_le_mul_of_nonneg_left hm_lt.le hlog2.le
  have hexp_le :
      Real.log 2 * k n + Real.log 2 * (m : ℝ) ≤
        Real.log 2 + ((201 : ℝ) / 100) * (Real.log 2 * k n) := by
    have h := hmul
    have h_expand : Real.log 2 * (((101 : ℝ) / 100) * k n + 1) =
        ((101 : ℝ) / 100) * (Real.log 2 * k n) + Real.log 2 := by ring_nf
    rw [h_expand] at h
    linarith
  calc
    exp (Real.log 2 * k n + Real.log 2 * (m : ℝ))
        ≤ exp (Real.log 2 + ((201 : ℝ) / 100) * (Real.log 2 * k n)) :=
          Real.exp_le_exp.mpr hexp_le
    _ = 2 * exp (((201 : ℝ) / 100) * (Real.log 2 * k n)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- **The H.5 cost bound from its literal form.**  The ceiling-free
`CantorArithmeticCostBound` follows from the literal H.5 inequality after the
fixed factor `2` is absorbed into `polyFactor`. -/
theorem cantorArithmeticCostBound_of_literal
    {k polyFactor Lc trialCost : ℕ → ℝ}
    (h : CantorArithmeticCostLiteral k polyFactor Lc trialCost)
    (hk : ∀ n, 0 ≤ k n) (hpoly : ∀ n, 0 ≤ polyFactor n)
    (hLc : ∀ n, 0 ≤ Lc n) :
    CantorArithmeticCostBound k (fun n => 2 * polyFactor n) Lc trialCost := by
  intro n
  have hkey := z_mul_cantorTrialCount_le k hk n
  have h1 : zOf k n * cantorTrialCount k n * polyFactor n ≤
      (2 * exp (((201 : ℝ) / 100) * (Real.log 2 * k n))) * polyFactor n :=
    mul_le_mul_of_nonneg_right hkey (hpoly n)
  have h2 : zOf k n * cantorTrialCount k n * polyFactor n * Lc n ≤
      (2 * exp (((201 : ℝ) / 100) * (Real.log 2 * k n))) *
        polyFactor n * Lc n :=
    mul_le_mul_of_nonneg_right h1 (hLc n)
  calc
    trialCost n ≤ zOf k n * cantorTrialCount k n * polyFactor n * Lc n := h n
    _ ≤ (2 * exp (((201 : ℝ) / 100) * (Real.log 2 * k n))) *
          polyFactor n * Lc n := h2
    _ = exp (((201 : ℝ) / 100) * (Real.log 2 * k n)) *
          (2 * polyFactor n) * Lc n := by ring_nf

/-! ## The reduced analytic inputs and the reduction to `PaperInputs` -/

/-- The three paper-level estimates, with their counting objects made explicit.
`younis` and `lpp` are the only analytic number-theory inputs; `cantor_literal`
is the paper's displayed H.5 cost, and the `ceil`-free cost is derived from it.
`cantor_arithmetic` is the same named correctness proposition carried by
`PaperInputs`. -/
structure AnalyticInputs where
  /-- The prime whose genus-two order is counted at scale `n`. -/
  p : ℕ → ℝ
  /-- The paper's `t_p = √(log p · log log p)`. -/
  t : ℕ → ℝ
  /-- The explicit `1 + o(1)` relative error. -/
  err : ℕ → ℝ
  /-- The prime is at least `2`, so the central interval is nonempty. -/
  p_ge_two : ∀ n, 2 ≤ p n
  /-- `k_y`. -/
  k : ℕ → ℝ
  /-- `k_y ≥ 0`, needed for the ceiling arithmetic. -/
  k_nonneg : ∀ n, 0 ≤ k n
  /-- The polynomial factor of H.5. -/
  polyFactor : ℕ → ℝ
  /-- The polynomial factor is nonnegative. -/
  polyFactor_nonneg : ∀ n, 0 ≤ polyFactor n
  /-- The confidence parameter `L_c`. -/
  Lc : ℕ → ℝ
  /-- The paper's confidence range `L_c ≥ 1`. -/
  Lc_ge_one : ∀ n, 1 ≤ Lc n
  /-- The per-call cost. -/
  trialCost : ℕ → ℝ
  /-- The finite set of quintic models attached to order `m` at scale `n`. -/
  fibreModels : ℕ → ℕ → Finset ℕ
  /-- **Younis, Theorem 1.3 (under RH)**, as an explicit smooth-order count. -/
  younis : YounisShortIntervalCount p t err
  /-- **Lenstra–Pila–Pomerance II, Theorem 1.1**, as a per-order fibre count. -/
  lpp : LPPOrderFibreCount p t err fibreModels
  /-- **KB (H.5), literal cost form.** -/
  cantor_literal : CantorArithmeticCostLiteral k polyFactor Lc trialCost
  /-- **KB H.3, genus-two Jacobian/Cantor correctness.** -/
  cantor_arithmetic : Prop
  /-- The Cantor/Jacobian correctness proposition holds. -/
  cantor_arithmetic_holds : cantor_arithmetic

namespace AnalyticInputs

variable (S : AnalyticInputs)

/-- The prime is positive. -/
theorem p_pos (n : ℕ) : 0 < S.p n := by
  have h := S.p_ge_two n
  linarith

/-- The smooth-order count is nonnegative. -/
theorem smoothOrderCount_nonneg (n : ℕ) : 0 ≤ smoothOrderCount S.p S.t S.err n := by
  unfold smoothOrderCount
  positivity

/-- Younis's lower bound makes the explicit smooth-order set nonempty, so an
eligible order can be chosen for the LPP fibre count. -/
theorem smoothOrders_nonempty (n : ℕ) :
    (centralSmoothOrders S.p S.t S.err n).Nonempty := by
  have hpos : 0 < S.p n ^ ((3 : ℝ) / 2) * exp (-(1 + S.err n) * S.t n) :=
    mul_pos (Real.rpow_pos_of_pos (S.p_pos n) ((3 : ℝ) / 2)) (exp_pos _)
  have hle := S.younis n
  have hcard : 0 < (centralSmoothOrders S.p S.t S.err n).card := by
    have : (0 : ℝ) < ((centralSmoothOrders S.p S.t S.err n).card : ℝ) :=
      lt_of_lt_of_le hpos hle
    exact_mod_cast this
  exact Finset.card_pos.mp hcard

/-- The least eligible smooth order, used as the representative order for the
per-order fibre count. -/
noncomputable def chosenOrder (n : ℕ) : ℕ :=
  (centralSmoothOrders S.p S.t S.err n).min' (S.smoothOrders_nonempty n)

/-- The chosen order is an eligible smooth order. -/
theorem chosenOrder_mem (n : ℕ) :
    S.chosenOrder n ∈ centralSmoothOrders S.p S.t S.err n :=
  (centralSmoothOrders S.p S.t S.err n).min'_mem (S.smoothOrders_nonempty n)

/-- **Younis's estimate from the explicit count.** -/
theorem younisShortIntervalEstimate_of_count :
    YounisShortIntervalEstimate S.p S.t S.err
      (fun n => smoothOrderCount S.p S.t S.err n) := by
  simpa [YounisShortIntervalCount, YounisShortIntervalEstimate, smoothOrderCount]
    using S.younis

/-- **The LPP estimate from the explicit per-order fibre count.** -/
theorem lppOrderFibreEstimate_of_count :
    LPPOrderFibreEstimate S.p S.t S.err
      (fun n => ((S.fibreModels n (S.chosenOrder n)).card : ℝ)) :=
  fun n => S.lpp n (S.chosenOrder n) (S.chosenOrder_mem n)

/-- **The H.5 cost bound from the literal ceiling form.** -/
theorem cantorArithmeticCostBound_of_literal_form :
    CantorArithmeticCostBound S.k (fun n => 2 * S.polyFactor n) S.Lc S.trialCost :=
  cantorArithmeticCostBound_of_literal S.cantor_literal S.k_nonneg
    S.polyFactor_nonneg (fun n => by linarith [S.Lc_ge_one n])

/-- **The reduction to `PaperInputs`.**  The explicit Younis count and LPP
fibre count supply the two analytic fields, the literal H.5 inequality supplies
the `ceil`-free cost field after the fixed factor `2` is absorbed into
`polyFactor`, and the Cantor correctness proposition is carried through. -/
noncomputable def toPaperInputs : PaperInputs where
  p := S.p
  t := S.t
  err := S.err
  smoothOrders := fun n => smoothOrderCount S.p S.t S.err n
  fibrePerOrder := fun n => ((S.fibreModels n (S.chosenOrder n)).card : ℝ)
  k := S.k
  polyFactor := fun n => 2 * S.polyFactor n
  Lc := S.Lc
  trialCost := S.trialCost
  younis := S.younisShortIntervalEstimate_of_count
  lpp := S.lppOrderFibreEstimate_of_count
  cantor_cost := S.cantorArithmeticCostBound_of_literal_form
  cantor_arithmetic := S.cantor_arithmetic
  cantor_arithmetic_holds := S.cantor_arithmetic_holds

/-- The `PaperInputs` reduction as a definition. -/
noncomputable def paperInputs_of_analytic : PaperInputs := S.toPaperInputs

/-- **The two halves of L30 from the analytic inputs.**  Combining the
`PaperInputs` reduction with the elementary failure analysis of
`RandomizedL30Sub` gives the `D^{-B}` failure statement and the `p^5` model
supply.  The model supply is stated on the explicit counts: the number of
smooth orders times the fibre count at the chosen order. -/
theorem l30_reduction_from_analytic (F : FailureData) :
    SubexpLoss F.loss ∧
      (∀ n, S.p n ^ (5 : ℝ) *
          exp (-(2 * (1 + S.err n)) * S.t n) ≤
        smoothOrderCount S.p S.t S.err n *
          ((S.fibreModels n (S.chosenOrder n)).card : ℝ)) := by
  simpa [toPaperInputs, smoothOrderCount] using
    (l30_reduction S.toPaperInputs F S.p_ge_two
      (fun n => S.smoothOrderCount_nonneg n))

end AnalyticInputs

/-! ## Axiom audit -/

#print axioms z_mul_cantorTrialCount_le
#print axioms cantorArithmeticCostBound_of_literal
#print axioms one_le_central_lower
#print axioms centralSmoothOrders_subset_global
#print axioms centralSmoothOrders_card_le_rankin
#print axioms AnalyticInputs.smoothOrders_nonempty
#print axioms AnalyticInputs.chosenOrder_mem
#print axioms AnalyticInputs.younisShortIntervalEstimate_of_count
#print axioms AnalyticInputs.lppOrderFibreEstimate_of_count
#print axioms AnalyticInputs.cantorArithmeticCostBound_of_literal_form
#print axioms AnalyticInputs.toPaperInputs
#print axioms AnalyticInputs.paperInputs_of_analytic
#print axioms AnalyticInputs.l30_reduction_from_analytic

end

end Cogentic.RandomizedL30Analytic
