import Cogentic.RandomizedL27Deuring

/-!
# L27 Hurwitz/Deuring reduction: the analytic class-number leaves

`Cogentic.RandomizedL27Deuring` leaves two paper-level `Prop`s for the
Deuring/Lenstra distribution of elliptic-curve orders:

* `DeuringTraceFormula` — a stage-one-smooth order `j` is realised by at least
  the Hurwitz class number of its Frobenius discriminant
  `D(p,j) = 4p - (p + 1 - j)²`;
* `HurwitzClassLower` — that Hurwitz class number is at least `κ√p`.

This file reduces both to smaller explicit analytic leaves and reassembles
`L27DeuringInputs`.

## Hurwitz side

Write `hurwitz D` for the Hurwitz class number `H(-D)` of the negative
discriminant `-D`, so that `D = 4p - t²` is the usual positive Frobenius
discriminant.  The lower bound is split into

* `HurwitzSiegelLowerTrace p hurwitz c`: the Siegel/Brauer–Siegel lower bound
  in the normalization used by LP §7, `H(-D) ≥ c√D` on the Frobenius-trace
  discriminants `D = 4p - t² > 0` (a statement about the class-number function
  alone, with no reference to the curve model or the smooth predicate).  The
  window form `HurwitzSiegelLowerWindow` and the global form
  `HurwitzSiegelLower` are also provided; each restricts to the trace form;
* `HurwitzDiscriminantScale p smooth θ`: the geometric nondegeneracy
  `θp ≤ D(p,j)` on smooth orders.  This is what lets the `√D` lower bound be
  converted into the Hasse-scale `√p` lower bound.

The arithmetic conversion is `hurwitzClassLower_of_siegel_trace_scale`: if
`κ ≤ c√θ`, then the two leaves give `HurwitzClassLower`.  The special case
`θ = 1` is supplied by `CentralTrace`, the statement that a smooth order has
trace `t = p + 1 - j` with `t² ≤ 3p`; then `D = 4p - t² ≥ p`, and
`hurwitzClassLower_of_siegel_centralTrace` only needs `κ ≤ c`.

The scale leaf is genuinely needed: `HasseBound` gives only `D ≥ 0`, and the
current `L27_1Inputs` contains no relation between the smooth predicate and the
interior of the Hasse window.  At the Hasse endpoints `D` can be small and the
`√p` lower bound is false for the actual Hurwitz class number.  The leaf is
therefore stated explicitly, not smuggled in; if the paper's smooth set is the
whole window, this is the exact missing restriction on that set.

## Deuring side

The one-sided trace formula is split into

* `DeuringTraceClassLower p traceCount hurwitz`: the Deuring/Waterhouse
  correspondence at the level of Frobenius traces,
  `H(-(4p - t²)) ≤ #curves with trace t`;
* `OrderCountContainsTraceClass p smooth orderCount traceCount`: the
  combinatorial fact that the curves of a fixed trace `t` are among the curves
  of the unique group order `j = p + 1 - t`.

The pointwise inequality `DeuringTraceFormula` follows by transitivity
(`deuringTraceFormula_of_traceClasses`).  The exact Deuring identity
`DeuringWaterhouseExact` implies the one-sided trace leaf
(`deuringTraceClassLower_of_exact`), recording that no curve is lost by passing
to the one-sided form.

## Bundle and capstone

`L27HurwitzInputs I` stores the two Hurwitz leaves, the two trace leaves, and the
two geometric fields already present in `L27DeuringInputs`
(`JInvariantStratification` and `4 ≤ p`).  `toDeuringInputs` reassembles
`L27DeuringInputs I`; all downstream L27.1 conclusions (`deuringLenstraCounts`,
`toPaperInputs`, `reduced_ledger`, `reduced_paper`, `toRatedLeaf`, `slot`, and
`reduction_of_hurwitz`) are derived by delegation and are also restated here.

No `sorry`, `admit`, `axiom`, or `native_decide`.  No count, class number, or
loss is set to zero.
-/

namespace Cogentic.RandomizedL27Hurwitz

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The Hurwitz class-number leaves -/

/-- The Frobenius discriminant attached directly to a trace `t`:
`4p - t²`.  It is nonnegative inside the Hasse interval and positive in its
interior. -/
def traceDisc (p : ℕ) (t : ℤ) : ℤ := 4 * (p : ℤ) - t ^ 2

/-- The trace discriminant of a group order is the Frobenius discriminant. -/
theorem traceDisc_hasseTrace (p j : ℕ) :
    traceDisc p (hasseTrace p j) = frobeniusDisc p j := rfl

/-- **Siegel/Brauer–Siegel lower bound for Hurwitz class numbers.**  For every
positive discriminant `D`, the Hurwitz class number `H(-D)` is at least
`c√D`.  This is the analytic class-number estimate, stated without reference to
the curve model or to the smooth predicate. -/
def HurwitzSiegelLower (hurwitz : ℤ → ℝ) (c : ℝ) : Prop :=
  ∀ D : ℤ, 0 < D → c * Real.sqrt (D : ℝ) ≤ hurwitz D

/-- **Siegel lower bound on the Hasse window.**  `H(-D) ≥ c√D` for positive
discriminants below the Hasse endpoint `4p`.  This is weaker than
`HurwitzSiegelLower`; it is an intermediate form between the global estimate and
the trace-restricted leaf stored in `L27HurwitzInputs`. -/
def HurwitzSiegelLowerWindow (p : ℕ → ℕ) (hurwitz : ℤ → ℝ) (c : ℝ) : Prop :=
  ∀ n (D : ℤ), 0 < D → D ≤ 4 * (p n : ℤ) →
    c * Real.sqrt (D : ℝ) ≤ hurwitz D

/-- **Siegel lower bound on Frobenius-trace discriminants.**  The smallest
analytic leaf used below: `H(-(4p - t²)) ≥ c√(4p - t²)` for every trace `t`
whose discriminant is positive.  This is the exact set of discriminants that
the Deuring trace formula evaluates, with no reference to the smooth predicate
or to the order count. -/
def HurwitzSiegelLowerTrace (p : ℕ → ℕ) (hurwitz : ℤ → ℝ) (c : ℝ) : Prop :=
  ∀ n (t : ℤ), 0 < traceDisc (p n) t →
    c * Real.sqrt ((traceDisc (p n) t : ℤ) : ℝ) ≤ hurwitz (traceDisc (p n) t)

/-- The global Siegel bound restricts to the Hasse window. -/
theorem hurwitzSiegelLowerWindow_of_global {p : ℕ → ℕ} {hurwitz : ℤ → ℝ}
    {c : ℝ} (h : HurwitzSiegelLower hurwitz c) :
    HurwitzSiegelLowerWindow p hurwitz c :=
  fun _ D hD _ => h D hD

/-- The windowed Siegel bound restricts to Frobenius-trace discriminants. -/
theorem hurwitzSiegelLowerTrace_of_window {p : ℕ → ℕ} {hurwitz : ℤ → ℝ}
    {c : ℝ} (h : HurwitzSiegelLowerWindow p hurwitz c) :
    HurwitzSiegelLowerTrace p hurwitz c := by
  intro n t ht
  apply h n (traceDisc (p n) t) ht
  unfold traceDisc
  have hsq : (0 : ℤ) ≤ t ^ 2 := sq_nonneg t
  linarith

/-- The global Siegel bound restricts to Frobenius-trace discriminants. -/
theorem hurwitzSiegelLowerTrace_of_global {p : ℕ → ℕ} {hurwitz : ℤ → ℝ}
    {c : ℝ} (h : HurwitzSiegelLower hurwitz c) :
    HurwitzSiegelLowerTrace p hurwitz c :=
  hurwitzSiegelLowerTrace_of_window (hurwitzSiegelLowerWindow_of_global h)

/-- **Nondegenerate Frobenius discriminants on smooth orders.**  A smooth order
retains at least a `θ`-fraction of the Hasse width: `θp ≤ 4p - t²`, where
`t = p + 1 - j`.  This is the geometric leaf needed to pass from the `√D`
Siegel bound to the `√p` Hasse-scale bound. -/
def HurwitzDiscriminantScale (p : ℕ → ℕ) (smooth : ℕ → ℕ → Bool)
    (θ : ℝ) : Prop :=
  ∀ n j, smooth n j = true →
    θ * (p n : ℝ) ≤ (frobeniusDisc (p n) j : ℝ)

/-- **Central trace on smooth orders.**  The trace `t = p + 1 - j` of a smooth
order satisfies `t² ≤ 3p`.  This is the concrete `θ = 1` form of
`HurwitzDiscriminantScale`: it keeps the order out of the outer part of the
Hasse interval, where `t²` approaches the endpoint value `4p`. -/
def CentralTrace (p : ℕ → ℕ) (smooth : ℕ → ℕ → Bool) : Prop :=
  ∀ n j, smooth n j = true →
    ((hasseTrace (p n) j : ℝ)) ^ 2 ≤ 3 * (p n : ℝ)

/-- The central-trace leaf gives the scale leaf with `θ = 1`. -/
theorem hurwitzDiscriminantScale_one_of_centralTrace {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} (h : CentralTrace p smooth) :
    HurwitzDiscriminantScale p smooth 1 := by
  intro n j hs
  have ht := h n j hs
  have hcast : ((frobeniusDisc (p n) j : ℤ) : ℝ) =
      4 * (p n : ℝ) - ((hasseTrace (p n) j : ℝ)) ^ 2 := by
    unfold frobeniusDisc hasseTrace
    push_cast
    ring
  rw [hcast]
  nlinarith [ht]

/-- The scale leaf makes every smooth Frobenius discriminant positive. -/
theorem frobeniusDisc_pos_of_scale {p : ℕ → ℕ} {smooth : ℕ → ℕ → Bool} {θ : ℝ}
    (hp : ∀ n, 0 < p n) (hθ : 0 < θ)
    (hscale : HurwitzDiscriminantScale p smooth θ) {n j : ℕ}
    (hs : smooth n j = true) : 0 < frobeniusDisc (p n) j := by
  have hpR : (0 : ℝ) < (p n : ℝ) := by exact_mod_cast hp n
  have hθp : (0 : ℝ) < θ * (p n : ℝ) := mul_pos hθ hpR
  have hDscale := hscale n j hs
  have hposR : (0 : ℝ) < (frobeniusDisc (p n) j : ℝ) :=
    lt_of_lt_of_le hθp hDscale
  exact_mod_cast hposR

/-- **The Hurwitz lower bound from the trace-restricted Siegel estimate and
nondegeneracy.**  If `κ ≤ c√θ`, the class-number bound
`H(-D) ≥ c√D` on Frobenius-trace discriminants, and the geometric inequality
`θp ≤ D(p,j)` imply `HurwitzClassLower` at the Hasse scale. -/
theorem hurwitzClassLower_of_siegel_trace_scale {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {hurwitz : ℤ → ℝ} {κ c θ : ℝ}
    (hp : ∀ n, 0 < p n) (hθ : 0 < θ) (hc : 0 ≤ c)
    (hκ : κ ≤ c * Real.sqrt θ)
    (hsiegel : HurwitzSiegelLowerTrace p hurwitz c)
    (hscale : HurwitzDiscriminantScale p smooth θ) :
    HurwitzClassLower p smooth hurwitz κ := by
  intro n j hs
  have hDpos : (0 : ℤ) < frobeniusDisc (p n) j :=
    frobeniusDisc_pos_of_scale hp hθ hscale hs
  have hDposT : 0 < traceDisc (p n) (hasseTrace (p n) j) := by
    simpa [traceDisc, frobeniusDisc] using hDpos
  have hS : c * Real.sqrt ((frobeniusDisc (p n) j : ℤ) : ℝ) ≤
      hurwitz (frobeniusDisc (p n) j) := by
    simpa [traceDisc, frobeniusDisc] using
      hsiegel n (hasseTrace (p n) j) hDposT
  have hscale' : θ * (p n : ℝ) ≤ (frobeniusDisc (p n) j : ℝ) := hscale n j hs
  have hsqrt := Real.sqrt_le_sqrt hscale'
  have hsqrtmul : Real.sqrt (θ * (p n : ℝ)) =
      Real.sqrt θ * Real.sqrt (p n : ℝ) := by
    rw [Real.sqrt_mul hθ.le]
  have hstep :
      κ * Real.sqrt (p n : ℝ) ≤
        c * Real.sqrt ((frobeniusDisc (p n) j : ℤ) : ℝ) := by
    calc
      κ * Real.sqrt (p n : ℝ) ≤
          (c * Real.sqrt θ) * Real.sqrt (p n : ℝ) :=
        mul_le_mul_of_nonneg_right hκ (Real.sqrt_nonneg _)
      _ = c * (Real.sqrt θ * Real.sqrt (p n : ℝ)) := by ring
      _ = c * Real.sqrt (θ * (p n : ℝ)) := by rw [hsqrtmul]
      _ ≤ c * Real.sqrt ((frobeniusDisc (p n) j : ℤ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrt hc
  exact hstep.trans hS

/-- **The Hurwitz lower bound from the windowed Siegel estimate.**  The window
form is stronger than the trace-restricted form, so it implies the same
conclusion. -/
theorem hurwitzClassLower_of_siegel_window_scale {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {hurwitz : ℤ → ℝ} {κ c θ : ℝ}
    (hp : ∀ n, 0 < p n) (hθ : 0 < θ) (hc : 0 ≤ c)
    (hκ : κ ≤ c * Real.sqrt θ)
    (hsiegel : HurwitzSiegelLowerWindow p hurwitz c)
    (hscale : HurwitzDiscriminantScale p smooth θ) :
    HurwitzClassLower p smooth hurwitz κ :=
  hurwitzClassLower_of_siegel_trace_scale hp hθ hc hκ
    (hurwitzSiegelLowerTrace_of_window hsiegel) hscale

/-- **The Hurwitz lower bound from the global Siegel estimate.**  The global
form implies the trace-restricted leaf, so this corollary keeps the classical
statement usable. -/
theorem hurwitzClassLower_of_siegel_scale {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {hurwitz : ℤ → ℝ} {κ c θ : ℝ}
    (hp : ∀ n, 0 < p n) (hθ : 0 < θ) (hc : 0 ≤ c)
    (hκ : κ ≤ c * Real.sqrt θ)
    (hsiegel : HurwitzSiegelLower hurwitz c)
    (hscale : HurwitzDiscriminantScale p smooth θ) :
    HurwitzClassLower p smooth hurwitz κ :=
  hurwitzClassLower_of_siegel_trace_scale hp hθ hc hκ
    (hurwitzSiegelLowerTrace_of_global hsiegel) hscale

/-- **The Hurwitz lower bound from the trace-restricted Siegel estimate and a
central trace.**  The `θ = 1` specialization: `H(-D) ≥ c√D` on
Frobenius-trace discriminants, `D ≥ p`, and `κ ≤ c` imply
`HurwitzClassLower`. -/
theorem hurwitzClassLower_of_siegel_centralTrace {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {hurwitz : ℤ → ℝ} {κ c : ℝ}
    (hp : ∀ n, 0 < p n) (hc : 0 ≤ c) (hκ : κ ≤ c)
    (hsiegel : HurwitzSiegelLowerTrace p hurwitz c)
    (hcentral : CentralTrace p smooth) :
    HurwitzClassLower p smooth hurwitz κ := by
  refine hurwitzClassLower_of_siegel_trace_scale hp zero_lt_one hc ?_ hsiegel
    (hurwitzDiscriminantScale_one_of_centralTrace hcentral)
  simpa using hκ

/-! ## 2. The Deuring trace-class leaves -/

/-- **One-sided Deuring/Waterhouse at fixed trace.**  For a positive Frobenius
discriminant `4p - t²`, the Hurwitz class number is realised by at least that
many curves over `F_p` with trace `t`.  This is the analytic trace-class form of
Deuring's correspondence, before identifying the group order. -/
def DeuringTraceClassLower (p : ℕ → ℕ) (traceCount : ℕ → ℤ → ℕ)
    (hurwitz : ℤ → ℝ) : Prop :=
  ∀ n (t : ℤ), 0 < traceDisc (p n) t →
    hurwitz (traceDisc (p n) t) ≤ (traceCount n t : ℝ)

/-- **Exact Deuring/Waterhouse at fixed trace.**  The stronger two-sided form:
the number of curves with trace `t` is exactly the Hurwitz class number of
`4p - t²`.  This is the classical statement; the one-sided leaf is its
inequality consequence. -/
def DeuringWaterhouseExact (p : ℕ → ℕ) (traceCount : ℕ → ℤ → ℕ)
    (hurwitz : ℤ → ℝ) : Prop :=
  ∀ n (t : ℤ), 0 < traceDisc (p n) t →
    (traceCount n t : ℝ) = hurwitz (traceDisc (p n) t)

/-- The exact trace identity implies the one-sided trace leaf. -/
theorem deuringTraceClassLower_of_exact {p : ℕ → ℕ}
    {traceCount : ℕ → ℤ → ℕ} {hurwitz : ℤ → ℝ}
    (h : DeuringWaterhouseExact p traceCount hurwitz) :
    DeuringTraceClassLower p traceCount hurwitz := by
  intro n t ht
  rw [h n t ht]

/-- **The curves of a fixed trace lie among the curves of its group order.**
A curve over `F_p` with trace `t` has exactly `p + 1 - t` points, so its trace
class is contained in the order count at `j = p + 1 - t`.  This is the
model-compatibility leaf separating the analytic Deuring count from the
combinatorial order count. -/
def OrderCountContainsTraceClass (p : ℕ → ℕ) (smooth : ℕ → ℕ → Bool)
    (orderCount : ℕ → ℕ → ℕ) (traceCount : ℕ → ℤ → ℕ) : Prop :=
  ∀ n j, smooth n j = true →
    traceCount n (hasseTrace (p n) j) ≤ orderCount n j

/-- **`DeuringTraceFormula` from the trace-class leaves.**  The analytic
one-sided Deuring count and the order-count containment compose pointwise. -/
theorem deuringTraceFormula_of_traceClasses {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {orderCount : ℕ → ℕ → ℕ}
    {traceCount : ℕ → ℤ → ℕ} {hurwitz : ℤ → ℝ}
    (htrace : DeuringTraceClassLower p traceCount hurwitz)
    (hcontains : OrderCountContainsTraceClass p smooth orderCount traceCount)
    (hpos : ∀ n j, smooth n j = true → 0 < frobeniusDisc (p n) j) :
    DeuringTraceFormula p smooth orderCount hurwitz := by
  intro n j hs
  have ht : 0 < traceDisc (p n) (hasseTrace (p n) j) := by
    simpa [traceDisc, frobeniusDisc] using hpos n j hs
  have h1 : hurwitz (frobeniusDisc (p n) j) ≤
      (traceCount n (hasseTrace (p n) j) : ℝ) := by
    simpa [traceDisc, frobeniusDisc] using
      htrace n (hasseTrace (p n) j) ht
  have h2 : (traceCount n (hasseTrace (p n) j) : ℝ) ≤ (orderCount n j : ℝ) := by
    exact_mod_cast hcontains n j hs
  exact h1.trans h2

/-! ## 3. The bundled Hurwitz inputs -/

/-- **The explicit analytic leaves behind LP §7's Hurwitz/Deuring counts.**

* `hurwitz` — the Hurwitz class number `H(-D)`;
* `traceCount` — the number of curves of each Frobenius trace;
* `c`, `θ` — the Siegel constant and the discriminant nondegeneracy fraction;
* `siegel_lower` — `H(-D) ≥ c√D` on Frobenius-trace discriminants;
* `disc_scale` — `θp ≤ D(p,j)` on smooth orders;
* `trace_class_lower` — the one-sided Deuring/Waterhouse count at fixed trace;
* `orderCount_contains_trace` — trace classes are contained in order counts;
* `j_invariant_strata` — the `j`-line stratification already used by
  `L27DeuringInputs`;
* `p_ge_four` — the small-prime prepass.

No field sets a class number, curve count, or probability to zero. -/
structure L27HurwitzInputs (I : L27_1Inputs) where
  /-- The Hurwitz class number `H(-D)`. -/
  hurwitz : ℤ → ℝ
  /-- Number of curves over `F_p` with a given Frobenius trace. -/
  traceCount : ℕ → ℤ → ℕ
  /-- Siegel constant in `H(-D) ≥ c√D`. -/
  c : ℝ
  /-- Nondegeneracy fraction `D(p,j) ≥ θp` on smooth orders. -/
  θ : ℝ
  /-- The Siegel constant is positive. -/
  c_pos : 0 < c
  /-- The nondegeneracy fraction is positive. -/
  θ_pos : 0 < θ
  /-- The Hasse-scale constant is below the Siegel constant at scale `√θ`. -/
  kappa_le : I.κ ≤ c * Real.sqrt θ
  /-- Siegel's lower bound on Frobenius-trace discriminants. -/
  siegel_lower : HurwitzSiegelLowerTrace I.p hurwitz c
  /-- Smooth Frobenius discriminants retain a `θ`-fraction of the Hasse width. -/
  disc_scale : HurwitzDiscriminantScale I.p I.smooth θ
  /-- One-sided Deuring/Waterhouse at fixed trace. -/
  trace_class_lower : DeuringTraceClassLower I.p traceCount hurwitz
  /-- Curves of a fixed trace are contained in the curves of that order. -/
  orderCount_contains_trace :
    OrderCountContainsTraceClass I.p I.smooth I.orderCount traceCount
  /-- The `j`-line stratification of the curves. -/
  j_invariant_strata : JInvariantStratification I.p I.orderCount I.orderTop
  /-- The target prime exceeds the two removed small primes. -/
  p_ge_four : ∀ n, 4 ≤ I.p n

namespace L27HurwitzInputs

variable {I : L27_1Inputs}

/-- Smooth Frobenius discriminants are positive. -/
theorem frobeniusDisc_pos (D : L27HurwitzInputs I) {n j : ℕ}
    (hs : I.smooth n j = true) : 0 < frobeniusDisc (I.p n) j :=
  frobeniusDisc_pos_of_scale (fun n => I.p_pos n) D.θ_pos D.disc_scale hs

/-- **Hasse compatibility.**  The smooth Frobenius discriminant lies in the
explicit window `[θp, 4p]`; the upper endpoint is the Hasse estimate
`frobeniusDisc_le_four_mul`. -/
theorem frobeniusDisc_window (D : L27HurwitzInputs I) {n j : ℕ}
    (hs : I.smooth n j = true) :
    D.θ * (I.p n : ℝ) ≤ (frobeniusDisc (I.p n) j : ℝ) ∧
      (frobeniusDisc (I.p n) j : ℝ) ≤ 4 * (I.p n : ℝ) := by
  refine ⟨D.disc_scale n j hs, ?_⟩
  have h := frobeniusDisc_le_four_mul (I.p n) j
  exact_mod_cast h

/-- The Hurwitz class-number lower bound from the Siegel and scale leaves. -/
theorem hurwitzClassLower (D : L27HurwitzInputs I) :
    HurwitzClassLower I.p I.smooth D.hurwitz I.κ :=
  hurwitzClassLower_of_siegel_trace_scale (fun n => I.p_pos n) D.θ_pos
    D.c_pos.le D.kappa_le D.siegel_lower D.disc_scale

/-- The one-sided Deuring trace formula from the trace-class leaves. -/
theorem deuringTraceFormula (D : L27HurwitzInputs I) :
    DeuringTraceFormula I.p I.smooth I.orderCount D.hurwitz :=
  deuringTraceFormula_of_traceClasses D.trace_class_lower
    D.orderCount_contains_trace (fun _ _ hs => D.frobeniusDisc_pos hs)

/-- Reassemble the smaller `L27DeuringInputs` bundle. -/
def toDeuringInputs (D : L27HurwitzInputs I) : L27DeuringInputs I where
  hurwitz := D.hurwitz
  deuring_trace := D.deuringTraceFormula
  hurwitz_class_lower := D.hurwitzClassLower
  j_invariant_strata := D.j_invariant_strata
  p_ge_four := D.p_ge_four

/-- **Direct form of the reduction.**  The four analytic leaves plus the two
geometric fields already required by `L27DeuringInputs` reassemble the bundle
without passing through the structure. -/
def toDeuringInputs_of_leaves {I : L27_1Inputs}
    (hurwitz : ℤ → ℝ) (traceCount : ℕ → ℤ → ℕ) {c θ : ℝ}
    (c_pos : 0 < c) (θ_pos : 0 < θ)
    (kappa_le : I.κ ≤ c * Real.sqrt θ)
    (siegel : HurwitzSiegelLowerTrace I.p hurwitz c)
    (scale : HurwitzDiscriminantScale I.p I.smooth θ)
    (trace : DeuringTraceClassLower I.p traceCount hurwitz)
    (contains : OrderCountContainsTraceClass I.p I.smooth I.orderCount traceCount)
    (strata : JInvariantStratification I.p I.orderCount I.orderTop)
    (hp4 : ∀ n, 4 ≤ I.p n) :
    L27DeuringInputs I where
  hurwitz := hurwitz
  deuring_trace := deuringTraceFormula_of_traceClasses trace contains
    (fun _ _ hs => frobeniusDisc_pos_of_scale (fun n => I.p_pos n) θ_pos scale hs)
  hurwitz_class_lower :=
    hurwitzClassLower_of_siegel_trace_scale (fun n => I.p_pos n) θ_pos
      c_pos.le kappa_le siegel scale
  j_invariant_strata := strata
  p_ge_four := hp4

/-- The per-order Deuring/Lenstra bound. -/
theorem deuringSmoothOrderCount (D : L27HurwitzInputs I) :
    DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ :=
  L27DeuringInputs.deuringSmoothOrderCount D.toDeuringInputs

/-- The sharp `2p + 8` total. -/
theorem jInvariantCurveTotal (D : L27HurwitzInputs I) :
    JInvariantCurveTotal I.p I.orderCount I.orderTop :=
  L27DeuringInputs.jInvariantCurveTotal D.toDeuringInputs

/-- The paper's `≤ 4p` total. -/
theorem hasseWindowCurveTotal (D : L27HurwitzInputs I) :
    HasseWindowCurveTotal I.p I.orderCount I.orderTop :=
  L27DeuringInputs.hasseWindowCurveTotal D.toDeuringInputs

/-- The bundled `DeuringLenstraCounts` hypothesis of `L27_1Sub`. -/
theorem deuringLenstraCounts (D : L27HurwitzInputs I) :
    DeuringLenstraCounts I :=
  L27DeuringInputs.deuringLenstraCounts D.toDeuringInputs

/-- Reassemble `L27PaperInputs` from the Hurwitz leaves and the five remaining
LP §7 inputs. -/
theorem toPaperInputs (D : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) :
    L27PaperInputs I :=
  L27DeuringInputs.toPaperInputs D.toDeuringInputs hhasse h0 h1 h2 hstage

/-- The L27.1 ledger from the Hurwitz leaves. -/
theorem reduced_ledger (D : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  L27DeuringInputs.reduced_ledger D.toDeuringInputs hhasse h0 h1 h2 hstage
    hbudget hlog

/-- The manuscript-rate deficit bound from the Hurwitz leaves. -/
theorem reduced_paper (D : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  L27DeuringInputs.reduced_paper D.toDeuringInputs hhasse h0 h1 h2 hstage
    hbudget hlog

/-- The L27.1 `RatedLeaf` from the Hurwitz leaves. -/
def toRatedLeaf (D : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) : RatedLeaf :=
  L27DeuringInputs.toRatedLeaf D.toDeuringInputs hhasse h0 h1 h2 hstage
    hbudget hlog

/-- The `C5` slot `exp (-2H)` for the assembled leaf. -/
theorem slot (D : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop,
      (D.toRatedLeaf hhasse h0 h1 h2 hstage hbudget hlog).loss n ≤
        Real.exp (-(2 : ℝ) * scale n) :=
  (D.toRatedLeaf hhasse h0 h1 h2 hstage hbudget hlog).slot

end L27HurwitzInputs

/-! ## 4. Capstone reduction -/

/-- **The full reduction from the Hurwitz/Deuring analytic leaves.**  The
Siegel bound, the discriminant scale, the trace-class count, the order-count
containment, Hasse, the three gcd-exit facts, stage-one success, the curve
budget, and the `log₂` multiplier imply both bundled `L27_1Sub` hypotheses and
both deficit conclusions. -/
theorem reduction_of_hurwitz {I : L27_1Inputs} (D : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  reduction_of_deuring D.toDeuringInputs hhasse h0 h1 h2 hstage hbudget hlog

/-- The Deuring half of the capstone, stated on its own. -/
theorem deuringLenstraCounts_of_hurwitz {I : L27_1Inputs}
    (D : L27HurwitzInputs I) : DeuringLenstraCounts I :=
  D.deuringLenstraCounts

/-- **Compatibility with `RandomizedL27Deuring`.**  Rebuilding the paper inputs
from the Hurwitz leaves yields exactly the same bundled Deuring/Lenstra
hypothesis as `L27Deuring`'s `L27PaperInputs`. -/
theorem deuringLenstraCounts_via_paperInputs {I : L27_1Inputs}
    (D : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) :
    DeuringLenstraCounts I :=
  L27PaperInputs.deuring (D.toPaperInputs hhasse h0 h1 h2 hstage)

/-- **No-loss check: the trace split is pointwise.**  The one-sided formula
`DeuringTraceFormula` is definitionally the pointwise inequality used in the
trace-class reduction; the two statements have the same content after
unfolding. -/
theorem deuringTraceFormula_iff_pointwise {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {orderCount : ℕ → ℕ → ℕ} {hurwitz : ℤ → ℝ} :
    DeuringTraceFormula p smooth orderCount hurwitz ↔
      ∀ n j, smooth n j = true →
        hurwitz (frobeniusDisc (p n) j) ≤ (orderCount n j : ℝ) :=
  Iff.rfl

/-- **No-loss check: the Hurwitz lower bound is the pointwise Siegel-scale
inequality.** -/
theorem hurwitzClassLower_iff_pointwise {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {hurwitz : ℤ → ℝ} {κ : ℝ} :
    HurwitzClassLower p smooth hurwitz κ ↔
      ∀ n j, smooth n j = true →
        κ * Real.sqrt (p n) ≤ hurwitz (frobeniusDisc (p n) j) :=
  Iff.rfl

/-! ## Axiom audit -/

#print axioms traceDisc_hasseTrace
#print axioms hurwitzDiscriminantScale_one_of_centralTrace
#print axioms frobeniusDisc_pos_of_scale
#print axioms hurwitzSiegelLowerWindow_of_global
#print axioms hurwitzSiegelLowerTrace_of_window
#print axioms hurwitzSiegelLowerTrace_of_global
#print axioms hurwitzClassLower_of_siegel_trace_scale
#print axioms hurwitzClassLower_of_siegel_window_scale
#print axioms hurwitzClassLower_of_siegel_scale
#print axioms hurwitzClassLower_of_siegel_centralTrace
#print axioms deuringTraceClassLower_of_exact
#print axioms deuringTraceFormula_of_traceClasses
#print axioms L27HurwitzInputs.frobeniusDisc_pos
#print axioms L27HurwitzInputs.frobeniusDisc_window
#print axioms L27HurwitzInputs.hurwitzClassLower
#print axioms L27HurwitzInputs.deuringTraceFormula
#print axioms L27HurwitzInputs.toDeuringInputs
#print axioms L27HurwitzInputs.toDeuringInputs_of_leaves
#print axioms L27HurwitzInputs.deuringSmoothOrderCount
#print axioms L27HurwitzInputs.jInvariantCurveTotal
#print axioms L27HurwitzInputs.hasseWindowCurveTotal
#print axioms L27HurwitzInputs.deuringLenstraCounts
#print axioms L27HurwitzInputs.toPaperInputs
#print axioms L27HurwitzInputs.reduced_ledger
#print axioms L27HurwitzInputs.reduced_paper
#print axioms L27HurwitzInputs.toRatedLeaf
#print axioms L27HurwitzInputs.slot
#print axioms reduction_of_hurwitz
#print axioms deuringLenstraCounts_of_hurwitz
#print axioms deuringLenstraCounts_via_paperInputs
#print axioms deuringTraceFormula_iff_pointwise
#print axioms hurwitzClassLower_iff_pointwise

end

end Cogentic.RandomizedL27Hurwitz
