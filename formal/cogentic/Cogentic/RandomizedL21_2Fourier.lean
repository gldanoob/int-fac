import Cogentic.RandomizedL21_2Perron
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

set_option linter.style.haveILetI false

/-!
# L21.2: the Fourier / Abel and tent-Chebyshev reductions

`Cogentic.RandomizedL21_2Perron` isolates two paper-level analytic statements
of the smooth-numbers-near-centres estimate:

* `fourierSupBound` — the partial-summation Fourier-gap bound
  `sup_{|t| ≤ X³} |μ̂ (t) - ν̂ (t)| ≤ e^{-a/3} U^{Ceps}`;
* `tentChebyshev` — the Chebyshev/tent comparison
  `badCount / (X+1) ≤ 4 (kΔ)² · l2Term`.

This file reduces both to strictly smaller explicit inputs.

## Fourier gap: the Abel step

The paper's gap is the difference between the discrete log-prime measure
`μ = (1/(2Δ)) Σ (log q)/q · δ_{log q}` on `[a,b]` and the Lebesgue probability
measure `ν = du/(2Δ)`.  Partial summation with the weight `1/v` rewrites it as

`μ̂(t) - ν̂(t) = (1/(2Δ)) · Abel (v ↦ Σ_{q≤v} (log q) q^{-it} - v^{1-it}/(1-it))`,

where `Abel f = f(e^b)/e^b - f(e^a)/e^a + ∫_{e^a}^{e^b} f(v)/v² dv`.
The right-hand side is the explicit function `abelGapOf`.  The smallest
structural input in the new bundle is therefore the identification
`fourierGap_eq_abel` of the abstract gap with `abelGapOf`; everything after it
is *proved*:

* `abel_transform_norm_le` is the real-variable content of partial summation:
  an `O (K v^{2/3} U^C)` error on `[e^a,e^b]` has Abel transform
  `O (K U^C e^{-a/3})`, because `∫ v^{-4/3} dv ≪ e^{-a/3}`;
* `twistedErr_le` absorbs the three Perron errors of `perronShift` into
  `3 Kper v^{2/3} U^Cper` (the same absorption as
  `RandomizedL21_2.twisted_prime_sum`, re-proved here for the new bundle);
* the polynomial/polynomial absorption `Kper` bounded, `Ceps ≥ Cper + 2`,
  `k ≤ log X` and `1/Δ ≤ log X` gives the displayed `supEps` bound.

The only remaining elementary parameter inputs are `Kper_bdd` (the Perron
constant is absolute), `Ceps_ge`, `k_le_U` and `a_ge_log_two`.

## Tent smoothing: the Chebyshev count

`tentChebyshev` is reduced to a *finite* Chebyshev/Markov inequality.  The new
bundle carries a finite family of centres `Fin (N n)` and an explicit
discrepancy profile `deficit n i`.  The bad set is
`{i : 1/(2kΔ) ≤ |deficit n i|}`, and `badCount` is *defined* as its density in
the dyad.  The Markov step

`#{bad}/N ≤ (2kΔ)² · (1/N) Σ deficit²`

is proved in `card_le_energy` from the single finite-sum inequality
`S.card · τ² ≤ Σ g²`.  The only analytic input left is the mean-square /
Plancherel comparison `tentMeanSquare`, which bounds the deficit energy by the
three frequency contributions `low + middle + tail`.

The assembled reduction is
`L21_2FourierInputs.toPerronInputs : L21_2FourierInputs → L21_2PerronInputs`,
hence also `toReducedInputs`, `toInputs`, `toRatedLeaf`, `toSubexpLeaf`, the
`B = 2` ledger slot and the paper-assumption reassembly.  The loss is still the
genuine quotient `badCount/(X+1)`, never set to zero.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2Fourier

open Filter Real MeasureTheory
open scoped BigOperators
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## The Abel transform of the twisted error -/

/-- The twisted Perron error `Σ_{q≤v} (log q) q^{-it} - v^{1-it}/(1-it)`. -/
def twistedErr (v t : ℝ) : ℂ :=
  twistedPrimeSum v t - twistedMain v t

/-- The Abel transform of the twisted error: the Fourier gap after the
partial-summation step with weight `1/v`.  Its first two terms are the boundary
contributions `f(e^b)/e^b - f(e^a)/e^a` and the integral is
`∫_{e^a}^{e^b} f(v)/v² dv`. -/
def abelGapOf (X : ℕ → ℝ) (c : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ((1 / (2 * spacingOf X c n) : ℝ) : ℂ) *
    (twistedErr (Real.exp (bOf X c n)) t / (Real.exp (bOf X c n) : ℂ) -
      twistedErr (Real.exp (aOf X c n)) t / (Real.exp (aOf X c n) : ℂ) +
      ∫ v in (Real.exp (aOf X c n))..(Real.exp (bOf X c n)),
        twistedErr v t / (v : ℂ) ^ 2)

/-- **Abel/partial-summation error propagation.**  If `f` is `O (K v^{2/3} U^C)`
on `[e^a, e^b]`, then its Abel transform with weight `1/v` is
`O (K U^C e^{-a/3})`.  The integral is controlled by `∫ v^{-4/3} dv ≪ e^{-a/3}`;
no arithmetic input is used beyond `a ≤ b` and `K, U ≥ 0`. -/
theorem abel_transform_norm_le {a b K U C : ℝ} {f : ℝ → ℂ}
    (hab : a ≤ b) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (hf : ∀ v ∈ Set.Icc (Real.exp a) (Real.exp b),
      ‖f v‖ ≤ K * v ^ (2 / 3 : ℝ) * U ^ C) :
    ‖f (Real.exp b) / (Real.exp b : ℂ) - f (Real.exp a) / (Real.exp a : ℂ) +
        ∫ v in (Real.exp a)..(Real.exp b), f v / (v : ℂ) ^ 2‖ ≤
      5 * K * Real.exp (-(a / 3)) * U ^ C := by
  have hA : 0 < Real.exp a := Real.exp_pos a
  have hB : 0 < Real.exp b := Real.exp_pos b
  have hAB : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  have hUc : 0 ≤ U ^ C := Real.rpow_nonneg hU C
  -- Boundary contribution at an arbitrary point `x` of the band.
  have hend (x : ℝ) (hax : a ≤ x) (hxb : x ≤ b) :
      ‖f (Real.exp x) / (Real.exp x : ℂ)‖ ≤ K * Real.exp (-(a / 3)) * U ^ C := by
    have hx : 0 < Real.exp x := Real.exp_pos x
    have hxI : Real.exp x ∈ Set.Icc (Real.exp a) (Real.exp b) :=
      ⟨Real.exp_le_exp.mpr hax, Real.exp_le_exp.mpr hxb⟩
    have h1 := hf (Real.exp x) hxI
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    have hdiv : Real.exp x ^ (2 / 3 : ℝ) / Real.exp x = Real.exp (-(x / 3)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one (Real.exp x), ← Real.rpow_add hx,
        Real.rpow_def_of_pos hx, Real.log_exp]
      congr 1
      ring
    calc
      ‖f (Real.exp x)‖ / Real.exp x
          ≤ (K * Real.exp x ^ (2 / 3 : ℝ) * U ^ C) / Real.exp x := by gcongr
      _ = K * (Real.exp x ^ (2 / 3 : ℝ) / Real.exp x) * U ^ C := by ring
      _ = K * Real.exp (-(x / 3)) * U ^ C := by rw [hdiv]
      _ ≤ K * Real.exp (-(a / 3)) * U ^ C := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hK) hUc
        exact Real.exp_le_exp.mpr (by linarith)
  -- The integral term.
  have hInt : ‖∫ v in (Real.exp a)..(Real.exp b), f v / (v : ℂ) ^ 2‖ ≤
      3 * K * U ^ C * Real.exp (-(a / 3)) := by
    have hzero : (0 : ℝ) ∉ Set.uIcc (Real.exp a) (Real.exp b) := by
      rw [Set.uIcc_of_le hAB]
      exact fun h => hA.not_ge h.1
    have hgint : IntervalIntegrable (fun v : ℝ => K * U ^ C * v ^ (-(4 / 3) : ℝ))
        volume (Real.exp a) (Real.exp b) :=
      (intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)).const_mul (K * U ^ C)
    have hpt : ∀ᵐ v ∂volume, v ∈ Set.Ioc (Real.exp a) (Real.exp b) →
        ‖f v / (v : ℂ) ^ 2‖ ≤ K * U ^ C * v ^ (-(4 / 3) : ℝ) := by
      filter_upwards with v hv
      have hvpos : 0 < v := hA.trans hv.1
      have hvI : v ∈ Set.Icc (Real.exp a) (Real.exp b) := ⟨le_of_lt hv.1, hv.2⟩
      have h1 := hf v hvI
      rw [norm_div, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hvpos]
      have h2 : v ^ (2 : ℝ) = v ^ 2 := Real.rpow_natCast v 2
      have hpoweq : v ^ (2 / 3 : ℝ) / v ^ 2 = v ^ (-(4 / 3) : ℝ) := by
        rw [← h2, div_eq_mul_inv,
          ← Real.rpow_neg (le_of_lt hvpos) (2 : ℝ), ← Real.rpow_add hvpos]
        norm_num
      calc
        ‖f v‖ / v ^ 2 ≤ (K * v ^ (2 / 3 : ℝ) * U ^ C) / v ^ 2 := by gcongr
        _ = K * U ^ C * (v ^ (2 / 3 : ℝ) / v ^ 2) := by ring
        _ = K * U ^ C * v ^ (-(4 / 3) : ℝ) := by rw [hpoweq]
    have hrpow : (∫ v in (Real.exp a)..(Real.exp b), v ^ (-(4 / 3) : ℝ)) =
        3 * (Real.exp a ^ (-(1 / 3) : ℝ) - Real.exp b ^ (-(1 / 3) : ℝ)) := by
      rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
      norm_num
      ring
    have hAexp : Real.exp a ^ (-(1 / 3) : ℝ) = Real.exp (-(a / 3)) := by
      rw [Real.rpow_def_of_pos hA, Real.log_exp]
      congr 1
      ring
    have hBexp : Real.exp b ^ (-(1 / 3) : ℝ) = Real.exp (-(b / 3)) := by
      rw [Real.rpow_def_of_pos hB, Real.log_exp]
      congr 1
      ring
    calc
      ‖∫ v in (Real.exp a)..(Real.exp b), f v / (v : ℂ) ^ 2‖
          ≤ ∫ v in (Real.exp a)..(Real.exp b), K * U ^ C * v ^ (-(4 / 3) : ℝ) :=
        intervalIntegral.norm_integral_le_of_norm_le hAB hpt hgint
      _ = (K * U ^ C) * (∫ v in (Real.exp a)..(Real.exp b),
            v ^ (-(4 / 3) : ℝ)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = (K * U ^ C) *
            (3 * (Real.exp a ^ (-(1 / 3) : ℝ) - Real.exp b ^ (-(1 / 3) : ℝ))) := by
        rw [hrpow]
      _ ≤ (K * U ^ C) * (3 * Real.exp (-(a / 3))) := by
        have hEb_le : Real.exp (-(b / 3)) ≤ Real.exp (-(a / 3)) :=
          Real.exp_le_exp.mpr (by linarith)
        have hdiff : Real.exp a ^ (-(1 / 3) : ℝ) - Real.exp b ^ (-(1 / 3) : ℝ) ≤
            Real.exp (-(a / 3)) := by
          rw [hAexp, hBexp]
          linarith [Real.exp_pos (-(b / 3))]
        have hstep := mul_le_mul_of_nonneg_left
          (show (3 : ℝ) * (Real.exp a ^ (-(1 / 3) : ℝ) -
              Real.exp b ^ (-(1 / 3) : ℝ)) ≤ 3 * Real.exp (-(a / 3)) by
            exact mul_le_mul_of_nonneg_left hdiff (by norm_num))
          (mul_nonneg hK hUc)
        simpa only [mul_comm, mul_left_comm, mul_assoc] using hstep
      _ = 3 * K * U ^ C * Real.exp (-(a / 3)) := by ring
  have htri : ‖f (Real.exp b) / (Real.exp b : ℂ) - f (Real.exp a) / (Real.exp a : ℂ) +
        ∫ v in (Real.exp a)..(Real.exp b), f v / (v : ℂ) ^ 2‖ ≤
      ‖f (Real.exp b) / (Real.exp b : ℂ)‖ +
        ‖f (Real.exp a) / (Real.exp a : ℂ)‖ +
        ‖∫ v in (Real.exp a)..(Real.exp b), f v / (v : ℂ) ^ 2‖ := by
    calc
      ‖f (Real.exp b) / (Real.exp b : ℂ) - f (Real.exp a) / (Real.exp a : ℂ) +
          ∫ v in (Real.exp a)..(Real.exp b), f v / (v : ℂ) ^ 2‖
          ≤ ‖f (Real.exp b) / (Real.exp b : ℂ) - f (Real.exp a) / (Real.exp a : ℂ)‖ +
              ‖∫ v in (Real.exp a)..(Real.exp b), f v / (v : ℂ) ^ 2‖ :=
        norm_add_le _ _
      _ ≤ (‖f (Real.exp b) / (Real.exp b : ℂ)‖ +
            ‖f (Real.exp a) / (Real.exp a : ℂ)‖) +
              ‖∫ v in (Real.exp a)..(Real.exp b), f v / (v : ℂ) ^ 2‖ := by
        gcongr
        exact norm_sub_le _ _
  have hb' := hend b hab le_rfl
  have ha' := hend a le_rfl hab
  calc
    ‖f (Real.exp b) / (Real.exp b : ℂ) - f (Real.exp a) / (Real.exp a : ℂ) +
        ∫ v in (Real.exp a)..(Real.exp b), f v / (v : ℂ) ^ 2‖
        ≤ (K * Real.exp (-(a / 3)) * U ^ C) +
            (K * Real.exp (-(a / 3)) * U ^ C) +
            (3 * K * U ^ C * Real.exp (-(a / 3))) := by
      exact htri.trans (add_le_add (add_le_add hb' ha') hInt)
    _ = 5 * K * Real.exp (-(a / 3)) * U ^ C := by ring

/-! ## The finite Chebyshev / Markov count -/

/-- **Finite Markov/Chebyshev inequality.**  If a centre is declared bad when the
absolute discrepancy is at least `τ`, then the bad fraction is at most
`τ⁻²` times the mean square discrepancy.  This is the counting step behind the
tent smoothing estimate. -/
theorem card_le_energy {N : ℕ} (hN : 0 < N) (g : Fin N → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ((Finset.univ.filter (fun i => τ ≤ |g i|)).card : ℝ) / (N : ℝ) ≤
      (1 / τ ^ 2) * ((1 / (N : ℝ)) * ∑ i : Fin N, (g i) ^ 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : ((Finset.univ.filter (fun i => τ ≤ |g i|)).card : ℝ) * τ ^ 2 ≤
      ∑ i : Fin N, (g i) ^ 2 := by
    calc
      ((Finset.univ.filter (fun i => τ ≤ |g i|)).card : ℝ) * τ ^ 2
          = ∑ _i ∈ Finset.univ.filter (fun i => τ ≤ |g i|), τ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => τ ≤ |g i|), (g i) ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have h : τ ≤ |g i| := (Finset.mem_filter.mp hi).2
        have h' : |τ| ≤ |g i| := by rwa [abs_of_pos hτ]
        calc
          τ ^ 2 = |τ| ^ 2 := by rw [abs_of_pos hτ]
          _ ≤ |g i| ^ 2 := pow_le_pow_left₀ (abs_nonneg τ) h' 2
          _ = (g i) ^ 2 := by rw [sq_abs]
      _ ≤ ∑ i : Fin N, (g i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => sq_nonneg (g i))
  have hdiv : ((Finset.univ.filter (fun i => τ ≤ |g i|)).card : ℝ) ≤
      (∑ i : Fin N, (g i) ^ 2) / τ ^ 2 := by
    rw [le_div_iff₀ (pow_pos hτ 2)]
    exact hcard
  have hdiv' : (∑ i : Fin N, (g i) ^ 2) / τ ^ 2 =
      (1 / τ ^ 2) * ∑ i : Fin N, (g i) ^ 2 := by ring
  rw [div_le_iff₀ hNpos]
  calc
    ((Finset.univ.filter (fun i => τ ≤ |g i|)).card : ℝ)
        ≤ (1 / τ ^ 2) * ∑ i : Fin N, (g i) ^ 2 := by
      rw [← hdiv']
      exact hdiv
    _ = (1 / τ ^ 2 * ((1 / (N : ℝ)) * ∑ i : Fin N, (g i) ^ 2)) * (N : ℝ) := by
      field_simp

/-- The Chebyshev threshold `τ = 1/(2kΔ)`; its reciprocal square is exactly the
tent constant `4 (kΔ)²`. -/
def chebThreshold (X : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  1 / (2 * kOf X c n * spacingOf X c n)

/-! ## The new bundle -/

/-- **L21.2 inputs with the Fourier and tent steps reduced.**

Compared with `L21_2PerronInputs`:

* the abstract `fourierGap` is tied to the Abel transform `abelGapOf` of the
  twisted error;
* the exceptional count is the finite Markov bad-set count from `N` and
  `deficit`, so `tentChebyshev` is *proved* from the finite Chebyshev
  inequality and the mean-square comparison `tentMeanSquare`;
* the remaining inputs are the absolute Perron constant, the exponent slack
  `Ceps ≥ Cper + 2`, and the two elementary parameter growth facts
  `k ≤ log X` and `a ≥ log 2`. -/
structure L21_2FourierInputs where
  /-- The dyadic centre bound `X`. -/
  X : ℕ → ℝ
  /-- The stage-one constant `c` (the paper takes `c = 1/√2`). -/
  c : ℝ
  /-- Perron constant in the vertical error `O (v^{2/3} U^C)`. -/
  Kper : ℕ → ℝ
  /-- The absolute exponent `C` of the Perron/twisted-sum errors. -/
  Cper : ℝ
  /-- Exponent in `ε = e^{-a/3} U^{Ceps}`. -/
  Ceps : ℝ
  /-- The Fourier gap `μ̂ (t) - ν̂ (t)`. -/
  fourierGap : ℕ → ℝ → ℂ
  smoothCount : ℕ → ℝ
  lowTerm : ℕ → ℝ
  middleTerm : ℕ → ℝ
  tailTerm : ℕ → ℝ
  /-- Exponent of the explicit polynomial factor `(1 + U)^{polyExp}`. -/
  polyExp : ℝ
  /-- The size of the finite centre sample. -/
  N : ℕ → ℕ
  /-- The explicit smoothed-density discrepancy at each sampled centre. -/
  deficit : (n : ℕ) → Fin (N n) → ℝ
  X_gt_one : ∀ n, 1 < X n
  c_pos : 0 < c
  c_le_one : c ≤ 1
  /-- `log X ≥ 3` for every band. -/
  U_ge_three : ∀ n, 3 ≤ bandLog X n
  Kper_nonneg : ∀ n, 0 ≤ Kper n
  Cper_ge_two : 2 ≤ Cper
  Ceps_nonneg : 0 ≤ Ceps
  polyExp_ge_three : 3 ≤ polyExp
  smoothCount_nonneg : ∀ n, 0 ≤ smoothCount n
  lowTerm_nonneg : ∀ n, 0 ≤ lowTerm n
  middleTerm_nonneg : ∀ n, 0 ≤ middleTerm n
  tailTerm_nonneg : ∀ n, 0 ≤ tailTerm n
  /-- The finite centre sample is nonempty. -/
  N_pos : ∀ n, 0 < N n
  /-- **Perron at `Re s = 2/3`** (unchanged paper input). -/
  perronShift : ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
      ‖twistedPrimeSum v t - twistedMain v t‖ ≤
        Kper n * (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper
          + v * (bandLog X n) ^ Cper / X n ^ 3
          + Real.sqrt v * (Real.log (2 * v)) ^ 2)
  /-- **The Perron constant is absolute.**  This replaces the unconstrained
  `Kper` growth of the abstract bundle by the paper's actual constant. -/
  Kper_bdd : ∃ K : ℝ, ∀ n, 3 * Kper n ≤ K
  /-- **Partial summation**: the Fourier gap is the Abel transform of the
  twisted error.  This is the structural content of the paper's
  partial-summation step; all estimates on `abelGapOf` are proved below. -/
  fourierGap_eq_abel : ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
    fourierGap n t = abelGapOf X c n t
  /-- The polynomial exponent absorbs the Abel boundary factor. -/
  Ceps_ge : Cper + 2 ≤ Ceps
  /-- `k = O (U^{1/2+o(1)})`, in the coarse form `k ≤ log X`. -/
  k_le_U : ∀ᶠ n : ℕ in atTop, kOf X c n ≤ bandLog X n
  /-- The lower band edge satisfies `e^a ≥ 2`. -/
  a_ge_log_two : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ aOf X c n
  /-- `b ≤ B` eventually, the paper's prime-product cutoff below `B = c T_X`. -/
  b_le_B : ∀ᶠ n : ℕ in atTop, bOf X c n ≤ logCutoff c X n
  /-- **The density-normalization count** (unchanged paper input). -/
  densityNormalization : ∀ᶠ n : ℕ in atTop,
    Real.sqrt (X n) *
        Real.exp (-(representationLog (kOf X c) (spacingOf X c) (bOf X c) n)) ≤
      smoothCount n
  /-- **Low frequency** (`|t| ≤ 1`). -/
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    lowTerm n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate X n)
  /-- **Middle frequency** (`1 < |t| ≤ X³`). -/
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    middleTerm n ≤ Real.exp (-((1 / c) - δ) * paperRate X n)
  /-- **High frequency** (`|t| > X³`). -/
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    tailTerm n ≤ Real.exp (-δ * paperRate X n)
  /-- **Mean-square / Plancherel comparison**: the deficit energy at the sampled
  centres is at most the sum of the three frequency contributions. -/
  tentMeanSquare : ∀ᶠ n : ℕ in atTop,
    (1 / (N n : ℝ)) * ∑ i : Fin (N n), (deficit n i) ^ 2 ≤
      lowTerm n + middleTerm n + tailTerm n
  /-- **Two-scale separation**. -/
  U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog X n
  /-- `log X ≤ exp (scale n)`. -/
  U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog X n ≤ Real.exp (scale n)

namespace L21_2FourierInputs

variable (F : L21_2FourierInputs)

/-! ### The explicit parameters -/

abbrev U (n : ℕ) : ℝ := UOf F.X n

abbrev T (n : ℕ) : ℝ := TOf F.X n

abbrev B (n : ℕ) : ℝ := BOf F.c F.X n

abbrev r (n : ℕ) : ℝ := rOf F.X F.c n

abbrev k (n : ℕ) : ℝ := kOf F.X F.c n

abbrev m (n : ℕ) : ℝ := mOf F.X F.c n

abbrev spacing (n : ℕ) : ℝ := spacingOf F.X F.c n

abbrev a (n : ℕ) : ℝ := aOf F.X F.c n

abbrev b (n : ℕ) : ℝ := bOf F.X F.c n

abbrev l2 (n : ℕ) : ℝ := F.lowTerm n + F.middleTerm n + F.tailTerm n

/-! ### Elementary parameter bounds -/

theorem U_pos (n : ℕ) : 0 < F.U n := lt_of_lt_of_le (by norm_num) (F.U_ge_three n)

theorem U_gt_one (n : ℕ) : 1 < F.U n := lt_of_lt_of_le (by norm_num) (F.U_ge_three n)

theorem logU_pos (n : ℕ) : 0 < Real.log (F.U n) := Real.log_pos (F.U_gt_one n)

theorem T_pos (n : ℕ) : 0 < F.T n := by
  unfold T TOf paperRate
  exact Real.sqrt_pos.mpr (mul_pos (F.U_pos n) (F.logU_pos n))

theorem T_nonneg (n : ℕ) : 0 ≤ F.T n := (F.T_pos n).le

theorem T_sq (n : ℕ) : F.T n ^ 2 = F.U n * Real.log (F.U n) := by
  unfold T TOf paperRate U UOf bandLog
  exact Real.sq_sqrt
    (mul_nonneg (Real.log_nonneg (le_of_lt (F.X_gt_one n))) (F.logU_pos n).le)

theorem T_le_U (n : ℕ) : F.T n ≤ F.U n := by
  have hU : 0 ≤ F.U n := (F.U_pos n).le
  have hlog : Real.log (F.U n) ≤ F.U n := Real.log_le_self hU
  have hsq : F.U n * Real.log (F.U n) ≤ (F.U n) ^ 2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hlog hU
  calc
    F.T n = Real.sqrt (F.T n ^ 2) := (Real.sqrt_sq (F.T_nonneg n)).symm
    _ = Real.sqrt (F.U n * Real.log (F.U n)) := by rw [F.T_sq n]
    _ ≤ Real.sqrt ((F.U n) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = F.U n := Real.sqrt_sq hU

theorem B_pos (n : ℕ) : 0 < F.B n := by
  unfold B BOf logCutoff
  exact mul_pos F.c_pos (F.T_pos n)

theorem B_le_T (n : ℕ) : F.B n ≤ F.T n := by
  unfold B BOf logCutoff
  exact mul_le_of_le_one_left (F.T_nonneg n) F.c_le_one

theorem one_lt_r (n : ℕ) : 1 < F.r n := by
  have hB := F.B_pos n
  have hBT : F.B n ≤ F.T n := F.B_le_T n
  have hTU : F.T n ≤ F.U n := F.T_le_U n
  have hlt : F.B n < F.U n + 1 := by linarith [F.U_pos n]
  unfold r rOf
  rw [one_lt_div hB]
  exact hlt

theorem r_pos (n : ℕ) : 0 < F.r n := lt_trans zero_lt_one (F.one_lt_r n)

theorem logr_pos (n : ℕ) : 0 < Real.log (F.r n) := Real.log_pos (F.one_lt_r n)

theorem exp_one_le_k (n : ℕ) : Real.exp 1 ≤ F.k n := by
  unfold k kOf
  have hr : 1 < F.r n := F.one_lt_r n
  have hr1 : 1 ≤ F.r n := le_of_lt hr
  have hlr : 0 < Real.log (F.r n) := F.logr_pos n
  by_cases h : Real.log (F.r n) ≤ 1
  · have hfac : 3 ≤ 1 + 2 / Real.log (F.r n) := by
      have h2 : 2 ≤ 2 / Real.log (F.r n) := by
        rw [le_div_iff₀ hlr]
        nlinarith
      linarith
    have hk3 : (3 : ℝ) ≤ F.r n * (1 + 2 / Real.log (F.r n)) := by
      calc
        (3 : ℝ) = 1 * 3 := by ring
        _ ≤ F.r n * (1 + 2 / Real.log (F.r n)) :=
          mul_le_mul hr1 hfac (by norm_num) (by positivity)
    exact le_trans Real.exp_one_lt_three.le hk3
  · have h1 : 1 ≤ Real.log (F.r n) := le_of_lt (lt_of_not_ge h)
    have hfac : 1 ≤ 1 + 2 / Real.log (F.r n) := by
      have h2 : 0 ≤ 2 / Real.log (F.r n) := div_nonneg (by norm_num) hlr.le
      linarith
    have hr_exp : Real.exp 1 ≤ F.r n := by
      calc
        Real.exp 1 ≤ Real.exp (Real.log (F.r n)) := Real.exp_le_exp.mpr h1
        _ = F.r n := Real.exp_log (F.r_pos n)
    calc
      Real.exp 1 = Real.exp 1 * 1 := by ring
      _ ≤ F.r n * (1 + 2 / Real.log (F.r n)) :=
        mul_le_mul hr_exp hfac (by norm_num) (F.r_pos n).le

theorem k_pos (n : ℕ) : 0 < F.k n :=
  lt_of_lt_of_le (Real.exp_pos 1) (F.exp_one_le_k n)

theorem logk_ge_one (n : ℕ) : 1 ≤ Real.log (F.k n) := by
  calc
    (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (F.k n) :=
      Real.log_le_log (Real.exp_pos 1) (F.exp_one_le_k n)

theorem logk_pos (n : ℕ) : 0 < Real.log (F.k n) :=
  lt_of_lt_of_le zero_lt_one (F.logk_ge_one n)

theorem m_pos (n : ℕ) : 0 < F.m n := by
  unfold m mOf
  apply div_pos
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [F.U_pos n]
  · exact F.k_pos n

theorem spacing_pos (n : ℕ) : 0 < F.spacing n := by
  unfold spacing spacingOf
  exact div_pos (F.m_pos n) (F.logk_pos n)

theorem spacing_le_m (n : ℕ) : F.spacing n ≤ F.m n := by
  unfold spacing spacingOf
  rw [div_le_iff₀ (F.logk_pos n)]
  calc
    F.m n = F.m n * 1 := by ring
    _ ≤ F.m n * Real.log (F.k n) :=
      mul_le_mul_of_nonneg_left (F.logk_ge_one n) (F.m_pos n).le

theorem a_le_b (n : ℕ) : F.a n ≤ F.b n := by
  unfold a b aOf bOf
  linarith [F.spacing_pos n]

theorem k_mul_spacing (n : ℕ) :
    F.k n * F.spacing n = (F.U n + Real.log 2 / 2) / Real.log (F.k n) := by
  unfold spacing spacingOf mOf
  have hk : F.k n ≠ 0 := (F.k_pos n).ne'
  have hl : Real.log (F.k n) ≠ 0 := (F.logk_pos n).ne'
  field_simp [hk, hl]

theorem one_div_spacing_eq (n : ℕ) :
    1 / F.spacing n = Real.log (F.k n) / F.m n := by
  unfold spacing spacingOf
  have hm : F.m n ≠ 0 := (F.m_pos n).ne'
  have hl : Real.log (F.k n) ≠ 0 := (F.logk_pos n).ne'
  field_simp [hm, hl]

/-! ### Growth of `U` and the cutoff bound -/

theorem U_grows : Tendsto F.U atTop atTop := by
  refine tendsto_atTop_mono' atTop (F.U_dominates 1 zero_lt_one) ?_
  simpa [pow_two, U] using scale_grows.atTop_mul_atTop₀ scale_grows

/-- `B = c T ≤ U/3` eventually, from `T/U → 0`. -/
theorem B_le_U : ∀ᶠ n : ℕ in atTop, F.B n ≤ F.U n / 3 := by
  have hTU : Tendsto (fun n => F.T n / F.U n) atTop (nhds 0) := by
    have h := Scale.tendsto_t_div_u F.U_grows
    convert h using 1
    ext n
    unfold Scale.t T TOf paperRate U UOf bandLog
    rfl
  have hcTU : Tendsto (fun n => F.c * (F.T n / F.U n)) atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := F.c)).mul hTU
    simpa using h
  have hev : ∀ᶠ n : ℕ in atTop, F.c * (F.T n / F.U n) < 1 / 3 :=
    (tendsto_order.mp hcTU).2 (1 / 3) (by norm_num)
  filter_upwards [hev] with n hn
  have hmul := mul_lt_mul_of_pos_right hn (F.U_pos n)
  have hmul' : F.c * F.T n < (1 / 3) * F.U n := by
    calc
      F.c * F.T n = F.c * (F.T n / F.U n) * F.U n := by
        rw [mul_assoc, div_mul_cancel₀ _ (F.U_pos n).ne']
      _ < (1 / 3) * F.U n := hmul
  have hB : F.B n = F.c * F.T n := rfl
  rw [hB]
  nlinarith

/-- The coarse absorption `k ≤ U` gives `m ≥ 1`. -/
theorem one_le_m (n : ℕ) (hkU : F.k n ≤ F.U n) : 1 ≤ F.m n := by
  unfold m mOf
  rw [le_div_iff₀ (F.k_pos n)]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [hkU, F.U_pos n]

/-- The coarse absorption `k ≤ U` gives `log k ≤ U`. -/
theorem logk_le_U (n : ℕ) (hkU : F.k n ≤ F.U n) : Real.log (F.k n) ≤ F.U n :=
  (Real.log_le_self (F.k_pos n).le).trans hkU

/-- `1/Δ ≤ U` from the two coarse bounds. -/
theorem one_div_spacing_le_U (n : ℕ) (hkU : F.k n ≤ F.U n) :
    1 / F.spacing n ≤ F.U n := by
  rw [F.one_div_spacing_eq n]
  have hl : 0 ≤ Real.log (F.k n) := (F.logk_pos n).le
  have hm : 1 ≤ F.m n := F.one_le_m n hkU
  calc
    Real.log (F.k n) / F.m n ≤ Real.log (F.k n) / 1 := by
      gcongr
    _ = Real.log (F.k n) := by ring
    _ ≤ F.U n := F.logk_le_U n hkU

/-! ### The twisted error after absorbing the Perron terms -/

/-- **Absorption of the three Perron errors.**  On `v ∈ [2, e^B]` and
`|t| ≤ X³`, the twisted error is `O (3 Kper v^{2/3} U^{Cper})`.  This is the
same estimate as `RandomizedL21_2.twisted_prime_sum`, re-proved for the new
bundle from `perronShift` and `B_le_U`. -/
theorem twistedErr_le :
    ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v → v ≤ smoothCutoff F.c F.X n →
      |t| ≤ F.X n ^ 3 →
        ‖twistedErr v t‖ ≤ (3 * F.Kper n) * v ^ (2 / 3 : ℝ) * (F.U n) ^ F.Cper := by
  filter_upwards [F.perronShift, F.B_le_U] with n hper hBU
  intro v t hv hvB ht
  have hU3' : 3 ≤ F.U n := F.U_ge_three n
  have hU0 : 0 < F.U n := lt_of_lt_of_le (by norm_num) hU3'
  have hU1 : 1 ≤ F.U n := by linarith
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hv1 : 1 ≤ v := le_trans (by norm_num) hv
  have hvExp : v ≤ Real.exp (F.U n / 3) := by
    have h : smoothCutoff F.c F.X n ≤ Real.exp (F.U n / 3) := by
      rw [smoothCutoff]
      exact Real.exp_le_exp.mpr hBU
    exact hvB.trans h
  have hX3 : F.X n ^ 3 = Real.exp (3 * F.U n) := by
    have hX : F.X n = Real.exp (F.U n) := by
      rw [U, UOf, bandLog, Real.exp_log (by linarith [F.X_gt_one n])]
    calc
      F.X n ^ 3 = Real.exp (F.U n) ^ 3 := by rw [hX]
      _ = Real.exp (3 * F.U n) := by
        simpa using (Real.exp_nat_mul (F.U n) 3).symm
  have hv13 : v ^ (1 / 3 : ℝ) ≤ F.X n ^ 3 := by
    have hexp : Real.exp (F.U n / 3) ^ (1 / 3 : ℝ) = Real.exp (F.U n / 9) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    have h1 : v ^ (1 / 3 : ℝ) ≤ Real.exp (F.U n / 3) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (le_of_lt hv0) hvExp (by norm_num)
    rw [hexp] at h1
    refine h1.trans ?_
    rw [hX3]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hvsplit : v ≤ v ^ (2 / 3 : ℝ) * F.X n ^ 3 := by
    have hveq : v = v ^ ((1 / 3 : ℝ) + 2 / 3) := by
      rw [show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, Real.rpow_one]
    have hvs : v ^ ((1 / 3 : ℝ) + 2 / 3) = v ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ) :=
      Real.rpow_add hv0 _ _
    have hm : v ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ) ≤
        F.X n ^ 3 * v ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hv13 (Real.rpow_nonneg (le_of_lt hv0) _)
    exact hveq.trans_le (hvs.le.trans (hm.trans (le_of_eq (show
      F.X n ^ 3 * v ^ (2 / 3 : ℝ) = v ^ (2 / 3 : ℝ) * F.X n ^ 3 by ring))))
  have hHor : v * (F.U n) ^ F.Cper / F.X n ^ 3 ≤
      v ^ (2 / 3 : ℝ) * (F.U n) ^ F.Cper := by
    have hX3pos : 0 < F.X n ^ 3 := pow_pos (by linarith [F.X_gt_one n]) 3
    rw [div_le_iff₀ hX3pos]
    have hveq : v * (F.U n) ^ F.Cper =
        (v / F.X n ^ 3) * F.X n ^ 3 * (F.U n) ^ F.Cper := by
      rw [div_mul_cancel₀ v hX3pos.ne']
    have hdiv : v / F.X n ^ 3 ≤ v ^ (2 / 3 : ℝ) := by
      rw [div_le_iff₀ hX3pos]
      exact hvsplit
    have hm : (v / F.X n ^ 3) * F.X n ^ 3 * (F.U n) ^ F.Cper ≤
        (v ^ (2 / 3 : ℝ) * F.X n ^ 3) * (F.U n) ^ F.Cper :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdiv (le_of_lt hX3pos))
        (Real.rpow_nonneg (le_of_lt hU0) _)
    exact hveq.trans_le (hm.trans (le_of_eq (show
      (v ^ (2 / 3 : ℝ) * F.X n ^ 3) * (F.U n) ^ F.Cper =
        v ^ (2 / 3 : ℝ) * (F.U n) ^ F.Cper * F.X n ^ 3 by ring)))
  have hPow : Real.sqrt v * (Real.log (2 * v)) ^ 2 ≤
      v ^ (2 / 3 : ℝ) * (F.U n) ^ F.Cper := by
    have hsqrt : Real.sqrt v ≤ v ^ (2 / 3 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hv1
        (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3)
    have hv2 : 2 * v ≤ Real.exp (F.U n) := by
      have h2 : 2 * v ≤ 2 * Real.exp (F.U n / 3) :=
        mul_le_mul_of_nonneg_left hvExp (by norm_num)
      have hlog2 : Real.log 2 ≤ (2 / 3 : ℝ) * F.U n := by
        have h2le : Real.log 2 ≤ 2 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        nlinarith
      calc
        2 * v ≤ 2 * Real.exp (F.U n / 3) := h2
        _ = Real.exp (Real.log 2) * Real.exp (F.U n / 3) := by
          rw [Real.exp_log (by norm_num)]
        _ = Real.exp (Real.log 2 + F.U n / 3) := by rw [← Real.exp_add]
        _ ≤ Real.exp (F.U n) := Real.exp_le_exp.mpr (by linarith)
    have hlogv : Real.log (2 * v) ≤ F.U n :=
      (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 2 * v)).mpr hv2
    have hsq : (Real.log (2 * v)) ^ 2 ≤ (F.U n) ^ (2 : ℝ) := by
      have hnn : 0 ≤ Real.log (2 * v) :=
        Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * v)
      rw [Real.rpow_two]
      nlinarith
    have hupow : (F.U n) ^ (2 : ℝ) ≤ (F.U n) ^ F.Cper :=
      Real.rpow_le_rpow_of_exponent_le hU1 F.Cper_ge_two
    have hlog : (Real.log (2 * v)) ^ 2 ≤ (F.U n) ^ F.Cper := hsq.trans hupow
    exact mul_le_mul hsqrt hlog (by positivity)
      (Real.rpow_nonneg (le_of_lt hv0) _)
  have hbracket :
      v ^ (2 / 3 : ℝ) * (F.U n) ^ F.Cper
        + v * (F.U n) ^ F.Cper / F.X n ^ 3
        + Real.sqrt v * (Real.log (2 * v)) ^ 2
      ≤ 3 * (v ^ (2 / 3 : ℝ) * (F.U n) ^ F.Cper) := by
    nlinarith [hHor, hPow]
  have hmain := hper v t hv hvB ht
  unfold twistedErr
  exact hmain.trans
    ((mul_le_mul_of_nonneg_left hbracket (F.Kper_nonneg n)).trans_eq (by ring))

/-! ### The Fourier sup bound -/

/-- **`fourierSupBound` reduced.**  The Abel transform of the twisted error is
bounded by `supEps` using `abel_transform_norm_le`, the absorbed Perron bound
`twistedErr_le`, the absolute constant `Kper_bdd`, and the coarse parameter
bounds `k ≤ U`, `1/Δ ≤ U`. -/
theorem fourierSupBound :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ F.X n ^ 3 →
      ‖F.fourierGap n t‖ ≤ supEps F.X (aOf F.X F.c) F.Ceps n := by
  obtain ⟨K, hK⟩ := F.Kper_bdd
  have hKnonneg : 0 ≤ K :=
    (mul_nonneg (by norm_num) (F.Kper_nonneg 0)).trans (hK 0)
  have hUbdd : ∀ᶠ n : ℕ in atTop, 5 * K / 2 ≤ F.U n :=
    F.U_grows.eventually_ge_atTop (5 * K / 2)
  filter_upwards [F.fourierGap_eq_abel, F.twistedErr_le, F.b_le_B,
    F.a_ge_log_two, F.k_le_U, hUbdd] with n hgap herr hb ha hkU hUbig
  intro t ht
  have h2A : (2 : ℝ) ≤ Real.exp (F.a n) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr ha
  have hAB : F.a n ≤ F.b n := F.a_le_b n
  have hexpB : Real.exp (F.b n) ≤ smoothCutoff F.c F.X n := by
    rw [smoothCutoff]
    exact Real.exp_le_exp.mpr hb
  have hperr : ∀ v ∈ Set.Icc (Real.exp (F.a n)) (Real.exp (F.b n)),
      ‖twistedErr v t‖ ≤ K * v ^ (2 / 3 : ℝ) * (F.U n) ^ F.Cper := by
    intro v hv
    have hv2 : 2 ≤ v := h2A.trans hv.1
    have hvB : v ≤ smoothCutoff F.c F.X n := hv.2.trans hexpB
    have h := herr v t hv2 hvB ht
    have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
    have hstep : (3 * F.Kper n) * v ^ (2 / 3 : ℝ) ≤ K * v ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right (hK n) (Real.rpow_nonneg hv0 _)
    exact h.trans (mul_le_mul_of_nonneg_right hstep
      (Real.rpow_nonneg (F.U_pos n).le _))
  have habel := abel_transform_norm_le (a := F.a n) (b := F.b n) (K := K)
    (U := F.U n) (C := F.Cper) (f := fun v => twistedErr v t)
    hAB hKnonneg (F.U_pos n).le hperr
  rw [hgap t]
  unfold abelGapOf
  have hΔ : 0 < F.spacing n := F.spacing_pos n
  have hcoefpos : (0 : ℝ) < 1 / (2 * F.spacing n) := by
    exact div_pos zero_lt_one (mul_pos (by norm_num) hΔ)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcoefpos]
  have hone : 1 / F.spacing n ≤ F.U n := F.one_div_spacing_le_U n hkU
  have hcoef : 5 * K / (2 * F.spacing n) ≤ (F.U n) ^ (2 : ℝ) := by
    have heq : 5 * K / (2 * F.spacing n) = (5 * K / 2) * (1 / F.spacing n) := by
      field_simp
    rw [heq]
    calc
      (5 * K / 2) * (1 / F.spacing n) ≤ F.U n * F.U n :=
        mul_le_mul hUbig hone (by positivity) (F.U_pos n).le
      _ = F.U n ^ 2 := by ring
      _ = (F.U n) ^ (2 : ℝ) := (Real.rpow_natCast (F.U n) 2).symm
  have habs : 5 * K * (F.U n) ^ F.Cper / (2 * F.spacing n) ≤
      (F.U n) ^ F.Ceps := by
    have hUpos : 0 < F.U n := F.U_pos n
    have hsplit : (F.U n) ^ (F.Cper + 2) =
        (F.U n) ^ F.Cper * (F.U n) ^ (2 : ℝ) :=
      Real.rpow_add hUpos F.Cper 2
    have hU1 : (1 : ℝ) ≤ F.U n := le_trans (by norm_num) (F.U_ge_three n)
    have hle : (F.U n) ^ (F.Cper + 2) ≤ (F.U n) ^ F.Ceps :=
      Real.rpow_le_rpow_of_exponent_le hU1 F.Ceps_ge
    have hmul : 5 * K * (F.U n) ^ F.Cper / (2 * F.spacing n) =
        (5 * K / (2 * F.spacing n)) * (F.U n) ^ F.Cper := by ring
    rw [hmul]
    calc
      (5 * K / (2 * F.spacing n)) * (F.U n) ^ F.Cper
          ≤ (F.U n) ^ (2 : ℝ) * (F.U n) ^ F.Cper :=
        mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hUpos.le _)
      _ = (F.U n) ^ (F.Cper + 2) := by rw [hsplit]; ring
      _ ≤ (F.U n) ^ F.Ceps := hle
  calc
    (1 / (2 * F.spacing n)) *
        ‖twistedErr (Real.exp (F.b n)) t / (Real.exp (F.b n) : ℂ) -
          twistedErr (Real.exp (F.a n)) t / (Real.exp (F.a n) : ℂ) +
          ∫ v in (Real.exp (F.a n))..(Real.exp (F.b n)), twistedErr v t / (v : ℂ) ^ 2‖
        ≤ (1 / (2 * F.spacing n)) *
            (5 * K * Real.exp (-(F.a n / 3)) * (F.U n) ^ F.Cper) := by
      exact mul_le_mul_of_nonneg_left habel hcoefpos.le
    _ = Real.exp (-(F.a n / 3)) *
          (5 * K * (F.U n) ^ F.Cper / (2 * F.spacing n)) := by ring
    _ ≤ Real.exp (-(F.a n / 3)) * (F.U n) ^ F.Ceps :=
      mul_le_mul_of_nonneg_left habs (Real.exp_pos _).le
    _ = supEps F.X (aOf F.X F.c) F.Ceps n := by
      unfold supEps
      congr 2
      ring

/-! ### The mass of the finite bad set -/

/-- The set of sampled centres at which the discrepancy is at least the
Chebyshev threshold. -/
def badSet (n : ℕ) : Finset (Fin (F.N n)) :=
  Finset.univ.filter (fun i => chebThreshold F.X F.c n ≤ |F.deficit n i|)

/-- The exceptional fraction, written as a genuine count: the bad density times
the dyadic length `X + 1`. -/
def badCount (n : ℕ) : ℝ :=
  ((F.badSet n).card : ℝ) / (F.N n : ℝ) * (F.X n + 1)

theorem badCount_nonneg (n : ℕ) : 0 ≤ F.badCount n := by
  unfold badCount
  have hN : (0 : ℝ) < F.N n := by exact_mod_cast F.N_pos n
  have hX : 0 ≤ F.X n + 1 := by linarith [le_of_lt (F.X_gt_one n)]
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hN.le) hX

theorem badCount_div (n : ℕ) :
    F.badCount n / (F.X n + 1) = ((F.badSet n).card : ℝ) / (F.N n : ℝ) := by
  have hX : F.X n + 1 ≠ 0 := by
    have := F.X_gt_one n
    linarith
  unfold badCount
  field_simp [hX]

/-- The reciprocal square of the Chebyshev threshold is `4 (kΔ)²`. -/
theorem threshold_sq_inv (n : ℕ) :
    1 / (chebThreshold F.X F.c n) ^ 2 = 4 * (F.k n * F.spacing n) ^ 2 := by
  unfold chebThreshold
  have hk : F.k n ≠ 0 := (F.k_pos n).ne'
  have hsp : F.spacing n ≠ 0 := (F.spacing_pos n).ne'
  field_simp
  ring

/-- **`tentChebyshev` reduced.**  Finite Markov on the discrepancy profile,
followed by the mean-square comparison `tentMeanSquare`.  The constant
`4 (kΔ)²` is exactly `τ⁻²` for `τ = 1/(2kΔ)`. -/
theorem tentChebyshev :
    ∀ᶠ n : ℕ in atTop,
      F.badCount n / (F.X n + 1) ≤
        4 * (F.k n * F.spacing n) ^ 2 *
          (F.lowTerm n + F.middleTerm n + F.tailTerm n) := by
  filter_upwards [F.tentMeanSquare] with n hms
  have hτ : 0 < chebThreshold F.X F.c n := by
    unfold chebThreshold
    exact one_div_pos.mpr
      (mul_pos (mul_pos (by norm_num) (F.k_pos n)) (F.spacing_pos n))
  have hmar := card_le_energy (F.N_pos n) (F.deficit n) hτ
  have hsq := F.threshold_sq_inv n
  calc
    F.badCount n / (F.X n + 1)
        = ((F.badSet n).card : ℝ) / (F.N n : ℝ) := F.badCount_div n
    _ ≤ (1 / (chebThreshold F.X F.c n) ^ 2) *
          ((1 / (F.N n : ℝ)) * ∑ i : Fin (F.N n), (F.deficit n i) ^ 2) := hmar
    _ ≤ (1 / (chebThreshold F.X F.c n) ^ 2) *
          (F.lowTerm n + F.middleTerm n + F.tailTerm n) := by
      exact mul_le_mul_of_nonneg_left hms
        (div_nonneg zero_le_one (sq_nonneg _))
    _ = 4 * (F.k n * F.spacing n) ^ 2 *
          (F.lowTerm n + F.middleTerm n + F.tailTerm n) := by rw [hsq]

/-! ### Assembly into `L21_2PerronInputs` -/

/-- The reduced bundle builds the Perron bundle: the gap bound and the tent
Chebyshev inequality are the theorems above; the other fields pass through. -/
def toPerronInputs : L21_2PerronInputs where
  X := F.X
  c := F.c
  Kper := F.Kper
  Cper := F.Cper
  Ceps := F.Ceps
  fourierGap := F.fourierGap
  smoothCount := F.smoothCount
  badCount := F.badCount
  lowTerm := F.lowTerm
  middleTerm := F.middleTerm
  tailTerm := F.tailTerm
  polyExp := F.polyExp
  X_gt_one := F.X_gt_one
  c_pos := F.c_pos
  c_le_one := F.c_le_one
  U_ge_three := F.U_ge_three
  Kper_nonneg := F.Kper_nonneg
  Cper_ge_two := F.Cper_ge_two
  Ceps_nonneg := F.Ceps_nonneg
  polyExp_ge_three := F.polyExp_ge_three
  smoothCount_nonneg := F.smoothCount_nonneg
  badCount_nonneg := F.badCount_nonneg
  lowTerm_nonneg := F.lowTerm_nonneg
  middleTerm_nonneg := F.middleTerm_nonneg
  tailTerm_nonneg := F.tailTerm_nonneg
  perronShift := F.perronShift
  fourierSupBound := F.fourierSupBound
  b_le_B := F.b_le_B
  tentChebyshev := F.tentChebyshev
  densityNormalization := F.densityNormalization
  fourierLow := F.fourierLow
  fourierMiddle := F.fourierMiddle
  fourierTail := F.fourierTail
  U_dominates := F.U_dominates
  U_le_exp := F.U_le_exp

/-- The reduced L21.2 bundle. -/
def toReducedInputs : L21_2ReducedInputs := F.toPerronInputs.toReducedInputs

/-- The parent `L21_2Inputs` assembled from the Fourier/Chebyshev inputs. -/
def toInputs : L21_2Inputs := F.toReducedInputs.toInputs

/-- The L21.2 `RatedLeaf`. -/
def toRatedLeaf : RatedLeaf := F.toReducedInputs.toRatedLeaf

/-- The `D^{-B}` form packaged as a `SubexpLeaf`. -/
def toSubexpLeaf : SubexpLeaf := F.toReducedInputs.toSubexpLeaf

theorem loss_nonneg (n : ℕ) : 0 ≤ F.toPerronInputs.toReducedInputs.loss n :=
  F.toPerronInputs.toReducedInputs.loss_nonneg n

theorem loss_le_paper :
    ∀ᶠ n : ℕ in atTop,
      F.toPerronInputs.toReducedInputs.loss n ≤
        Real.exp (-((F.c / 64) * paperRate F.X n)) :=
  F.toPerronInputs.toReducedInputs.loss_le_paper

theorem loss_le_ledger :
    ∀ᶠ n : ℕ in atTop,
      F.toPerronInputs.toReducedInputs.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  F.toPerronInputs.toReducedInputs.loss_le_ledger

/-- The `C5Leaf.ellipticExceptional` slot, when identified with this loss, is
eventually at most `exp (-2 * scale n)`. -/
theorem slot_le {slots : C5LossSlots}
    (h : slots .ellipticExceptional = F.toPerronInputs.toReducedInputs.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .ellipticExceptional n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  L21_2ReducedInputs.slot_le F.toPerronInputs.toReducedInputs h

/-- The eleven remaining leaves plus the reduced L21.2 inputs give the full
paper assumptions. -/
def paperAssumptions_of_fourier
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (A : PaperAnalyticAssumptionsWithoutL21_2 E C) :
    PaperAnalyticAssumptions E C :=
  L21_2ReducedInputs.paperAssumptions_of_reduced F.toReducedInputs A

end L21_2FourierInputs

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2Fourier.abel_transform_norm_le
#print axioms Cogentic.RandomizedL21_2Fourier.card_le_energy
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.B_le_U
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.twistedErr_le
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.fourierSupBound
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.badCount_nonneg
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.threshold_sq_inv
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.tentChebyshev
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.toPerronInputs
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.toReducedInputs
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.toInputs
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.toRatedLeaf
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.toSubexpLeaf
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.slot_le
#print axioms Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs.paperAssumptions_of_fourier

end Cogentic.RandomizedL21_2Fourier
