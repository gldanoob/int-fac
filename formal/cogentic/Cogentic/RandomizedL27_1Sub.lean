import Cogentic.RandomizedL27_1

/-!
# L27.1 sub-lemmas: the elementary core of the Lenstra–Pomerance estimate

`Cogentic.RandomizedL27_1` proves the Lenstra–Pomerance ECM failure estimate from
a structure `L27_1Inputs` that bundles both the paper-level inputs and the
elementary counting.  This file separates the two layers.

The paper-level content is isolated in two explicit `Prop`s:

* `DeuringLenstraCounts` — the Deuring/Lenstra distribution of curve orders
  (the per-order Hurwitz class-number lower bound and the total `≤ 4p` count in
  the Hasse window);
* `EllipticCurveGroupLaw` — Hasse's theorem, the gcd-exit lemma over `Z/nZ`, and
  the stage-one success bound for a smooth order.  These are the genuinely
  elliptic-curve/algebraic-geometry inputs and are *not* proved here.

Everything else in the L27.1 chain is elementary and is proved in this file:

1. **Hasse interval arithmetic**: the two endpoint inequalities extracted from
   `|j - (p + 1)| ≤ 2√p`, the AM–GM bound `2√p ≤ p + 1`, the width `4√p`, and
   the fact that an integer window top dominates every realised order.
2. **Chernoff + union bound**: `(1 - x)^m ≤ exp (-(m x))`, the finite union
   bound `1 - ∏ (1 - εᵢ) ≤ ∑ εᵢ`, and the resulting joint-failure estimate for
   independent curve draws.
3. **Curve-budget exponent arithmetic**: from
   `(2 + η) H ≤ E`, the log-factor `exp ((η/2) H)` is absorbed into either
   `exp (-2H)` (the ledger rate) or `exp (-E/2)` (the manuscript rate).
4. **Log-factor subexponential conversion**: `LogFactorSubexp` is equivalent to
   the additive form `log (log₂ cofactor) ≤ δ H`, and it is stable under fixed
   powers and fixed multiplicative constants.

The final theorems `reduced_ledger` and `reduced_paper` re-derive the L27.1
conclusions from `DeuringLenstraCounts`, `EllipticCurveGroupLaw`, the curve
budget, and the log-factor input, using the elementary lemmas above.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL27_1Sub

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. Hasse interval arithmetic -/

/-- Upper endpoint of the Hasse interval, extracted from the absolute-value form. -/
theorem hasse_upper {p j : ℝ} (h : |j - (p + 1)| ≤ 2 * Real.sqrt p) :
    j ≤ p + 1 + 2 * Real.sqrt p := by
  have := (abs_le.mp h).2
  linarith

/-- Lower endpoint of the Hasse interval, extracted from the absolute-value form. -/
theorem hasse_lower {p j : ℝ} (h : |j - (p + 1)| ≤ 2 * Real.sqrt p) :
    p + 1 - 2 * Real.sqrt p ≤ j := by
  have := (abs_le.mp h).1
  linarith

/-- The Hasse interval is symmetric around `p + 1`; its width is `4√p`. -/
theorem hasse_width (p : ℝ) :
    (p + 1 + 2 * Real.sqrt p) - (p + 1 - 2 * Real.sqrt p) = 4 * Real.sqrt p := by
  ring

/-- AM–GM: `2√p ≤ p + 1`, so the lower Hasse endpoint is nonnegative. -/
theorem two_mul_sqrt_le_add_one (p : ℝ) (hp : 0 ≤ p) :
    2 * Real.sqrt p ≤ p + 1 := by
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp
  nlinarith [sq_nonneg (Real.sqrt p - 1)]

/-- The lower Hasse endpoint is nonnegative. -/
theorem hasse_lower_nonneg (p : ℝ) (hp : 0 ≤ p) :
    0 ≤ p + 1 - 2 * Real.sqrt p := by
  linarith [two_mul_sqrt_le_add_one p hp]

/-- For an integer prime bound `p ≥ 1`, `√p ≤ p`. -/
theorem sqrt_le_self_nat {p : ℕ} (hp : 1 ≤ p) : Real.sqrt (p : ℝ) ≤ (p : ℝ) := by
  rw [Real.sqrt_le_left (by positivity)]
  have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  nlinarith

/-- Consequently the Hasse width is at most `4p` for `p ≥ 1`. -/
theorem four_mul_sqrt_le_four_mul {p : ℕ} (hp : 1 ≤ p) :
    4 * Real.sqrt (p : ℝ) ≤ 4 * (p : ℝ) := by
  linarith [sqrt_le_self_nat hp]

/-- If the integer top dominates the Hasse upper endpoint, it dominates every
realised curve order.  This is the exact arithmetic step that lets the sums in
`smoothCurves`/`curveTotal` run over `Finset.range (orderTop + 1)`. -/
theorem hasse_order_le_orderTop {p j top : ℕ}
    (h : |(j : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ))
    (htop : (p : ℝ) + 1 + 2 * Real.sqrt (p : ℝ) ≤ (top : ℝ)) :
    j ≤ top := by
  have hup := hasse_upper h
  have hcast : (j : ℝ) ≤ (top : ℝ) := by linarith
  exact_mod_cast hcast

/-- Generic Hasse support: `HasseBound` plus the integer endpoint `orderTop_spec`
kill every order strictly above `orderTop`. -/
theorem hasse_support {p : ℕ → ℕ} {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (hhasse : HasseBound p orderCount)
    (htop : ∀ n, (p n : ℝ) + 1 + 2 * Real.sqrt (p n) ≤ (orderTop n : ℝ))
    {n j : ℕ} (hj : orderTop n < j) : orderCount n j = 0 := by
  by_contra hne
  have hup := hasse_upper (hhasse n j hne)
  have hspec := htop n
  have hjr : (j : ℝ) ≤ (orderTop n : ℝ) := by linarith
  have hlt : (orderTop n : ℝ) < (j : ℝ) := by exact_mod_cast hj
  linarith

/-- The Hasse bound in the bundled form used by `L27_1Inputs`: no curve has an
order strictly above the integer Hasse endpoint `orderTop`. -/
theorem orderCount_eq_zero_of_orderTop_lt (I : L27_1Inputs) {n j : ℕ}
    (hj : I.orderTop n < j) : I.orderCount n j = 0 :=
  hasse_support I.hasse I.orderTop_spec hj

/-- Every stage-one-smooth order lies inside the summed Hasse window. -/
theorem smooth_order_le_orderTop (I : L27_1Inputs) {n j : ℕ}
    (hs : I.smooth n j = true) : j ≤ I.orderTop n := by
  by_contra h
  push Not at h
  exact I.smooth_realized n j hs (orderCount_eq_zero_of_orderTop_lt I h)

/-! ## 2. Chernoff and the union bound -/

/-- The Chernoff step for one event: `(1 - x)^m ≤ exp (-(m x))` for `x ≤ 1`. -/
theorem one_sub_pow_le_exp_neg {x : ℝ} (hx1 : x ≤ 1) (m : ℕ) :
    (1 - x) ^ m ≤ Real.exp (-((m : ℝ) * x)) := by
  have hbase : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
  have hnonneg : 0 ≤ 1 - x := by linarith
  calc
    (1 - x) ^ m ≤ (Real.exp (-x)) ^ m := pow_le_pow_left₀ hnonneg hbase m
    _ = Real.exp (-((m : ℝ) * x)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Finite union bound: for probabilities `εᵢ ∈ [0, 1]`,
`1 - ∏ (1 - εᵢ) ≤ ∑ εᵢ`. -/
theorem union_bound_finset {ι : Type*} (s : Finset ι) (ε : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ ε i) (h1 : ∀ i ∈ s, ε i ≤ 1) :
    1 - ∏ i ∈ s, (1 - ε i) ≤ ∑ i ∈ s, ε i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have h0s : ∀ i ∈ s, 0 ≤ ε i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1s : ∀ i ∈ s, ε i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have hP0 : 0 ≤ ∏ i ∈ s, (1 - ε i) :=
        Finset.prod_nonneg fun i hi => by linarith [h1s i hi]
      have hP1 : ∏ i ∈ s, (1 - ε i) ≤ 1 :=
        Finset.prod_le_one (fun i hi => by linarith [h1s i hi])
          (fun i hi => by linarith [h0s i hi])
      have hIH := ih h0s h1s
      have ha0 : 0 ≤ ε a := h0 a (Finset.mem_insert_self a s)
      have hxP : ε a * (∏ i ∈ s, (1 - ε i)) ≤ ε a := by
        nlinarith [mul_le_mul_of_nonneg_left hP1 ha0]
      nlinarith [hIH]

/-- Union bound for `m` identical draws: `1 - (1 - x)^m ≤ m x`. -/
theorem one_sub_pow_le_nat_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    1 - (1 - x) ^ m ≤ (m : ℝ) * x := by
  have h := union_bound_finset (Finset.range m) (fun _ => x)
    (fun i _ => hx0) (fun i _ => hx1)
  simpa using h

/-- One curve whose success probability is at least `d` fails with probability
at most `exp (-d)`. -/
theorem curve_fail_le_exp_of_success {s d : ℝ} (hs : d ≤ s) :
    1 - s ≤ Real.exp (-d) := by
  have hle : 1 - s ≤ 1 - d := by linarith
  exact hle.trans (Real.one_sub_le_exp_neg d)

/-- Chernoff for `m` independent draws: if every draw has failure at most
`1 - d`, the joint failure is at most `exp (-(m d))`. -/
theorem joint_failure_le_exp {s d : ℝ} {m : ℕ}
    (hd1 : d ≤ 1) (hs : d ≤ s) (hs1 : s ≤ 1) :
    (1 - s) ^ m ≤ Real.exp (-((m : ℝ) * d)) := by
  have hnonneg : 0 ≤ 1 - s := by linarith
  have hle : 1 - s ≤ 1 - d := by linarith
  calc
    (1 - s) ^ m ≤ (1 - d) ^ m := pow_le_pow_left₀ hnonneg hle m
    _ ≤ Real.exp (-((m : ℝ) * d)) := one_sub_pow_le_exp_neg hd1 m

/-! ## 3. Curve-budget exponent arithmetic -/

/-- From the curve-budget inequality `(2 + η) H ≤ E`, the additive headroom
`(η/2) H` is at most `E/2`. -/
theorem budget_half_le {H E η : ℝ} (hH : 0 ≤ H)
    (h : (2 + η) * H ≤ E) : (η / 2) * H ≤ E / 2 := by
  have hηH : η * H ≤ E := by
    have : η * H ≤ (2 + η) * H := by nlinarith
    linarith
  nlinarith

/-- The ledger exponent inequality: after paying the log-factor headroom, the
exponent is still at most `-2H`. -/
theorem budget_ledger_le {H E η : ℝ} (hH : 0 ≤ H) (hη : 0 < η)
    (h : (2 + η) * H ≤ E) : (η / 2) * H - E ≤ -2 * H := by
  have hηH : η * H ≤ E := by
    have : η * H ≤ (2 + η) * H := by nlinarith
    linarith
  nlinarith

/-- The manuscript-rate exponent inequality: after paying the log-factor
headroom, the exponent is at most `-E/2`. -/
theorem budget_paper_le {H E η : ℝ} (hH : 0 ≤ H)
    (h : (2 + η) * H ≤ E) : (η / 2) * H - E ≤ -(E / 2) := by
  have hhalf := budget_half_le hH h
  linarith

/-- A failure probability at most `exp (-E)` is at most `exp (-(2+η)H)` once the
curve budget holds. -/
theorem failure_le_exp_of_budget {fail H E η : ℝ}
    (hbudget : (2 + η) * H ≤ E) (hfail : fail ≤ Real.exp (-E)) :
    fail ≤ Real.exp (-((2 + η) * H)) :=
  hfail.trans (Real.exp_le_exp.mpr (by linarith))

/-- **Curve-budget absorption.**  A log-factor of size `exp ((η/2)H)` and a
failure of size `exp (-E)` multiply to at most `exp (-2H)` when the budget
`(2+η)H ≤ E` holds.  This is the ledger rate. -/
theorem loss_le_exp_of_budget {H E L fail η : ℝ}
    (hH : 0 ≤ H) (hη : 0 < η) (hbudget : (2 + η) * H ≤ E)
    (hfail0 : 0 ≤ fail)
    (hlog : L ≤ Real.exp ((η / 2) * H))
    (hfail : fail ≤ Real.exp (-E)) :
    L * fail ≤ Real.exp (-2 * H) := by
  calc
    L * fail ≤ Real.exp ((η / 2) * H) * Real.exp (-E) :=
      mul_le_mul hlog hfail hfail0 (Real.exp_pos _).le
    _ = Real.exp ((η / 2) * H - E) := by
      rw [← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-2 * H) := Real.exp_le_exp.mpr (budget_ledger_le hH hη hbudget)

/-- **Curve-budget absorption at the manuscript rate.**  The same product is at
most `exp (-E/2)`. -/
theorem loss_le_exp_half_of_budget {H E L fail η : ℝ}
    (hH : 0 ≤ H) (hbudget : (2 + η) * H ≤ E)
    (hfail0 : 0 ≤ fail)
    (hlog : L ≤ Real.exp ((η / 2) * H))
    (hfail : fail ≤ Real.exp (-E)) :
    L * fail ≤ Real.exp (-(E / 2)) := by
  calc
    L * fail ≤ Real.exp ((η / 2) * H) * Real.exp (-E) :=
      mul_le_mul hlog hfail hfail0 (Real.exp_pos _).le
    _ = Real.exp ((η / 2) * H - E) := by
      rw [← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-(E / 2)) := Real.exp_le_exp.mpr (budget_paper_le hH hbudget)

/-! ## 4. Log-factor subexponential conversion -/

/-- For `m ≥ 2`, `log₂ m ≥ 1`. -/
theorem one_le_log2_of_two_le {m : ℕ} (hm : 2 ≤ m) : 1 ≤ m.log2 := by
  rw [Nat.le_log2 (by omega : m ≠ 0)]
  simpa using hm

/-- `LogFactorSubexp` in additive form: the logarithm of `log₂(cofactor)` is
`o(H)`, i.e. `log (log₂ cofactor) ≤ δ H` eventually. -/
theorem LogFactorSubexp.log_le {cofactor : ℕ → ℕ}
    (hcof : ∀ n, 2 ≤ cofactor n) (h : LogFactorSubexp cofactor) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      Real.log ((cofactor n).log2 : ℝ) ≤ δ * scale n := by
  intro δ hδ
  filter_upwards [h δ hδ] with n hn
  have hpos : 0 < ((cofactor n).log2 : ℝ) := by
    have h1 := one_le_log2_of_two_le (hcof n)
    exact_mod_cast (lt_of_lt_of_le zero_lt_one h1)
  rw [Real.log_le_iff_le_exp hpos]
  exact hn

/-- Conversely, the additive subexponential form implies `LogFactorSubexp`. -/
theorem logFactorSubexp_of_log_le {cofactor : ℕ → ℕ}
    (hcof : ∀ n, 2 ≤ cofactor n)
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      Real.log ((cofactor n).log2 : ℝ) ≤ δ * scale n) :
    LogFactorSubexp cofactor := by
  intro δ hδ
  filter_upwards [h δ hδ] with n hn
  have hpos : 0 < ((cofactor n).log2 : ℝ) := by
    have h1 := one_le_log2_of_two_le (hcof n)
    exact_mod_cast (lt_of_lt_of_le zero_lt_one h1)
  calc
    ((cofactor n).log2 : ℝ) = Real.exp (Real.log ((cofactor n).log2 : ℝ)) :=
      (Real.exp_log hpos).symm
    _ ≤ Real.exp (δ * scale n) := Real.exp_le_exp.mpr hn

/-- The multiplicative and additive subexponential forms are equivalent. -/
theorem logFactorSubexp_iff_log_le {cofactor : ℕ → ℕ}
    (hcof : ∀ n, 2 ≤ cofactor n) :
    LogFactorSubexp cofactor ↔
      ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
        Real.log ((cofactor n).log2 : ℝ) ≤ δ * scale n :=
  ⟨LogFactorSubexp.log_le hcof, logFactorSubexp_of_log_le hcof⟩

/-- Every fixed power of the log factor remains subexponential.  This is the
form used when a polynomial number of recursive nodes multiplies the per-node
failure. -/
theorem LogFactorSubexp.pow_le {cofactor : ℕ → ℕ} (h : LogFactorSubexp cofactor)
    (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ((cofactor n).log2 : ℝ) ^ k ≤ Real.exp (δ * scale n) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · filter_upwards [scale_grows.eventually_ge_atTop 0] with n hn
    simp only [pow_zero]
    exact Real.one_le_exp (mul_nonneg hδ.le hn)
  · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hδ' : 0 < δ / (k : ℝ) := div_pos hδ hkR
    filter_upwards [h (δ / (k : ℝ)) hδ'] with n hn
    have hnonneg : 0 ≤ ((cofactor n).log2 : ℝ) := Nat.cast_nonneg _
    calc
      ((cofactor n).log2 : ℝ) ^ k
          ≤ (Real.exp ((δ / (k : ℝ)) * scale n)) ^ k :=
        pow_le_pow_left₀ hnonneg hn k
      _ = Real.exp (δ * scale n) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp [hkR.ne']

/-- A fixed positive multiple of the log factor is still subexponential; the
constant is absorbed by the growing scale. -/
theorem LogFactorSubexp.const_mul_le {cofactor : ℕ → ℕ}
    (h : LogFactorSubexp cofactor) {c : ℝ} (hc : 0 ≤ c) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, c * ((cofactor n).log2 : ℝ) ≤ Real.exp (δ * scale n) := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · filter_upwards [scale_grows.eventually_ge_atTop 0] with n hn
    simp only [zero_mul]
    exact (Real.exp_pos (δ * scale n)).le
  · have hδ2 : 0 < δ / 2 := by linarith
    filter_upwards [h (δ / 2) hδ2,
      scale_grows.eventually_ge_atTop (max 0 (2 * Real.log c / δ))] with n hn hscale
    have hcle : Real.log c ≤ (δ / 2) * scale n := by
      have hge : 2 * Real.log c / δ ≤ scale n := (le_max_right _ _).trans hscale
      have hmul := mul_le_mul_of_nonneg_left hge (by positivity : (0 : ℝ) ≤ δ / 2)
      have hid : (δ / 2) * (2 * Real.log c / δ) = Real.log c := by
        field_simp [hδ.ne']
      rw [hid] at hmul
      exact hmul
    have hc_le : c ≤ Real.exp ((δ / 2) * scale n) := by
      calc
        c = Real.exp (Real.log c) := (Real.exp_log hcpos).symm
        _ ≤ Real.exp ((δ / 2) * scale n) := Real.exp_le_exp.mpr hcle
    have hlog2_nonneg : 0 ≤ ((cofactor n).log2 : ℝ) := Nat.cast_nonneg _
    calc
      c * ((cofactor n).log2 : ℝ)
          ≤ Real.exp ((δ / 2) * scale n) * Real.exp ((δ / 2) * scale n) :=
        mul_le_mul hc_le hn hlog2_nonneg (Real.exp_pos _).le
      _ = Real.exp (δ * scale n) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-! ## 5. The paper-level inputs left as explicit `Prop`s -/

/-- **Paper-level Deuring/Lenstra counts.**  The per-order Hurwitz class-number
lower bound for smooth orders, and the total `≤ 4p` count of curves in the Hasse
window.  These are the curve-count inputs of LP §7; they are not proved here. -/
def DeuringLenstraCounts (I : L27_1Inputs) : Prop :=
  (∀ n j, I.smooth n j = true →
      I.κ * Real.sqrt (I.p n) ≤ (I.orderCount n j : ℝ)) ∧
    ∀ n, curveTotal I.orderCount I.orderTop n ≤ 4 * (I.p n : ℝ)

/-- **Paper-level elliptic-curve group law inputs.**  Hasse's theorem, the
gcd-exit lemma for curves over `Z/nZ`, and the stage-one success bound for a
smooth order.  These are the algebraic-geometry inputs of LP §7; they are not
proved here. -/
def EllipticCurveGroupLaw (I : L27_1Inputs) : Prop :=
  HasseBound I.p I.orderCount ∧
    GCDExitBound I.p I.gcdFail (fun n => 1 - I.success n) ∧
      StageOneSuccess
        (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success

/-! ## 6. Reduction of the elementary counting chain -/

/-- Summing the per-order Deuring count over the smooth orders of the Hasse
window.  This is the `DeuringSmoothCount` estimate with the pointwise
paper-level count as the only non-elementary input. -/
theorem smoothCurves_ge_of_pointwise {p : ℕ → ℕ} (psi : ℝ) {κ : ℝ} {n : ℕ}
    (smooth : ℕ → ℕ → Bool) (orderCount : ℕ → ℕ → ℕ) (orderTop : ℕ → ℕ)
    (hκ : 0 ≤ κ)
    (hcount : ∀ j, smooth n j = true →
      κ * Real.sqrt (p n) ≤ (orderCount n j : ℝ))
    (hpsi : psi ≤ smoothCount smooth orderTop n) :
    κ * Real.sqrt (p n) * psi ≤ smoothCurves smooth orderCount orderTop n := by
  have hpoint : ∀ j ∈ Finset.range (orderTop n + 1),
      (if smooth n j then (κ * Real.sqrt (p n) : ℝ) else 0) ≤
        (if smooth n j then (orderCount n j : ℝ) else 0) := by
    intro j _
    by_cases h : smooth n j = true
    · simp only [h, if_true]
      exact hcount j h
    · simp [h]
  have hsum : (∑ j ∈ Finset.range (orderTop n + 1),
        (if smooth n j then (κ * Real.sqrt (p n) : ℝ) else 0)) ≤
      smoothCurves smooth orderCount orderTop n := by
    simpa [smoothCurves] using Finset.sum_le_sum hpoint
  have hfactor :
      (∑ j ∈ Finset.range (orderTop n + 1),
        (if smooth n j then (κ * Real.sqrt (p n) : ℝ) else 0)) =
      (κ * Real.sqrt (p n)) * smoothCount smooth orderTop n := by
    rw [smoothCount, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : smooth n j = true <;> simp [h]
  have hk : 0 ≤ κ * Real.sqrt (p n) := mul_nonneg hκ (Real.sqrt_nonneg _)
  calc
    κ * Real.sqrt (p n) * psi
        = (κ * Real.sqrt (p n)) * psi := by ring
    _ ≤ (κ * Real.sqrt (p n)) * smoothCount smooth orderTop n :=
      mul_le_mul_of_nonneg_left hpsi hk
    _ = (∑ j ∈ Finset.range (orderTop n + 1),
          (if smooth n j then (κ * Real.sqrt (p n) : ℝ) else 0)) := hfactor.symm
    _ ≤ smoothCurves smooth orderCount orderTop n := hsum

/-- The bundled `DeuringSmoothCount` lower bound for the L27.1 data. -/
theorem deuringSmoothCount_of (I : L27_1Inputs)
    (h : DeuringLenstraCounts I) (n : ℕ) :
    I.κ * Real.sqrt (I.p n) * I.psi n ≤ I.SC n := by
  simpa [L27_1Inputs.SC] using
    smoothCurves_ge_of_pointwise (p := I.p) (psi := I.psi n) (κ := I.κ) (n := n)
      I.smooth I.orderCount I.orderTop I.κ_pos.le (fun j hj => h.1 n j hj)
      (I.psi_card n)

/-- Pure fraction arithmetic: a numerator lower bound and a denominator upper
bound `CT ≤ 4p` give the `κψ/(4√p)` lower bound for the smooth fraction. -/
theorem fraction_lower_of_counts {p psi κ SC CT : ℝ}
    (hκ : 0 ≤ κ) (hpsi : 0 ≤ psi) (hp : 0 < p)
    (hCTpos : 0 < CT) (hCT : CT ≤ 4 * p)
    (hcount : κ * Real.sqrt p * psi ≤ SC) :
    κ * psi / (4 * Real.sqrt p) ≤ SC / CT := by
  have hnum : 0 ≤ κ * Real.sqrt p * psi :=
    mul_nonneg (mul_nonneg hκ (Real.sqrt_nonneg _)) hpsi
  have h1 : κ * Real.sqrt p * psi / (4 * p) ≤ κ * Real.sqrt p * psi / CT :=
    div_le_div_of_nonneg_left hnum hCTpos hCT
  have h2 : κ * Real.sqrt p * psi / (4 * p) =
      κ * psi / (4 * Real.sqrt p) := by
    have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp.le
    have hs : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    calc
      κ * Real.sqrt p * psi / (4 * p)
          = κ * Real.sqrt p * psi / (4 * (Real.sqrt p * Real.sqrt p)) := by rw [hsq]
      _ = κ * psi / (4 * Real.sqrt p) := by field_simp [hs]
  calc
    κ * psi / (4 * Real.sqrt p)
        = κ * Real.sqrt p * psi / (4 * p) := h2.symm
    _ ≤ κ * Real.sqrt p * psi / CT := h1
    _ ≤ SC / CT := div_le_div_of_nonneg_right hcount hCTpos.le

/-- The smooth-fraction lower bound `κψ/(4√p) ≤ SF` from the Deuring counts. -/
theorem smoothFraction_lower_of (I : L27_1Inputs)
    (h : DeuringLenstraCounts I) (n : ℕ) :
    I.κ * I.psi n / (4 * Real.sqrt (I.p n)) ≤ I.SF n := by
  have hp : (0 : ℝ) < (I.p n : ℝ) := by exact_mod_cast I.p_pos n
  simpa [L27_1Inputs.SF, L27_1Inputs.SC, L27_1Inputs.CT] using
    fraction_lower_of_counts (p := (I.p n : ℝ)) (psi := I.psi n) (κ := I.κ)
      (SC := I.SC n) (CT := I.CT n) I.κ_pos.le (I.psi_nonneg n) hp
      (I.curveTotal_pos n) (h.2 n) (deuringSmoothCount_of I h n)

/-- Pure arithmetic conversion from the fraction bound and the stage-one
success bound to the LP density bound `(κ/4) ψ/(√p log y) ≤ success`. -/
theorem cRate_density_le_of_fraction {κ psi p y SF success : ℝ}
    (hp : 0 < p) (hy : 1 < y)
    (hfrac : κ * psi / (4 * Real.sqrt p) ≤ SF)
    (hstage : SF / Real.log y ≤ success) :
    (κ / 4) * (psi / (Real.sqrt p * Real.log y)) ≤ success := by
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hdiv : κ * psi / (4 * Real.sqrt p) / Real.log y ≤ SF / Real.log y :=
    div_le_div_of_nonneg_right hfrac hlog.le
  have hEq : κ * psi / (4 * Real.sqrt p) / Real.log y =
      (κ / 4) * (psi / (Real.sqrt p * Real.log y)) := by
    have hs : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    have hl : Real.log y ≠ 0 := hlog.ne'
    field_simp [hs, hl]
  calc
    (κ / 4) * (psi / (Real.sqrt p * Real.log y))
        = κ * psi / (4 * Real.sqrt p) / Real.log y := hEq.symm
    _ ≤ SF / Real.log y := hdiv
    _ ≤ success := hstage

/-- The per-curve success lower bound `cRate * D ≤ success` for the L27.1 data,
using the Deuring counts and the stage-one success input. -/
theorem cRate_mul_density_le_success_of (I : L27_1Inputs)
    (h : DeuringLenstraCounts I) (hell : EllipticCurveGroupLaw I) (n : ℕ) :
    I.cRate * I.D n ≤ I.success n := by
  have hp : (0 : ℝ) < (I.p n : ℝ) := by exact_mod_cast I.p_pos n
  have hstage : I.SF n / Real.log (I.y n) ≤ I.success n := by
    simpa [L27_1Inputs.SF, L27_1Inputs.SC, L27_1Inputs.CT, smoothFraction]
      using hell.2.2 n
  simpa [L27_1Inputs.cRate, L27_1Inputs.D, density] using
    cRate_density_le_of_fraction (κ := I.κ) (psi := I.psi n) (p := (I.p n : ℝ))
      (y := I.y n) (SF := I.SF n) (success := I.success n)
      hp (I.y_gt_one n) (smoothFraction_lower_of I h n) hstage

/-- The joint failure of the independent curve draws is at most
`exp (-(κ/4) · #curves · ψ/(√p log y))`. -/
theorem splitFail_le_exp_of (I : L27_1Inputs)
    (h : DeuringLenstraCounts I) (hell : EllipticCurveGroupLaw I) (n : ℕ) :
    I.splitFail n ≤ Real.exp (-(I.cRate * I.rate n)) := by
  have hd1 : I.cRate * I.D n ≤ 1 :=
    (cRate_mul_density_le_success_of I h hell n).trans (I.success_le_one n)
  have hs : I.cRate * I.D n ≤ I.success n := cRate_mul_density_le_success_of I h hell n
  have hjoint : (1 - I.success n) ^ I.curves n ≤
      Real.exp (-(((I.curves n : ℝ)) * (I.cRate * I.D n))) :=
    joint_failure_le_exp hd1 hs (I.success_le_one n)
  have hexp : Real.exp (-(((I.curves n : ℝ)) * (I.cRate * I.D n))) =
      Real.exp (-(I.cRate * I.rate n)) := by
    congr 1
    unfold L27_1Inputs.rate L27_1Inputs.D density
    ring
  calc
    I.splitFail n = (1 - I.success n) ^ I.curves n := I.independence n
    _ ≤ Real.exp (-(((I.curves n : ℝ)) * (I.cRate * I.D n))) := hjoint
    _ = Real.exp (-(I.cRate * I.rate n)) := hexp

/-- The joint failure is nonnegative. -/
theorem splitFail_nonneg_of (I : L27_1Inputs) (n : ℕ) : 0 ≤ I.splitFail n := by
  unfold L27_1Inputs.splitFail
  rw [I.independence n]
  refine pow_nonneg ?_ _
  have h := I.success_le_one n
  linarith

/-- The L27.1 deficit is nonnegative. -/
theorem loss_nonneg_of (I : L27_1Inputs) (n : ℕ) : 0 ≤ I.loss n := by
  unfold L27_1Inputs.loss
  exact mul_nonneg (Nat.cast_nonneg _) (splitFail_nonneg_of I n)

/-! ## 7. The reduced L27.1 conclusions -/

/-- **Reduced L27.1 ledger.**  From the paper-level Deuring/Lenstra counts and
elliptic-curve group-law inputs, the curve budget, and the log-factor
subexponential input, the recursive ECM deficit is eventually at most
`exp (-2H)`.  No curve count or group law is assumed beyond the two explicit
`Prop`s. -/
theorem reduced_ledger (I : L27_1Inputs)
    (hdeuring : DeuringLenstraCounts I) (hell : EllipticCurveGroupLaw I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) := by
  filter_upwards [hbudget, hlog (I.η / 2) (by linarith [I.η_pos]),
    scale_grows.eventually_ge_atTop 0] with n hb hl hs
  have hbudget' : (2 + I.η) * scale n ≤ I.cRate * I.rate n := by
    simpa [L27_1Inputs.cRate, L27_1Inputs.rate, L27_1Inputs.D, density] using hb
  have hfail := splitFail_le_exp_of I hdeuring hell n
  have h := loss_le_exp_of_budget (H := scale n) (E := I.cRate * I.rate n)
    (L := ((I.cofactor n).log2 : ℝ)) (fail := I.splitFail n) (η := I.η)
    hs I.η_pos hbudget' (splitFail_nonneg_of I n) hl hfail
  simpa [L27_1Inputs.loss] using h

/-- **Reduced L27.1 manuscript rate.**  With the same explicit paper-level
inputs, the deficit is eventually at most `exp (-(κ/8) · #curves · ψ/(√p log y))`. -/
theorem reduced_paper (I : L27_1Inputs)
    (hdeuring : DeuringLenstraCounts I) (hell : EllipticCurveGroupLaw I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) := by
  filter_upwards [hbudget, hlog (I.η / 2) (by linarith [I.η_pos]),
    scale_grows.eventually_ge_atTop 0] with n hb hl hs
  have hbudget' : (2 + I.η) * scale n ≤ I.cRate * I.rate n := by
    simpa [L27_1Inputs.cRate, L27_1Inputs.rate, L27_1Inputs.D, density] using hb
  have hfail := splitFail_le_exp_of I hdeuring hell n
  have h := loss_le_exp_half_of_budget (H := scale n) (E := I.cRate * I.rate n)
    (L := ((I.cofactor n).log2 : ℝ)) (fail := I.splitFail n) (η := I.η)
    hs hbudget' (splitFail_nonneg_of I n) hl hfail
  have hgoal : Real.exp (-((I.cRate * I.rate n) / 2)) =
      Real.exp (-((I.cRate / 2) * I.rate n)) := by
    congr 1
    ring
  simpa [L27_1Inputs.loss, hgoal] using h

/-- The reduced L27.1 data as a `RatedLeaf`: the manuscript rate is the paper
bound and the ledger is the explicit curve-budget estimate. -/
def toRatedLeaf (I : L27_1Inputs)
    (hdeuring : DeuringLenstraCounts I) (hell : EllipticCurveGroupLaw I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) : RatedLeaf where
  loss := I.loss
  loss_nonneg := loss_nonneg_of I
  rate := I.rate
  c := I.cRate / 2
  c_pos := by
    unfold L27_1Inputs.cRate
    linarith [I.κ_pos]
  paper := reduced_paper I hdeuring hell hbudget hlog
  ledger := reduced_ledger I hdeuring hell hbudget hlog

/-- The reduced `RatedLeaf` satisfies the C5 `exp (-2H)` slot. -/
theorem toRatedLeaf_slot (I : L27_1Inputs)
    (hdeuring : DeuringLenstraCounts I) (hell : EllipticCurveGroupLaw I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop,
      (toRatedLeaf I hdeuring hell hbudget hlog).loss n ≤
        Real.exp (-(2 : ℝ) * scale n) :=
  (toRatedLeaf I hdeuring hell hbudget hlog).slot

/-! ## 8. Compatibility with the bundled `L27_1Inputs` -/

/-- The parent structure's Deuring fields are exactly the explicit
`DeuringLenstraCounts` `Prop`. -/
theorem deuringLenstraCounts_of_inputs (I : L27_1Inputs) : DeuringLenstraCounts I :=
  ⟨I.deuring_count, I.curve_total_le⟩

/-- The parent structure's elliptic-curve fields are exactly the explicit
`EllipticCurveGroupLaw` `Prop`. -/
theorem ellipticCurveGroupLaw_of_inputs (I : L27_1Inputs) : EllipticCurveGroupLaw I :=
  ⟨I.hasse, I.gcd_exit, I.stage_one⟩

/-- Reproducing the L27.1 ledger from the bundled inputs through the reduced
sub-lemmas. -/
theorem reduced_ledger_inputs (I : L27_1Inputs) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  reduced_ledger I (deuringLenstraCounts_of_inputs I) (ellipticCurveGroupLaw_of_inputs I)
    I.curve_budget I.logFactor_subexp

/-- Reproducing the L27.1 manuscript rate from the bundled inputs through the
reduced sub-lemmas. -/
theorem reduced_paper_inputs (I : L27_1Inputs) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  reduced_paper I (deuringLenstraCounts_of_inputs I) (ellipticCurveGroupLaw_of_inputs I)
    I.curve_budget I.logFactor_subexp

/-! ## Axiom audit -/

#print axioms hasse_upper
#print axioms hasse_lower
#print axioms two_mul_sqrt_le_add_one
#print axioms four_mul_sqrt_le_four_mul
#print axioms hasse_order_le_orderTop
#print axioms hasse_support
#print axioms one_sub_pow_le_exp_neg
#print axioms union_bound_finset
#print axioms one_sub_pow_le_nat_mul
#print axioms joint_failure_le_exp
#print axioms budget_ledger_le
#print axioms budget_paper_le
#print axioms loss_le_exp_of_budget
#print axioms loss_le_exp_half_of_budget
#print axioms LogFactorSubexp.log_le
#print axioms logFactorSubexp_of_log_le
#print axioms LogFactorSubexp.pow_le
#print axioms LogFactorSubexp.const_mul_le
#print axioms deuringSmoothCount_of
#print axioms smoothFraction_lower_of
#print axioms cRate_mul_density_le_success_of
#print axioms splitFail_le_exp_of
#print axioms reduced_ledger
#print axioms reduced_paper
#print axioms toRatedLeaf
#print axioms toRatedLeaf_slot
#print axioms deuringLenstraCounts_of_inputs
#print axioms ellipticCurveGroupLaw_of_inputs
#print axioms reduced_ledger_inputs
#print axioms reduced_paper_inputs

end

end Cogentic.RandomizedL27_1Sub
