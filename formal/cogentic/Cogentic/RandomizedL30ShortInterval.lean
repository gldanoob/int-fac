import Cogentic.RandomizedL30Interval

/-!
# L30: the explicit short-interval odd-smooth count

`Cogentic/RandomizedL30Interval.lean` reduced the paper's odd short-interval
density to the explicit count

```
YounisOddShortIntervalCount c p t err :
  ∀ n, c * p_n^{3/2} ≤ centralOddSmoothCount p t err n .
```

The present file makes that count the primary object and records the exact
relations to the paper-scale count, to the global parity bound, and to the
existing prime-bin smooth-set construction.

## What is proved

1. **The smallest explicit short-interval count.**  The set-level statement
   `CentralOddSmoothSetCountLower` says that, at every band, an honest finite
   subset of `centralOddSmoothOrders` has cardinality at least
   `c p^{3/2}`.  It is *equivalent* to `YounisOddShortIntervalCount`
   (`centralOddSmoothSetCountLower_iff`), so the cardinality formulation loses
   nothing.  A family of subsets with the required cardinality supplies the
   count (`shortIntervalCount_of_setFamily`).

2. **The paper-scale comparison.**  In the paper regime `(1+ε)t ≥ 0`, the
   exponential factor `exp (-(1+ε)t)` is at most one, so the fixed-density
   short count implies the paper-scale count
   (`paperShortCount_of_shortIntervalCount`).  Conversely, the paper-scale
   count implies the fixed-density count only in the opposite corner
   `(1+ε)t ≤ 0` (`shortIntervalCount_of_paperShortCount_of_nonpos`).  This
   records explicitly that the fixed-density statement is the stronger one at
   the manuscript cutoff; it is not silently substituted for the paper count.

3. **The global parity bound.**  Composing with the parity reduction of
   `RandomizedL30Relative` gives relative short-interval density from the
   explicit count (`relativeShortInterval_of_shortIntervalCount`), and then,
   with the global odd lower bound, the paper's odd central count
   (`younisOddCentralCount_of_shortIntervalCount`).  This is the chain in which
   the unconditional bound `globalOddSmoothCount ≤ p²/4 + 1/2` is used.

4. **A genuine paper-regime construction.**  The powers-of-two device is
   useless here: an odd-half power of two is necessarily `2`
   (`oddHalf_pow_two_eq_two`), so even the first band of the witness regime
   cannot be supplied by powers of two
   (`paperWitness_powTwo_insufficient`).  Instead we use the actual smooth set
   `{p_n² - (4j+2) : j < 8^{n+3}}` of
   `Cogentic.RandomizedL30Relative`.  At the paper scale
   `t = paperT witnessP` with the explicit relative error
   `paperWitnessErr n = 3 log (witnessP n) / paperT witnessP n`, the cutoff is
   `p³ exp (t) ≥ p³`, so the whole witness set is smooth.  This proves

   ```
   YounisOddShortIntervalCount (1/8) witnessP (paperT witnessP) paperWitnessErr
   ```

   unconditionally, together with `PaperRegime witnessP (paperT witnessP)
   paperWitnessErr`.  The construction is genuinely positive (`8^{n+3}`
   orders), never a zero count.

   **Scope of the construction.**  This is the large-cutoff corner of the
   formal `PaperRegime`: the formal structure only asks `t = paperT p` and
   `0 ≤ ε`, and here `ε` is deliberately chosen to make the cutoff dominate
   `p³`.  It is not the manuscript's `ε → 0` cutoff.  At that cutoff §2 shows
   that the fixed-density statement implies the paper-scale count (the
   implication runs in the stronger-to-weaker direction), so the paper-scale
   estimate is not a substitute for the fixed-density statement.  The
   manuscript-cutoff residual is the explicit paper-scale count, and §6 gives
   its exact transfer from the existing `centeredBinProducts` construction.

5. **The prime-bin bridge.**  For the existing smooth-number density estimates,
   `doubledCenteredBinProducts` is the parity-corrected prime-bin set
   `{2 x : x ∈ centeredBinProducts …}`.  When the bins are bounded below by
   three, every `x` is odd, hence `2 x ≡ 2 (mod 4)`, and when the doubled
   multiplicative strip lies inside the central interval every such order is a
   central odd smooth order (`doubledCenteredBinProducts_subset_centralOddSmoothOrders`).
   Consequently any lower bound on `centeredBinProducts` transfers to
   `centralOddSmoothCount` (`centralOddSmoothCount_lower_of_binCount`).  This is
   the exact implication supplied by the existing density construction; the
   sharp paper-scale lower bound for `centeredBinProducts` remains the analytic
   input isolated elsewhere.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no count or error
is set to zero.
-/

namespace Cogentic.RandomizedL30ShortInterval

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Relative
open Cogentic.RandomizedL30Interval
open Cogentic.Randomized

noncomputable section

/-! ## 1. The smallest explicit short-interval count -/

/-- **The set-level short-interval count.**  At every band there is an honest
finite subset of the central odd smooth orders whose cardinality is at least
`c p^{3/2}`.  This is the smallest explicit form of the count: it mentions no
smoothness cutoff and no global quantity, only a literal finite subset of the
paper's set. -/
def CentralOddSmoothSetCountLower (c : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ n, ∃ S : Finset ℕ,
    S ⊆ centralOddSmoothOrders p t err n ∧
      c * p n ^ ((3 : ℝ) / 2) ≤ (S.card : ℝ)

/-- The set-level count is exactly the cardinality count. -/
theorem centralOddSmoothSetCountLower_iff {c : ℝ} {p t err : ℕ → ℝ} :
    CentralOddSmoothSetCountLower c p t err ↔
      YounisOddShortIntervalCount c p t err := by
  constructor
  · intro h n
    obtain ⟨S, hsub, hcard⟩ := h n
    have hle : (S.card : ℝ) ≤ centralOddSmoothCount p t err n := by
      unfold centralOddSmoothCount
      exact_mod_cast Finset.card_le_card hsub
    exact hcard.trans hle
  · intro h n
    exact ⟨centralOddSmoothOrders p t err n, subset_rfl, h n⟩

/-- A family of explicit subsets with the required cardinality supplies the
short-interval count.  This is the form in which a construction (prime bins,
the witness set, or a direct enumeration) is consumed. -/
theorem shortIntervalCount_of_setFamily {c : ℝ} {p t err : ℕ → ℝ}
    {S : ℕ → Finset ℕ}
    (hsub : ∀ n, S n ⊆ centralOddSmoothOrders p t err n)
    (hcard : ∀ n, c * p n ^ ((3 : ℝ) / 2) ≤ (S n).card) :
    YounisOddShortIntervalCount c p t err := by
  intro n
  have hle : ((S n).card : ℝ) ≤ centralOddSmoothCount p t err n := by
    unfold centralOddSmoothCount
    exact_mod_cast Finset.card_le_card (hsub n)
  exact (hcard n).trans hle

/-- The set-level count is nonempty whenever the demand is positive: the
witnessing set contains a genuine element, not a formal zero. -/
theorem setCount_card_pos_of_pos {c : ℝ} {p t err : ℕ → ℝ}
    (h : CentralOddSmoothSetCountLower c p t err) {n : ℕ}
    (hpos : 0 < c * p n ^ ((3 : ℝ) / 2)) :
    0 < (Classical.choose (h n)).card := by
  have hspec := Classical.choose_spec (h n)
  have hle : (0 : ℝ) < ((Classical.choose (h n)).card : ℝ) :=
    lt_of_lt_of_le hpos hspec.2
  exact_mod_cast hle

/-! ## 2. The paper-scale comparison -/

/-- **The fixed-density count implies the paper-scale count.**  When
`(1 + ε) t ≥ 0`, the factor `exp (-(1+ε)t)` is at most one, so the paper's
displayed count `c p^{3/2} exp (-(1+ε)t)` is weaker than the fixed-density
count. -/
theorem paperShortCount_of_shortIntervalCount {c : ℝ} {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (h : YounisOddShortIntervalCount c p t err)
    (hexp : ∀ n, 0 ≤ (1 + err n) * t n) :
    YounisOddPaperShortCount c p t err := by
  intro n
  have hp_nonneg : (0 : ℝ) ≤ p n := by linarith [hp n]
  have hp32 : (0 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hp_nonneg _
  have he : Real.exp (-(1 + err n) * t n) ≤ 1 := by
    calc
      Real.exp (-(1 + err n) * t n) ≤ Real.exp 0 := by
        apply Real.exp_le_exp.mpr
        have hneg : -(1 + err n) * t n = -((1 + err n) * t n) := by ring
        rw [hneg]
        exact neg_nonpos.mpr (hexp n)
      _ = 1 := Real.exp_zero
  by_cases hc : 0 ≤ c
  · have hnon : (0 : ℝ) ≤ c * p n ^ ((3 : ℝ) / 2) := mul_nonneg hc hp32
    calc
      c * p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n)
          ≤ c * p n ^ ((3 : ℝ) / 2) * 1 :=
            mul_le_mul_of_nonneg_left he hnon
      _ = c * p n ^ ((3 : ℝ) / 2) := by ring
      _ ≤ centralOddSmoothCount p t err n := h n
  · have hc' : c < 0 := lt_of_not_ge hc
    have hepos : (0 : ℝ) ≤ Real.exp (-(1 + err n) * t n) := (Real.exp_pos _).le
    have hleft : c * p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc'.le hp32) hepos
    have hright : (0 : ℝ) ≤ centralOddSmoothCount p t err n := by
      unfold centralOddSmoothCount
      positivity
    exact hleft.trans hright

/-- **The paper-scale count in the nonpositive-exponent corner.**  If
`(1 + ε) t ≤ 0`, then `exp (-(1+ε)t) ≥ 1`, so the paper-scale count is at
least the fixed-density count.  Together with the preceding theorem this shows
that the two statements agree exactly on `(1+ε)t = 0`; away from that corner the
fixed-density statement is strictly stronger when the exponent is positive. -/
theorem shortIntervalCount_of_paperShortCount_of_nonpos {c : ℝ} {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (h : YounisOddPaperShortCount c p t err)
    (hexp : ∀ n, (1 + err n) * t n ≤ 0) :
    YounisOddShortIntervalCount c p t err := by
  intro n
  have hp_nonneg : (0 : ℝ) ≤ p n := by linarith [hp n]
  have hp32 : (0 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hp_nonneg _
  have he : (1 : ℝ) ≤ Real.exp (-(1 + err n) * t n) := by
    calc
      (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (-(1 + err n) * t n) := by
        apply Real.exp_le_exp.mpr
        have hneg : -(1 + err n) * t n = -((1 + err n) * t n) := by ring
        rw [hneg]
        exact neg_nonneg.mpr (hexp n)
  by_cases hc : 0 ≤ c
  · have hnon : (0 : ℝ) ≤ c * p n ^ ((3 : ℝ) / 2) := mul_nonneg hc hp32
    have hle : c * p n ^ ((3 : ℝ) / 2) ≤
        c * p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n) := by
      calc
        c * p n ^ ((3 : ℝ) / 2) = c * p n ^ ((3 : ℝ) / 2) * 1 := by ring
        _ ≤ c * p n ^ ((3 : ℝ) / 2) *
              Real.exp (-(1 + err n) * t n) :=
            mul_le_mul_of_nonneg_left he hnon
    exact hle.trans (h n)
  · have hc' : c < 0 := lt_of_not_ge hc
    have hepos : (0 : ℝ) ≤ Real.exp (-(1 + err n) * t n) := (Real.exp_pos _).le
    have hleft : c * p n ^ ((3 : ℝ) / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc'.le hp32
    have hright : (0 : ℝ) ≤ centralOddSmoothCount p t err n := by
      unfold centralOddSmoothCount
      positivity
    exact hleft.trans hright

/-! ## 3. The global parity bound and the reduction to the paper count -/

/-- **The global parity bound in density form.**  The unconditional bound
`globalOddSmoothCount ≤ p²/4 + 1/2` gives `Ψ_odd(p²,Y)/p² ≤ 3/8` for `p ≥ 2`.
This is the upper-density companion used by the relative short-interval
reduction. -/
theorem globalOddSmoothCount_div_sq_le_three_eighths {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) :
    globalOddSmoothCount p t err n / p n ^ 2 ≤ 3 / 8 := by
  have hp_pos : (0 : ℝ) < p n := by linarith [hp]
  have hp2 : (0 : ℝ) < p n ^ 2 := pow_pos hp_pos 2
  have hp4 : (4 : ℝ) ≤ p n ^ 2 := by
    have hp2' : (2 : ℝ) ≤ p n := by exact_mod_cast hp
    nlinarith [sq_nonneg (p n - 2), hp2']
  have hG := globalOddSmoothCount_le_quarter_sq (p := p) (t := t) (err := err) hp
  rw [div_le_iff₀ hp2]
  nlinarith

/-- **Relative short-interval density from the explicit count.**  The parity
bound `globalOddSmoothCount ≤ p²/4 + 1/2` is what turns the fixed interval
count `c p^{3/2}` into `A |interval| Ψ_odd / p²` with `3 A / 8 ≤ c`.  This is
the composition of `intervalDensity_of_shortIntervalCount` with the parity
reduction of `RandomizedL30Relative`. -/
theorem relativeShortInterval_of_shortIntervalCount {A c : ℝ} {p t err : ℕ → ℝ}
    (hA : 0 ≤ A) (hp : ∀ n, 2 ≤ p n) (hAc : 3 * A / 8 ≤ c)
    (h : YounisOddShortIntervalCount c p t err) :
    YounisOddRelativeShortInterval A p t err :=
  younisOddRelative_of_intervalDensity hA hp hAc
    (intervalDensity_of_shortIntervalCount hp h)

/-- **The odd central count from the explicit short count and the global lower
bound.**  This is the full parity chain: the explicit short-interval count plus
the global odd lower bound give `YounisOddCentralCount`, with the interval
cardinality loss absorbed by `A B ≥ 4`. -/
theorem younisOddCentralCount_of_shortIntervalCount {A B c : ℝ} {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) (hA : 0 < A) (hB : 0 < B) (hAB : 4 ≤ A * B)
    (hAc : 3 * A / 8 ≤ c)
    (h : YounisOddShortIntervalCount c p t err)
    (hglob : YounisOddGlobalLower B p t err) :
    YounisOddCentralCount p t err :=
  younisOddCentralCount_of_density hp hA hB hAB
    (relativeShortInterval_of_shortIntervalCount hA.le hp hAc h) hglob

/-! ## 4. The concrete paper-regime witness -/

/-- The explicit relative error at the witness scale:
`ε_n = 3 log p_n / t_{p_n}`.  The resulting paper cutoff is
`exp ((1+ε_n) t_n) = p_n³ exp (t_n)`, which dominates the witness cutoff
`p_n³`. -/
def paperWitnessErr (n : ℕ) : ℝ :=
  3 * Real.log (witnessP n) / paperT witnessP n

/-- The witness scale is at least `256`. -/
theorem witnessP_ge_256 (n : ℕ) : (256 : ℝ) ≤ witnessP n := by
  unfold witnessP
  have h : (4 : ℝ) ^ 4 ≤ (4 : ℝ) ^ (n + 4) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at h ⊢
  exact h

/-- `log p_n` is positive. -/
theorem witnessP_log_pos (n : ℕ) : 0 < Real.log (witnessP n) := by
  apply Real.log_pos
  linarith [witnessP_ge_two n]

/-- `log log p_n` is positive.  This only uses `p_n ≥ 256 > e`. -/
theorem witnessP_log_log_pos (n : ℕ) : 0 < Real.log (Real.log (witnessP n)) := by
  apply Real.log_pos
  have h256 := witnessP_ge_256 n
  have hlog : Real.log 256 ≤ Real.log (witnessP n) :=
    Real.log_le_log (by norm_num) h256
  have h256log : (1 : ℝ) < Real.log 256 := by
    have h : Real.log 256 = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      norm_num
    rw [h]
    nlinarith [Real.log_two_gt_d9]
  linarith

/-- The paper scale at the witness is positive. -/
theorem paperT_witness_pos (n : ℕ) : 0 < paperT witnessP n := by
  unfold paperT
  exact Real.sqrt_pos.mpr (mul_pos (witnessP_log_pos n) (witnessP_log_log_pos n))

/-- The explicit paper cutoff at the witness scale. -/
theorem paperWitness_cutoff_eq (n : ℕ) :
    smoothCutoff (paperT witnessP) paperWitnessErr n =
      witnessP n ^ 3 * Real.exp (paperT witnessP n) := by
  unfold smoothCutoff paperWitnessErr
  have ht : paperT witnessP n ≠ 0 := (paperT_witness_pos n).ne'
  have harg : (1 + 3 * Real.log (witnessP n) / paperT witnessP n) *
      paperT witnessP n =
        paperT witnessP n + 3 * Real.log (witnessP n) := by
    field_simp
  rw [harg, Real.exp_add]
  have hcube : Real.exp (3 * Real.log (witnessP n)) = witnessP n ^ 3 := by
    rw [show (3 : ℝ) * Real.log (witnessP n) =
        ((3 : ℕ) : ℝ) * Real.log (witnessP n) by norm_num]
    rw [Real.exp_nat_mul, Real.exp_log (witnessP_pos n)]
  rw [hcube]
  ring

/-- The paper cutoff at the witness scale dominates the witness cutoff `p³`. -/
theorem paperWitness_cutoff_ge_witnessT (n : ℕ) :
    smoothCutoff witnessT witnessErr n ≤
      smoothCutoff (paperT witnessP) paperWitnessErr n := by
  rw [smoothCutoff_witnessT, paperWitness_cutoff_eq]
  have hp3 : (0 : ℝ) ≤ witnessP n ^ 3 := pow_nonneg (witnessP_pos n).le 3
  have he1 : (1 : ℝ) ≤ Real.exp (paperT witnessP n) := by
    calc
      (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (paperT witnessP n) :=
          Real.exp_le_exp.mpr (paperT_witness_pos n).le
  calc
    witnessP n ^ 3 = witnessP n ^ 3 * 1 := by ring
    _ ≤ witnessP n ^ 3 * Real.exp (paperT witnessP n) :=
        mul_le_mul_of_nonneg_left he1 hp3

/-- **The explicit paper-regime short-interval count.**  At
`p = witnessP`, `t = paperT p`, and `ε = paperWitnessErr`, the central interval
contains at least `p^{3/2}/8` odd smooth orders.  The count is the cardinality
of the constructed witness set `{p² - (4j+2)}`, not a power-of-two count. -/
theorem paperWitness_shortIntervalCount :
    YounisOddShortIntervalCount (1 / 8) witnessP (paperT witnessP) paperWitnessErr := by
  intro n
  have hcount := witnessLevel_le_centralOddSmoothCount_of_cutoff
    (t := paperT witnessP) (err := paperWitnessErr)
    (fun m => paperWitness_cutoff_ge_witnessT m) n
  have hlevel : (1 / 8) * witnessP n ^ ((3 : ℝ) / 2) = (witnessLevel n : ℝ) := by
    rw [witnessP_rpow_three_halves]
    unfold witnessLevel
    rw [show n + 4 = (n + 3) + 1 by omega, pow_succ]
    push_cast
    ring
  rw [hlevel]
  exact hcount

/-- The witness tuple is a paper regime in the formal sense: the scale is
`t_p` and the relative error is nonnegative. -/
theorem paperWitness_regime :
    PaperRegime witnessP (paperT witnessP) paperWitnessErr := by
  refine ⟨rfl, ?_⟩
  intro n
  unfold paperWitnessErr
  exact div_nonneg (mul_nonneg (by norm_num) (witnessP_log_pos n).le)
    (paperT_witness_pos n).le

/-- The witness family supplies the set-level count directly. -/
theorem paperWitness_setCount :
    CentralOddSmoothSetCountLower (1 / 8) witnessP (paperT witnessP) paperWitnessErr := by
  intro n
  refine ⟨witnessLocalSet n, ?_, ?_⟩
  · exact (witnessLocalSet_subset n).trans
      (centralOddSmoothOrders_mono_cutoff (paperWitness_cutoff_ge_witnessT n))
  · rw [witnessLocalSet_card]
    have hlevel : (1 / 8) * witnessP n ^ ((3 : ℝ) / 2) = (witnessLevel n : ℝ) := by
      rw [witnessP_rpow_three_halves]
      unfold witnessLevel
      rw [show n + 4 = (n + 3) + 1 by omega, pow_succ]
      push_cast
      ring
    rw [hlevel]

/-- The paper-scale count at the witness regime. -/
theorem paperWitness_paperShortCount :
    YounisOddPaperShortCount (1 / 8) witnessP (paperT witnessP) paperWitnessErr := by
  refine paperShortCount_of_shortIntervalCount
    (hp := fun n => witnessP_ge_two n) paperWitness_shortIntervalCount ?_
  intro n
  have ht : 0 ≤ paperT witnessP n := (paperT_witness_pos n).le
  have he : 0 ≤ paperWitnessErr n := paperWitness_regime.2 n
  nlinarith [mul_nonneg he ht]

/-- **The global odd lower bound at the witness regime**, with the explicit
constant `48`.  Since the paper cutoff is `p³ exp (t) ≥ p³`, the target
`48 p² exp (-(1+ε)t) = 48 / (p exp t)` is at most one, while the constructed
central odd set already has `p^{3/2}/8 ≥ 1` elements. -/
theorem paperWitness_globalLower :
    YounisOddGlobalLower 48 witnessP (paperT witnessP) paperWitnessErr := by
  intro n
  have hshort := paperWitness_shortIntervalCount n
  have hmono := centralOddSmoothOrders_subset_globalOdd
    (p := witnessP) (t := paperT witnessP) (err := paperWitnessErr)
    (witnessP_ge_two n)
  have hcard : centralOddSmoothCount witnessP (paperT witnessP) paperWitnessErr n ≤
      globalOddSmoothCount witnessP (paperT witnessP) paperWitnessErr n := by
    unfold centralOddSmoothCount globalOddSmoothCount
    exact_mod_cast Finset.card_le_card hmono
  have hglob : (1 / 8) * witnessP n ^ ((3 : ℝ) / 2) ≤
      globalOddSmoothCount witnessP (paperT witnessP) paperWitnessErr n :=
    hshort.trans hcard
  have hexp_eq : Real.exp (-(1 + paperWitnessErr n) * paperT witnessP n) =
      1 / smoothCutoff (paperT witnessP) paperWitnessErr n := by
    unfold smoothCutoff
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have htarget_eq : 48 * witnessP n ^ 2 *
      Real.exp (-(1 + paperWitnessErr n) * paperT witnessP n) =
        48 / (witnessP n * Real.exp (paperT witnessP n)) := by
    rw [hexp_eq, paperWitness_cutoff_eq]
    have hp : witnessP n ≠ 0 := (witnessP_pos n).ne'
    have he : Real.exp (paperT witnessP n) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  have hden_pos : (0 : ℝ) < witnessP n * Real.exp (paperT witnessP n) := by
    exact mul_pos (witnessP_pos n) (Real.exp_pos _)
  have htarget_le_one : 48 / (witnessP n * Real.exp (paperT witnessP n)) ≤ 1 := by
    rw [div_le_one hden_pos]
    have hp256 : (256 : ℝ) ≤ witnessP n := witnessP_ge_256 n
    have he1 : (1 : ℝ) ≤ Real.exp (paperT witnessP n) := by
      calc
        (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (paperT witnessP n) :=
            Real.exp_le_exp.mpr (paperT_witness_pos n).le
    calc
      (48 : ℝ) ≤ witnessP n := by linarith
      _ = witnessP n * 1 := by ring
      _ ≤ witnessP n * Real.exp (paperT witnessP n) :=
          mul_le_mul_of_nonneg_left he1 (witnessP_pos n).le
  have hgt1 : (1 : ℝ) ≤ (1 / 8) * witnessP n ^ ((3 : ℝ) / 2) := by
    have hp32 : (8 : ℝ) ≤ witnessP n ^ ((3 : ℝ) / 2) := by
      rw [witnessP_rpow_three_halves]
      have h : (8 : ℝ) ^ 1 ≤ (8 : ℝ) ^ (n + 4) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      simpa using h
    nlinarith
  calc
    48 * witnessP n ^ 2 *
        Real.exp (-(1 + paperWitnessErr n) * paperT witnessP n)
        = 48 / (witnessP n * Real.exp (paperT witnessP n)) := htarget_eq
    _ ≤ 1 := htarget_le_one
    _ ≤ (1 / 8) * witnessP n ^ ((3 : ℝ) / 2) := hgt1
    _ ≤ globalOddSmoothCount witnessP (paperT witnessP) paperWitnessErr n := hglob

/-- **The relative short-interval density at the witness regime**, obtained
from the explicit count and the global parity bound. -/
theorem paperWitness_relative :
    YounisOddRelativeShortInterval (1 / 3) witnessP (paperT witnessP) paperWitnessErr :=
  paperRelative_of_shortIntervalCount
    (A := 1 / 3) (a := 1 / 8) (by norm_num)
    (fun n => witnessP_ge_two n) (by norm_num)
    paperWitness_shortIntervalCount

/-- **The paper's odd central count at the witness regime.**  This is the full
chain: explicit short count `→` parity/relative density `→` global lower `→`
odd central count. -/
theorem paperWitness_centralCount :
    YounisOddCentralCount witnessP (paperT witnessP) paperWitnessErr :=
  younisOddCentralCount_of_density
    (p := witnessP) (t := paperT witnessP) (err := paperWitnessErr)
    (A := 1 / 3) (B := 48)
    (fun n => witnessP_ge_two n) (by norm_num) (by norm_num) (by norm_num)
    paperWitness_relative paperWitness_globalLower

/-- The unrestricted Younis count at the witness regime. -/
theorem paperWitness_younisCount :
    YounisShortIntervalCount witnessP (paperT witnessP) paperWitnessErr :=
  younisShortIntervalCount_of_odd paperWitness_centralCount

/-! ## 5. Powers of two cannot supply the count -/

/-- The powers of two in the central interval. -/
def powTwoCentralOrders (p : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (centralOrderInterval p n).filter fun m => ∃ j : ℕ, m = 2 ^ j

/-- The odd-half powers of two in the central interval. -/
def powTwoCentralOddOrders (p : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (powTwoCentralOrders p n).filter IsOddHalfOrder

/-- The only odd-half power of two is `2`. -/
theorem oddHalf_pow_two_eq_two {j : ℕ} (h : (2 : ℕ) ^ j % 4 = 2) :
    (2 : ℕ) ^ j = 2 := by
  cases j with
  | zero => norm_num at h
  | succ j =>
    cases j with
    | zero => norm_num
    | succ k =>
      exfalso
      have hpow : (2 : ℕ) ^ (k + 1 + 1) = 4 * 2 ^ k := by
        rw [pow_succ, pow_succ]
        ring
      rw [hpow] at h
      have hmod : (4 * 2 ^ k) % 4 = 0 := by
        rw [Nat.mul_mod]
        norm_num
      omega

/-- Every set of odd-half powers of two has at most one element. -/
theorem powTwoCentralOddOrders_card_le_one (p : ℕ → ℝ) (n : ℕ) :
    (powTwoCentralOddOrders p n).card ≤ 1 := by
  have hsub : powTwoCentralOddOrders p n ⊆ ({2} : Finset ℕ) := by
    intro m hm
    simp only [powTwoCentralOddOrders, powTwoCentralOrders, Finset.mem_filter] at hm
    obtain ⟨⟨_, j, rfl⟩, hodd⟩ := hm
    rw [oddHalf_pow_two_eq_two hodd]
    simp
  calc
    (powTwoCentralOddOrders p n).card ≤ ({2} : Finset ℕ).card :=
      Finset.card_le_card hsub
    _ = 1 := by simp

/-- **Powers of two fail already at the first witness band.**  The required
count at `n = 0` is `p_0^{3/2}/8 = 512`, while all odd-half powers of two
together contribute at most one order. -/
theorem paperWitness_powTwo_insufficient :
    ¬ ((1 / 8) * witnessP 0 ^ ((3 : ℝ) / 2) ≤
        ((powTwoCentralOddOrders witnessP 0).card : ℝ)) := by
  intro h
  have hcard : (powTwoCentralOddOrders witnessP 0).card ≤ 1 :=
    powTwoCentralOddOrders_card_le_one witnessP 0
  have hcardR : ((powTwoCentralOddOrders witnessP 0).card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  have hgt : (1 : ℝ) < (1 / 8) * witnessP 0 ^ ((3 : ℝ) / 2) := by
    rw [witnessP_rpow_three_halves]
    norm_num
  linarith

/-! ## 6. The prime-bin smooth-set bridge -/

/-- The parity-corrected prime-bin set: every product is doubled, so an odd
product becomes an odd-half order `2 x ≡ 2 (mod 4)`. -/
def doubledCenteredBinProducts (P δ : ℝ) (J k a : ℕ) : Finset ℕ :=
  (centeredBinProducts P δ J k a).image fun x => 2 * x

/-- Membership in the doubled prime-bin set. -/
theorem mem_doubledCenteredBinProducts {P δ : ℝ} {J k a m : ℕ} :
    m ∈ doubledCenteredBinProducts P δ J k a ↔
      ∃ x ∈ centeredBinProducts P δ J k a, 2 * x = m := by
  simp [doubledCenteredBinProducts]

/-- Doubling does not change the cardinality. -/
theorem doubledCenteredBinProducts_card (P δ : ℝ) (J k a : ℕ) :
    (doubledCenteredBinProducts P δ J k a).card =
      (centeredBinProducts P δ J k a).card := by
  unfold doubledCenteredBinProducts
  rw [Finset.card_image_of_injOn]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h

/-- Every prime-bin product with all bins above three is odd. -/
theorem centeredBinProducts_odd_of_oddBins {P δ : ℝ} {J k a : ℕ}
    (hodd : ∀ j < J, 3 ≤ centeredBinFloor P δ a k j)
    {x : ℕ} (hx : x ∈ centeredBinProducts P δ J k a) :
    Odd x := by
  classical
  unfold centeredBinProducts primeBinPatternProducts at hx
  obtain ⟨s, hs, hprod⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hprod
  have hfmem (i : s) :
      f i ∈ primeBin (centeredBinFloor P δ a k i)
        (centeredBinFloor P δ a k (i + 1)) :=
    Fintype.mem_piFinset.mp hf i
  have hprime (i : s) : Nat.Prime (f i) :=
    (Finset.mem_filter.mp (hfmem i)).2
  have hgt (i : s) : 3 < f i := by
    have hi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hfmem i)).1).1
    have hsub := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).1
    have hj : (i : ℕ) < J := Finset.mem_range.mp (hsub i.2)
    have h3 := hodd (i : ℕ) hj
    omega
  have hmain := Finset.prod_induction (s := (Finset.univ : Finset s)) f
    (fun n => Odd n) (fun a b ha hb => ha.mul hb) (by norm_num)
    (fun i _ => (hprime i).odd_of_ne_two (by
      have h := hgt i
      omega))
  simpa using hmain

/-- For odd `n`, the doubled order `2 n` is `2` modulo `4`. -/
theorem two_mul_odd_mod_four {n : ℕ} (hn : Odd n) : (2 * n) % 4 = 2 := by
  obtain ⟨a, rfl⟩ := hn
  omega

/-- **The prime-bin bridge.**  If every bin is bounded below by three, the
doubled multiplicative strip lies inside the central interval, and the smooth
cutoff dominates every bin floor together with `2`, then every doubled
prime-bin product is a central odd smooth order. -/
theorem doubledCenteredBinProducts_subset_centralOddSmoothOrders
    {P δ : ℝ} {J k a : ℕ} {p t err : ℕ → ℝ} {n : ℕ}
    (hP : 0 ≤ P) (hk : 0 < k)
    (hodd : ∀ j < J, 3 ≤ centeredBinFloor P δ a k j)
    (hlo : p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 < 2 * P ^ k)
    (hhi : 2 * (P ^ k * Real.exp ((k : ℝ) * δ)) ≤ p n ^ 2)
    (hfloor : ∀ j < J, (centeredBinFloor P δ a k (j + 1) : ℝ) ≤
      smoothCutoff t err n)
    (hy2 : 2 ≤ smoothCutoff t err n) :
    doubledCenteredBinProducts P δ J k a ⊆ centralOddSmoothOrders p t err n := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ := mem_doubledCenteredBinProducts.mp hm
  have hxpos : 0 < x := by
    unfold centeredBinProducts primeBinPatternProducts at hx
    obtain ⟨s, hs, hprod⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hprod
    exact Finset.prod_pos fun i _ =>
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hf i)).2.pos
  have hstrip := centeredBinProducts_mem_strip hP hk hx
  have hcast : ((2 * x : ℕ) : ℝ) = 2 * (x : ℝ) := by
    rw [Nat.cast_mul]
    norm_num
  have hlo' : p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 < (2 * x : ℕ) := by
    have h2 : 2 * P ^ k ≤ ((2 * x : ℕ) : ℝ) := by
      rw [hcast]
      exact mul_le_mul_of_nonneg_left hstrip.1 (by norm_num : (0 : ℝ) ≤ 2)
    exact lt_of_lt_of_le hlo h2
  have hhi' : ((2 * x : ℕ) : ℝ) ≤ p n ^ 2 := by
    have h2 : ((2 * x : ℕ) : ℝ) ≤ 2 * (P ^ k * Real.exp ((k : ℝ) * δ)) := by
      rw [hcast]
      exact mul_le_mul_of_nonneg_left hstrip.2 (by norm_num : (0 : ℝ) ≤ 2)
    exact h2.trans hhi
  have hmemI : 2 * x ∈ centralOrderInterval p n := by
    rw [centralOrderInterval, Finset.mem_Icc]
    constructor
    · rw [Nat.ceil_le]
      exact hlo'.le
    · exact Nat.le_floor hhi'
  have hsmooth : IsSmoothUpTo (smoothCutoff t err n) (2 * x) := by
    intro q hq
    have hqprime := Nat.prime_of_mem_primeFactors hq
    have hdvd : q ∣ 2 * x := Nat.dvd_of_mem_primeFactors hq
    rcases hqprime.dvd_mul.mp hdvd with hq2 | hqx
    · have hqeq : q = 2 := (Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_two).mp hq2
      rw [hqeq]
      exact hy2
    · have hxmem : q ∈ x.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqprime, hqx, hxpos.ne'⟩
      exact centeredBinProducts_smooth hfloor hx q hxmem
  have hxodd : Odd x := centeredBinProducts_odd_of_oddBins hodd hx
  have hoddhalf : IsOddHalfOrder (2 * x) := two_mul_odd_mod_four hxodd
  rw [centralOddSmoothOrders, Finset.mem_filter]
  exact ⟨by
    rw [centralSmoothOrders, Finset.mem_filter]
    exact ⟨hmemI, hsmooth⟩, hoddhalf⟩

/-- A lower bound on the prime-bin count transfers to the central odd smooth
count whenever the doubled strip lies in the central interval. -/
theorem centralOddSmoothCount_lower_of_binCount
    {P δ : ℝ} {J k a : ℕ} {p t err : ℕ → ℝ} {n : ℕ} {c : ℝ}
    (hP : 0 ≤ P) (hk : 0 < k)
    (hodd : ∀ j < J, 3 ≤ centeredBinFloor P δ a k j)
    (hlo : p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 < 2 * P ^ k)
    (hhi : 2 * (P ^ k * Real.exp ((k : ℝ) * δ)) ≤ p n ^ 2)
    (hfloor : ∀ j < J, (centeredBinFloor P δ a k (j + 1) : ℝ) ≤
      smoothCutoff t err n)
    (hy2 : 2 ≤ smoothCutoff t err n)
    (hcount : c ≤ ((centeredBinProducts P δ J k a).card : ℝ)) :
    c ≤ centralOddSmoothCount p t err n := by
  have hsub := doubledCenteredBinProducts_subset_centralOddSmoothOrders
    hP hk hodd hlo hhi hfloor hy2
  have hcard : ((doubledCenteredBinProducts P δ J k a).card : ℝ) ≤
      centralOddSmoothCount p t err n := by
    unfold centralOddSmoothCount
    exact_mod_cast Finset.card_le_card hsub
  rw [doubledCenteredBinProducts_card] at hcard
  exact hcount.trans hcard

/-- **The short-interval count from a family of prime-bin density estimates.**
If, at every band, the existing `centeredBinProducts` construction produces a
doubled strip inside the central interval with at least `c p^{3/2}` elements,
then `YounisOddShortIntervalCount c` holds.  This is the exact composition of
the density construction with the parity correction; the analytic lower bound
on `centeredBinProducts` itself is the separate input. -/
theorem shortIntervalCount_of_binCount_family
    {c : ℝ} {p t err : ℕ → ℝ} {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hP : ∀ n, 0 ≤ P n)
    (hk : ∀ n, 0 < k n)
    (hodd : ∀ n j, j < J n →
      3 ≤ centeredBinFloor (P n) (δ n) (a n) (k n) j)
    (hlo : ∀ n, p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 < 2 * P n ^ k n)
    (hhi : ∀ n, 2 * (P n ^ k n * Real.exp ((k n : ℝ) * δ n)) ≤ p n ^ 2)
    (hfloor : ∀ n j, j < J n →
      (centeredBinFloor (P n) (δ n) (a n) (k n) (j + 1) : ℝ) ≤
        smoothCutoff t err n)
    (hy2 : ∀ n, 2 ≤ smoothCutoff t err n)
    (hcount : ∀ n,
      c * p n ^ ((3 : ℝ) / 2) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    YounisOddShortIntervalCount c p t err := by
  intro n
  exact centralOddSmoothCount_lower_of_binCount
    (hP n) (hk n) (fun j hj => hodd n j hj) (hlo n) (hhi n)
    (fun j hj => hfloor n j hj) (hy2 n) (hcount n)

/-- **The paper-scale short-interval count from a family of prime-bin density
estimates.**  This is the same composition as
`shortIntervalCount_of_binCount_family`, but with the paper's exponential
normalisation `exp (-(1+ε)t)` kept on the lower-bound side.  It is the exact
form in which a `centeredBinProducts` density estimate at the manuscript cutoff
feeds `YounisOddPaperShortCount`. -/
theorem paperShortCount_of_binCount_family
    {c : ℝ} {p t err : ℕ → ℝ} {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hP : ∀ n, 0 ≤ P n)
    (hk : ∀ n, 0 < k n)
    (hodd : ∀ n j, j < J n →
      3 ≤ centeredBinFloor (P n) (δ n) (a n) (k n) j)
    (hlo : ∀ n, p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 < 2 * P n ^ k n)
    (hhi : ∀ n, 2 * (P n ^ k n * Real.exp ((k n : ℝ) * δ n)) ≤ p n ^ 2)
    (hfloor : ∀ n j, j < J n →
      (centeredBinFloor (P n) (δ n) (a n) (k n) (j + 1) : ℝ) ≤
        smoothCutoff t err n)
    (hy2 : ∀ n, 2 ≤ smoothCutoff t err n)
    (hcount : ∀ n,
      c * p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    YounisOddPaperShortCount c p t err := by
  intro n
  exact centralOddSmoothCount_lower_of_binCount
    (hP n) (hk n) (fun j hj => hodd n j hj) (hlo n) (hhi n)
    (fun j hj => hfloor n j hj) (hy2 n) (hcount n)

/-! ## Axiom audit -/

#print axioms centralOddSmoothSetCountLower_iff
#print axioms shortIntervalCount_of_setFamily
#print axioms paperShortCount_of_shortIntervalCount
#print axioms shortIntervalCount_of_paperShortCount_of_nonpos
#print axioms globalOddSmoothCount_div_sq_le_three_eighths
#print axioms relativeShortInterval_of_shortIntervalCount
#print axioms younisOddCentralCount_of_shortIntervalCount
#print axioms paperWitness_shortIntervalCount
#print axioms paperWitness_regime
#print axioms paperWitness_setCount
#print axioms paperWitness_paperShortCount
#print axioms paperWitness_globalLower
#print axioms paperWitness_relative
#print axioms paperWitness_centralCount
#print axioms paperWitness_younisCount
#print axioms powTwoCentralOddOrders_card_le_one
#print axioms paperWitness_powTwo_insufficient
#print axioms doubledCenteredBinProducts_card
#print axioms centeredBinProducts_odd_of_oddBins
#print axioms doubledCenteredBinProducts_subset_centralOddSmoothOrders
#print axioms centralOddSmoothCount_lower_of_binCount
#print axioms shortIntervalCount_of_binCount_family
#print axioms paperShortCount_of_binCount_family

end

end Cogentic.RandomizedL30ShortInterval
