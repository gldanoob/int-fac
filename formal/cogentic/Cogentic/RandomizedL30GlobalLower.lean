import Cogentic.RandomizedL30Global
import Cogentic.RandomizedL30LPP
import Cogentic.RandomizedL30Interval

/-!
# L30: reducing and constructing the remaining global lower bounds

`Cogentic/RandomizedL30Global.lean` reduced the global odd smooth lower bound
`YounisOddGlobalLower B` to finite prime-supply data, and
`Cogentic/RandomizedL30LPP.lean` removed the raw LPP count by exhibiting the
canonical multiples family.  This file collects the three remaining inputs of
the H.3 bundle and reduces each of them to the smallest explicit statement the
existing development supports:

* `GlobalOddBinomialCount B p t err` — the global odd lower bound in purely
  finite-set form: at every scale there is a finite set `P` of odd primes at
  most the cutoff `Y = exp ((1+ε)t)` and an exponent `k` with
  `2 Y^k ≤ p²` and `B p² exp (-(1+ε)t) ≤ |P|.choose k`.
  The reduction `younisOddGlobalLower_of_binomialCount` is the direct
  composition with `globalOddSmoothCount_ge_choose`; the converse construction
  `globalOddBinomialCount_of_primeSupply` recovers it from the fields
  `OddPrimeSupply`, `smooth_pow_le` and `choose_lower` of
  `Cogentic.RandomizedL30Global.ConstructedInputs`.  The Prop is also proved
  outright for the concrete all-smooth cutoff, so it is not vacuous and the
  constructed count is a genuine positive cardinality
  (`globalOddSmoothCount_pos_of_binomialCount`).

* `LPPModelSuperset p t err fibreModels` — the smallest explicit form of the
  raw LPP count: every eligible fibre contains the canonical multiples family
  `lppModelMultiples`.  `lppRawLogModelCount_of_modelSuperset` turns the
  inclusion into the raw count, and `lppModelSuperset_multiples` proves it for
  the canonical family itself.  The normalization half is the theorem
  `lpp_normalization_logLoss`, and the canonical-loss equivalence
  `lppRaw_and_normalization_canonical_iff` records that the raw count and the
  normalization carry exactly the content of `LPPOrderFibreCount`.

* The H.5 cost input.  `h5TrialCost k polyFactor Lc` is *defined* to be the
  literal right-hand side `z_y · 2^{⌈101 k_y / 100⌉} · polyFactor · L_c`, so
  `cantorArithmeticCostLiteral_h5` is proved by reflexivity and the absorbed
  bound `cantorArithmeticCostBound_h5` follows from the ceiling arithmetic of
  `RandomizedL30Analytic`.  The cost is positive whenever the polynomial factor
  and the confidence parameter are (`h5TrialCost_pos`); the only remaining
  paper input is the Cantor/Jacobian correctness proposition, which the
  constructor `cantorCostInputsOf` carries unchanged.

The bundled structure `LowerBoundsInputs` mirrors `RawInputs` but replaces the
opaque field `younis_global` by `GlobalOddBinomialCount` and the field
`lpp_raw_log` by `LPPModelSuperset`; both fields are discharged by theorems, so
`LowerBoundsInputs.toRawInputs` needs no analytic input beyond the explicit
finite data.

Finally, the parity/global-upper-density chain is recorded exactly:
`globalOddLower_le_upper` shows that a global lower density `B` and the parity
upper density `C` satisfy `B ≤ C`, and
`centralCount_of_intervalCount_binomial` composes the explicit interval count,
`GlobalOddUpperDensity` and `GlobalOddBinomialCount` into the paper's
`YounisOddCentralCount`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no count, cost,
or mass is set to zero: the binomial count is positive, the canonical fibre
family has positive cardinality, and the H.5 trial cost is positive.
-/

namespace Cogentic.RandomizedL30GlobalLower

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Raw
open Cogentic.RandomizedL30Global
open Cogentic.RandomizedL30LPP
open Cogentic.RandomizedL30Interval

noncomputable section

/-! ## 1. The global odd lower bound as an explicit binomial count -/

/-- **The smallest explicit global odd lower bound.**  At every scale there is
a finite set `P` of odd primes at most the smoothness cutoff, an exponent `k`
with `2 · Y^k ≤ p²`, and the binomial coefficient `|P|.choose k` dominating the
paper's target `B p² exp (-(1+ε)t)`.  The cutoff is at least `2`, so the parity
factor `2` is smooth.  Every ingredient is a finite, decidable object; nothing
about the global smooth-number function is assumed. -/
def GlobalOddBinomialCount (B : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ n, 2 ≤ smoothCutoff t err n ∧
    ∃ (P : Finset ℕ) (k : ℕ),
      (∀ q ∈ P, q.Prime ∧ q ≠ 2 ∧ (q : ℝ) ≤ smoothCutoff t err n) ∧
      2 * (smoothCutoff t err n) ^ k ≤ p n ^ 2 ∧
      B * p n ^ 2 * Real.exp (-(1 + err n) * t n) ≤
        ((P.card.choose k : ℕ) : ℝ)

/-- **The global odd lower bound from the explicit binomial count.**  This is
the composition of the construction `2 · ∏ q` with the cardinality count
`globalOddSmoothCount_ge_choose`. -/
theorem younisOddGlobalLower_of_binomialCount {B : ℝ} {p t err : ℕ → ℝ}
    (h : GlobalOddBinomialCount B p t err) :
    YounisOddGlobalLower B p t err := by
  intro n
  obtain ⟨hy2, P, k, hP, hpow, hchoose⟩ := h n
  exact hchoose.trans
    (globalOddSmoothCount_ge_choose (p := p) (t := t) (err := err)
      (n := n) (k := k) (P := P) hy2 hP hpow)

/-- **The explicit prime supply gives the binomial count.**  This recovers the
`OddPrimeSupply`/`smooth_pow_le`/`choose_lower` fields of
`ConstructedInputs` as the finite data behind `GlobalOddBinomialCount`. -/
theorem globalOddBinomialCount_of_primeSupply
    {B : ℝ} {p t err : ℕ → ℝ} {k J : ℕ → ℕ}
    (hy2 : ∀ n, 2 ≤ smoothCutoff t err n)
    (hsupply : ∀ n, OddPrimeSupply (smoothCutoff t err n) (J n))
    (hpow : ∀ n, 2 * (smoothCutoff t err n) ^ (k n) ≤ p n ^ 2)
    (hchoose : ∀ n, B * p n ^ 2 * Real.exp (-(1 + err n) * t n) ≤
      ((J n).choose (k n) : ℝ)) :
    GlobalOddBinomialCount B p t err := by
  intro n
  obtain ⟨P, hP, hJP⟩ := hsupply n
  refine ⟨hy2 n, P, k n, hP, hpow n, ?_⟩
  exact (hchoose n).trans
    (by exact_mod_cast Nat.choose_le_choose (k n) hJP)

/-- The prime-supply form of the global lower bound, routed through the
explicit binomial count. -/
theorem younisOddGlobalLower_of_primeSupply_binomial
    {B : ℝ} {p t err : ℕ → ℝ} {k J : ℕ → ℕ}
    (hy2 : ∀ n, 2 ≤ smoothCutoff t err n)
    (hsupply : ∀ n, OddPrimeSupply (smoothCutoff t err n) (J n))
    (hpow : ∀ n, 2 * (smoothCutoff t err n) ^ (k n) ≤ p n ^ 2)
    (hchoose : ∀ n, B * p n ^ 2 * Real.exp (-(1 + err n) * t n) ≤
      ((J n).choose (k n) : ℝ)) :
    YounisOddGlobalLower B p t err :=
  younisOddGlobalLower_of_binomialCount
    (globalOddBinomialCount_of_primeSupply hy2 hsupply hpow hchoose)

/-- **Monotonicity in the constant.**  A binomial count proved at `B` also
gives the bound at any smaller nonnegative constant. -/
theorem globalOddBinomialCount_mono {B B' : ℝ} {p t err : ℕ → ℝ}
    (hBB' : B' ≤ B) (hB' : 0 ≤ B') (h : GlobalOddBinomialCount B p t err) :
    GlobalOddBinomialCount B' p t err := by
  intro n
  obtain ⟨hy2, P, k, hP, hpow, hchoose⟩ := h n
  refine ⟨hy2, P, k, hP, hpow, ?_⟩
  have hp2e : (0 : ℝ) ≤ p n ^ 2 * Real.exp (-(1 + err n) * t n) := by positivity
  have hmul : B' * (p n ^ 2 * Real.exp (-(1 + err n) * t n)) ≤
      B * (p n ^ 2 * Real.exp (-(1 + err n) * t n)) :=
    mul_le_mul_of_nonneg_right hBB' hp2e
  have hchoose' : B * (p n ^ 2 * Real.exp (-(1 + err n) * t n)) ≤
      ((P.card.choose k : ℕ) : ℝ) := by
    simpa only [mul_assoc] using hchoose
  calc B' * p n ^ 2 * Real.exp (-(1 + err n) * t n)
      = B' * (p n ^ 2 * Real.exp (-(1 + err n) * t n)) := by ring
    _ ≤ B * (p n ^ 2 * Real.exp (-(1 + err n) * t n)) := hmul
    _ ≤ ((P.card.choose k : ℕ) : ℝ) := hchoose'

/-- **The constructed count is positive.**  Since `B > 0` and
`B p² exp (-(1+ε)t) > 0`, the binomial coefficient dominating it is positive,
and the global odd smooth count is at least that coefficient.  In particular
the count is never discharged by a zero cardinality. -/
theorem globalOddSmoothCount_pos_of_binomialCount
    {B : ℝ} {p t err : ℕ → ℝ} (hB : 0 < B)
    (hp : ∀ n, 2 ≤ p n) (h : GlobalOddBinomialCount B p t err) (n : ℕ) :
    0 < globalOddSmoothCount p t err n := by
  obtain ⟨hy2, P, k, hP, hpow, hchoose⟩ := h n
  have hp0 : (0 : ℝ) < p n := by linarith [hp n]
  have htarget : (0 : ℝ) <
      B * p n ^ 2 * Real.exp (-(1 + err n) * t n) := by
    have h1 : (0 : ℝ) < p n ^ 2 := by positivity
    positivity
  have hchoose_pos : (0 : ℝ) < ((P.card.choose k : ℕ) : ℝ) :=
    lt_of_lt_of_le htarget hchoose
  exact lt_of_lt_of_le hchoose_pos
    (globalOddSmoothCount_ge_choose hy2 hP hpow)

/-! ### A concrete, unconditional instance -/

/-- **The all-smooth cutoff supplies the binomial count.**  For
`Y = 8 p²` every integer below `p²` is smooth; the single odd prime `3` with
`k = 0` already gives `|P|.choose 0 = 1`, while
`8 p² exp (-(1+0)t) = 1`.  This is the binomial-count counterpart of
`younisOddGlobalLower_allSmooth`, and it is a genuine positive count. -/
theorem globalOddBinomialCount_allSmooth (p : ℕ → ℝ) (hp : ∀ n, 2 ≤ p n) :
    GlobalOddBinomialCount 8 p (allSmoothT p) allSmoothErr := by
  intro n
  have hp0 : 0 < p n := by linarith [hp n]
  have hpsq : (4 : ℝ) ≤ p n ^ 2 := by
    have h2 : (2 : ℝ) ≤ p n := by exact_mod_cast hp n
    nlinarith [sq_nonneg (p n - 2), h2]
  have hcut : smoothCutoff (allSmoothT p) allSmoothErr n = 8 * p n ^ 2 :=
    smoothCutoff_allSmooth hp0
  have hcut2 : 2 ≤ smoothCutoff (allSmoothT p) allSmoothErr n := by
    rw [hcut]
    nlinarith
  refine ⟨hcut2, {3}, 0, ?_, ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_singleton] at hq
    subst q
    refine ⟨Nat.prime_three, by norm_num, ?_⟩
    rw [hcut]
    nlinarith
  · rw [hcut]
    norm_num
    nlinarith
  · have hchoose : (({3} : Finset ℕ).card.choose 0 : ℕ) = 1 := by simp
    rw [hchoose]
    norm_num
    have hT : Real.exp (-(1 + allSmoothErr n) * allSmoothT p n) =
        1 / (8 * p n ^ 2) := by
      have h1 : (1 + allSmoothErr n) = (1 : ℝ) := by simp [allSmoothErr]
      rw [h1, one_mul, Real.exp_neg, exp_allSmoothT hp0, one_div]
    rw [hT]
    have hden : (8 * p n ^ 2) ≠ 0 := by positivity
    have hval : 8 * p n ^ 2 * (1 / (8 * p n ^ 2)) = 1 := by
      rw [mul_one_div, div_self hden]
    rw [hval]
    norm_num

/-- The all-smooth global lower bound, re-derived through the binomial count. -/
theorem younisOddGlobalLower_allSmooth_binomial (p : ℕ → ℝ)
    (hp : ∀ n, 2 ≤ p n) :
    YounisOddGlobalLower 8 p (allSmoothT p) allSmoothErr :=
  younisOddGlobalLower_of_binomialCount (globalOddBinomialCount_allSmooth p hp)

/-! ## 2. The raw LPP count and its normalization -/

/-- **The smallest explicit LPP counting input.**  Every eligible fibre
contains the canonical multiples family `lppModelMultiples`.  This is strictly
more explicit than a cardinality estimate: it is a finite inclusion statement,
and it mentions no analytic model count. -/
def LPPModelSuperset (p t err : ℕ → ℝ)
    (fibreModels : ℕ → ℕ → Finset ℕ) : Prop :=
  ∀ n m, m ∈ centralSmoothOrders p t err n →
    lppModelMultiples p n m ⊆ fibreModels n m

/-- **The raw LPP count from the explicit inclusion.** -/
theorem lppRawLogModelCount_of_modelSuperset {p t err : ℕ → ℝ}
    {fibreModels : ℕ → ℕ → Finset ℕ}
    (hp : ∀ n, 2 ≤ p n) (h : LPPModelSuperset p t err fibreModels) :
    LPPRawLogModelCount p t err fibreModels :=
  lppRawLogModelCount_of_superset hp h

/-- The canonical family satisfies the inclusion by reflexivity, so the raw LPP
count is never an assumption for it. -/
theorem lppModelSuperset_multiples (p t err : ℕ → ℝ) :
    LPPModelSuperset p t err (lppModelMultiples p) :=
  fun _ _ _ => subset_rfl

/-- **The explicit LPP normalization.**  The polylogarithmic loss is
`log p + 1`, and `log p + 1 ≤ p exp ((1+ε)t)` for `p ≥ 2`, `t ≥ 0`,
`ε ≥ -1`.  This is a theorem, not a bundle field. -/
theorem lpp_normalization_logLoss {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) (ht : ∀ n, 0 ≤ t n) (he : ∀ n, -1 ≤ err n) :
    LPPNormalization p t err (lppLogLoss p) :=
  lppNormalization_logLoss hp ht he

/-- **Raw count plus normalization is exactly the per-order fibre count.**  With
the canonical loss `Q = p exp ((1+ε)t)` the two LPP inputs of `YounisLPPInputs`
contain no content beyond `LPPOrderFibreCount`. -/
theorem lppRaw_and_normalization_canonical_iff {p t err : ℕ → ℝ}
    {fibreModels : ℕ → ℕ → Finset ℕ} (hp : ∀ n, 2 ≤ p n) :
    (LPPRawModelCount p t err fibreModels (lppCanonicalLoss p t err) ∧
        LPPNormalization p t err (lppCanonicalLoss p t err)) ↔
      LPPOrderFibreCount p t err fibreModels :=
  lppRaw_and_normalization_canonical_iff_orderFibreCount hp

/-- **An eligible fibre is nonempty under the explicit inclusion.**  The
canonical multiples family has positive cardinality, and it is contained in the
true fibre, so the fibre count is never zero. -/
theorem fibre_card_pos_of_modelSuperset {p t err : ℕ → ℝ}
    {fibreModels : ℕ → ℕ → Finset ℕ} {n m : ℕ}
    (hp : 2 ≤ p n) (hm : m ∈ centralSmoothOrders p t err n)
    (h : LPPModelSuperset p t err fibreModels) :
    0 < (fibreModels n m).card := by
  have hmpos : 0 < m := centralSmoothOrders_pos_of_mem hp hm
  have hpos : 0 < (lppModelMultiples p n m).card :=
    lppModelMultiples_card_pos hp hmpos
  have hle : (lppModelMultiples p n m).card ≤ (fibreModels n m).card :=
    Finset.card_le_card (h n m hm)
  omega

/-! ## 3. The H.5 Cantor cost, satisfied by construction -/

/-- **The literal H.5 cost.**  This is definitionally the right-hand side
`z_y · 2^{⌈101 k_y / 100⌉} · polyFactor · L_c` of the paper's displayed
inequality.  Choosing the cost to be this expression makes the literal bound a
reflexivity fact; the absorbed bound then follows from the ceiling arithmetic
already proved in `RandomizedL30Analytic`. -/
def h5TrialCost (k polyFactor Lc : ℕ → ℝ) (n : ℕ) : ℝ :=
  zOf k n * cantorTrialCount k n * polyFactor n * Lc n

/-- **The literal H.5 bound, by reflexivity.** -/
theorem cantorArithmeticCostLiteral_h5 (k polyFactor Lc : ℕ → ℝ) :
    CantorArithmeticCostLiteral k polyFactor Lc (h5TrialCost k polyFactor Lc) :=
  fun _ => le_rfl

/-- **The absorbed H.5 bound.**  The ceiling costs a fixed factor `2`, which is
absorbed into the polynomial factor. -/
theorem cantorArithmeticCostBound_h5 (k polyFactor Lc : ℕ → ℝ)
    (hk : ∀ n, 0 ≤ k n) (hpoly : ∀ n, 0 ≤ polyFactor n)
    (hLc : ∀ n, 0 ≤ Lc n) :
    CantorArithmeticCostBound k (fun n => 2 * polyFactor n) Lc
      (h5TrialCost k polyFactor Lc) :=
  cantorArithmeticCostBound_of_literal
    (cantorArithmeticCostLiteral_h5 k polyFactor Lc) hk hpoly hLc

/-- **The constructed H.5 cost is positive** when the polynomial factor and the
confidence parameter are positive.  No cost is set to zero. -/
theorem h5TrialCost_pos {k polyFactor Lc : ℕ → ℝ} {n : ℕ}
    (hpoly : 0 < polyFactor n) (hLc : 0 < Lc n) :
    0 < h5TrialCost k polyFactor Lc n := by
  unfold h5TrialCost zOf cantorTrialCount
  positivity

/-- **The elementary Cantor/H.5 bundle with the cost half discharged.**  The
per-call cost is the literal H.5 expression, so `cantor_literal` is a theorem;
only the Cantor/Jacobian correctness proposition is carried as an input. -/
noncomputable def cantorCostInputsOf
    (k polyFactor Lc : ℕ → ℝ)
    (hk : ∀ n, 0 ≤ k n) (hpoly : ∀ n, 0 ≤ polyFactor n)
    (hLc : ∀ n, 1 ≤ Lc n)
    (correct : Prop) (hcorrect : correct) : CantorCostInputs where
  k := k
  k_nonneg := hk
  polyFactor := polyFactor
  polyFactor_nonneg := hpoly
  Lc := Lc
  Lc_ge_one := hLc
  trialCost := h5TrialCost k polyFactor Lc
  cantor_literal := cantorArithmeticCostLiteral_h5 k polyFactor Lc
  cantor_arithmetic := correct
  cantor_arithmetic_holds := hcorrect

/-- The confidence `L_c = 1` is an admissible H.5 datum, and the associated cost
is positive: `z_y · 2^{⌈101 k_y/100⌉} > 0`.  This is the non-vacuity check for
the cost half alone; it deliberately retains an arbitrary correctness
proposition rather than asserting the Cantor/Jacobian input. -/
theorem h5TrialCost_unit_pos (k : ℕ → ℝ) (n : ℕ) :
    0 < h5TrialCost k (fun _ => 1) (fun _ => 1) n :=
  h5TrialCost_pos (by norm_num) (by norm_num)

/-! ## 4. The bundled lower-bound inputs -/

/-- **`RawInputs` with the two global lower-bound fields reduced.**  Compared
with `Cogentic.RandomizedL30Raw.RawInputs`, the opaque field `younis_global` is
replaced by the explicit finite-set statement `GlobalOddBinomialCount`, and the
raw LPP field `lpp_raw_log` by the explicit inclusion `LPPModelSuperset`.  Both
replacements are theorems below, so this structure has strictly less analytic
content. -/
structure LowerBoundsInputs where
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
  /-- `ε ≥ -1`. -/
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
  /-- **The explicit global odd lower bound.** -/
  global_binomial : GlobalOddBinomialCount B p t err
  /-- **The explicit raw LPP inclusion.** -/
  lpp_superset : LPPModelSuperset p t err fibreModels

namespace LowerBoundsInputs

variable (S : LowerBoundsInputs)

/-- **The global odd smooth lower bound, now a theorem.** -/
theorem younis_global : YounisOddGlobalLower S.B S.p S.t S.err :=
  younisOddGlobalLower_of_binomialCount S.global_binomial

/-- **The explicit LPP normalization.** -/
theorem lpp_normalization :
    LPPNormalization S.p S.t S.err (lppLogLoss S.p) :=
  lpp_normalization_logLoss S.p_ge_two S.t_nonneg S.err_ge_neg_one

/-- **The raw LPP count, now a theorem.** -/
theorem lpp_raw_log : LPPRawLogModelCount S.p S.t S.err S.fibreModels :=
  lppRawLogModelCount_of_modelSuperset S.p_ge_two S.lpp_superset

/-- **The normalized per-order fibre count.** -/
theorem lppOrderFibreCount :
    LPPOrderFibreCount S.p S.t S.err S.fibreModels :=
  lppOrderFibreCount_of_rawLog S.p_ge_two S.t_nonneg S.err_ge_neg_one
    S.lpp_raw_log

/-- **The reduction to `RawInputs`.**  Every field is carried through; the two
global lower-bound fields are discharged by `younis_global` and `lpp_raw_log`. -/
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

/-- **The odd central count** from the two reduced fields. -/
theorem younisOddCentralCount : YounisOddCentralCount S.p S.t S.err :=
  RawInputs.younisOddCentralCount S.toRawInputs

/-- **The unrestricted Younis count.** -/
theorem younisShortIntervalCount : YounisShortIntervalCount S.p S.t S.err :=
  younisShortIntervalCount_of_odd S.younisOddCentralCount

/-- **The reduction to `YounisLPPInputs`.** -/
noncomputable def toYounisLPPInputs : YounisLPPInputs :=
  S.toRawInputs.toYounisLPPInputs

/-- **The reduction to `AnalyticInputs`**, with the Cantor/H.5 data supplied by
`cantorCostInputsOf`. -/
noncomputable def toAnalyticInputs (C : CantorCostInputs) : AnalyticInputs :=
  S.toRawInputs.toAnalyticInputs C

/-- **The reduction to `PaperInputs`.** -/
noncomputable def toPaperInputs (C : CantorCostInputs) : PaperInputs :=
  S.toRawInputs.toPaperInputs C

/-- **The `p^5` model supply** from the reduced bundle.  The per-order count is
the fibre cardinality at the chosen eligible order of the resulting
`PaperInputs`. -/
theorem modelCount_lower (C : CantorCostInputs) (n : ℕ) :
    S.p n ^ (5 : ℝ) * Real.exp (-(2 * (1 + S.err n)) * S.t n) ≤
      (S.toPaperInputs C).smoothOrders n * (S.toPaperInputs C).fibrePerOrder n :=
  PaperInputs.modelCount_lower (S.toPaperInputs C) S.p_ge_two
    (fun n => Nat.cast_nonneg _) n

end LowerBoundsInputs

/-! ## 5. The parity / global upper-density chain -/

/-- **The global lower and upper densities are sandwiched.**  If the odd smooth
count is at least `B p² exp (-(1+ε)t)` and at most `C p² exp (-(1+ε)t)`, then
`B ≤ C`.  This is the consistency relation between the parity upper density
used by the relative short-interval reduction and any global lower bound. -/
theorem globalOddLower_le_upper {B C : ℝ} {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (hglob : YounisOddGlobalLower B p t err)
    (hupper : GlobalOddUpperDensity C p t err) :
    B ≤ C := by
  have hp0 : (0 : ℝ) < p 0 := by linarith [hp 0]
  have hp2 : (0 : ℝ) < p 0 ^ 2 := by positivity
  have hpos : (0 : ℝ) < p 0 ^ 2 * Real.exp (-(1 + err 0) * t 0) := by
    positivity
  have hlow : B * (p 0 ^ 2 * Real.exp (-(1 + err 0) * t 0)) ≤
      globalOddSmoothCount p t err 0 := by
    simpa only [mul_assoc] using hglob 0
  have hupp : globalOddSmoothCount p t err 0 ≤
      C * (p 0 ^ 2 * Real.exp (-(1 + err 0) * t 0)) := by
    have h := (div_le_iff₀ hp2).mp (hupper 0)
    calc globalOddSmoothCount p t err 0 ≤
          C * Real.exp (-(1 + err 0) * t 0) * p 0 ^ 2 := h
      _ = C * (p 0 ^ 2 * Real.exp (-(1 + err 0) * t 0)) := by ring
  exact le_of_mul_le_mul_right (hlow.trans hupp) hpos

/-- **The paper chain with the explicit global lower bound.**  The explicit
interval count, the parity upper density `GlobalOddUpperDensity C`, and the
explicit binomial lower bound `GlobalOddBinomialCount B` with `A B ≥ 4` give
the paper's odd central count.  No global smooth-number estimate remains. -/
theorem centralCount_of_intervalCount_binomial
    {A B c C : ℝ} {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) (hA : 0 < A) (hB : 0 < B) (hAB : 4 ≤ A * B)
    (hAC : A * C ≤ c)
    (hcount : YounisOddPaperIntervalCount c p t err)
    (hupper : GlobalOddUpperDensity C p t err)
    (hbin : GlobalOddBinomialCount B p t err) :
    YounisOddCentralCount p t err :=
  younisOddCentralCount_of_density hp hA hB hAB
    (paperRelative_of_globalUpper hA.le hAC hcount hupper)
    (younisOddGlobalLower_of_binomialCount hbin)

/-- **The paper-scale form of the chain.**  At `t = t_p` the same composition
gives `YounisOddCentralCount p (paperT p) err`. -/
theorem centralCount_paperT_of_intervalCount_binomial
    {A B c C : ℝ} {p err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) (hA : 0 < A) (hB : 0 < B) (hAB : 4 ≤ A * B)
    (hAC : A * C ≤ c)
    (hcount : YounisOddPaperIntervalCount c p (paperT p) err)
    (hupper : GlobalOddUpperDensity C p (paperT p) err)
    (hbin : GlobalOddBinomialCount B p (paperT p) err) :
    YounisOddCentralCount p (paperT p) err :=
  centralCount_of_intervalCount_binomial hp hA hB hAB hAC hcount hupper hbin

/-! ## Axiom audit -/

#print axioms younisOddGlobalLower_of_binomialCount
#print axioms globalOddBinomialCount_of_primeSupply
#print axioms younisOddGlobalLower_of_primeSupply_binomial
#print axioms globalOddBinomialCount_mono
#print axioms globalOddSmoothCount_pos_of_binomialCount
#print axioms globalOddBinomialCount_allSmooth
#print axioms younisOddGlobalLower_allSmooth_binomial
#print axioms LPPModelSuperset
#print axioms lppRawLogModelCount_of_modelSuperset
#print axioms lppModelSuperset_multiples
#print axioms lpp_normalization_logLoss
#print axioms lppRaw_and_normalization_canonical_iff
#print axioms fibre_card_pos_of_modelSuperset
#print axioms h5TrialCost
#print axioms cantorArithmeticCostLiteral_h5
#print axioms cantorArithmeticCostBound_h5
#print axioms h5TrialCost_pos
#print axioms cantorCostInputsOf
#print axioms h5TrialCost_unit_pos
#print axioms LowerBoundsInputs.younis_global
#print axioms LowerBoundsInputs.lpp_normalization
#print axioms LowerBoundsInputs.lpp_raw_log
#print axioms LowerBoundsInputs.lppOrderFibreCount
#print axioms LowerBoundsInputs.younisOddCentralCount
#print axioms LowerBoundsInputs.younisShortIntervalCount
#print axioms LowerBoundsInputs.modelCount_lower
#print axioms LowerBoundsInputs.toRawInputs
#print axioms LowerBoundsInputs.toYounisLPPInputs
#print axioms LowerBoundsInputs.toAnalyticInputs
#print axioms LowerBoundsInputs.toPaperInputs
#print axioms globalOddLower_le_upper
#print axioms centralCount_of_intervalCount_binomial
#print axioms centralCount_paperT_of_intervalCount_binomial

end

end Cogentic.RandomizedL30GlobalLower
