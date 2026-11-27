import Cogentic.RandomizedPaperLeafStatements
import Cogentic.RandomizedPrimeBinSupply

/-!
# L18.4: rational-good environments at the shrunken denominator interval

The manuscript's L18.4 (blueprint §2 C5.a `[INFRA]`, KeyBreak Lemma G.3 p.107,
`research/keybreak-balanced-ideal-pair-audit.md` §Denominator) is the analytic
input that makes the field-pool first moment run on a *rational-good* environment
after the denominator interval has been shrunk to the narrower scale

`b ∈ (2V/3, (2V/3)(1 + 1/d)]`.

The paper proves a deficit `D^{-B}` for every `B`.  This file decomposes that
statement into three explicit estimates and proves the `SubexpLeaf` from them.

## The three estimates

1. **Large sieve / second moment** (`large_sieve`).  Summed over the `K`
   denominator cells, the second moment of the numerator counts is at most
   `C · (M V²) · (E_conv / d)`: the upper support length is `O(M V²)`, the bound is
   linear in the multiplicity-one convolution energy `E_conv`, and restricting to
   the shrunken interval divides the energy by the order `d`.

2. **RH prime counts in the denominator cells** (`cell_prime_count`,
   `cell_numerator_count`).  The shrunken interval is cut into `K = V^{1/4}`
   comparable cells.  Under RH each cell contains at least
   `V / (2 d K log V)` denominators, obtained by subtracting the two prime
   counting prefixes; the condition `d K log² V = o(√V)` makes the prime-counting
   error negligible relative to the cell width.  On a root-`ℓ` progression a
   denominator carries at least `V ρ / (2 ℓ)` numerator points.  The product is
   the cell mean `V² ρ / (4 d K ℓ log V)`, and the total mean is
   `V² ρ / (4 d ℓ log V)`.

3. **Rational-good cell partition and energy loss** (`thin_pair_fraction`).  A
   determinant strip `|det| ≪ V²/K` meets `O(1)` numerator cells inside each
   denominator cell and `O(K)` cell pairs in all, so the relative thin-pair
   fraction is `O(1/K)`.  The `K` factor in the deficit `K · (S2/μ²)` is the union
   bound over the `K` relative cell thresholds; dividing the variance by the new
   squared mean loses exactly one factor `d`, which cancels the `1/d` energy
   division and leaves the single factor `d` in `coeff`.

## The arithmetic reduction

`log V = D^{O(1)}` while `log D = scale n`, so `W = log V` dominates every fixed
multiple of `scale n` (`W_dominates`), and the remaining factors are `D^{O(1)}`
(`W_upper`, `C_upper`, …, `rho_inv_upper`).  Hence the deficit
`K · (S2/μ²) + thin` is `D^{-B}` for every `B`: the mesh `K = V^{1/4}` makes both
`1/K` and the `K/V²` factor super-polynomially small.

Nothing here is a `sorry`, an `axiom`, or `native_decide`, and the loss is not set
to zero: `loss n = K n * (S2 n / μ n ^ 2) + thin n` with all three terms explicit.

The reusable `[LEAN]` input is the RH prime-bin supply of
`RandomizedPrimeBinSupply` (`cell_card_lower_of_primeBinSupply`,
`cell_card_lower_from_critical_line`).  The C5.a pool union bound in
`RandomizedEpochPool` bounds the probability that a pool of independent draws
misses a retained prime; it is the neighbouring assembly step, not the
deterministic rational exception bounded here, so it is not consumed by this
reduction.
-/

namespace Cogentic.RandomizedL18_4

open Filter Real
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedOneThirdAsymptotic
open scoped BigOperators

/-- The denominator scale `V = exp (log V)`. -/
noncomputable def denomScale (W : ℕ → ℝ) (n : ℕ) : ℝ := exp (W n)

/-- The cell mesh `K = V^{1/4}`: the number of comparable denominator cells. -/
noncomputable def cellMesh (W : ℕ → ℝ) (n : ℕ) : ℝ := exp (W n / 4)

/-! ## The decomposed L18.4 inputs -/

/-- The three paper-level estimates behind L18.4, together with the explicit
scales and the `D^{O(1)}` bookkeeping needed to turn them into `D^{-B}`.

The fields `large_sieve`, `cell_prime_count`, `cell_numerator_count` and
`thin_pair_fraction` are the analytic content of KB G.3 p.107; see the module
docstring for their exact reading.  They are hypotheses: the manuscript proves
them, and this file proves that they imply the C5 L18.4 slot. -/
structure L18_4Inputs where
  /-- Logarithmic denominator scale `W = log V`. -/
  W : ℕ → ℝ
  /-- Field degree `d`. -/
  d : ℕ → ℝ
  /-- Root index `ℓ` on the numerator progression. -/
  ell : ℕ → ℝ
  /-- Reference density `ρ` of the numerator progression. -/
  rho : ℕ → ℝ
  /-- Large-sieve constant. -/
  C : ℕ → ℝ
  /-- Upper support factor: the support length is `O (M V²)`. -/
  M : ℕ → ℝ
  /-- Undivided multiplicity-one convolution energy `E_conv`. -/
  Econv : ℕ → ℝ
  /-- Summed second moment of the numerator counts over the `K` cells. -/
  S2 : ℕ → ℝ
  /-- Minimum number of denominators in a cell (RH cell count). -/
  Ncell : ℕ → ℝ
  /-- Minimum number of numerator points per denominator on a root-`ℓ` progression. -/
  Nnum : ℕ → ℝ
  /-- The relative thin / small-determinant pair fraction. -/
  thin : ℕ → ℝ
  /-- Exponent in `log V = D^{cW}`. -/
  cW : ℝ
  /-- Exponent in the large-sieve constant `C = D^{cC}`. -/
  cC : ℝ
  /-- Exponent in the support factor `M = D^{cM}`. -/
  cM : ℝ
  /-- Exponent in the undivided energy `E_conv = D^{cE}`. -/
  cE : ℝ
  /-- Exponent in the field degree `d = D^{cd}`. -/
  cd : ℝ
  /-- Exponent in the root index `ℓ = D^{cell}`. -/
  cell : ℝ
  /-- Exponent in the reciprocal density `1/ρ = D^{cρ}`. -/
  cρ : ℝ
  /-- `log V` is nonnegative. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- The field degree is positive. -/
  d_pos : ∀ n, 0 < d n
  /-- The root index is positive. -/
  ell_pos : ∀ n, 0 < ell n
  /-- The reference density is positive. -/
  rho_pos : ∀ n, 0 < rho n
  /-- The large-sieve constant is positive. -/
  C_pos : ∀ n, 0 < C n
  /-- The support factor is positive. -/
  M_pos : ∀ n, 0 < M n
  /-- The undivided convolution energy is nonnegative. -/
  Econv_nonneg : ∀ n, 0 ≤ Econv n
  /-- The summed second moment is nonnegative. -/
  S2_nonneg : ∀ n, 0 ≤ S2 n
  /-- The cell denominator count is nonnegative. -/
  Ncell_nonneg : ∀ n, 0 ≤ Ncell n
  /-- The numerator count is nonnegative. -/
  Nnum_nonneg : ∀ n, 0 ≤ Nnum n
  /-- The thin-pair fraction is nonnegative. -/
  thin_nonneg : ∀ n, 0 ≤ thin n
  /-- The `log V` exponent is nonnegative. -/
  cW_nonneg : 0 ≤ cW
  /-- The large-sieve exponent is nonnegative. -/
  cC_nonneg : 0 ≤ cC
  /-- The support exponent is nonnegative. -/
  cM_nonneg : 0 ≤ cM
  /-- The energy exponent is nonnegative. -/
  cE_nonneg : 0 ≤ cE
  /-- The degree exponent is nonnegative. -/
  cd_nonneg : 0 ≤ cd
  /-- The root-index exponent is nonnegative. -/
  cell_nonneg : 0 ≤ cell
  /-- The reciprocal-density exponent is nonnegative. -/
  cρ_nonneg : 0 ≤ cρ
  /-- **Large sieve / second moment** (KB G.3 p.107, `[INFRA]`).  Summed over the
  `K` denominator cells, the second moment of the numerator counts is at most
  `C · (M V²) · (E_conv / d)`: the upper support length `O(M V²)`, linearity in
  the multiplicity-one convolution energy, and the `1/d` energy division caused by
  the shrunken denominator interval. -/
  large_sieve : ∀ n,
    S2 n ≤ C n * (M n * denomScale W n ^ 2) * (Econv n / d n)
  /-- **RH prime counts in the denominator cells** (KB G.3 p.107).  Under RH the
  prime-counting error is `o` of the cell width because `d K log² V = o(√V)`, so
  each of the `K` comparable cells contains at least `V / (2 d K log V)`
  denominators. -/
  cell_prime_count : ∀ n,
    denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤ Ncell n
  /-- **RH numerator count on a root-`ℓ` progression** (KB G.3 p.107, G.4).  Each
  denominator in a cell contributes at least `V ρ / (2 ℓ)` numerator points on the
  root-`ℓ` progression. -/
  cell_numerator_count : ∀ n,
    denomScale W n * rho n / (2 * ell n) ≤ Nnum n
  /-- **Rational-good cell partition / thin pairs** (KB G.3 p.107, G.15).
  A determinant strip `|det| ≪ V²/K` meets `O(1)` numerator cells inside each
  denominator cell and `O(K)` cell pairs in all; after normalization by the new
  mean the relative thin-pair fraction is at most `1/K`. -/
  thin_pair_fraction : ∀ n, thin n ≤ 1 / cellMesh W n
  /-- `log V = D^{O(1)}`: an upper bound with the explicit exponent `cW`. -/
  W_upper : ∀ n, W n ≤ exp (cW * scale n)
  /-- `C = D^{O(1)}`. -/
  C_upper : ∀ n, C n ≤ exp (cC * scale n)
  /-- `M = D^{O(1)}`. -/
  M_upper : ∀ n, M n ≤ exp (cM * scale n)
  /-- `E_conv = D^{O(1)}`. -/
  Econv_upper : ∀ n, Econv n ≤ exp (cE * scale n)
  /-- `d = D^{O(1)}`. -/
  d_upper : ∀ n, d n ≤ exp (cd * scale n)
  /-- `ℓ = D^{O(1)}`. -/
  ell_upper : ∀ n, ell n ≤ exp (cell * scale n)
  /-- `1/ρ = D^{O(1)}`, i.e. `ρ ≥ D^{-O(1)}`. -/
  rho_inv_upper : ∀ n, 1 / rho n ≤ exp (cρ * scale n)
  /-- `log V` dominates every fixed multiple of `log D = scale n`.  This is the
  content of `log V = D^{O(1)}` with `D = exp (scale n)`: `exp (Ω (scale n))`
  beats `c · scale n` for every fixed `c`.  It is a growth-rate fact, not the
  L18.4 conclusion. -/
  W_dominates : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, c * scale n ≤ W n

namespace L18_4Inputs

variable (I : L18_4Inputs)

/-- The denominator scale `V = exp W`. -/
noncomputable def V (n : ℕ) : ℝ := denomScale I.W n

/-- The cell mesh `K = exp (W/4) = V^{1/4}`. -/
noncomputable def K (n : ℕ) : ℝ := cellMesh I.W n

/-- The per-cell mean `N_den · N_num`. -/
noncomputable def muCell (n : ℕ) : ℝ := I.Ncell n * I.Nnum n

/-- The total mean over the `K` cells. -/
noncomputable def mu (n : ℕ) : ℝ := I.K n * I.muCell n

/-- The deterministic reference mean `V² ρ / (4 d ℓ log V)` obtained from the RH
cell counts. -/
noncomputable def muRef (n : ℕ) : ℝ :=
  I.V n ^ 2 * I.rho n / (4 * I.d n * I.ell n * (1 + I.W n))

/-- The `D^{O(1)}` coefficient left after the large sieve and the energy division:
`16 C M E_conv d ℓ² / ρ²`.  The single factor `d` is the energy loss of the
shrunken denominator interval. -/
noncomputable def coeff (n : ℕ) : ℝ :=
  16 * I.C n * I.M n * I.Econv n * I.d n * I.ell n ^ 2 / I.rho n ^ 2

/-- The combined `D^{O(1)}` exponent of `coeff · (1 + log V)²`. -/
noncomputable def csum : ℝ :=
  Real.log 16 + I.cC + I.cM + I.cE + I.cd + 2 * I.cell + 2 * I.cρ +
    (1 + 2 * I.cW)

/-- The rational-good deficit contributed by the `K` cell thresholds:
`K · (S2 / μ²)`, the union bound over the cell partition. -/
noncomputable def cellDeficit (n : ℕ) : ℝ := I.K n * (I.S2 n / I.mu n ^ 2)

/-- The L18.4 rational exception: the cell second-moment deficit plus the relative
thin-pair fraction.  This is the deficit charged to the C5 slot
`C5Leaf.rationalGoodEnvironments`. -/
noncomputable def loss (n : ℕ) : ℝ := I.cellDeficit n + I.thin n

theorem V_pos (n : ℕ) : 0 < I.V n := by
  unfold V denomScale
  exact exp_pos _

theorem K_pos (n : ℕ) : 0 < I.K n := by
  unfold K cellMesh
  exact exp_pos _

theorem muRef_pos (n : ℕ) : 0 < I.muRef n := by
  have hV : 0 < I.V n := I.V_pos n
  have hrho : 0 < I.rho n := I.rho_pos n
  have hd : 0 < I.d n := I.d_pos n
  have hell : 0 < I.ell n := I.ell_pos n
  have h1W : 0 < 1 + I.W n := by linarith [I.W_nonneg n]
  unfold muRef
  positivity

theorem csum_pos : 0 < I.csum := by
  unfold csum
  have h16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have h1W : 0 ≤ 1 + 2 * I.cW := by linarith [I.cW_nonneg]
  nlinarith only [h16, h1W, I.cC_nonneg, I.cM_nonneg, I.cE_nonneg, I.cd_nonneg,
    I.cell_nonneg, I.cρ_nonneg]

/-- The product of the two RH cell counts gives the cell mean
`V² ρ / (4 d K ℓ log V)`. -/
theorem muCell_lower (n : ℕ) :
    I.V n ^ 2 * I.rho n / (4 * I.d n * I.K n * I.ell n * (1 + I.W n)) ≤
      I.muCell n := by
  have hnum_nn : 0 ≤ denomScale I.W n * I.rho n / (2 * I.ell n) := by
    have hV : 0 < denomScale I.W n := by unfold denomScale; exact exp_pos _
    have hrho : 0 < I.rho n := I.rho_pos n
    have hell : 0 < I.ell n := I.ell_pos n
    positivity
  have hle := mul_le_mul (I.cell_prime_count n) (I.cell_numerator_count n)
    hnum_nn (I.Ncell_nonneg n)
  have hleft :
      (denomScale I.W n / (2 * I.d n * cellMesh I.W n * (1 + I.W n))) *
          (denomScale I.W n * I.rho n / (2 * I.ell n)) =
        denomScale I.W n ^ 2 * I.rho n /
          (4 * I.d n * cellMesh I.W n * I.ell n * (1 + I.W n)) := by
    have hd : (I.d n) ≠ 0 := (I.d_pos n).ne'
    have hK : cellMesh I.W n ≠ 0 := by simpa only [K] using (I.K_pos n).ne'
    have hell : (I.ell n) ≠ 0 := (I.ell_pos n).ne'
    have h1W : (1 + I.W n) ≠ 0 := by linarith [I.W_nonneg n]
    field_simp [hd, hK, hell, h1W]
    ring
  rw [hleft] at hle
  simpa [muCell, V, K] using hle

/-- The total mean is at least `V² ρ / (4 d ℓ log V)`: the cell factor `K`
cancels. -/
theorem mu_lower (n : ℕ) : I.muRef n ≤ I.mu n := by
  have hle := mul_le_mul_of_nonneg_left (I.muCell_lower n) (I.K_pos n).le
  simp only [K, V] at hle
  have hleft :
      cellMesh I.W n * (denomScale I.W n ^ 2 * I.rho n /
          (4 * I.d n * cellMesh I.W n * I.ell n * (1 + I.W n))) =
        denomScale I.W n ^ 2 * I.rho n /
          (4 * I.d n * I.ell n * (1 + I.W n)) := by
    have hd : (I.d n) ≠ 0 := (I.d_pos n).ne'
    have hK : cellMesh I.W n ≠ 0 := by simpa only [K] using (I.K_pos n).ne'
    have hell : (I.ell n) ≠ 0 := (I.ell_pos n).ne'
    have h1W : (1 + I.W n) ≠ 0 := by linarith [I.W_nonneg n]
    field_simp [hd, hK, hell, h1W]
  rw [hleft] at hle
  simpa [mu, muRef, V, K] using hle

theorem mu_pos (n : ℕ) : 0 < I.mu n :=
  (I.muRef_pos n).trans_le (I.mu_lower n)

/-- The multiplicity-one energy bookkeeping: the large sieve is linear in
`E_conv / d`, while dividing the variance by the squared cell mean manufactures a
`d²`.  The two combine to exactly one factor `d` (`E_conv / d · d² = E_conv · d`),
which is the `O(d)` energy loss recorded in
`research/keybreak-balanced-ideal-pair-audit.md` §Denominator. -/
theorem energy_loss_eq (n : ℕ) :
    I.Econv n / I.d n * I.d n ^ 2 = I.Econv n * I.d n := by
  have hd : (I.d n) ≠ 0 := (I.d_pos n).ne'
  field_simp [hd]

/-- The large-sieve bound, the cell mean lower bound and the `1/d` energy loss
give the explicit cell deficit
`coeff · (1 + log V)² · exp (-(7/4) log V)`. -/
theorem cellDeficit_le (n : ℕ) :
    I.cellDeficit n ≤
      I.coeff n * (1 + I.W n) ^ 2 * exp (-(7 / 4 : ℝ) * I.W n) := by
  have hmu := I.mu_lower n
  have hmu0 := I.muRef_pos n
  have hmu_pos : 0 < I.mu n := hmu0.trans_le hmu
  have hratio : I.S2 n / I.mu n ^ 2 ≤ I.S2 n / I.muRef n ^ 2 := by
    refine div_le_div_of_nonneg_left (I.S2_nonneg n) (pow_pos hmu0 2) ?_
    nlinarith only [hmu0, hmu]
  have hsieve := I.large_sieve n
  have hstep : I.S2 n / I.muRef n ^ 2 ≤
      (I.C n * (I.M n * I.V n ^ 2) * (I.Econv n / I.d n)) /
        I.muRef n ^ 2 :=
    div_le_div_of_nonneg_right hsieve (sq_nonneg _)
  have hid :
      (I.C n * (I.M n * I.V n ^ 2) * (I.Econv n / I.d n)) /
          I.muRef n ^ 2 =
        I.coeff n * (1 + I.W n) ^ 2 / I.V n ^ 2 := by
    unfold coeff muRef V denomScale
    have hd : (I.d n) ≠ 0 := (I.d_pos n).ne'
    have hell : (I.ell n) ≠ 0 := (I.ell_pos n).ne'
    have h1W : (1 + I.W n) ≠ 0 := by linarith [I.W_nonneg n]
    have hrho : (I.rho n) ≠ 0 := (I.rho_pos n).ne'
    field_simp [hd, hell, h1W, hrho]
    ring
  have hKV : I.K n / I.V n ^ 2 = exp (-(7 / 4 : ℝ) * I.W n) := by
    have hV2 : I.V n ^ 2 = exp (2 * I.W n) := by
      unfold V denomScale
      rw [pow_two, ← exp_add]
      congr 1
      ring
    rw [K, cellMesh, hV2, ← exp_sub]
    congr 1
    ring
  calc
    I.cellDeficit n = I.K n * (I.S2 n / I.mu n ^ 2) := rfl
    _ ≤ I.K n * (I.coeff n * (1 + I.W n) ^ 2 / I.V n ^ 2) :=
      mul_le_mul_of_nonneg_left (hratio.trans (hstep.trans_eq hid)) (I.K_pos n).le
    _ = I.coeff n * (1 + I.W n) ^ 2 * (I.K n / I.V n ^ 2) := by ring
    _ = I.coeff n * (1 + I.W n) ^ 2 * exp (-(7 / 4 : ℝ) * I.W n) := by rw [hKV]

/-- The deficit is bounded by the cell deficit plus the thin-pair fraction, and
the latter is exactly `exp (-(1/4) log V)`. -/
theorem loss_le (n : ℕ) :
    I.loss n ≤
      I.coeff n * (1 + I.W n) ^ 2 * exp (-(7 / 4 : ℝ) * I.W n) +
        exp (-(1 / 4 : ℝ) * I.W n) := by
  have hthin := I.thin_pair_fraction n
  have hKinv : 1 / I.K n = exp (-(1 / 4 : ℝ) * I.W n) := by
    rw [K, cellMesh, one_div, ← exp_neg]
    congr 1
    ring
  calc
    I.loss n = I.cellDeficit n + I.thin n := rfl
    _ ≤ I.coeff n * (1 + I.W n) ^ 2 * exp (-(7 / 4 : ℝ) * I.W n) + 1 / I.K n :=
      add_le_add (I.cellDeficit_le n) hthin
    _ = I.coeff n * (1 + I.W n) ^ 2 * exp (-(7 / 4 : ℝ) * I.W n) +
          exp (-(1 / 4 : ℝ) * I.W n) := by rw [hKinv]

/-- Absorb the `(1 + log V)²` factor.  Since `log V ≥ 1` and
`log V ≤ D^{cW}`, the product is at most `D^{1 + 2 cW}`. -/
theorem one_add_W_sq_le {n : ℕ} (hW1 : 1 ≤ I.W n) (hH4 : Real.log 4 ≤ scale n) :
    (1 + I.W n) ^ 2 ≤ exp ((1 + 2 * I.cW) * scale n) := by
  have hWpos : 0 < I.W n := lt_of_lt_of_le zero_lt_one hW1
  have hle : 1 + I.W n ≤ 2 * I.W n := by linarith
  have hsq : (1 + I.W n) ^ 2 ≤ (2 * I.W n) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hle 2
  have hWsq : (I.W n) ^ 2 ≤ exp ((2 * I.cW) * scale n) := by
    calc
      (I.W n) ^ 2 ≤ (exp (I.cW * scale n)) ^ 2 :=
        pow_le_pow_left₀ hWpos.le (I.W_upper n) 2
      _ = exp ((2 * I.cW) * scale n) := by
        rw [pow_two, ← exp_add]
        congr 1
        ring
  have h4 : (4 : ℝ) ≤ exp (scale n) := by
    calc
      (4 : ℝ) = exp (Real.log 4) := (exp_log (by norm_num)).symm
      _ ≤ exp (scale n) := exp_le_exp.mpr hH4
  calc
    (1 + I.W n) ^ 2 ≤ (2 * I.W n) ^ 2 := hsq
    _ = 4 * (I.W n) ^ 2 := by ring
    _ ≤ exp (scale n) * exp ((2 * I.cW) * scale n) :=
      mul_le_mul h4 hWsq (sq_nonneg _) (exp_pos _).le
    _ = exp ((1 + 2 * I.cW) * scale n) := by
      rw [← exp_add]
      congr 1
      ring

/-- Each `D^{O(1)}` factor of `coeff` is absorbed into a single exponent. -/
theorem coeff_le_exp (n : ℕ) (hH1 : 1 ≤ scale n) :
    I.coeff n ≤
      exp ((Real.log 16 + I.cC + I.cM + I.cE + I.cd + 2 * I.cell + 2 * I.cρ) *
        scale n) := by
  have hlog16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have h16 : (16 : ℝ) ≤ exp (Real.log 16 * scale n) := by
    calc
      (16 : ℝ) = exp (Real.log 16) := (exp_log (by norm_num)).symm
      _ ≤ exp (Real.log 16 * scale n) := by
        apply exp_le_exp.mpr
        simpa using mul_le_mul_of_nonneg_left hH1 hlog16.le
  have hell2 : I.ell n ^ 2 ≤ exp ((2 * I.cell) * scale n) := by
    calc
      I.ell n ^ 2 ≤ (exp (I.cell * scale n)) ^ 2 :=
        pow_le_pow_left₀ (I.ell_pos n).le (I.ell_upper n) 2
      _ = exp ((2 * I.cell) * scale n) := by
        rw [pow_two, ← exp_add]
        congr 1
        ring
  have hrho2 : 1 / I.rho n ^ 2 ≤ exp ((2 * I.cρ) * scale n) := by
    have hsq := mul_le_mul (I.rho_inv_upper n) (I.rho_inv_upper n)
      (div_nonneg zero_le_one (I.rho_pos n).le) (exp_pos _).le
    calc
      1 / I.rho n ^ 2 = (1 / I.rho n) * (1 / I.rho n) := by
        have hrho : (I.rho n) ≠ 0 := (I.rho_pos n).ne'
        field_simp [hrho]
      _ ≤ exp (I.cρ * scale n) * exp (I.cρ * scale n) := hsq
      _ = exp ((2 * I.cρ) * scale n) := by
        rw [← exp_add]
        congr 1
        ring
  unfold coeff
  have step1 : 16 * I.C n ≤ exp (Real.log 16 * scale n) * exp (I.cC * scale n) :=
    mul_le_mul h16 (I.C_upper n) (I.C_pos n).le (exp_pos _).le
  have step2 : 16 * I.C n * I.M n ≤
      exp (Real.log 16 * scale n) * exp (I.cC * scale n) * exp (I.cM * scale n) := by
    calc
      16 * I.C n * I.M n = (16 * I.C n) * I.M n := by ring
      _ ≤ (exp (Real.log 16 * scale n) * exp (I.cC * scale n)) *
            exp (I.cM * scale n) :=
        mul_le_mul step1 (I.M_upper n) (I.M_pos n).le
          (mul_nonneg (exp_pos _).le (exp_pos _).le)
  have step3 : 16 * I.C n * I.M n * I.Econv n ≤
      exp (Real.log 16 * scale n) * exp (I.cC * scale n) * exp (I.cM * scale n) *
        exp (I.cE * scale n) := by
    calc
      16 * I.C n * I.M n * I.Econv n = (16 * I.C n * I.M n) * I.Econv n := by ring
      _ ≤ (exp (Real.log 16 * scale n) * exp (I.cC * scale n) * exp (I.cM * scale n)) *
            exp (I.cE * scale n) :=
        mul_le_mul step2 (I.Econv_upper n) (I.Econv_nonneg n)
          (mul_nonneg (mul_nonneg (exp_pos _).le (exp_pos _).le) (exp_pos _).le)
  have step4 : 16 * I.C n * I.M n * I.Econv n * I.d n ≤
      exp (Real.log 16 * scale n) * exp (I.cC * scale n) * exp (I.cM * scale n) *
        exp (I.cE * scale n) * exp (I.cd * scale n) := by
    calc
      16 * I.C n * I.M n * I.Econv n * I.d n =
          (16 * I.C n * I.M n * I.Econv n) * I.d n := by ring
      _ ≤ (exp (Real.log 16 * scale n) * exp (I.cC * scale n) * exp (I.cM * scale n) *
            exp (I.cE * scale n)) * exp (I.cd * scale n) :=
        mul_le_mul step3 (I.d_upper n) (I.d_pos n).le
          (mul_nonneg (mul_nonneg (mul_nonneg (exp_pos _).le (exp_pos _).le)
            (exp_pos _).le) (exp_pos _).le)
  have step5 : 16 * I.C n * I.M n * I.Econv n * I.d n * I.ell n ^ 2 ≤
      exp (Real.log 16 * scale n) * exp (I.cC * scale n) * exp (I.cM * scale n) *
        exp (I.cE * scale n) * exp (I.cd * scale n) *
          exp ((2 * I.cell) * scale n) := by
    calc
      16 * I.C n * I.M n * I.Econv n * I.d n * I.ell n ^ 2 =
          (16 * I.C n * I.M n * I.Econv n * I.d n) * I.ell n ^ 2 := by ring
      _ ≤ (exp (Real.log 16 * scale n) * exp (I.cC * scale n) * exp (I.cM * scale n) *
            exp (I.cE * scale n) * exp (I.cd * scale n)) *
            exp ((2 * I.cell) * scale n) :=
        mul_le_mul step4 hell2 (sq_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (exp_pos _).le (exp_pos _).le)
            (exp_pos _).le) (exp_pos _).le) (exp_pos _).le)
  calc
    16 * I.C n * I.M n * I.Econv n * I.d n * I.ell n ^ 2 / I.rho n ^ 2 =
        16 * I.C n * I.M n * I.Econv n * I.d n * I.ell n ^ 2 *
          (1 / I.rho n ^ 2) := by rw [div_eq_mul_inv]; ring
    _ ≤ exp (Real.log 16 * scale n) * exp (I.cC * scale n) *
          exp (I.cM * scale n) * exp (I.cE * scale n) * exp (I.cd * scale n) *
          exp ((2 * I.cell) * scale n) * exp ((2 * I.cρ) * scale n) := by
      calc
        16 * I.C n * I.M n * I.Econv n * I.d n * I.ell n ^ 2 * (1 / I.rho n ^ 2) =
            (16 * I.C n * I.M n * I.Econv n * I.d n * I.ell n ^ 2) *
              (1 / I.rho n ^ 2) := by ring
        _ ≤ (exp (Real.log 16 * scale n) * exp (I.cC * scale n) * exp (I.cM * scale n) *
              exp (I.cE * scale n) * exp (I.cd * scale n) *
                exp ((2 * I.cell) * scale n)) * exp ((2 * I.cρ) * scale n) :=
          mul_le_mul step5 hrho2 (div_nonneg zero_le_one (sq_nonneg _))
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
              (exp_pos _).le (exp_pos _).le) (exp_pos _).le) (exp_pos _).le)
              (exp_pos _).le) (exp_pos _).le)
    _ = exp ((Real.log 16 + I.cC + I.cM + I.cE + I.cd + 2 * I.cell +
          2 * I.cρ) * scale n) := by
      simp only [← Real.exp_add]
      congr 1
      ring

/-- The full `D^{O(1)}` coefficient of the loss. -/
theorem coeff_mul_le_exp (n : ℕ) (hW1 : 1 ≤ I.W n) (hH1 : 1 ≤ scale n)
    (hH4 : Real.log 4 ≤ scale n) :
    I.coeff n * (1 + I.W n) ^ 2 ≤ exp (I.csum * scale n) := by
  have hc := I.coeff_le_exp n hH1
  have hw := I.one_add_W_sq_le hW1 hH4
  calc
    I.coeff n * (1 + I.W n) ^ 2 ≤
        exp ((Real.log 16 + I.cC + I.cM + I.cE + I.cd + 2 * I.cell + 2 * I.cρ) *
            scale n) * exp ((1 + 2 * I.cW) * scale n) :=
      mul_le_mul hc hw (by positivity) (exp_pos _).le
    _ = exp (I.csum * scale n) := by
      rw [← exp_add]
      congr 1
      unfold csum
      ring

/-- Eventual form of `coeff_mul_le_exp`, using `W_dominates 1` to get
`log V ≥ 1`. -/
theorem eventually_coeff_mul_le :
    ∀ᶠ n : ℕ in atTop,
      I.coeff n * (1 + I.W n) ^ 2 ≤ exp (I.csum * scale n) := by
  filter_upwards [I.W_dominates 1 (by norm_num),
    scale_grows.eventually_ge_atTop 1,
    scale_grows.eventually_ge_atTop (Real.log 4)] with n hWbig hH1 hH4
  have hW1 : 1 ≤ I.W n := by
    have h : (1 : ℝ) * scale n ≤ I.W n := hWbig
    linarith
  exact I.coeff_mul_le_exp n hW1 hH1 hH4

/-- **Main arithmetic step.**  With the mesh constant `c = 8B + 8 csum + 8`, the
deficit is eventually at most `exp (-B log D)`. -/
theorem loss_le_exp_neg (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ exp (-B * scale n) := by
  set c : ℝ := 8 * B + 8 * I.csum + 8 with hcdef
  have hcpos : 0 < c := by
    have hcs := I.csum_pos
    nlinarith only [hcs, hB, hcdef]
  filter_upwards [I.W_dominates c hcpos, I.eventually_coeff_mul_le,
    I.W_dominates 1 (by norm_num), scale_grows.eventually_ge_atTop 1,
    scale_grows.eventually_ge_atTop (Real.log 2 / B)] with n hWbig hcoeff hW1 hH1 hHlog
  have hW1' : 1 ≤ I.W n := by
    have h : (1 : ℝ) * scale n ≤ I.W n := hW1
    linarith
  have hHnonneg : 0 ≤ scale n := by linarith
  have hWnonneg : 0 ≤ I.W n := by linarith
  have hlog2 : Real.log 2 ≤ B * scale n := by
    have h := (div_le_iff₀ hB).mp hHlog
    nlinarith only [h]
  -- First term: `coeff · (1 + W)² · exp (-(7/4) W)`.
  have hterm1 :
      I.coeff n * (1 + I.W n) ^ 2 * exp (-(7 / 4 : ℝ) * I.W n) ≤
        exp (-2 * B * scale n) := by
    have hmul :
        I.coeff n * (1 + I.W n) ^ 2 * exp (-(7 / 4 : ℝ) * I.W n) ≤
          exp (I.csum * scale n) * exp (-(7 / 4 : ℝ) * I.W n) :=
      mul_le_mul_of_nonneg_right hcoeff (exp_pos _).le
    have hexp :
        exp (I.csum * scale n) * exp (-(7 / 4 : ℝ) * I.W n) =
          exp (I.csum * scale n + -(7 / 4 : ℝ) * I.W n) := by
      rw [← exp_add]
    have hcge : I.csum + 2 * B ≤ (7 / 4 : ℝ) * c := by
      rw [hcdef]
      nlinarith only [I.csum_pos, hB]
    have hstep1 : (I.csum + 2 * B) * scale n ≤ (7 / 4 : ℝ) * (c * scale n) := by
      calc
        (I.csum + 2 * B) * scale n ≤ ((7 / 4 : ℝ) * c) * scale n :=
          mul_le_mul_of_nonneg_right hcge hHnonneg
        _ = (7 / 4 : ℝ) * (c * scale n) := by ring
    have hstep2 : (7 / 4 : ℝ) * (c * scale n) ≤ (7 / 4 : ℝ) * I.W n :=
      mul_le_mul_of_nonneg_left hWbig (by norm_num)
    calc
      I.coeff n * (1 + I.W n) ^ 2 * exp (-(7 / 4 : ℝ) * I.W n) ≤
          exp (I.csum * scale n) * exp (-(7 / 4 : ℝ) * I.W n) := hmul
      _ = exp (I.csum * scale n + -(7 / 4 : ℝ) * I.W n) := hexp
      _ ≤ exp (-2 * B * scale n) := by
        apply exp_le_exp.mpr
        nlinarith only [hstep1, hstep2]
  -- Second term: `exp (-(1/4) W)`.
  have hterm2 : exp (-(1 / 4 : ℝ) * I.W n) ≤ exp (-2 * B * scale n) := by
    apply exp_le_exp.mpr
    have hcge : 2 * B ≤ (1 / 4 : ℝ) * c := by
      rw [hcdef]
      nlinarith only [I.csum_pos, hB]
    have hstep1 : (2 * B) * scale n ≤ ((1 / 4 : ℝ) * c) * scale n :=
      mul_le_mul_of_nonneg_right hcge hHnonneg
    have hstep2 : ((1 / 4 : ℝ) * c) * scale n ≤ (1 / 4 : ℝ) * I.W n := by
      nlinarith only [hWbig]
    nlinarith only [hstep1, hstep2]
  calc
    I.loss n ≤ I.coeff n * (1 + I.W n) ^ 2 * exp (-(7 / 4 : ℝ) * I.W n) +
        exp (-(1 / 4 : ℝ) * I.W n) := I.loss_le n
    _ ≤ exp (-2 * B * scale n) + exp (-2 * B * scale n) :=
      add_le_add hterm1 hterm2
    _ = 2 * exp (-2 * B * scale n) := by ring
    _ ≤ exp (B * scale n) * exp (-2 * B * scale n) := by
      refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
      calc
        (2 : ℝ) = exp (Real.log 2) := (exp_log (by norm_num)).symm
        _ ≤ exp (B * scale n) := exp_le_exp.mpr hlog2
    _ = exp (-B * scale n) := by
      rw [← exp_add]
      congr 1
      ring

/-- **The L18.4 paper statement.**  The decomposed inputs give the manuscript's
`D^{-B}` for every `B`. -/
theorem subexpLoss : SubexpLoss I.loss := fun B hB => I.loss_le_exp_neg B hB

/-- The loss is a genuine nonnegative deficit: neither the cell second-moment
term nor the thin-pair fraction is set to zero. -/
theorem loss_nonneg (n : ℕ) : 0 ≤ I.loss n := by
  have hcell : 0 ≤ I.cellDeficit n := by
    unfold cellDeficit
    exact mul_nonneg (I.K_pos n).le (div_nonneg (I.S2_nonneg n) (sq_nonneg _))
  exact add_nonneg hcell (I.thin_nonneg n)

/-- **The L18.4 `SubexpLeaf`.** -/
noncomputable def toSubexpLeaf : SubexpLeaf where
  loss := I.loss
  loss_nonneg := I.loss_nonneg
  paper := I.subexpLoss

/-- The `B = 2` instance is exactly the `C5Inputs.l18_4` eventuality. -/
theorem slot_le {slots : C5LossSlots}
    (h : slots .rationalGoodEnvironments = I.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .rationalGoodEnvironments n ≤ exp (-(2 : ℝ) * scale n) := by
  rw [h]
  exact I.subexpLoss 2 (by norm_num)

end L18_4Inputs

/-! ## Reusing the RH prime-bin supply for the cell count -/

/-- **RH prime counts in an integer denominator cell.**  The prime-bin supply
bound says that a bin `(A, B]` contains all but a square-root error of its width.
Once the width dominates twice that error, the bin has at least
`(B - A) / (2 log B)` primes.  This is the concrete form of
`L18_4Inputs.cell_prime_count` for an integer cell of width `V / (d K)`. -/
theorem cell_card_lower_of_primeBinSupply {K0 : ℝ} (_hK0 : 0 ≤ K0)
    (hsupply : ∀ A B : ℕ, 2 ≤ A → A ≤ B →
      (B : ℝ) - (A : ℝ) -
          K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
        ((Cogentic.Randomized.primeBin A B).card : ℝ) * Real.log (B : ℝ))
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) {lg : ℝ} (hlg : 0 < lg)
    (hlog : Real.log (B : ℝ) ≤ lg)
    (herr : K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
      ((B : ℝ) - (A : ℝ)) / 2) :
    ((B : ℝ) - (A : ℝ)) / (2 * lg) ≤
      ((Cogentic.Randomized.primeBin A B).card : ℝ) := by
  rcases eq_or_lt_of_le hAB with rfl | hABlt
  · simp
  · have hcard_nn :
        (0 : ℝ) ≤ ((Cogentic.Randomized.primeBin A B).card : ℝ) :=
      Nat.cast_nonneg _
    have hmain := hsupply A B hA hAB
    have hwidth : (0 : ℝ) < (B : ℝ) - (A : ℝ) := by
      have h : (A : ℝ) < (B : ℝ) := by exact_mod_cast hABlt
      linarith
    have h2 : (B : ℝ) - (A : ℝ) ≤
        2 * (((Cogentic.Randomized.primeBin A B).card : ℝ) * Real.log (B : ℝ)) := by
      linarith only [hmain, herr]
    have h3 : ((Cogentic.Randomized.primeBin A B).card : ℝ) * Real.log (B : ℝ) ≤
        ((Cogentic.Randomized.primeBin A B).card : ℝ) * lg :=
      mul_le_mul_of_nonneg_left hlog hcard_nn
    have h4 : (B : ℝ) - (A : ℝ) ≤
        2 * (((Cogentic.Randomized.primeBin A B).card : ℝ) * lg) := by
      nlinarith only [h2, h3]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * lg)]
    nlinarith only [h4]

/-- The critical-line prime-bin supply supplies the RH cell count of L18.4. -/
theorem cell_card_lower_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧
      ∀ {A B : ℕ}, 2 ≤ A → A ≤ B → ∀ {lg : ℝ}, 0 < lg →
        Real.log (B : ℝ) ≤ lg →
        K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
            ((B : ℝ) - (A : ℝ)) / 2 →
          ((B : ℝ) - (A : ℝ)) / (2 * lg) ≤
            ((Cogentic.Randomized.primeBin A B).card : ℝ) := by
  obtain ⟨K0, hK0, hsup⟩ := Cogentic.Randomized.primeBin_supply_from_critical_line line
  exact ⟨K0, hK0, fun hA hAB hlg hlog herr =>
    cell_card_lower_of_primeBinSupply hK0 hsup hA hAB (lg := hlg) hlog herr⟩

/-! ## Axiom audit -/

#print axioms L18_4Inputs.muCell_lower
#print axioms L18_4Inputs.mu_lower
#print axioms L18_4Inputs.energy_loss_eq
#print axioms L18_4Inputs.cellDeficit_le
#print axioms L18_4Inputs.loss_le
#print axioms L18_4Inputs.coeff_le_exp
#print axioms L18_4Inputs.coeff_mul_le_exp
#print axioms L18_4Inputs.loss_le_exp_neg
#print axioms L18_4Inputs.subexpLoss
#print axioms L18_4Inputs.toSubexpLeaf
#print axioms L18_4Inputs.slot_le
#print axioms cell_card_lower_of_primeBinSupply
#print axioms cell_card_lower_from_critical_line

end Cogentic.RandomizedL18_4
