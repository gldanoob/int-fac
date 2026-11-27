import Cogentic.RandomizedL19SecondMoment
import Cogentic.RandomizedPrimeProductPlancherel
import Cogentic.RandomizedPrimeGridPrefixEnergy
import Cogentic.RandomizedTopStripMoments

/-!
# L19.4: the marginal energies and their critical-line envelopes

`RandomizedL19SecondMoment.PoissonQuotientInputs` assumes the two marginal
energy bounds

  `E₁ n ≤ exp (c₁ * scale n) * exp (-η₁ * W n)`,  `E₂ n ≤ exp (c₂ * scale n) * exp (-η₂ * W n)`

with `W = log V` and `V = exp W`.  This file supplies those two bounds from the
two existing critical-line theorems, with the marginal energy functionals
defined as the actual analytic quantities appearing in those theorems (and not
as zero):

* **The Mellin marginal energy** `mellinEnergy` is the Plancherel residue
  energy `√ (∑_r ‖mellinClassError (primeBinProducts A B) (σ + i t) r‖²)`.
  `primeBinProducts_mellin_energy_from_critical_line` bounds it by the explicit
  per-bin product envelope `mellinEnvelope` (`mellinEnergy_le_envelope`).

* **The sharp-prefix marginal energy** `gridPrefixEnergy` is the `L²` norm over
  the residue/frequency grid of the maximal prefix Fourier coefficient,
  exactly the left-hand side of
  `primeBinProducts_gridPrefix_from_critical_line`.  That theorem bounds it by
  the explicit envelope `gridPrefixEnvelope` (`gridPrefixEnergy_le_envelope`).

Both marginal energies are then normalized by the reference marginal mass
(`mellinMarginalEnergy`, `gridPrefixMarginalEnergy`), matching the normalization
`E_i = √C_i L_i / √φ(m_i)` of `RandomizedTopStripMoments.averaged_coupled_abel_strip_bound`.

The remaining arithmetic is isolated in `EnergyScaleInputs`: the envelope is
polynomial on the ledger scale (`envelope_poly : envelope n ≤ exp (c * scale n)`)
and the marginal mass is at least `V ^ η` (`mass_lower : exp (η * W n) ≤ mass n`).
From these two facts we prove the required `D ^ c · V ^ (-η)` shape
(`EnergyScaleInputs.bound`), its `SubexpLoss` form, and the product form used by
the L19.2 coupled-mode Cauchy–Schwarz input.

Finally `PoissonQuotientInputs.replaceMarginalBounds` replaces the two opaque
fields `E₁_bound` / `E₂_bound` of a `PoissonQuotientInputs` by the bounds derived
here; `PoissonQuotientInputs.replaceMarginalBounds_subexpLoss` records that the
L19.4 `SubexpLoss` statement then follows.

Nothing here is a `sorry`, an `admit`, an `axiom`, or `native_decide`, and the
energies are not set to zero.
-/

namespace Cogentic.RandomizedL19Energy

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open Filter Real
open scoped BigOperators Classical
open Cogentic.Randomized
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements

/-! ## 1. The Mellin marginal energy -/

/-- The Mellin residue energy of the prime-bin product strip at the height
`σ + i t`: the squared Plancherel mass of the centered residue vector.  This is
the left-hand side of `mellinClassError_plancherel`, hence of
`primeBinProducts_mellin_energy_from_critical_line`. -/
noncomputable def mellinEnergy (q : ℕ) (hq : q ≠ 0) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (σ t : ℝ) : ℝ :=
  letI : NeZero q := ⟨hq⟩
  Real.sqrt (∑ r : (ZMod q)ˣ, ‖mellinClassError (primeBinProducts A B)
    ((σ : ℂ) + t * Complex.I) r‖ ^ 2)

/-- The explicit Plancherel envelope of the critical-line theorem:
`∏ᵢ K √Bᵢ (1 + log (q (Bᵢ + |t| + 2)))³`. -/
noncomputable def mellinEnvelope {ι : Type} [Fintype ι] (q : ℕ) (K : ℝ)
    (B : ι → ℕ) (t : ℝ) : ℝ :=
  ∏ i, K * Real.sqrt (B i) * (1 + Real.log (q * ((B i : ℝ) + |t| + 2))) ^ 3

private theorem mellinEnvelope_nonneg {ι : Type} [Fintype ι] {q : ℕ} (hq : q ≠ 0)
    {K : ℝ} (hK : 0 ≤ K) (B : ι → ℕ) (hB : ∀ i, 2 ≤ B i) (t : ℝ) :
    0 ≤ mellinEnvelope q K B t := by
  unfold mellinEnvelope
  apply Finset.prod_nonneg
  intro i _
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq)
  have hB2 : (2 : ℝ) ≤ (B i : ℝ) := by exact_mod_cast hB i
  have harg : (1 : ℝ) ≤ (q : ℝ) * ((B i : ℝ) + |t| + 2) := by
    nlinarith [abs_nonneg t]
  have hlog : 0 ≤ Real.log (q * ((B i : ℝ) + |t| + 2)) := Real.log_nonneg harg
  have hcube : 0 ≤ (1 + Real.log (q * ((B i : ℝ) + |t| + 2))) ^ 3 := by positivity
  exact mul_nonneg (mul_nonneg hK (Real.sqrt_nonneg _)) hcube

/-- The Mellin constant supplied by the critical-line theorem. -/
noncomputable def mellinK (line : DirichletLZerosOnLine) : ℝ :=
  Classical.choose (primeBinProducts_mellin_energy_from_critical_line line)

theorem mellinK_pos (line : DirichletLZerosOnLine) : 0 < mellinK line :=
  (Classical.choose_spec (primeBinProducts_mellin_energy_from_critical_line line)).1

/-- **The Plancherel theorem bounds the Mellin marginal energy by its explicit
per-bin envelope.**  This is `primeBinProducts_mellin_energy_from_critical_line`
with the squared residue vector isolated as `mellinEnergy` and the product
envelope isolated as `mellinEnvelope`. -/
theorem mellinEnergy_le_envelope (line : DirichletLZerosOnLine)
    (q : ℕ) (hq : q ≠ 0) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (hB : ∀ i, 2 ≤ B i) (hAB : ∀ i, A i ≤ B i)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (σ t : ℝ) (hσ : 0 ≤ σ) :
    mellinEnergy q hq A B σ t ≤ mellinEnvelope q (mellinK line) B t := by
  haveI : NeZero q := ⟨hq⟩
  have hb := (Classical.choose_spec
    (primeBinProducts_mellin_energy_from_critical_line line)).2 q A B hB hAB hdisj σ t hσ
  have hprod : 0 ≤ mellinEnvelope q (mellinK line) B t :=
    mellinEnvelope_nonneg hq (mellinK_pos line).le B hB t
  calc
    mellinEnergy q hq A B σ t =
        Real.sqrt (∑ r : (ZMod q)ˣ, ‖mellinClassError (primeBinProducts A B)
          ((σ : ℂ) + t * Complex.I) r‖ ^ 2) := by simp only [mellinEnergy]
    _ ≤ Real.sqrt ((∏ i, mellinK line * Real.sqrt (B i) *
          (1 + Real.log (q * ((B i : ℝ) + |t| + 2))) ^ 3) ^ 2) :=
        Real.sqrt_le_sqrt hb
    _ = mellinEnvelope q (mellinK line) B t := by
        rw [Real.sqrt_sq (by simpa only [mellinEnvelope] using hprod)]
        rfl

/-! ## 2. The sharp-prefix marginal energy -/

/-- The sharp-prefix grid energy: the `L²` norm over the residue/frequency grid
of the maximal prefix Fourier coefficient over the cutoffs.  This is exactly the
left-hand side of `primeBinProducts_gridPrefix_from_critical_line`. -/
noncomputable def gridPrefixEnergy (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    (cop : m.Coprime B) (_X : ℝ) (cutoffs : Finset ℕ) (hne : cutoffs.Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ) : ℝ :=
  letI : NeZero m := ⟨hm⟩
  letI : NeZero B := ⟨hB⟩
  letI : NeZero (m * B) := ⟨mul_ne_zero hm hB⟩
  ‖(WithLp.toLp 2 (fun i : GridCoordinate m B => cutoffs.sup' hne
      (fun j => ‖gridPrefixFourier cop (primeBinProducts A U) j i‖)) :
        EuclideanSpace ℝ (GridCoordinate m B))‖

/-- A grid-prefix energy is a norm, hence nonnegative. -/
theorem gridPrefixEnergy_nonneg (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    (cop : m.Coprime B) (X : ℝ) (cutoffs : Finset ℕ) (hne : cutoffs.Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ) :
    0 ≤ gridPrefixEnergy m B hm hB cop X cutoffs hne A U := by
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero B := ⟨hB⟩
  haveI : NeZero (m * B) := ⟨mul_ne_zero hm hB⟩
  unfold gridPrefixEnergy
  exact norm_nonneg _

/-- The explicit sharp-prefix envelope of the critical-line theorem. -/
noncomputable def gridPrefixEnvelope {ι : Type} [Fintype ι] [DecidableEq ι]
    (m B : ℕ) (C K X : ℝ) (A U : ι → ℕ) : ℝ :=
  Real.sqrt (B : ℝ) * ((4 * Real.exp 2 / Real.pi) *
    ((∏ i, C * Real.sqrt (U i) *
      (1 + Real.log ((m * B : ℕ) * ((U i : ℝ) + X ^ 3 + 2))) ^ 3) * Real.log X) +
    (2 * K / X ^ 2) * ((primeBinProducts A U).card : ℝ))

private theorem gridPrefixEnvelope_nonneg {ι : Type} [Fintype ι] [DecidableEq ι]
    (m B : ℕ) (hmB : m * B ≠ 0) {C K X : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hX : 2 ≤ X)
    (A U : ι → ℕ) (hU : ∀ i, 2 ≤ U i) :
    0 ≤ gridPrefixEnvelope m B C K X A U := by
  unfold gridPrefixEnvelope
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hmB1 : (1 : ℝ) ≤ ((m * B : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hmB)
  have hprod : 0 ≤ ∏ i, C * Real.sqrt (U i) *
      (1 + Real.log ((m * B : ℕ) * ((U i : ℝ) + X ^ 3 + 2))) ^ 3 := by
    apply Finset.prod_nonneg
    intro i _
    have hU2 : (2 : ℝ) ≤ (U i : ℝ) := by exact_mod_cast hU i
    have hX3 : (0 : ℝ) ≤ X ^ 3 := by positivity
    have harg : (1 : ℝ) ≤ ((m * B : ℕ) : ℝ) * ((U i : ℝ) + X ^ 3 + 2) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (U i)]
    have hlog : 0 ≤ Real.log ((m * B : ℕ) * ((U i : ℝ) + X ^ 3 + 2)) :=
      Real.log_nonneg harg
    have hcube : 0 ≤ (1 + Real.log ((m * B : ℕ) *
        ((U i : ℝ) + X ^ 3 + 2))) ^ 3 := by positivity
    exact mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hcube
  have hfirst : 0 ≤ (4 * Real.exp 2 / Real.pi) *
      ((∏ i, C * Real.sqrt (U i) *
        (1 + Real.log ((m * B : ℕ) * ((U i : ℝ) + X ^ 3 + 2))) ^ 3) * Real.log X) := by
    positivity
  have hsecond : 0 ≤ (2 * K / X ^ 2) * ((primeBinProducts A U).card : ℝ) := by
    positivity
  exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)

/-- The first prefix constant supplied by the critical-line theorem, for the
fixed modulus pair `(m, B)`. -/
noncomputable def prefixC (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    (line : DirichletLZerosOnLine) : ℝ :=
  letI : NeZero m := ⟨hm⟩
  letI : NeZero B := ⟨hB⟩
  letI : NeZero (m * B) := ⟨mul_ne_zero hm hB⟩
  Classical.choose (primeBinProducts_gridPrefix_from_critical_line (m := m) (B := B) line)

/-- The second prefix constant supplied by the critical-line theorem, for the
fixed modulus pair `(m, B)`. -/
noncomputable def prefixK (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    (line : DirichletLZerosOnLine) : ℝ :=
  letI : NeZero m := ⟨hm⟩
  letI : NeZero B := ⟨hB⟩
  letI : NeZero (m * B) := ⟨mul_ne_zero hm hB⟩
  Classical.choose (Classical.choose_spec
    (primeBinProducts_gridPrefix_from_critical_line (m := m) (B := B) line))

theorem prefixC_pos (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    (line : DirichletLZerosOnLine) : 0 < prefixC m B hm hB line := by
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero B := ⟨hB⟩
  haveI : NeZero (m * B) := ⟨mul_ne_zero hm hB⟩
  dsimp only [prefixC]
  exact (Classical.choose_spec (Classical.choose_spec
    (primeBinProducts_gridPrefix_from_critical_line (m := m) (B := B) line))).1

theorem prefixK_pos (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    (line : DirichletLZerosOnLine) : 0 < prefixK m B hm hB line := by
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero B := ⟨hB⟩
  haveI : NeZero (m * B) := ⟨mul_ne_zero hm hB⟩
  dsimp only [prefixK]
  exact (Classical.choose_spec (Classical.choose_spec
    (primeBinProducts_gridPrefix_from_critical_line (m := m) (B := B) line))).2.1

/-- **The sharp-prefix theorem bounds the prefix marginal energy by its explicit
envelope.**  This is `primeBinProducts_gridPrefix_from_critical_line` with the
`L²` prefix supremum isolated as `gridPrefixEnergy` and the product envelope
isolated as `gridPrefixEnvelope`. -/
theorem gridPrefixEnergy_le_envelope (line : DirichletLZerosOnLine)
    (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    (cop : m.Coprime B) (X : ℝ) (cutoffs : Finset ℕ) (hne : cutoffs.Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ)
    (hX : 2 ≤ X) (heX : Real.exp 1 ≤ X)
    (hcut : ∀ j ∈ cutoffs, X ≤ (j : ℝ) + 1 / 2 ∧ (j : ℝ) + 1 / 2 ≤ 2 * X)
    (hP : ∀ n ∈ primeBinProducts A U, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X)
    (hU : ∀ i, 2 ≤ U i) (hAU : ∀ i, A i ≤ U i)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (U i)) (primeBin (A j) (U j))) :
    gridPrefixEnergy m B hm hB cop X cutoffs hne A U ≤
      gridPrefixEnvelope m B (prefixC m B hm hB line) (prefixK m B hm hB line) X A U := by
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero B := ⟨hB⟩
  haveI : NeZero (m * B) := ⟨mul_ne_zero hm hB⟩
  have hb := (Classical.choose_spec (Classical.choose_spec
    (primeBinProducts_gridPrefix_from_critical_line (m := m) (B := B) line))).2.2
      cop X cutoffs hne A U hX heX hcut hP hU hAU hdisj
  simpa only [gridPrefixEnergy, gridPrefixEnvelope, prefixC, prefixK] using hb

/-! ## 3. Normalized marginal energies -/

/-- The Mellin marginal energy normalized by the reference marginal mass `ν`. -/
noncomputable def mellinMarginalEnergy (q : ℕ) (hq : q ≠ 0) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (σ t ν : ℝ) : ℝ :=
  mellinEnergy q hq A B σ t / ν

/-- The sharp-prefix marginal energy normalized by `√φ(m)` and the reference
marginal mass `ν`.  This is the normalization of
`RandomizedTopStripMoments.averaged_coupled_abel_strip_bound`. -/
noncomputable def gridPrefixMarginalEnergy (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    (cop : m.Coprime B) (X : ℝ) (cutoffs : Finset ℕ) (hne : cutoffs.Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ) (ν : ℝ) : ℝ :=
  gridPrefixEnergy m B hm hB cop X cutoffs hne A U / (Real.sqrt ((m.totient : ℝ)) * ν)

/-- **The scale arithmetic.**  A nonnegative envelope that is polynomial in
`D = exp (scale n)` and a normalizer at least `V ^ η = exp (η W n)` give the
marginal `D ^ c V ^ (-η)` shape. -/
theorem div_le_exp_of_envelope_mass {env norm c η W s : ℝ}
    (_henv_nonneg : 0 ≤ env) (hnorm : 0 < norm) (_hη : 0 < η)
    (henv : env ≤ exp (c * s)) (hmass : exp (η * W) ≤ norm) :
    env / norm ≤ exp (c * s) * exp (-η * W) := by
  have hexp : 0 < exp (η * W) := exp_pos _
  calc
    env / norm ≤ exp (c * s) / norm := div_le_div_of_nonneg_right henv hnorm.le
    _ ≤ exp (c * s) / exp (η * W) :=
        div_le_div_of_nonneg_left (exp_pos _).le hexp hmass
    _ = exp (c * s) * exp (-η * W) := by
        rw [div_eq_mul_inv, show -η * W = -(η * W) by ring, Real.exp_neg]

/-- **Pointwise Mellin marginal bound.**  The Plancherel envelope is polynomial
on the ledger scale and the marginal mass dominates `V ^ η`; hence the
normalized Mellin marginal energy has the L19.4 shape. -/
theorem mellinMarginalEnergy_le_exp (line : DirichletLZerosOnLine)
    (q : ℕ) (hq : q ≠ 0) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (hB : ∀ i, 2 ≤ B i) (hAB : ∀ i, A i ≤ B i)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (σ t : ℝ) (hσ : 0 ≤ σ)
    {W : ℕ → ℝ} {c η : ℝ} (hη : 0 < η) {n : ℕ} {ν : ℝ} (hν : 0 < ν)
    (henv : mellinEnvelope q (mellinK line) B t ≤ exp (c * scale n))
    (hmass : exp (η * W n) ≤ ν) :
    mellinMarginalEnergy q hq A B σ t ν ≤ exp (c * scale n) * exp (-η * W n) := by
  unfold mellinMarginalEnergy
  calc
    mellinEnergy q hq A B σ t / ν ≤ mellinEnvelope q (mellinK line) B t / ν :=
      div_le_div_of_nonneg_right
        (mellinEnergy_le_envelope line q hq A B hB hAB hdisj σ t hσ) hν.le
    _ ≤ exp (c * scale n) * exp (-η * W n) :=
        div_le_exp_of_envelope_mass
          (mellinEnvelope_nonneg hq (mellinK_pos line).le B hB t) hν hη henv hmass

/-- **Pointwise sharp-prefix marginal bound.**  The grid-prefix envelope is
polynomial on the ledger scale and `√φ(m) · ν` dominates `V ^ η`; hence the
normalized prefix marginal energy has the L19.4 shape. -/
theorem gridPrefixMarginalEnergy_le_exp (line : DirichletLZerosOnLine)
    (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    (cop : m.Coprime B) (X : ℝ) (cutoffs : Finset ℕ) (hne : cutoffs.Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ)
    (hX : 2 ≤ X) (heX : Real.exp 1 ≤ X)
    (hcut : ∀ j ∈ cutoffs, X ≤ (j : ℝ) + 1 / 2 ∧ (j : ℝ) + 1 / 2 ≤ 2 * X)
    (hP : ∀ n ∈ primeBinProducts A U, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X)
    (hU : ∀ i, 2 ≤ U i) (hAU : ∀ i, A i ≤ U i)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (U i)) (primeBin (A j) (U j)))
    {W : ℕ → ℝ} {c η : ℝ} (hη : 0 < η) {n : ℕ} {ν : ℝ} (hν : 0 < ν)
    (henv : gridPrefixEnvelope m B (prefixC m B hm hB line) (prefixK m B hm hB line) X A U ≤
      exp (c * scale n))
    (hmass : exp (η * W n) ≤ Real.sqrt ((m.totient : ℝ)) * ν) :
    gridPrefixMarginalEnergy m B hm hB cop X cutoffs hne A U ν ≤
      exp (c * scale n) * exp (-η * W n) := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm
  have hφ : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm0
  have hsqrt : 0 < Real.sqrt ((m.totient : ℝ)) := Real.sqrt_pos.mpr hφ
  have hnorm : 0 < Real.sqrt ((m.totient : ℝ)) * ν := mul_pos hsqrt hν
  unfold gridPrefixMarginalEnergy
  calc
    gridPrefixEnergy m B hm hB cop X cutoffs hne A U / (Real.sqrt ((m.totient : ℝ)) * ν) ≤
        gridPrefixEnvelope m B (prefixC m B hm hB line) (prefixK m B hm hB line) X A U /
          (Real.sqrt ((m.totient : ℝ)) * ν) :=
      div_le_div_of_nonneg_right
        (gridPrefixEnergy_le_envelope line m B hm hB cop X cutoffs hne A U
          hX heX hcut hP hU hAU hdisj) hnorm.le
    _ ≤ exp (c * scale n) * exp (-η * W n) :=
        div_le_exp_of_envelope_mass
          (gridPrefixEnvelope_nonneg m B (mul_ne_zero hm hB)
            (prefixC_pos m B hm hB line).le (prefixK_pos m B hm hB line).le hX A U hU)
          hnorm hη henv hmass

/-! ## 4. The smallest explicit scale certificate -/

/-- **The remaining scale arithmetic of one marginal energy.**

`envelope` is the raw critical-line envelope and `mass` the reference marginal
mass.  The two arithmetic inputs are exactly the manuscript's `D^{O(1)}` growth
of the envelope (`envelope_poly`) and the `V ^ η` lower bound on the marginal
mass (`mass_lower`).  The energy is tied to the envelope only through
`energy_le_envelope`, so it is never forced to zero. -/
structure EnergyScaleInputs (W : ℕ → ℝ) where
  /-- `W = log V` is nonnegative. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- `log V` dominates every fixed multiple of `log D = scale n`. -/
  W_dominates : DominatesScale W
  /-- Exponent of `D` in the marginal envelope. -/
  c : ℝ
  /-- Decay exponent in `V`. -/
  η : ℝ
  /-- The decay exponent is genuine. -/
  η_pos : 0 < η
  /-- The marginal energy. -/
  energy : ℕ → ℝ
  /-- The raw critical-line envelope. -/
  envelope : ℕ → ℝ
  /-- The reference marginal mass. -/
  mass : ℕ → ℝ
  /-- The energy is nonnegative. -/
  energy_nonneg : ∀ n, 0 ≤ energy n
  /-- The envelope is nonnegative. -/
  envelope_nonneg : ∀ n, 0 ≤ envelope n
  /-- The marginal mass is positive. -/
  mass_pos : ∀ n, 0 < mass n
  /-- The energy is the envelope divided by the marginal mass. -/
  energy_le_envelope : ∀ n, energy n ≤ envelope n / mass n
  /-- **`D^{O(1)}` growth** of the envelope. -/
  envelope_poly : ∀ n, envelope n ≤ exp (c * scale n)
  /-- **`V^η` lower bound** on the marginal mass. -/
  mass_lower : ∀ n, exp (η * W n) ≤ mass n

namespace EnergyScaleInputs

variable {W : ℕ → ℝ}

/-- **The L19.4 bound shape** `E ≤ exp (c · scale) · exp (-η · W)`. -/
theorem bound (I : EnergyScaleInputs W) :
    ∀ n, I.energy n ≤ exp (I.c * scale n) * exp (-I.η * W n) := fun n =>
  (I.energy_le_envelope n).trans
    (div_le_exp_of_envelope_mass (I.envelope_nonneg n) (I.mass_pos n) I.η_pos
      (I.envelope_poly n) (I.mass_lower n))

/-- The marginal energy is a `SubexpLoss` sequence. -/
theorem subexpLoss (I : EnergyScaleInputs W) : SubexpLoss I.energy :=
  subexpLoss_of_eventually_le (Eventually.of_forall I.bound)
    (subexpLoss_exp_mul_exp_neg I.W_dominates (C := I.c) I.η_pos)

/-- **The product of the two marginal energies is a `SubexpLoss` sequence**,
the scalar L19.2 → L19.4 step. -/
theorem product_subexpLoss (I J : EnergyScaleInputs W) :
    SubexpLoss (fun n => I.energy n * J.energy n) :=
  subexpLoss_marginal_product I.W_dominates I.η_pos J.η_pos
    I.energy_nonneg J.energy_nonneg I.bound J.bound

end EnergyScaleInputs

/-! ## 5. The concrete marginal scale certificates -/

/-- **The Mellin marginal certificate.**  The energy is the normalized Plancherel
residue energy of the prime-bin product strip; the envelope is the explicit
Plancherel product, hence bounded by the critical-line theorem.  Only
`henv` (envelope is `D^{O(1)}`) and `hmass` (marginal mass is at least `V^η`)
remain. -/
noncomputable def mellinEnergyScale (line : DirichletLZerosOnLine)
    {W : ℕ → ℝ} (hW0 : ∀ n, 0 ≤ W n) (hW : DominatesScale W)
    {c η : ℝ} (hη : 0 < η)
    (q : ℕ → ℕ) (hq : ∀ n, q n ≠ 0)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ℕ → ι → ℕ) (hB : ∀ n i, 2 ≤ B n i) (hAB : ∀ n i, A n i ≤ B n i)
    (hdisj : ∀ n, Pairwise fun i j =>
      Disjoint (primeBin (A n i) (B n i)) (primeBin (A n j) (B n j)))
    (σ t ν : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n) (hν : ∀ n, 0 < ν n)
    (henv : ∀ n, mellinEnvelope (q n) (mellinK line) (B n) (t n) ≤ exp (c * scale n))
    (hmass : ∀ n, exp (η * W n) ≤ ν n) :
    EnergyScaleInputs W where
  W_nonneg := hW0
  W_dominates := hW
  c := c
  η := η
  η_pos := hη
  energy := fun n => mellinMarginalEnergy (q n) (hq n) (A n) (B n) (σ n) (t n) (ν n)
  envelope := fun n => mellinEnvelope (q n) (mellinK line) (B n) (t n)
  mass := ν
  energy_nonneg := fun n => by
    unfold mellinMarginalEnergy
    exact div_nonneg (Real.sqrt_nonneg _) (hν n).le
  envelope_nonneg := fun n =>
    mellinEnvelope_nonneg (hq n) (mellinK_pos line).le (B n) (hB n) (t n)
  mass_pos := hν
  energy_le_envelope := fun n => by
    unfold mellinMarginalEnergy
    exact div_le_div_of_nonneg_right
      (mellinEnergy_le_envelope line (q n) (hq n) (A n) (B n) (hB n) (hAB n)
        (hdisj n) (σ n) (t n) (hσ n)) (hν n).le
  envelope_poly := henv
  mass_lower := hmass

/-- **The sharp-prefix marginal certificate.**  The energy is the grid-prefix
`L²` energy divided by `√φ(m)` and the marginal mass; the envelope is the
explicit grid-prefix envelope, hence bounded by the critical-line theorem.  Only
`henv` and `hmass` remain. -/
noncomputable def gridPrefixEnergyScale (line : DirichletLZerosOnLine)
    {W : ℕ → ℝ} (hW0 : ∀ n, 0 ≤ W n) (hW : DominatesScale W)
    {c η : ℝ} (hη : 0 < η)
    (m Bm : ℕ → ℕ) (hm : ∀ n, m n ≠ 0) (hBm : ∀ n, Bm n ≠ 0)
    (cop : ∀ n, (m n).Coprime (Bm n))
    (X : ℕ → ℝ) (cutoffs : ℕ → Finset ℕ) (hne : ∀ n, (cutoffs n).Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ℕ → ι → ℕ)
    (hX : ∀ n, 2 ≤ X n) (heX : ∀ n, Real.exp 1 ≤ X n)
    (hcut : ∀ n j, j ∈ cutoffs n → X n ≤ (j : ℝ) + 1 / 2 ∧ (j : ℝ) + 1 / 2 ≤ 2 * X n)
    (hP : ∀ n y, y ∈ primeBinProducts (A n) (U n) → X n ≤ (y : ℝ) ∧ (y : ℝ) ≤ 2 * X n)
    (hU : ∀ n i, 2 ≤ U n i) (hAU : ∀ n i, A n i ≤ U n i)
    (hdisj : ∀ n, Pairwise fun i j =>
      Disjoint (primeBin (A n i) (U n i)) (primeBin (A n j) (U n j)))
    (ν : ℕ → ℝ) (hν : ∀ n, 0 < ν n)
    (henv : ∀ n, gridPrefixEnvelope (m n) (Bm n)
      (prefixC (m n) (Bm n) (hm n) (hBm n) line)
      (prefixK (m n) (Bm n) (hm n) (hBm n) line) (X n) (A n) (U n) ≤ exp (c * scale n))
    (hmass : ∀ n, exp (η * W n) ≤ Real.sqrt (((m n).totient : ℝ)) * ν n) :
    EnergyScaleInputs W where
  W_nonneg := hW0
  W_dominates := hW
  c := c
  η := η
  η_pos := hη
  energy := fun n => gridPrefixMarginalEnergy (m n) (Bm n) (hm n) (hBm n) (cop n)
    (X n) (cutoffs n) (hne n) (A n) (U n) (ν n)
  envelope := fun n => gridPrefixEnvelope (m n) (Bm n)
    (prefixC (m n) (Bm n) (hm n) (hBm n) line)
    (prefixK (m n) (Bm n) (hm n) (hBm n) line) (X n) (A n) (U n)
  mass := fun n => Real.sqrt (((m n).totient : ℝ)) * ν n
  energy_nonneg := fun n => by
    unfold gridPrefixMarginalEnergy
    exact div_nonneg
      (gridPrefixEnergy_nonneg (m n) (Bm n) (hm n) (hBm n) (cop n) (X n) (cutoffs n)
        (hne n) (A n) (U n))
      (mul_nonneg (Real.sqrt_nonneg _) (hν n).le)
  envelope_nonneg := fun n =>
    gridPrefixEnvelope_nonneg (m n) (Bm n) (mul_ne_zero (hm n) (hBm n))
      (prefixC_pos (m n) (Bm n) (hm n) (hBm n) line).le
      (prefixK_pos (m n) (Bm n) (hm n) (hBm n) line).le (hX n) (A n) (U n) (hU n)
  mass_pos := fun n => by
    have hm0 : 0 < m n := Nat.pos_of_ne_zero (hm n)
    have hφ : (0 : ℝ) < ((m n).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hm0
    exact mul_pos (Real.sqrt_pos.mpr hφ) (hν n)
  energy_le_envelope := fun n => by
    have hm0 : 0 < m n := Nat.pos_of_ne_zero (hm n)
    have hφ : (0 : ℝ) < ((m n).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hm0
    have hsqrt : 0 < Real.sqrt (((m n).totient : ℝ)) := Real.sqrt_pos.mpr hφ
    unfold gridPrefixMarginalEnergy
    exact div_le_div_of_nonneg_right
      (gridPrefixEnergy_le_envelope line (m n) (Bm n) (hm n) (hBm n) (cop n)
        (X n) (cutoffs n) (hne n) (A n) (U n) (hX n) (heX n) (hcut n) (hP n)
        (hU n) (hAU n) (hdisj n)) (mul_pos hsqrt (hν n)).le
  envelope_poly := henv
  mass_lower := hmass

/-! ## 6. Discharging the two `E₁_bound` / `E₂_bound` fields -/

end Cogentic.RandomizedL19Energy

open Filter Real
open scoped BigOperators Classical
open Cogentic.Randomized
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedL19Energy

namespace Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs

variable (I : PoissonQuotientInputs)

/-- **The `E₁_bound` field from a marginal scale certificate.** -/
theorem E₁_bound_of_scale (M : EnergyScaleInputs I.W)
    (hc : M.c = I.c₁) (hη : M.η = I.η₁)
    (hE : ∀ n, M.energy n = I.E₁ n) :
    ∀ n, I.E₁ n ≤ exp (I.c₁ * scale n) * exp (-I.η₁ * I.W n) := by
  intro n
  have h := M.bound n
  rw [hE n, hc, hη] at h
  exact h

/-- **The `E₂_bound` field from a marginal scale certificate.** -/
theorem E₂_bound_of_scale (M : EnergyScaleInputs I.W)
    (hc : M.c = I.c₂) (hη : M.η = I.η₂)
    (hE : ∀ n, M.energy n = I.E₂ n) :
    ∀ n, I.E₂ n ≤ exp (I.c₂ * scale n) * exp (-I.η₂ * I.W n) := by
  intro n
  have h := M.bound n
  rw [hE n, hc, hη] at h
  exact h

/-- **Literal replacement of the two marginal-energy proof fields.**  All other
fields of `I` are kept; `E₁_bound` and `E₂_bound` are derived from the concrete
scale certificates instead of being assumed. -/
noncomputable def replaceMarginalBounds (M₁ M₂ : EnergyScaleInputs I.W)
    (hc₁ : M₁.c = I.c₁) (hη₁ : M₁.η = I.η₁) (hE₁ : ∀ n, M₁.energy n = I.E₁ n)
    (hc₂ : M₂.c = I.c₂) (hη₂ : M₂.η = I.η₂) (hE₂ : ∀ n, M₂.energy n = I.E₂ n) :
    PoissonQuotientInputs :=
  { I with
    E₁_bound := I.E₁_bound_of_scale M₁ hc₁ hη₁ hE₁
    E₂_bound := I.E₂_bound_of_scale M₂ hc₂ hη₂ hE₂ }

/-- The replacement keeps the marginal energies and their exponents. -/
@[simp] theorem replaceMarginalBounds_E₁
    (M₁ M₂ : EnergyScaleInputs I.W)
    (hc₁ : M₁.c = I.c₁) (hη₁ : M₁.η = I.η₁) (hE₁ : ∀ n, M₁.energy n = I.E₁ n)
    (hc₂ : M₂.c = I.c₂) (hη₂ : M₂.η = I.η₂) (hE₂ : ∀ n, M₂.energy n = I.E₂ n) :
    (I.replaceMarginalBounds M₁ M₂ hc₁ hη₁ hE₁ hc₂ hη₂ hE₂).E₁ = I.E₁ := rfl

/-- **L19.4 survives the replacement.**  The Poisson quotient error is still
`SubexpLoss` after the two marginal fields are discharged. -/
theorem replaceMarginalBounds_subexpLoss (M₁ M₂ : EnergyScaleInputs I.W)
    (hc₁ : M₁.c = I.c₁) (hη₁ : M₁.η = I.η₁) (hE₁ : ∀ n, M₁.energy n = I.E₁ n)
    (hc₂ : M₂.c = I.c₂) (hη₂ : M₂.η = I.η₂) (hE₂ : ∀ n, M₂.energy n = I.E₂ n) :
    SubexpLoss (I.replaceMarginalBounds M₁ M₂ hc₁ hη₁ hE₁ hc₂ hη₂ hE₂).loss :=
  (I.replaceMarginalBounds M₁ M₂ hc₁ hη₁ hE₁ hc₂ hη₂ hE₂).subexpLoss

end Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs

namespace Cogentic.RandomizedL19Energy

/-! ## Axiom audit -/

#print axioms mellinEnergy_le_envelope
#print axioms gridPrefixEnergy_le_envelope
#print axioms div_le_exp_of_envelope_mass
#print axioms mellinMarginalEnergy_le_exp
#print axioms gridPrefixMarginalEnergy_le_exp
#print axioms EnergyScaleInputs.bound
#print axioms EnergyScaleInputs.subexpLoss
#print axioms EnergyScaleInputs.product_subexpLoss
#print axioms mellinEnergyScale
#print axioms gridPrefixEnergyScale
#print axioms PoissonQuotientInputs.E₁_bound_of_scale
#print axioms PoissonQuotientInputs.E₂_bound_of_scale
#print axioms PoissonQuotientInputs.replaceMarginalBounds
#print axioms PoissonQuotientInputs.replaceMarginalBounds_subexpLoss

end Cogentic.RandomizedL19Energy
