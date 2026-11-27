import Cogentic.RandomizedL20_2Saddle
import Cogentic.RandomizedL19Energy

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# L20.2: the per-coordinate energy budget

`Cogentic.RandomizedL20_2Char.CoordinateEnergyBudget E μ crtError charError` is
the one-coordinate input of the G.10 off-diagonal estimate:

`E n ^ 2 ≤ (crtError n + charError n) * μ n ^ 2`.

The existing `RandomizedL20_2Saddle.coordinateEnergyBudget_of_mellinEnvelope`
proves it for the Mellin Plancherel energy once an explicit envelope-fit
inequality is supplied.  This file isolates that remaining fit as the smallest
explicit per-coordinate statement and proves the reduction for both existing
critical-line energies:

* **The generic reduction.**  `CoordinateEnvelopeFit env μ crtError charError`
  says that the square of an envelope `env` fits the arithmetic budget.  Any
  actual energy `E` with `E n ≤ env n` then satisfies
  `CoordinateEnergyBudget E μ crtError charError`.  The energy is only tied to
  `env` through the existing estimate; it is never set to zero and no energy
  index is hidden in the fit.
* **The Mellin route.**  `mellinEnergy` is the Plancherel residue norm of
  `RandomizedL19Energy`, and `mellinEnergy_le_envelope` is the existing
  critical-line GRH estimate.  `coordinateEnergyBudget_of_mellinEnvelope`
  therefore gives the budget from `MellinCoordinateFit`, which is exactly the
  scalar inequality `mellinEnvelope ^ 2 ≤ (crtError + charError) * μ ^ 2`.
* **The sharp grid-prefix route.**  `gridPrefixEnergy` is the `L²` norm of the
  maximal sharp-prefix Fourier coefficient over the residue/frequency grid, the
  left-hand side of `primeBinProducts_gridPrefix_from_critical_line`.
  `gridPrefixEnergy_le_envelope` is the existing critical-line estimate, and
  `coordinateEnergyBudget_of_gridPrefixEnvelope` gives the budget from
  `GridPrefixCoordinateFit`, again only the square of the explicit envelope
  compared with the arithmetic budget.

The file also records that the generic fit is *exact*:
`CoordinateEnergyBudget E μ crtError charError` and
`CoordinateEnvelopeFit E μ crtError charError` are the same proposition, so the
reduction loses nothing.

No `sorry`, `admit`, `axiom`, `native_decide`, and no energy or error is set to
zero.
-/

namespace Cogentic.RandomizedL20_2CoordinateEnergy

open Filter Real
open scoped BigOperators Classical
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Sub
open Cogentic.RandomizedL20_2Char
open Cogentic.RandomizedL19Energy
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.Window

/-! ## 1. The smallest explicit per-coordinate energy statement -/

/-- **The smallest remaining per-coordinate energy input.**  An envelope `env`
for the actual coordinate energy has its square inside the CRT plus
smooth-character budget.  There is no character index, no cell index and no
hidden energy: the actual energy will be bounded by `env` separately through the
existing analytic estimate. -/
def CoordinateEnvelopeFit (env μ crtError charError : ℕ → ℝ) : Prop :=
  ∀ n, env n ^ 2 ≤ (crtError n + charError n) * μ n ^ 2

/-- The generic fit is exactly the coordinate energy budget with the energy
replaced by its envelope.  This records that the reduction below loses nothing:
the only remaining content is the scalar comparison of the squared envelope with
the arithmetic budget. -/
theorem coordinateEnergyBudget_iff_envelope
    {E μ crtError charError : ℕ → ℝ} :
    CoordinateEnergyBudget E μ crtError charError ↔
      CoordinateEnvelopeFit E μ crtError charError :=
  Iff.rfl

/-- **The generic reduction.**  If the squared actual energy is bounded by the
squared envelope and the squared envelope fits the arithmetic budget, then the
coordinate energy budget holds.  No sign hypothesis on `E` is needed because the
hypothesis is stated on squares. -/
theorem coordinateEnergyBudget_of_sq_le_envelope
    {E env μ crtError charError : ℕ → ℝ}
    (hE : ∀ n, E n ^ 2 ≤ env n ^ 2)
    (hfit : CoordinateEnvelopeFit env μ crtError charError) :
    CoordinateEnergyBudget E μ crtError charError :=
  fun n => (hE n).trans (hfit n)

/-- **The generic reduction from a nonnegative pointwise envelope.**  This is
the shape produced by the critical-line estimates: the actual energy is a norm
and is at most the explicit envelope. -/
theorem coordinateEnergyBudget_of_le_envelope
    {E env μ crtError charError : ℕ → ℝ}
    (hE : ∀ n, 0 ≤ E n) (hle : ∀ n, E n ≤ env n)
    (hfit : CoordinateEnvelopeFit env μ crtError charError) :
    CoordinateEnergyBudget E μ crtError charError :=
  coordinateEnergyBudget_of_sq_le_envelope
    (fun n => pow_le_pow_left₀ (hE n) (hle n) 2) hfit

/-- The same reduction with an absolute-value envelope, for energies whose
nonnegativity is not available at the call site. -/
theorem coordinateEnergyBudget_of_abs_le_envelope
    {E env μ crtError charError : ℕ → ℝ}
    (hle : ∀ n, |E n| ≤ env n)
    (hfit : CoordinateEnvelopeFit env μ crtError charError) :
    CoordinateEnergyBudget E μ crtError charError :=
  coordinateEnergyBudget_of_sq_le_envelope
    (fun n => by
      have h := pow_le_pow_left₀ (abs_nonneg (E n)) (hle n) 2
      rwa [sq_abs] at h) hfit

/-! ## 2. The Mellin Plancherel energy -/

/-- The Mellin coordinate energy is nonnegative: it is a Euclidean norm. -/
theorem mellinEnergy_nonneg (q : ℕ) (hq : q ≠ 0) {ι : Type} [Fintype ι]
    [DecidableEq ι] (A B : ι → ℕ) (σ t : ℝ) :
    0 ≤ mellinEnergy q hq A B σ t := by
  unfold mellinEnergy
  exact Real.sqrt_nonneg _

/-- **The explicit scalar fit for the Mellin energy.**  The square of the
critical-line Plancherel envelope is at most the CRT plus smooth-character
budget times `μ ^ 2`.  This is the only remaining inequality on this route. -/
def MellinCoordinateFit (line : DirichletLZerosOnLine) (q : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (B : ι → ℕ) (t : ℕ → ℝ)
    (μ crtError charError : ℕ → ℝ) : Prop :=
  CoordinateEnvelopeFit (fun n => mellinEnvelope q (mellinK line) B (t n))
    μ crtError charError

/-- **`CoordinateEnergyBudget` from the existing Mellin estimate.**  The actual
coordinate energy is `mellinEnergy`, and `mellinEnergy_le_envelope` is the
critical-line GRH estimate.  The only remaining input is `MellinCoordinateFit`,
the scalar comparison of the squared envelope with the budget. -/
theorem coordinateEnergyBudget_of_mellinEnvelope
    (line : DirichletLZerosOnLine) (q : ℕ) (hq : q ≠ 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ)
    (hB : ∀ i, 2 ≤ B i) (hAB : ∀ i, A i ≤ B i)
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (σ t : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n)
    {μ crtError charError : ℕ → ℝ}
    (hfit : MellinCoordinateFit line q B t μ crtError charError) :
    CoordinateEnergyBudget
      (fun n => mellinEnergy q hq A B (σ n) (t n))
      μ crtError charError := by
  refine coordinateEnergyBudget_of_le_envelope
    (fun n => mellinEnergy_nonneg q hq A B (σ n) (t n)) ?_ hfit
  intro n
  exact mellinEnergy_le_envelope line q hq A B hB hAB hdisj (σ n) (t n) (hσ n)

/-- The Mellin reduction in the same `primeBinMellinEnergy` shape used by
`RandomizedL20_2Char`, with the actual Plancherel residue energy normalized by
the square root exactly as in `coordinateEnergyBudget_of_mellinEnvelope` of
`RandomizedL20_2Saddle`.  The constant is the one extracted from the existing
critical-line estimate, so the fit is stated with that same constant. -/
theorem exists_coordinateEnergyBudget_of_primeBinMellinEnvelope
    (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
        (A B : ι → ℕ), (∀ i, 2 ≤ B i) → (∀ i, A i ≤ B i) →
        (Pairwise fun i j =>
          Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        ∀ (σ t : ℕ → ℝ), (∀ n, 0 ≤ σ n) →
        ∀ {μ crtError charError : ℕ → ℝ},
        (∀ n,
          (∏ i, K * Real.sqrt (B i) *
            (1 + Real.log (q * ((B i : ℝ) + |t n| + 2))) ^ 3) ^ 2 ≤
            (crtError n + charError n) * μ n ^ 2) →
        CoordinateEnergyBudget
          (fun n => Real.sqrt
            (primeBinMellinEnergy q A B ((σ n : ℂ) + t n * Complex.I)))
          μ crtError charError := by
  obtain ⟨K, hK, hfit⟩ := primeBinMellinEnergy_le_of_fit line
  refine ⟨K, hK, ?_⟩
  intro q _ ι _ _ A B hB hAB hdisj σ t hσ μ crtError charError hbudget n
  have hE := hfit q A B hB hAB hdisj (σ n) (t n) (hσ n) (hbudget n)
  have hnonneg :
      0 ≤ primeBinMellinEnergy q A B ((σ n : ℂ) + t n * Complex.I) := by
    unfold primeBinMellinEnergy
    positivity
  rwa [Real.sq_sqrt hnonneg]

/-! ## 3. The sharp grid-prefix energy -/

/-- **The explicit scalar fit for the sharp grid-prefix energy.**  The square of
the grid-prefix envelope is at most the CRT plus smooth-character budget times
`μ ^ 2`. -/
def GridPrefixCoordinateFit (m B : ℕ) (C K : ℝ) (X : ℕ → ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ)
    (μ crtError charError : ℕ → ℝ) : Prop :=
  CoordinateEnvelopeFit (fun n => gridPrefixEnvelope m B C K (X n) A U)
    μ crtError charError

/-- **`CoordinateEnergyBudget` from the existing sharp grid-prefix estimate.**
The actual coordinate energy is `gridPrefixEnergy`, and
`gridPrefixEnergy_le_envelope` is
`primeBinProducts_gridPrefix_from_critical_line` packaged with its explicit
envelope.  The only remaining input is `GridPrefixCoordinateFit`. -/
theorem coordinateEnergyBudget_of_gridPrefixEnvelope
    (line : DirichletLZerosOnLine) (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    (cop : m.Coprime B) (X : ℕ → ℝ) (cutoffs : ℕ → Finset ℕ)
    (hne : ∀ n, (cutoffs n).Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ)
    (hU : ∀ i, 2 ≤ U i) (hAU : ∀ i, A i ≤ U i)
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (U i)) (primeBin (A j) (U j)))
    (hX : ∀ n, 2 ≤ X n) (heX : ∀ n, Real.exp 1 ≤ X n)
    (hcut : ∀ n j, j ∈ cutoffs n →
      X n ≤ (j : ℝ) + 1 / 2 ∧ (j : ℝ) + 1 / 2 ≤ 2 * X n)
    (hP : ∀ n k, k ∈ primeBinProducts A U →
      X n ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * X n)
    {μ crtError charError : ℕ → ℝ}
    (hfit : GridPrefixCoordinateFit m B (prefixC m B hm hB line)
      (prefixK m B hm hB line) X A U μ crtError charError) :
    CoordinateEnergyBudget
      (fun n => gridPrefixEnergy m B hm hB cop (X n) (cutoffs n) (hne n) A U)
      μ crtError charError := by
  refine coordinateEnergyBudget_of_le_envelope
    (fun n => gridPrefixEnergy_nonneg m B hm hB cop (X n) (cutoffs n) (hne n) A U)
    ?_ hfit
  intro n
  exact gridPrefixEnergy_le_envelope line m B hm hB cop (X n) (cutoffs n)
    (hne n) A U (hX n) (heX n) (hcut n) (hP n) hU hAU hdisj

/-! ## 4. Axiom audit -/

#print axioms coordinateEnergyBudget_iff_envelope
#print axioms coordinateEnergyBudget_of_sq_le_envelope
#print axioms coordinateEnergyBudget_of_le_envelope
#print axioms coordinateEnergyBudget_of_abs_le_envelope
#print axioms mellinEnergy_nonneg
#print axioms coordinateEnergyBudget_of_mellinEnvelope
#print axioms exists_coordinateEnergyBudget_of_primeBinMellinEnvelope
#print axioms coordinateEnergyBudget_of_gridPrefixEnvelope

end Cogentic.RandomizedL20_2CoordinateEnergy
