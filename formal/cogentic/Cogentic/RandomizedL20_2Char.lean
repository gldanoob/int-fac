import Cogentic.RandomizedL20_2Sub
import Cogentic.RandomizedPrimeProductPlancherel
import Cogentic.RandomizedPrimeBinRelativeError

set_option linter.style.haveILetI false

/-!
# L20.2: reducing the smooth-character inputs

`Cogentic.RandomizedL20_2Sub` leaves two smooth-character objects as
paper-level fields of `L20_2SubInputs`:

* `char_sum : SmoothCharacterSumBound charError cChar`, the abstract statement
  that the smooth-character error budget decays like `exp (-c D log D)`;
* `offdiag_budget : SmoothCharacterOffDiagonalBudget E₁ E₂ μ crtError charError`,
  the abstract statement that the coupled-mode product `E₁ E₂` fits inside the
  CRT plus smooth-character budget times `μ²`.

This file reduces both to concrete statements about *actual* character sums and
*actual* second-moment energies, and connects the character side to the GRH
prime-bin estimates that already exist in the repository.

## The reductions

1. **Concrete smooth-character sums** (`SmoothCharacterData`,
   `smoothCharacterError`).  At each ledger index we record a finite smooth
   support, a complex weight, and the total mass of the weight.  The normalized
   nonprincipal character error is the supremum of
   `‖∑ m ∈ support, χ m * w m‖ / mass` over nonprincipal `χ`.  It is a genuine
   relative error: `smoothCharacterError D ≤ 1` is proved from the total-mass
   bound, so it is not a placeholder.
2. **`SmoothCharacterSumBound` reduced** (`smoothCharacterSumBound_of_concrete`):
   if every nonprincipal sum is at most `exp (-c D log D) · mass`, then the
   abstract budget `SmoothCharacterSumBound (fun n => smoothCharacterError (data n)) c`
   holds.  The supremum definition is what makes the abstract decay statement
   a consequence of the concrete sums.
3. **Prime-bin GRH reduction** (`primeBinProducts_twist_le`,
   `primeBinConcreteEstimate_of_productBound`).  For the product sets
   `primeBinProducts A B`, the existing `PrimeBinProductBound` gives the
   unnormalized GRH envelope.  The only remaining input is the *explicit*
   `PrimeBinCharacterDecay`: the GRH envelope is at most
   `exp (-c D log D)` times the product-set cardinality.  That inequality is
   stated in terms of exactly the quantities appearing in
   `Randomized.primeBin_product_from_critical_line`, so the paper-level input
   is entirely explicit.  `centeredResidueEnergy_le_of_smoothCharacterError`
   also converts the concrete character bound into the Plancherel residue
   energy, so the character and energy sides use the same object.
4. **Off-diagonal budget reduced** (`CoordinateEnergyBudget`,
   `smoothCharacterOffDiagonalBudget_of_coordinateEnergy`).  The product
   `E₁ E₂` is bounded by the CRT plus smooth-character budget whenever each
   one-coordinate squared energy is bounded by that budget; the proof is AM–GM,
   `2 E₁ E₂ ≤ E₁² + E₂²`.
5. **Existing GRH prime-bin energy feeds the coordinates**
   (`primeBinMellinEnergy`, `primeBinMellinEnergy_le_of_fit`).  The existing
   L² residue energy estimate
   `Randomized.primeBinProducts_mellin_energy_from_critical_line` bounds the
   explicit `primeBinMellinEnergy`.  If that explicit envelope fits the budget,
   the coordinate energy does too.
6. **The reduced bundle** (`L20_2CharInputs`, `toSubInputs`, `toInputs`,
   `toConcentrationLeaf`).  The two abstract smooth-character fields are
   replaced by concrete data and energy bounds, and the original `L20_2Inputs`
   (hence the `ConcentrationLeaf` and the `B = 2` ledger slot) is rebuilt.

No `sorry`, `admit`, `axiom`, or `native_decide`.  The error is the actual
normalized character error and the actual coordinate energy; nothing is set to
zero by fiat.
-/

namespace Cogentic.RandomizedL20_2Char

open Filter Real
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Sub
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.Window

/-! ## 1. Concrete smooth-character sums -/

/-- The data of a smooth character sum at one ledger index: a finite smooth
support, a complex weight, and the total mass of the weight.  The total-mass
bound makes `smoothCharacterError` a genuine relative error. -/
structure SmoothCharacterData where
  /-- The modulus of the Dirichlet characters. -/
  q : ℕ
  /-- The finite smooth support. -/
  support : Finset ℕ
  /-- The complex weight (for example `n ↦ n^{-s}`). -/
  weight : ℕ → ℂ
  /-- The total mass `∑ ‖weight m‖` upper bound. -/
  mass : ℝ
  /-- The mass is positive. -/
  mass_pos : 0 < mass
  /-- The mass dominates the total absolute weight. -/
  total_le : ∑ m ∈ support, ‖weight m‖ ≤ mass

/-- The normalized nonprincipal character error of a smooth support: the
supremum of `‖twist support weight χ‖ / mass` over nonprincipal characters. -/
noncomputable def smoothCharacterError (D : SmoothCharacterData) : ℝ :=
  sSup { x : ℝ | ∃ χ : DirichletCharacter ℂ D.q, χ ≠ 1 ∧
    x = ‖twist D.support D.weight χ‖ / D.mass }

/-- The trivial absolute bound: the twisted sum is at most the total mass. -/
theorem twist_norm_le_mass (D : SmoothCharacterData) (χ : DirichletCharacter ℂ D.q) :
    ‖twist D.support D.weight χ‖ ≤ D.mass := by
  unfold twist
  calc
    ‖∑ n ∈ D.support, χ n * D.weight n‖
        ≤ ∑ n ∈ D.support, ‖χ n * D.weight n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ D.support, ‖D.weight n‖ := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
    _ ≤ D.mass := D.total_le

/-- The normalized character error is nonnegative. -/
theorem smoothCharacterError_nonneg (D : SmoothCharacterData) :
    0 ≤ smoothCharacterError D := by
  apply Real.sSup_nonneg
  intro x hx
  obtain ⟨χ, _, rfl⟩ := hx
  exact div_nonneg (norm_nonneg _) D.mass_pos.le

/-- If every nonprincipal twisted sum is at most `B · mass`, then the
normalized character error is at most `B`. -/
theorem smoothCharacterError_le (D : SmoothCharacterData) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ χ : DirichletCharacter ℂ D.q, χ ≠ 1 →
      ‖twist D.support D.weight χ‖ ≤ B * D.mass) :
    smoothCharacterError D ≤ B := by
  apply Real.sSup_le _ hB
  intro x hx
  obtain ⟨χ, hχ, rfl⟩ := hx
  rw [div_le_iff₀ D.mass_pos]
  exact h χ hχ

/-- The smooth-character error is a genuine relative error: it is at most one.
This uses only the total-mass bound, no analytic input. -/
theorem smoothCharacterError_le_one (D : SmoothCharacterData) :
    smoothCharacterError D ≤ 1 := by
  apply smoothCharacterError_le D zero_le_one
  intro χ _
  simpa using twist_norm_le_mass D χ

/-- **From a smooth-character bound to the Plancherel energy.**  If the
normalized smooth-character error is at most `B`, then the centered residue
vector has squared energy at most `(B · mass)²`.  This is
`Randomized.classMass_centered_sq_le` applied to the concrete support and
weight, so the character side and the energy side use the same object. -/
theorem centeredResidueEnergy_le_of_smoothCharacterError
    (D : SmoothCharacterData) [NeZero D.q] {B : ℝ}
    (h : smoothCharacterError D ≤ B) :
    ∑ r : (ZMod D.q)ˣ, ‖classMass D.support D.weight r -
        twist D.support D.weight (1 : DirichletCharacter ℂ D.q) / D.q.totient‖ ^ 2 ≤
      (B * D.mass) ^ 2 := by
  have hbdd : BddAbove { x : ℝ | ∃ χ : DirichletCharacter ℂ D.q, χ ≠ 1 ∧
      x = ‖twist D.support D.weight χ‖ / D.mass } := by
    refine ⟨1, ?_⟩
    rintro x ⟨χ, _, rfl⟩
    rw [div_le_one D.mass_pos]
    exact twist_norm_le_mass D χ
  apply classMass_centered_sq_le
  intro χ hχ
  have hmem : ‖twist D.support D.weight χ‖ / D.mass ∈
      { x : ℝ | ∃ χ : DirichletCharacter ℂ D.q, χ ≠ 1 ∧
        x = ‖twist D.support D.weight χ‖ / D.mass } := ⟨χ, hχ, rfl⟩
  have hle : ‖twist D.support D.weight χ‖ / D.mass ≤ B :=
    (le_csSup hbdd hmem).trans h
  rw [div_le_iff₀ D.mass_pos] at hle
  exact hle

/-- **`SmoothCharacterSumBound` reduced.**  A uniform exponential bound on the
concrete smooth-character sums implies the abstract L20.2 error-budget
statement with `charError n = smoothCharacterError (data n)`. -/
theorem smoothCharacterSumBound_of_concrete
    (data : ℕ → SmoothCharacterData) {c : ℝ} (hc : 0 < c)
    (h : ∀ n (χ : DirichletCharacter ℂ (data n).q), χ ≠ 1 →
      ‖twist (data n).support (data n).weight χ‖ ≤
        exp (-c * paperD n * scale n) * (data n).mass) :
    SmoothCharacterSumBound (fun n => smoothCharacterError (data n)) c := by
  refine ⟨hc, fun n => ⟨smoothCharacterError_nonneg (data n), ?_⟩⟩
  exact smoothCharacterError_le (data n) (exp_pos _).le (fun χ hχ => h n χ hχ)

/-! ## 2. Reduction to the existing GRH prime-bin estimate -/

/-- The explicit GRH prime-bin character envelope from
`Randomized.primeBin_product_from_critical_line`. -/
noncomputable def primeBinRelativeEnvelope (K : ℝ) (q : ℕ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (_A B : ι → ℕ) : ℝ :=
  ∏ i, 2 * K * (1 + Real.log (3 * q * B i)) ^ 2 * Real.sqrt (B i)

/-- The remaining explicit analytic input for a prime-bin product set: the GRH
envelope is at most the manuscript rate `exp (-c D log D)` times the number of
distinct integer products.  This is exactly Lemma G.2's decay applied to the
product set. -/
def PrimeBinCharacterDecay (K c : ℝ) (q : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (n : ℕ) : Prop :=
  primeBinRelativeEnvelope K q A B ≤
    exp (-c * paperD n * scale n) * ((primeBinProducts A B).card : ℝ)

/-- The existing `PrimeBinProductBound` controls the *unnormalized* twist of a
product set.  This is the GRH character estimate in the form consumed below. -/
theorem primeBinProducts_twist_le (hb : PrimeBinProductBound) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ),
        (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
        (Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        ‖twist (primeBinProducts A B) (fun _ => 1) χ‖ ≤
          primeBinRelativeEnvelope K q A B := by
  obtain ⟨K, hK, hbound⟩ := hb
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ ι _ _ A B hA hAB hdisj
  have h := hbound q χ hχ A B hA hAB
  rw [← primeBinProducts_character_sum χ A B hdisj] at h
  simpa [twist, primeBinRelativeEnvelope, mul_one] using h

/-- **Prime-bin smooth-character estimate.**  The existing GRH product bound
together with the explicit decay of its envelope gives the concrete
smooth-character estimate on the product set. -/
theorem primeBinConcreteEstimate_of_decay
    {K c : ℝ}
    (hbound : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ),
        (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
        (Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        ‖twist (primeBinProducts A B) (fun _ => 1) χ‖ ≤
          primeBinRelativeEnvelope K q A B)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ)
    (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    {n : ℕ} (hdecay : PrimeBinCharacterDecay K c q A B n) :
    ‖twist (primeBinProducts A B) (fun _ => 1) χ‖ ≤
      exp (-c * paperD n * scale n) * ((primeBinProducts A B).card : ℝ) :=
  (hbound q χ hχ A B hA hAB hdisj).trans hdecay

/-- **Reduction to the existing GRH estimate.**  From `PrimeBinProductBound`
one obtains a constant `K` such that the concrete smooth-character estimate on
every admissible product set follows from the explicit decay
`PrimeBinCharacterDecay K c`. -/
theorem primeBinConcreteEstimate_of_productBound (hb : PrimeBinProductBound) {c : ℝ} :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ),
        (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
        (Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        ∀ {n : ℕ}, PrimeBinCharacterDecay K c q A B n →
        ‖twist (primeBinProducts A B) (fun _ => 1) χ‖ ≤
          exp (-c * paperD n * scale n) * ((primeBinProducts A B).card : ℝ) := by
  obtain ⟨K, _hK, hbound⟩ := primeBinProducts_twist_le hb
  exact ⟨K, _hK, fun q _ χ hχ ι _ _ A B hA hAB hdisj n hdecay =>
    primeBinConcreteEstimate_of_decay hbound hχ A B hA hAB hdisj hdecay⟩

/-! ## 3. The off-diagonal budget reduced to coordinate energies -/

/-- The per-coordinate energy input for the G.10 off-diagonal estimate: each
one-coordinate squared second moment fits the CRT plus smooth-character budget
times `μ²`. -/
def CoordinateEnergyBudget (E μ crtError charError : ℕ → ℝ) : Prop :=
  ∀ n, E n ^ 2 ≤ (crtError n + charError n) * μ n ^ 2

/-- **`SmoothCharacterOffDiagonalBudget` reduced.**  If both coordinate
energies fit the budget, then their product does: AM–GM gives
`2 E₁ E₂ ≤ E₁² + E₂² ≤ 2 (crtError + charError) μ²`. -/
theorem smoothCharacterOffDiagonalBudget_of_coordinateEnergy
    {E₁ E₂ μ crtError charError : ℕ → ℝ}
    (h₁ : CoordinateEnergyBudget E₁ μ crtError charError)
    (h₂ : CoordinateEnergyBudget E₂ μ crtError charError) :
    SmoothCharacterOffDiagonalBudget E₁ E₂ μ crtError charError := by
  intro n
  have hsum : E₁ n ^ 2 + E₂ n ^ 2 ≤
      2 * ((crtError n + charError n) * μ n ^ 2) := by
    linarith only [h₁ n, h₂ n]
  have hamgm : 2 * (E₁ n * E₂ n) ≤ E₁ n ^ 2 + E₂ n ^ 2 := by
    nlinarith only [sq_nonneg (E₁ n - E₂ n)]
  linarith only [hsum, hamgm]

/-- A version of the reduction starting from square-root envelopes, the shape
produced by a Plancherel energy estimate. -/
theorem smoothCharacterOffDiagonalBudget_of_sqrtEnvelope
    {E₁ E₂ μ crtError charError : ℕ → ℝ}
    (hE₂ : ∀ n, 0 ≤ E₂ n)
    (hμ : ∀ n, 0 ≤ (crtError n + charError n) * μ n ^ 2)
    (h₁ : ∀ n, E₁ n ≤ Real.sqrt ((crtError n + charError n) * μ n ^ 2))
    (h₂ : ∀ n, E₂ n ≤ Real.sqrt ((crtError n + charError n) * μ n ^ 2)) :
    SmoothCharacterOffDiagonalBudget E₁ E₂ μ crtError charError := by
  intro n
  have hprod : E₁ n * E₂ n ≤
      Real.sqrt ((crtError n + charError n) * μ n ^ 2) *
        Real.sqrt ((crtError n + charError n) * μ n ^ 2) :=
    mul_le_mul (h₁ n) (h₂ n) (hE₂ n) (Real.sqrt_nonneg _)
  rw [Real.mul_self_sqrt (hμ n)] at hprod
  exact hprod

/-! ## 4. Existing GRH prime-bin Mellin energy feeds the coordinates -/

/-- The explicit L² residue energy of a prime-bin product set at a complex
height.  This is the left-hand side of
`Randomized.primeBinProducts_mellin_energy_from_critical_line`. -/
noncomputable def primeBinMellinEnergy (q : ℕ) [NeZero q] {ι : Type}
    [Fintype ι] [DecidableEq ι] (A B : ι → ℕ) (s : ℂ) : ℝ :=
  ∑ r : (ZMod q)ˣ, ‖mellinClassError (primeBinProducts A B) s r‖ ^ 2

/-- The existing GRH prime-bin Mellin energy estimate, re-exported with the
explicit envelope. -/
theorem primeBinMellinEnergy_le (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
      (A B : ι → ℕ), (∀ i, 2 ≤ B i) → (∀ i, A i ≤ B i) →
      (Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
      ∀ σ t : ℝ, 0 ≤ σ →
      primeBinMellinEnergy q A B ((σ : ℂ) + t * Complex.I) ≤
        (∏ i, K * Real.sqrt (B i) *
          (1 + Real.log (q * ((B i : ℝ) + |t| + 2))) ^ 3) ^ 2 := by
  simpa only [primeBinMellinEnergy] using
    (primeBinProducts_mellin_energy_from_critical_line line)

/-- **The existing GRH energy fits the budget.**  If the explicit prime-bin
Mellin envelope is at most a budget `B`, then the corresponding residue energy
is at most `B`.  This is the precise bridge from the GRH prime-bin estimate to
a coordinate energy. -/
theorem primeBinMellinEnergy_le_of_fit (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
      (A B : ι → ℕ), (∀ i, 2 ≤ B i) → (∀ i, A i ≤ B i) →
      (Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
      ∀ σ t : ℝ, 0 ≤ σ → ∀ {budget : ℝ},
      (∏ i, K * Real.sqrt (B i) *
          (1 + Real.log (q * ((B i : ℝ) + |t| + 2))) ^ 3) ^ 2 ≤ budget →
      primeBinMellinEnergy q A B ((σ : ℂ) + t * Complex.I) ≤ budget := by
  obtain ⟨K, hK, h⟩ := primeBinMellinEnergy_le line
  exact ⟨K, hK, fun q _ ι _ _ A B hB hAB hdisj σ t hσ budget hfit =>
    (h q A B hB hAB hdisj σ t hσ).trans hfit⟩

/-! ## 5. The reduced L20.2 input bundle -/

/-- The L20.2 inputs with both smooth-character fields made concrete.  The
abstract `SmoothCharacterSumBound` and `SmoothCharacterOffDiagonalBudget` are
replaced by:

* `charData` and `char_concrete`: actual smooth-character sums at the
  manuscript rate;
* `energy₁` and `energy₂`: each coordinate energy fits the CRT plus
  (concrete) smooth-character budget.

The saddle point remains the Appendix C paper-level input. -/
structure L20_2CharInputs where
  /-- The saddle-point scale `Λ_d`. -/
  Λ : ℕ → ℝ
  /-- The ideal interior mean `μ`. -/
  μ : ℕ → ℝ
  /-- The proxy score bound `L`. -/
  L : ℕ → ℝ
  /-- The constant in `Λ ≥ c D log D`. -/
  cLam : ℝ
  /-- The constant in `μ ≥ exp (η Λ)`. -/
  η : ℝ
  /-- The smooth-character decay constant. -/
  cChar : ℝ
  /-- The smooth-character decay constant is positive. -/
  cChar_pos : 0 < cChar
  /-- The polynomial exponent constant in `L ≤ exp (cL (log D)^5)`. -/
  cL : ℝ
  /-- Appendix C, scale part (paper-level). -/
  saddle_scale : SaddlePointScaleLower Λ cLam
  /-- Appendix C, mean part (paper-level). -/
  saddle_mean : SaddlePointMeanLower μ Λ η
  /-- `L` is nonnegative. -/
  L_nonneg : ∀ n, 0 ≤ L n
  /-- The polynomial exponent constant is nonnegative. -/
  cL_nonneg : 0 ≤ cL
  /-- The polynomial proxy bound. -/
  L_upper : ∀ n, L n ≤ exp (cL * (scale n) ^ 5)
  /-- The concrete smooth-character data at each ledger index. -/
  charData : ℕ → SmoothCharacterData
  /-- The concrete smooth-character sums decay at the manuscript rate. -/
  char_concrete : ∀ n (χ : DirichletCharacter ℂ (charData n).q), χ ≠ 1 →
    ‖twist (charData n).support (charData n).weight χ‖ ≤
      exp (-cChar * paperD n * scale n) * (charData n).mass
  /-- The finite interior cell at each ledger index. -/
  cell : ∀ n, CellData n (L n)
  /-- The ideal mean is the actual mean of the cell. -/
  μ_eq : ∀ n, μ n = (cell n).mean (cell n).f
  /-- The proxy mean exceeds the actual mean by the geometric CRT error. -/
  proxy_error : ∀ n, (cell n).mean (cell n).proxy ≤ μ n + geometricCRTError n
  /-- The CRT error is dominated by the mean. -/
  proxy_error_le_mean : ∀ n, geometricCRTError n ≤ μ n
  /-- The first one-coordinate second-moment envelope. -/
  E₁ : ℕ → ℝ
  /-- The second one-coordinate second-moment envelope. -/
  E₂ : ℕ → ℝ
  /-- The coupled-mode Cauchy–Schwarz bound for the off-diagonal sum. -/
  coupled : OffDiagonalCoupledBound (fun n => (cell n).cross) E₁ E₂
  /-- The first coordinate energy fits the CRT plus smooth-character budget. -/
  energy₁ : ∀ n, E₁ n ^ 2 ≤
    (geometricCRTError n + smoothCharacterError (charData n)) * μ n ^ 2
  /-- The second coordinate energy fits the CRT plus smooth-character budget. -/
  energy₂ : ∀ n, E₂ n ^ 2 ≤
    (geometricCRTError n + smoothCharacterError (charData n)) * μ n ^ 2

namespace L20_2CharInputs

/-- The concrete smooth-character budget of the reduced bundle. -/
noncomputable def charError (S : L20_2CharInputs) : ℕ → ℝ :=
  fun n => smoothCharacterError (S.charData n)

/-- The reduced bundle builds the `L20_2SubInputs` bundle: the abstract
smooth-character fields are discharged from the concrete sums and energies. -/
noncomputable def toSubInputs (S : L20_2CharInputs) : L20_2SubInputs where
  Λ := S.Λ
  μ := S.μ
  L := S.L
  charError := S.charError
  cLam := S.cLam
  η := S.η
  cChar := S.cChar
  cL := S.cL
  saddle_scale := S.saddle_scale
  saddle_mean := S.saddle_mean
  L_nonneg := S.L_nonneg
  cL_nonneg := S.cL_nonneg
  L_upper := S.L_upper
  char_sum := smoothCharacterSumBound_of_concrete S.charData S.cChar_pos S.char_concrete
  cell := S.cell
  μ_eq := S.μ_eq
  proxy_error := S.proxy_error
  proxy_error_le_mean := S.proxy_error_le_mean
  E₁ := S.E₁
  E₂ := S.E₂
  coupled := S.coupled
  offdiag_budget :=
    smoothCharacterOffDiagonalBudget_of_coordinateEnergy S.energy₁ S.energy₂

/-- The reduced bundle builds the original `L20_2Inputs`. -/
noncomputable def toInputs (S : L20_2CharInputs) : L20_2Inputs :=
  S.toSubInputs.toInputs

/-- The concentration leaf built from the reduced inputs. -/
noncomputable def toConcentrationLeaf (S : L20_2CharInputs) : ConcentrationLeaf :=
  S.toInputs.toConcentrationLeaf

/-- The reduced bundle realizes the parent deficit exactly. -/
theorem toInputs_loss_eq (S : L20_2CharInputs) (n : ℕ) :
    S.toInputs.loss n =
      |(S.cell n).mean (S.cell n).f - (S.cell n).mean (S.cell n).proxy| / S.μ n :=
  rfl

/-- The reduced bundle's deficit is nonnegative. -/
theorem loss_nonneg (S : L20_2CharInputs) (n : ℕ) : 0 ≤ S.toInputs.loss n :=
  S.toInputs.loss_nonneg n

/-- The `B = 2` ledger slot for the reduced inputs. -/
theorem slot_le (S : L20_2CharInputs) :
    ∀ᶠ n : ℕ in atTop,
      S.toInputs.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.toInputs.slot_le

end L20_2CharInputs

/-! ## Axiom audit -/

#print axioms twist_norm_le_mass
#print axioms smoothCharacterError_nonneg
#print axioms smoothCharacterError_le
#print axioms smoothCharacterError_le_one
#print axioms centeredResidueEnergy_le_of_smoothCharacterError
#print axioms smoothCharacterSumBound_of_concrete
#print axioms primeBinProducts_twist_le
#print axioms primeBinConcreteEstimate_of_decay
#print axioms primeBinConcreteEstimate_of_productBound
#print axioms smoothCharacterOffDiagonalBudget_of_coordinateEnergy
#print axioms smoothCharacterOffDiagonalBudget_of_sqrtEnvelope
#print axioms primeBinMellinEnergy_le
#print axioms primeBinMellinEnergy_le_of_fit
#print axioms L20_2CharInputs.toSubInputs
#print axioms L20_2CharInputs.toInputs
#print axioms L20_2CharInputs.toConcentrationLeaf
#print axioms L20_2CharInputs.toInputs_loss_eq
#print axioms L20_2CharInputs.loss_nonneg
#print axioms L20_2CharInputs.slot_le

end Cogentic.RandomizedL20_2Char
