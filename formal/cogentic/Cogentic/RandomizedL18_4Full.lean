import Cogentic.RandomizedL18_4LargeSieveInputs
import Cogentic.RandomizedL18_4CellData
import Cogentic.RandomizedL18_4Mass
import Cogentic.RandomizedL18_4ThinAggregate

/-!
# L18.4: the full certificate

This file composes the four L18.4 sub-certificates into one `L18_4Certificate`
whose `toInputs` is a literal `L18_4Inputs` with all four analytic fields
discharged:

* `large_sieve` from `LargeSieveCertificate` (Plancherel/Bessel summation plus
  the rational-cell lattice count);
* `cell_prime_count` from `CellData` (the actual prime count in the canonical
  integer cell, via the critical-line prime-bin supply);
* `cell_numerator_count` from `MassErrorInputs` (the root-progression count of
  the actual numerator pool);
* `thin_pair_fraction` from `ThinAggregate` (the determinant-level strip count,
  the rational-good mark count and the fixed power margin).

The ambient scales, the explicit `D^{O(1)}` exponents, the upper bounds and the
growth-rate domination `W_dominates` remain explicit fields, as allowed by the
wave-7 brief (W43).  The three `LargeSieveCertificate`/`CellData`/`MassErrorInputs`
data are matched to the ambient data through the explicit adapter equalities
`hS2` (`S2 = secondMoment`) and `hNcell` (`Ncell = CellData.Ncell`).

`ThinAggregate` is stated for a full `L18_4Inputs`, while the input is what this
file is constructing.  To break the resulting type dependency, the raw fields of
the aggregate are bundled as `ThinAggregateData`; the same three counting
arguments are replayed there (`ThinAggregateData.strip_count`,
`mark_count`, `cutoff_in_range`), and the final `L18_4Inputs` is obtained by
`replaceThinPairFraction` with the genuine `ThinAggregate` built over it, so the
final thin bound is the aggregate's own `thin_pair_fraction`.

Nothing is a `sorry`, an `axiom` or a `native_decide`; no loss is set to zero.
-/

namespace Cogentic.RandomizedL18_4

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.Randomized

/-! ## 1. The ambient L18.4 data -/

/-- All the data fields of `L18_4Inputs` together with the explicit scales,
positivity/nonnegativity facts, the `D^{O(1)}` upper bounds and the growth-rate
domination `W_dominates`.  The four analytic proof fields are *not* part of this
record: they are discharged by the sub-certificates. -/
structure L18_4Ambient where
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
  /-- Upper support factor. -/
  M : ℕ → ℝ
  /-- Undivided multiplicity-one convolution energy. -/
  Econv : ℕ → ℝ
  /-- Summed second moment of the numerator counts. -/
  S2 : ℕ → ℝ
  /-- Minimum number of denominators in a cell. -/
  Ncell : ℕ → ℝ
  /-- Minimum number of numerator points per denominator. -/
  Nnum : ℕ → ℝ
  /-- The relative thin / small-determinant pair fraction. -/
  thin : ℕ → ℝ
  cW : ℝ
  cC : ℝ
  cM : ℝ
  cE : ℝ
  cd : ℝ
  cell : ℝ
  cρ : ℝ
  W_nonneg : ∀ n, 0 ≤ W n
  d_pos : ∀ n, 0 < d n
  ell_pos : ∀ n, 0 < ell n
  rho_pos : ∀ n, 0 < rho n
  C_pos : ∀ n, 0 < C n
  M_pos : ∀ n, 0 < M n
  Econv_nonneg : ∀ n, 0 ≤ Econv n
  S2_nonneg : ∀ n, 0 ≤ S2 n
  Ncell_nonneg : ∀ n, 0 ≤ Ncell n
  Nnum_nonneg : ∀ n, 0 ≤ Nnum n
  thin_nonneg : ∀ n, 0 ≤ thin n
  cW_nonneg : 0 ≤ cW
  cC_nonneg : 0 ≤ cC
  cM_nonneg : 0 ≤ cM
  cE_nonneg : 0 ≤ cE
  cd_nonneg : 0 ≤ cd
  cell_nonneg : 0 ≤ cell
  cρ_nonneg : 0 ≤ cρ
  W_upper : ∀ n, W n ≤ exp (cW * scale n)
  C_upper : ∀ n, C n ≤ exp (cC * scale n)
  M_upper : ∀ n, M n ≤ exp (cM * scale n)
  Econv_upper : ∀ n, Econv n ≤ exp (cE * scale n)
  d_upper : ∀ n, d n ≤ exp (cd * scale n)
  ell_upper : ∀ n, ell n ≤ exp (cell * scale n)
  rho_inv_upper : ∀ n, 1 / rho n ≤ exp (cρ * scale n)
  W_dominates : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, c * scale n ≤ W n

/-- Assemble a literal `L18_4Inputs` from the ambient data and the four analytic
proof fields. -/
noncomputable def L18_4Ambient.toInputs (A : L18_4Ambient)
    (large_sieve : ∀ n,
      A.S2 n ≤ A.C n * (A.M n * denomScale A.W n ^ 2) * (A.Econv n / A.d n))
    (cell_prime_count : ∀ n,
      denomScale A.W n / (2 * A.d n * cellMesh A.W n * (1 + A.W n)) ≤ A.Ncell n)
    (cell_numerator_count : ∀ n,
      denomScale A.W n * A.rho n / (2 * A.ell n) ≤ A.Nnum n)
    (thin_pair_fraction : ∀ n, A.thin n ≤ 1 / cellMesh A.W n) :
    L18_4Inputs where
  W := A.W
  d := A.d
  ell := A.ell
  rho := A.rho
  C := A.C
  M := A.M
  Econv := A.Econv
  S2 := A.S2
  Ncell := A.Ncell
  Nnum := A.Nnum
  thin := A.thin
  cW := A.cW
  cC := A.cC
  cM := A.cM
  cE := A.cE
  cd := A.cd
  cell := A.cell
  cρ := A.cρ
  W_nonneg := A.W_nonneg
  d_pos := A.d_pos
  ell_pos := A.ell_pos
  rho_pos := A.rho_pos
  C_pos := A.C_pos
  M_pos := A.M_pos
  Econv_nonneg := A.Econv_nonneg
  S2_nonneg := A.S2_nonneg
  Ncell_nonneg := A.Ncell_nonneg
  Nnum_nonneg := A.Nnum_nonneg
  thin_nonneg := A.thin_nonneg
  cW_nonneg := A.cW_nonneg
  cC_nonneg := A.cC_nonneg
  cM_nonneg := A.cM_nonneg
  cE_nonneg := A.cE_nonneg
  cd_nonneg := A.cd_nonneg
  cell_nonneg := A.cell_nonneg
  cρ_nonneg := A.cρ_nonneg
  large_sieve := large_sieve
  cell_prime_count := cell_prime_count
  cell_numerator_count := cell_numerator_count
  thin_pair_fraction := thin_pair_fraction
  W_upper := A.W_upper
  C_upper := A.C_upper
  M_upper := A.M_upper
  Econv_upper := A.Econv_upper
  d_upper := A.d_upper
  ell_upper := A.ell_upper
  rho_inv_upper := A.rho_inv_upper
  W_dominates := A.W_dominates

/-! ## 2. The raw data of `ThinAggregate` -/

/-- The data fields of `ThinAggregate`, stated directly in terms of the ambient
functions instead of a full `L18_4Inputs`.  The field types are exactly those of
`ThinAggregate` after unfolding the projections of the input; this is what lets
the final `L18_4Inputs` be assembled before the `ThinAggregate` term exists. -/
structure ThinAggregateData (W d ell rho thin Ncell Nnum : ℕ → ℝ) where
  /-- The lattice box model of the retained marks at each stage. -/
  box : ℕ → LatticeBox
  /-- The reference density `ρ` of the numerator progression. -/
  dens : ℕ → ℝ
  /-- The reference density is positive. -/
  dens_pos : ∀ n, 0 < dens n
  /-- The reference density is at most one. -/
  dens_le_one : ∀ n, dens n ≤ 1
  /-- The root index is the geometric modulus. -/
  ell_eq : ∀ n, ell n = ((box n).q : ℝ)
  /-- `thin` is at most the normalized number of ordered strip pairs. -/
  thin_le_pairFraction : ∀ n, thin n ≤
    ((stripPairSet (box n).S
      (denomScale W n ^ 2 / thinCutoff W (fun m => (box m).L) dens n)).card : ℝ) /
      (((box n).S.card : ℝ) ^ 2)
  /-- The rational-good cell marks are retained. -/
  retained_cell_count : ∀ n, cellMesh W n * Ncell n * Nnum n ≤ ((box n).S.card : ℝ)
  /-- Constant bookkeeping for `mark_count`. -/
  const_le : ∀ n, 4 * d n * dens n ≤ rho n
  /-- The fixed power margin `2 q (1 + log V) ≤ ρ V²/K`. -/
  power_margin : ∀ n,
    2 * ((box n).q : ℝ) * (1 + W n) ≤ dens n * denomScale W n ^ 2 / cellMesh W n

namespace ThinAggregateData

variable {W d ell rho thin Ncell Nnum : ℕ → ℝ}

/-- The geometric modulus `q` of the raw aggregate. -/
noncomputable def q (T : ThinAggregateData W d ell rho thin Ncell Nnum) (n : ℕ) : ℝ :=
  ((T.box n).q : ℝ)

/-- The per-level solution bound `L₀`. -/
noncomputable def L (T : ThinAggregateData W d ell rho thin Ncell Nnum) (n : ℕ) : ℝ :=
  (T.box n).L

/-- The retained mark set. -/
noncomputable def S (T : ThinAggregateData W d ell rho thin Ncell Nnum) (n : ℕ) :
    Finset (ℤ × ℤ) := (T.box n).S

/-- The number of retained marks. -/
noncomputable def R (T : ThinAggregateData W d ell rho thin Ncell Nnum) (n : ℕ) : ℝ :=
  ((T.box n).S.card : ℝ)

/-- The per-level bound is at least one. -/
theorem L_ge_one (T : ThinAggregateData W d ell rho thin Ncell Nnum) (n : ℕ) :
    1 ≤ T.L n := by
  have hb : (0 : ℝ) < ((T.box n).bmin : ℝ) := by exact_mod_cast (T.box n).bmin_pos
  have hd : (0 : ℝ) ≤ ((T.box n).hi - (T.box n).lo : ℤ) := by
    exact_mod_cast sub_nonneg.mpr (T.box n).lo_le_hi
  have h0 : (0 : ℝ) ≤ ((T.box n).hi - (T.box n).lo : ℤ) / ((T.box n).bmin : ℝ) :=
    div_nonneg hd hb.le
  have := (T.box n).level_bound
  rw [L]
  linarith

/-- **`strip_count` for the raw data.**  Identical to
`ThinAggregate.strip_count`, with the ambient denominators substituted for the
input's projections. -/
theorem strip_count (T : ThinAggregateData W d ell rho thin Ncell Nnum) (n : ℕ)
    {k : ℝ} (hk : 0 < k) :
    ((stripPairSet (T.S n) (denomScale W n ^ 2 / k)).card : ℝ) ≤
      (1 + 2 * T.L n * (denomScale W n ^ 2 / (T.q n * k))) * T.R n := by
  have hX : 0 ≤ denomScale W n ^ 2 / k := div_nonneg (sq_nonneg _) hk.le
  have h := stripPairSet_card_le (T.box n) hX
  have harg : (denomScale W n ^ 2 / k) / ((T.box n).q : ℝ) =
      denomScale W n ^ 2 / (T.q n * k) := by
    rw [q]
    have hq : ((T.box n).q : ℝ) ≠ 0 := by
      exact_mod_cast (T.box n).q_pos.ne'
    field_simp
  rw [harg] at h
  simpa [L, S, R, q] using h

/-- **`mark_count` for the raw data.**  The cell denominator and numerator lower
bounds, the retained-cell inclusion and the constant comparison give
`ρ V²/(q (1 + log V)) ≤ R`. -/
theorem mark_count (T : ThinAggregateData W d ell rho thin Ncell Nnum)
    (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 0 < d n) (hrho : ∀ n, 0 < rho n)
    (hNc : ∀ n, denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤ Ncell n)
    (hNn : ∀ n, denomScale W n * rho n / (2 * ell n) ≤ Nnum n) (n : ℕ) :
    T.dens n * (denomScale W n ^ 2 / (T.q n * (1 + W n))) ≤ T.R n := by
  have hV : 0 < denomScale W n := by unfold denomScale; exact exp_pos _
  have hK : 0 < cellMesh W n := by unfold cellMesh; exact exp_pos _
  have hq : 0 < T.q n := by
    rw [q]
    exact_mod_cast (T.box n).q_pos
  have h1W : 0 < 1 + W n := by linarith [hW n]
  have hNc' : denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤ Ncell n := hNc n
  have hNn' : denomScale W n * rho n / (2 * T.q n) ≤ Nnum n := by
    have h := hNn n
    rw [T.ell_eq n] at h
    exact h
  have hprod := ThinAggregate.mark_count_arith hV (hrho n) (hd n) hK hq h1W hNc' hNn'
    (T.const_le n)
  calc
    T.dens n * (denomScale W n ^ 2 / (T.q n * (1 + W n))) ≤
        cellMesh W n * Ncell n * Nnum n := hprod
    _ ≤ T.R n := T.retained_cell_count n

/-- **`cutoff_in_range` for the raw data.**  The fixed power margin makes the
determinant cutoff carry at least one level. -/
theorem cutoff_in_range (T : ThinAggregateData W d ell rho thin Ncell Nnum)
    (hW : ∀ n, 0 ≤ W n) (n : ℕ) :
    1 ≤ 2 * T.L n *
      (denomScale W n ^ 2 / (T.q n * thinCutoff W T.L T.dens n)) := by
  have hK : 0 < cellMesh W n := by unfold cellMesh; exact exp_pos _
  have hL : 0 < T.L n := lt_of_lt_of_le zero_lt_one (T.L_ge_one n)
  have hdens : 0 < T.dens n := T.dens_pos n
  have hq : 0 < T.q n := by
    rw [q]
    exact_mod_cast (T.box n).q_pos
  have h1W : 0 < 1 + W n := by linarith [hW n]
  have hthin_ne : thinCutoff W T.L T.dens n ≠ 0 := by
    unfold thinCutoff
    positivity
  have hcell_ne : cellMesh W n ≠ 0 := hK.ne'
  have hL_ne : T.L n ≠ 0 := hL.ne'
  have hdens_ne : T.dens n ≠ 0 := hdens.ne'
  have h1W_ne : (1 + W n) ≠ 0 := h1W.ne'
  have hq_ne : T.q n ≠ 0 := hq.ne'
  have hid : 2 * T.L n *
        (denomScale W n ^ 2 / (T.q n * thinCutoff W T.L T.dens n)) =
      T.dens n * denomScale W n ^ 2 /
        (2 * T.q n * (1 + W n) * cellMesh W n) := by
    unfold thinCutoff
    field_simp
    ring
  rw [hid]
  rw [le_div_iff₀ (by positivity)]
  have hp := T.power_margin n
  have hmul := mul_le_mul_of_nonneg_right hp hK.le
  rw [div_mul_cancel₀ _ hcell_ne] at hmul
  simpa [q, mul_assoc] using hmul

/-- Assemble the `ThinPairInputs` record from the raw aggregate data and the two
cell count fields. -/
noncomputable def toThinPairInputs (T : ThinAggregateData W d ell rho thin Ncell Nnum)
    (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 0 < d n) (hrho : ∀ n, 0 < rho n)
    (hNc : ∀ n, denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤ Ncell n)
    (hNn : ∀ n, denomScale W n * rho n / (2 * ell n) ≤ Nnum n) :
    ThinPairInputs W thin where
  q := T.q
  dens := T.dens
  R := T.R
  L := T.L
  thinPairs := fun n k => ((stripPairSet (T.S n) (denomScale W n ^ 2 / k)).card : ℝ)
  W_nonneg := hW
  q_pos := fun n => by
    rw [q]
    exact_mod_cast (T.box n).q_pos
  dens_pos := T.dens_pos
  dens_le_one := T.dens_le_one
  R_pos := fun n => by
    have hq : 0 < T.q n := by
      rw [q]
      exact_mod_cast (T.box n).q_pos
    have hV : 0 < denomScale W n := by unfold denomScale; exact exp_pos _
    have h1W : 0 < 1 + W n := by linarith [hW n]
    have hpos : 0 < T.dens n *
        (denomScale W n ^ 2 / (T.q n * (1 + W n))) :=
      mul_pos (T.dens_pos n) (div_pos (pow_pos hV 2) (mul_pos hq h1W))
    exact lt_of_lt_of_le hpos (T.mark_count hW hd hrho hNc hNn n)
  L_ge_one := T.L_ge_one
  thinPairs_nonneg := fun n X => Nat.cast_nonneg _
  thin_le_pairFraction := T.thin_le_pairFraction
  strip_count := fun n k hk => T.strip_count n hk
  cutoff_in_range := T.cutoff_in_range hW
  mark_count := T.mark_count hW hd hrho hNc hNn

/-- **`thin_pair_fraction` from the raw aggregate data.**  The final thin bound
`thin ≤ 1/K` is the aggregate's own conclusion. -/
theorem thin_pair_fraction (T : ThinAggregateData W d ell rho thin Ncell Nnum)
    (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 0 < d n) (hrho : ∀ n, 0 < rho n)
    (hNc : ∀ n, denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤ Ncell n)
    (hNn : ∀ n, denomScale W n * rho n / (2 * ell n) ≤ Nnum n) (n : ℕ) :
    thin n ≤ 1 / cellMesh W n :=
  (T.toThinPairInputs hW hd hrho hNc hNn).thin_pair_fraction n

/-- Interpret the raw aggregate data as an actual `ThinAggregate` over an input
whose data functions are exactly the raw parameters.  The equality arguments are
all definitional in the composition below. -/
noncomputable def toThinAggregate (T : ThinAggregateData W d ell rho thin Ncell Nnum)
    (I : L18_4Inputs)
    (hW : W = I.W) (hd : d = I.d) (hell : ell = I.ell) (hrho : rho = I.rho)
    (hthin : thin = I.thin) (hNcell : Ncell = I.Ncell) (hNnum : Nnum = I.Nnum) :
    ThinAggregate I := by
  subst hW hd hell hrho hthin hNcell hNnum
  exact
    { box := T.box
      dens := T.dens
      dens_pos := T.dens_pos
      dens_le_one := T.dens_le_one
      ell_eq := T.ell_eq
      thin_le_pairFraction := T.thin_le_pairFraction
      retained_cell_count := T.retained_cell_count
      const_le := T.const_le
      power_margin := T.power_margin }

end ThinAggregateData

/-! ## 3. The full certificate -/

/-- **The L18.4 full certificate.**  Ambient data plus the four sub-certificates.
The explicit adapter equalities are `hS2` (identifying the second moment with the
residue energy of the large-sieve certificate) and `hNcell` (identifying the cell
count with the actual prime count of the `CellData` cell). -/
structure L18_4Certificate extends L18_4Ambient where
  /-- The large-sieve certificate: residue energy and rational-cell lattice count. -/
  largeSieve : LargeSieveCertificate W d C M Econv
  /-- Adapter: `S2` is the certificate's residue energy. -/
  hS2 : ∀ n, S2 n = largeSieve.secondMoment n
  /-- The canonical denominator cell. -/
  cellData : CellData W d
  /-- Adapter: `Ncell` is the actual prime count of the cell. -/
  hNcell : ∀ n, Ncell n = cellData.Ncell n
  /-- The prime-bin supply constant. -/
  cellK0 : ℝ
  /-- The supply constant is nonnegative. -/
  cellK0_nonneg : 0 ≤ cellK0
  /-- The critical-line prime-bin supply. -/
  cellSupply : ∀ {A B : ℕ}, 2 ≤ A → A ≤ B → ∀ {lg : ℝ}, 0 < lg →
    Real.log (B : ℝ) ≤ lg →
    cellK0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
        ((B : ℝ) - (A : ℝ)) / 2 →
      ((B : ℝ) - (A : ℝ)) / (2 * lg) ≤ ((primeBin A B).card : ℝ)
  /-- The square-root error fits in the cell width. -/
  cellSupplyFit : ∀ n,
    2 * d n * cellK0 * (1 + Real.log 3 + W n) ^ 2 ≤ cellMesh W n
  /-- The numerator-pool counting inputs. -/
  mass : MassErrorInputs W ell rho
  /-- The root residue of the numerator progression. -/
  numR : ∀ n, (ZMod (mass.q n))ˣ
  /-- The numerator pool is coprime to the root modulus. -/
  numCoprime : ∀ n m,
    m ∈ numeratorPool (mass.A n) (mass.B n) (mass.patterns n) → m.Coprime (mass.q n)
  /-- `Nnum` is the actual root-residue count. -/
  numEq : ∀ n, Nnum n =
    (progressionCount (mass.A n) (mass.B n) (mass.patterns n) (mass.q n) (numR n) : ℝ)
  /-- The RH progression deviation of the actual count. -/
  numDeviation : ∀ n,
    |(progressionCount (mass.A n) (mass.B n) (mass.patterns n) (mass.q n) (numR n) : ℝ) -
      (coprimeCount (mass.A n) (mass.B n) (mass.patterns n) (mass.q n) : ℝ) /
        (mass.q n).totient| ≤
      progressionError mass.K (mass.q n) (mass.B n) (mass.patterns n)
  /-- The raw data of the `ThinAggregate` sub-certificate. -/
  thinData : ThinAggregateData W d ell rho thin Ncell Nnum

namespace L18_4Certificate

/-- **The composed `L18_4Inputs`.**  All four analytic fields are proved from the
sub-certificates:
`large_sieve` from `largeSieve`/`hS2`, `cell_prime_count` from
`cellData`/`hNcell`/the prime-bin supply, `cell_numerator_count` from `mass`, and
`thin_pair_fraction` from the genuine `ThinAggregate` built over the resulting
input. -/
noncomputable def toInputs (C : L18_4Certificate) : L18_4Inputs :=
  let hls : ∀ n,
      C.S2 n ≤ C.C n * (C.M n * denomScale C.W n ^ 2) * (C.Econv n / C.d n) :=
    (LargeSieveInputs.of_certificate C.largeSieve C.hS2).large_sieve_all
  let hcp : ∀ n,
      denomScale C.W n / (2 * C.d n * cellMesh C.W n * (1 + C.W n)) ≤ C.Ncell n := by
    intro n
    rw [C.hNcell n]
    exact cell_prime_count_of_cellData C.cellK0_nonneg C.cellSupply C.W_nonneg
      C.d_pos C.cellData C.cellSupplyFit n
  let hcn : ∀ n, denomScale C.W n * C.rho n / (2 * C.ell n) ≤ C.Nnum n := fun n =>
    (C.mass.toNumeratorCountInputs C.Nnum C.numR C.numCoprime C.numEq
      C.numDeviation).numerator_count n
  let hthin : ∀ n, C.thin n ≤ 1 / cellMesh C.W n := fun n =>
    C.thinData.thin_pair_fraction C.W_nonneg C.d_pos C.rho_pos hcp hcn n
  let I : L18_4Inputs := C.toL18_4Ambient.toInputs hls hcp hcn hthin
  let thinAgg : ThinAggregate I :=
    C.thinData.toThinAggregate I rfl rfl rfl rfl rfl rfl rfl
  I.replaceThinPairFraction thinAgg.toThinPairInputs

/-- **The L18.4 `D^{-B}` deficit** for the composed inputs. -/
theorem subexpLoss (C : L18_4Certificate) : SubexpLoss C.toInputs.loss :=
  C.toInputs.subexpLoss

/-- **The composed L18.4 `SubexpLeaf`.** -/
noncomputable def toSubexpLeaf (C : L18_4Certificate) : SubexpLeaf :=
  C.toInputs.toSubexpLeaf

/-- **The `B = 2` slot bound** for the composed inputs. -/
theorem slot_le (C : L18_4Certificate) {slots : C5LossSlots}
    (h : slots .rationalGoodEnvironments = C.toInputs.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .rationalGoodEnvironments n ≤ exp (-(2 : ℝ) * scale n) :=
  C.toInputs.slot_le h

end L18_4Certificate

/-! ## Axiom audit -/

#print axioms ThinAggregateData.mark_count
#print axioms ThinAggregateData.cutoff_in_range
#print axioms ThinAggregateData.toThinPairInputs
#print axioms ThinAggregateData.thin_pair_fraction
#print axioms ThinAggregateData.toThinAggregate
#print axioms L18_4Certificate.toInputs
#print axioms L18_4Certificate.subexpLoss
#print axioms L18_4Certificate.toSubexpLeaf
#print axioms L18_4Certificate.slot_le

end Cogentic.RandomizedL18_4
