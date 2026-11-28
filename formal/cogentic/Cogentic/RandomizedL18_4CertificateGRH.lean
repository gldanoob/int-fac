import Cogentic.RandomizedL18_4Inhabitant
import Cogentic.RandomizedPaperEndpointWave31

/-!
# L18.4: a paper-regime certificate from the critical line

`RandomizedL18_4Inhabitant` reduces `L18_4Certificate` to two residuals of the
concrete toy core `iCore`: growth of its constant `W`, and the critical-line
prime-bin supply.  This file removes both by replacing the toy core with a
paper-regime construction: `W` grows like `(scale n)^2`, the denominator cell is
the integer cell `(2, floor V]`, the numerator pool is the actual prime bin
`(2, floor V]`, and the thin marks are `R` explicit primitive points with
`R >= K Ncell Nnum`.

The critical line supplies both the prime-bin constant `K0` and the progression
constant `Kmass = patternK (patternProgression_of_critical_line line)`.  A single
threshold `T(K0, Kmass)` (the point where the exponential `exp (x/4)` absorbs
every polynomial in `K0`, `Kmass` and `x`) makes all pointwise inequalities hold
at `W n = max T ((scale n)^2)`.  The supply fit is then pointwise, the cell and
numerator counts are actual prime counts, and the thin fraction is `1/R`.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count, mass,
error or loss is set to zero.
-/

namespace Cogentic.RandomizedL18_4

open Filter Real
open scoped BigOperators ENNReal
open Cogentic.Randomized
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedOneThirdAsymptotic

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-! ## 1. The paper-regime threshold -/

/-- The elementary regime facts needed at a logarithmic scale `x = log V`:
`exp x` is large, and `exp (x/4)` absorbs the supply error at `K0` and the mass
error at `Kmass`. -/
structure PaperRegime (K0 Kmass x : ℝ) : Prop where
  one_le : 1 ≤ x
  exp_ge_six : 6 ≤ Real.exp x
  exp_quarter_ge_sixteen : 16 ≤ Real.exp (1 / 4 * x)
  supply_small :
    32 * K0 * (1 + Real.log 3 + x) ^ 2 ≤ Real.exp (1 / 4 * x)
  mass_small :
    4096 * Kmass * (1 + Real.log 3 + x) ^ 2 ≤ Real.exp (1 / 4 * x)
  poly_sq : (1 + x) ^ 2 ≤ Real.exp (1 / 4 * x)
  linear : 16 * (1 + x) ≤ Real.exp x
  power : 32 * (1 + x) ^ 2 ≤ Real.exp (7 / 4 * x)

/-- **The paper-regime threshold.**  For fixed nonnegative `K0`, `Kmass` there is
a scale `T` beyond which every polynomial factor is dominated by `exp (x/4)`. -/
theorem exists_paperRegime (K0 Kmass : ℝ) (hK0 : 0 ≤ K0) (hKm : 0 ≤ Kmass) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ x : ℝ, T ≤ x → PaperRegime K0 Kmass x := by
  have hsupply : ∀ᶠ x : ℝ in atTop,
      32 * K0 * (1 + Real.log 3 + x) ^ 2 ≤ Real.exp (1 / 4 * x) :=
    exp_eventually_dominates_supply_polynomial (C := 32 * K0) (c := (1 / 4 : ℝ))
      (by positivity) (by norm_num)
  have hmass : ∀ᶠ x : ℝ in atTop,
      4096 * Kmass * (1 + Real.log 3 + x) ^ 2 ≤ Real.exp (1 / 4 * x) :=
    exp_eventually_dominates_supply_polynomial (C := 4096 * Kmass)
      (c := (1 / 4 : ℝ)) (by positivity) (by norm_num)
  have hpoly : ∀ᶠ x : ℝ in atTop, (1 + x) ^ 2 ≤ Real.exp (1 / 4 * x) := by
    have h := exp_eventually_dominates_supply_polynomial (C := (1 : ℝ))
      (c := (1 / 4 : ℝ)) zero_le_one (by norm_num)
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hbase : 1 + x ≤ 1 + Real.log 3 + x := by linarith
    have hsq : (1 + x) ^ 2 ≤ (1 + Real.log 3 + x) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hbase 2
    have hx' : (1 + Real.log 3 + x) ^ 2 ≤ Real.exp (1 / 4 * x) := by
      simpa [one_mul] using hx
    exact hsq.trans hx' 
  have hlin : ∀ᶠ x : ℝ in atTop, 16 * (1 + x) ≤ Real.exp x := by
    have h := exp_eventually_dominates_supply_polynomial (C := (16 : ℝ))
      (c := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hbase : 1 + x ≤ 1 + Real.log 3 + x := by linarith
    have hnn : 0 ≤ 1 + x := by linarith
    have hsq : 1 + x ≤ (1 + Real.log 3 + x) ^ 2 := by
      have h1 : 1 + x ≤ (1 + Real.log 3 + x) := by linarith
      have h2 : (1 + Real.log 3 + x) ≤ (1 + Real.log 3 + x) ^ 2 := by
        have h3 : 1 ≤ 1 + Real.log 3 + x := by linarith
        nlinarith only [h3]
      exact h1.trans h2
    have hstep : 16 * (1 + x) ≤ 16 * (1 + Real.log 3 + x) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    calc
      16 * (1 + x) ≤ 16 * (1 + Real.log 3 + x) ^ 2 := hstep
      _ ≤ Real.exp (1 / 2 * x) := hx
      _ = Real.exp x / Real.exp (x / 2) := by
        rw [← Real.exp_sub]
        congr 1
        ring
      _ ≤ Real.exp x := by
        have hpos : 0 < Real.exp (x / 2) := Real.exp_pos _
        have hge' : 1 ≤ Real.exp (x / 2) :=
          Real.one_le_exp (by linarith : (0 : ℝ) ≤ x / 2)
        exact div_le_self (Real.exp_pos x).le hge'
  have hpow : ∀ᶠ x : ℝ in atTop, 32 * (1 + x) ^ 2 ≤ Real.exp (7 / 4 * x) := by
    have h := exp_eventually_dominates_supply_polynomial (C := (32 : ℝ))
      (c := (7 / 4 : ℝ)) (by norm_num) (by norm_num)
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hbase : 1 + x ≤ 1 + Real.log 3 + x := by linarith
    have hsq : (1 + x) ^ 2 ≤ (1 + Real.log 3 + x) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hbase 2
    calc
      32 * (1 + x) ^ 2 ≤ 32 * (1 + Real.log 3 + x) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ ≤ Real.exp (7 / 4 * x) := hx
  have hx1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have hx6 : ∀ᶠ x : ℝ in atTop, 6 ≤ Real.exp x := by
    filter_upwards [eventually_ge_atTop (Real.log 6)] with x hx
    calc
      6 = Real.exp (Real.log 6) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp x := Real.exp_le_exp.mpr hx
  have hx16 : ∀ᶠ x : ℝ in atTop, 16 ≤ Real.exp (1 / 4 * x) := by
    filter_upwards [eventually_ge_atTop (4 * Real.log 16)] with x hx
    calc
      16 = Real.exp (Real.log 16) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (1 / 4 * x) := by
        apply Real.exp_le_exp.mpr
        linarith
  have hall : ∀ᶠ x : ℝ in atTop, PaperRegime K0 Kmass x := by
    filter_upwards [hx1, hx6, hx16, hsupply, hmass, hpoly, hlin, hpow] with
      x h1 h6 h16 hs hm hp hl hw
    exact ⟨h1, h6, h16, hs, hm, hp, hl, hw⟩
  obtain ⟨T, hT⟩ := eventually_atTop.1 hall
  refine ⟨max T 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro x hx
  exact hT x ((le_max_left _ _).trans hx)

/-! ## 2. The paper-regime data -/

/-- The critical-line prime-bin supply constant. -/
noncomputable def paperK0 (line : DirichletLZerosOnLine) : ℝ := cellK0OfLine line

/-- The progression bound supplied by the critical line. -/
theorem paperProg (line : DirichletLZerosOnLine) : PrimePatternProgressionBound :=
  patternProgression_of_critical_line line

/-- The progression error constant. -/
noncomputable def paperKmass (line : DirichletLZerosOnLine) : ℝ :=
  patternK (paperProg line)

theorem paperK0_nonneg (line : DirichletLZerosOnLine) : 0 ≤ paperK0 line :=
  cellK0OfLine_nonneg line

theorem paperKmass_nonneg (line : DirichletLZerosOnLine) : 0 ≤ paperKmass line :=
  patternK_nonneg (paperProg line)

/-- The paper-regime threshold, chosen from the existence lemma. -/
noncomputable def paperT (line : DirichletLZerosOnLine) : ℝ :=
  Classical.choose (exists_paperRegime (paperK0 line) (paperKmass line)
    (paperK0_nonneg line) (paperKmass_nonneg line))

theorem paperT_nonneg (line : DirichletLZerosOnLine) : 0 ≤ paperT line :=
  (Classical.choose_spec (exists_paperRegime (paperK0 line) (paperKmass line)
    (paperK0_nonneg line) (paperKmass_nonneg line))).1

theorem paperT_spec (line : DirichletLZerosOnLine) {x : ℝ} (hx : paperT line ≤ x) :
    PaperRegime (paperK0 line) (paperKmass line) x :=
  (Classical.choose_spec (exists_paperRegime (paperK0 line) (paperKmass line)
    (paperK0_nonneg line) (paperKmass_nonneg line))).2 x hx

/-- The logarithmic denominator scale `W = max T (scale n)^2`. -/
noncomputable def paperW (line : DirichletLZerosOnLine) (n : ℕ) : ℝ :=
  max (paperT line) ((scale n) ^ 2)

/-- `V = exp W`. -/
noncomputable def paperV (line : DirichletLZerosOnLine) (n : ℕ) : ℝ :=
  Real.exp (paperW line n)

/-- `K = V^{1/4} = exp (W/4)`. -/
noncomputable def paperK (line : DirichletLZerosOnLine) (n : ℕ) : ℝ :=
  Real.exp (paperW line n / 4)

/-- `1 + log V`. -/
noncomputable def paperC (line : DirichletLZerosOnLine) (n : ℕ) : ℝ :=
  1 + paperW line n

/-- The field degree, equal to `1/4`. -/
noncomputable def paperD (line : DirichletLZerosOnLine) (n : ℕ) : ℝ := 1 / 4

/-- The root index, equal to `1`. -/
noncomputable def paperEll (line : DirichletLZerosOnLine) (n : ℕ) : ℝ := 1

/-- The reference density `1/(16 (1 + log V))`. -/
noncomputable def paperRho (line : DirichletLZerosOnLine) (n : ℕ) : ℝ :=
  1 / (16 * paperC line n)

/-- The integer upper endpoint `floor V`. -/
noncomputable def paperB (line : DirichletLZerosOnLine) (n : ℕ) : ℕ :=
  Nat.floor (paperV line n)

/-- The guaranteed lower population of the numerator bin, `floor (V/(8(1+log V)))`. -/
noncomputable def paperM (line : DirichletLZerosOnLine) (n : ℕ) : ℕ :=
  Nat.floor (paperV line n / (8 * paperC line n))

theorem paperW_ge_T (line : DirichletLZerosOnLine) (n : ℕ) :
    paperT line ≤ paperW line n := le_max_left _ _

theorem paperW_ge_scale_sq (line : DirichletLZerosOnLine) (n : ℕ) :
    (scale n) ^ 2 ≤ paperW line n := le_max_right _ _

theorem paperW_nonneg (line : DirichletLZerosOnLine) (n : ℕ) : 0 ≤ paperW line n :=
  (paperT_nonneg line).trans (paperW_ge_T line n)

theorem paperRegime (line : DirichletLZerosOnLine) (n : ℕ) :
    PaperRegime (paperK0 line) (paperKmass line) (paperW line n) :=
  paperT_spec line (paperW_ge_T line n)

theorem paperV_eq_exp (line : DirichletLZerosOnLine) (n : ℕ) :
    paperV line n = Real.exp (paperW line n) := rfl

theorem paperK_eq_exp (line : DirichletLZerosOnLine) (n : ℕ) :
    paperK line n = Real.exp (paperW line n / 4) := rfl

theorem paperV_pos (line : DirichletLZerosOnLine) (n : ℕ) : 0 < paperV line n :=
  Real.exp_pos _

theorem paperK_pos (line : DirichletLZerosOnLine) (n : ℕ) : 0 < paperK line n :=
  Real.exp_pos _

theorem paperC_pos (line : DirichletLZerosOnLine) (n : ℕ) : 0 < paperC line n := by
  have h := (paperRegime line n).one_le
  unfold paperC
  linarith

theorem paperC_nonneg (line : DirichletLZerosOnLine) (n : ℕ) : 0 ≤ paperC line n :=
  (paperC_pos line n).le

theorem paperRho_pos (line : DirichletLZerosOnLine) (n : ℕ) : 0 < paperRho line n := by
  unfold paperRho
  exact div_pos zero_lt_one (mul_pos (by norm_num) (paperC_pos line n))

theorem paperB_le_V (line : DirichletLZerosOnLine) (n : ℕ) :
    (paperB line n : ℝ) ≤ paperV line n :=
  Nat.floor_le (paperV_pos line n).le

theorem paperB_two_le (line : DirichletLZerosOnLine) (n : ℕ) : 2 ≤ paperB line n := by
  have h6 : (6 : ℝ) ≤ paperV line n := (paperRegime line n).exp_ge_six
  have h2 : (2 : ℝ) ≤ paperV line n := by linarith
  exact Nat.le_floor h2

theorem paperB_ge_V_sub_one (line : DirichletLZerosOnLine) (n : ℕ) :
    paperV line n < (paperB line n : ℝ) + 1 :=
  Nat.lt_floor_add_one _


/-! ## 3. The denominator cell and the large sieve -/

/-- The paper-regime denominator cell `(2, floor V]`.  Its width is at least
`V/(dK)` because `K = exp (W/4) >= 16`, and its upper endpoint is `floor V <= V`. -/
noncomputable def paperCellData (line : DirichletLZerosOnLine) :
    CellData (paperW line) (paperD line) where
  A := fun _ => 2
  B := paperB line
  A_two := by intro n; norm_num
  A_le_B := by intro n; exact paperB_two_le line n
  B_le_V := by
    intro n
    simpa only [denomScale, paperV_eq_exp] using paperB_le_V line n
  width := by
    intro n
    have hK16' : 16 ≤ Real.exp ((1 / 4 : ℝ) * paperW line n) :=
      (paperRegime line n).exp_quarter_ge_sixteen
    have hK16 : (16 : ℝ) ≤ paperK line n := by
      simpa [paperK, div_eq_mul_inv, mul_comm] using hK16' 
    have hV6 : (6 : ℝ) ≤ paperV line n := by
      simpa [paperV] using (paperRegime line n).exp_ge_six
    have hB := paperB_ge_V_sub_one line n
    have hKpos : 0 < paperK line n := paperK_pos line n
    have hVpos : 0 < paperV line n := paperV_pos line n
    have hden : paperD line n * paperK line n = paperK line n / 4 := by
      unfold paperD
      ring
    have hcore : (4 : ℝ) / paperK line n ≤ 4 / 16 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hK16
    have hstep : paperV line n / (paperD line n * paperK line n) ≤ paperV line n / 4 := by
      have hden' : paperD line n * paperK line n = paperK line n / 4 := hden
      rw [hden']
      have heq : paperV line n / (paperK line n / 4) = paperV line n * (4 / paperK line n) := by
        field_simp [hKpos.ne']
      rw [heq]
      calc
        paperV line n * (4 / paperK line n) ≤ paperV line n * (4 / 16) :=
          mul_le_mul_of_nonneg_left hcore hVpos.le
        _ = paperV line n / 4 := by ring
    have hBge : paperV line n - 3 ≤ (paperB line n : ℝ) - 2 := by linarith
    have h34 : paperV line n / 4 ≤ paperV line n - 3 := by nlinarith only [hV6]
    calc
      denomScale (paperW line) n / (paperD line n * cellMesh (paperW line) n) =
          paperV line n / (paperD line n * paperK line n) := rfl
      _ ≤ paperV line n / 4 := hstep
      _ ≤ paperV line n - 3 := h34
      _ ≤ (paperB line n : ℝ) - 2 := hBge

/-- `Ncell` is the actual prime count of the cell `(2, floor V]`. -/
noncomputable def paperNcell (line : DirichletLZerosOnLine) (n : ℕ) : ℝ :=
  (paperCellData line).Ncell n

theorem paperNcell_nonneg (line : DirichletLZerosOnLine) (n : ℕ) :
    0 ≤ paperNcell line n :=
  (paperCellData line).Ncell_nonneg n

/-- The concrete large-sieve certificate at the paper-regime `W`: one cell,
modulus `3`, numerator set `{1}`, constant weight `1`, `A = 1`, `perCell = 1`. -/
noncomputable def paperLargeSieve (line : DirichletLZerosOnLine) :
    LargeSieveCertificate.{0} (paperW line) (paperD line) (fun _ => 1) (fun _ => 1)
      (fun _ => 1) where
  ι := fun _ => PUnit
  fintype := fun _ => inferInstance
  q := fun _ _ => 3
  q_ne_zero := by intro n i; norm_num
  P := fun _ _ => {1}
  w := fun _ _ _ => 1
  A := fun _ => 1
  A_nonneg := by intro n; norm_num
  spectral := by
    intro n i χ hχ
    simp [Cogentic.Window.twist]
  d_pos := by intro n; norm_num [paperD]
  Econv_nonneg := by intro n; norm_num
  nonempty := fun _ => ⟨PUnit.unit⟩
  perCell := fun _ => 1
  perCell_nonneg := by intro n; norm_num
  perCell_ge_one := by intro n; norm_num
  energy_le := by intro n; norm_num [paperD]
  latticeCount := by
    intro n
    have hV : 1 ≤ paperV line n := by
      have h6 : (6 : ℝ) ≤ Real.exp (paperW line n) := (paperRegime line n).exp_ge_six
      simpa [paperV] using (by linarith : (1 : ℝ) ≤ Real.exp (paperW line n))
    simp only [Pi.one_apply, Fintype.card_punit, Nat.cast_one, div_one, mul_one]
    rw [show denomScale (paperW line) n = paperV line n from rfl]
    have hpow : (1 : ℝ) ≤ (paperV line n) ^ 2 := one_le_pow₀ hV
    simpa using hpow

/-- The second moment is the residue energy of the concrete certificate. -/
noncomputable def paperS2 (line : DirichletLZerosOnLine) (n : ℕ) : ℝ :=
  (paperLargeSieve line).secondMoment n

theorem paperS2_nonneg (line : DirichletLZerosOnLine) (n : ℕ) : 0 ≤ paperS2 line n := by
  unfold paperS2 LargeSieveCertificate.secondMoment residueEnergy
  positivity

/-! ## 4. The numerator prime bin -/

/-- The lower endpoint of the single numerator bin. -/
noncomputable def paperMassA (line : DirichletLZerosOnLine) (n i : ℕ) : ℕ := 2

/-- The upper endpoint of the numerator bin: `floor V` at slot `0`, and the empty
bin `(2,2]` elsewhere. -/
noncomputable def paperMassB (line : DirichletLZerosOnLine) (n i : ℕ) : ℕ :=
  if i = 0 then paperB line n else 2

/-- The single occupied pattern `{0}`. -/
noncomputable def paperPatterns (line : DirichletLZerosOnLine) : ℕ → Finset (Finset ℕ) :=
  fun _ => {({0} : Finset ℕ)}

/-- The relative error parameter of the product saving. -/
noncomputable def paperU (line : DirichletLZerosOnLine) (n : ℕ) : ℝ :=
  64 * paperKmass line * (paperC line n) ^ 3

/-- The product scale of the product saving. -/
noncomputable def paperX (line : DirichletLZerosOnLine) (n : ℕ) : ℝ :=
  (paperB line n : ℝ) / 2

/-- The empty second bin. -/
theorem primeBin_two_two : primeBin 2 2 = (∅ : Finset ℕ) := by
  ext p
  simp [primeBin]

/-- The two bin slots used by the certificate are pairwise disjoint: slot `0` is
`(2, floor V]`, every other slot is the empty bin `(2,2]`. -/
theorem paperMass_disjoint (line : DirichletLZerosOnLine) (n : ℕ) :
    Pairwise fun i j =>
      Disjoint (primeBin (paperMassA line n i) (paperMassB line n i))
        (primeBin (paperMassA line n j) (paperMassB line n j)) := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · exact (hij hj.symm).elim
    · rw [show primeBin (paperMassA line n j) (paperMassB line n j) = ∅ by
        simp [paperMassA, paperMassB, hj, primeBin_two_two]]
      simp
  · rw [show primeBin (paperMassA line n i) (paperMassB line n i) = ∅ by
      simp [paperMassA, paperMassB, hi, primeBin_two_two]]
    simp

theorem paperMassA_two (line : DirichletLZerosOnLine) (n i : ℕ) :
    2 ≤ paperMassA line n i := by
  unfold paperMassA
  norm_num

theorem paperMassA_le_B (line : DirichletLZerosOnLine) (n i : ℕ) :
    paperMassA line n i ≤ paperMassB line n i := by
  unfold paperMassA paperMassB
  split_ifs
  · exact paperB_two_le line n
  · norm_num

/-- **The prime count of the numerator bin.**  The critical-line supply, the
pointwise supply fit and the cell width give at least `V/(4(1+log V))` primes in
`(2, floor V]`. -/
theorem paperBin_count_lower (line : DirichletLZerosOnLine) (n : ℕ) :
    paperV line n / (4 * paperC line n) ≤ ((primeBin 2 (paperB line n)).card : ℝ) := by
  have hK0 : 0 ≤ paperK0 line := paperK0_nonneg line
  have hsupply : PrimeBinSupply (paperK0 line) := cellK0OfLine_supply line
  have hB2 : 2 ≤ paperB line n := paperB_two_le line n
  have hBV : (paperB line n : ℝ) ≤ Real.exp (paperW line n) := by
    simpa [paperV] using paperB_le_V line n
  have hWnn : 0 ≤ paperW line n := paperW_nonneg line n
  have hdpos : (0 : ℝ) < (1 / 4 : ℝ) := by norm_num
  have hsmall : 2 * (1 / 4 : ℝ) * paperK0 line *
      (1 + Real.log 3 + paperW line n) ^ 2 ≤ Real.exp (paperW line n / 4) := by
    have hreg := (paperRegime line n).supply_small
    have hnonneg : 0 ≤ (1 + Real.log 3 + paperW line n) ^ 2 := sq_nonneg _
    have hcoef : 2 * (1 / 4 : ℝ) * paperK0 line ≤ 32 * paperK0 line := by
      nlinarith only [hK0]
    calc
      2 * (1 / 4 : ℝ) * paperK0 line * (1 + Real.log 3 + paperW line n) ^ 2
          ≤ (32 * paperK0 line) * (1 + Real.log 3 + paperW line n) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef hnonneg
      _ ≤ Real.exp (paperW line n / 4) := by
        simpa [mul_assoc, div_eq_mul_inv, mul_comm, mul_left_comm] using hreg
  have hsupplyErr := primeBin_supply_of_cell_width hK0 hWnn hdpos hB2 hBV hsmall
  have hwidth : paperV line n / ((1 / 4 : ℝ) * paperK line n) ≤
      (paperB line n : ℝ) - 2 := by
    simpa [paperD, paperV, paperK, denomScale, cellMesh, paperCellData] using
      (paperCellData line).width n
  have herr : paperK0 line * (1 + Real.log (3 * (paperB line n : ℝ))) ^ 2 *
      Real.sqrt (paperB line n : ℝ) ≤ ((paperB line n : ℝ) - 2) / 2 := by
    have h1 : paperK0 line * (1 + Real.log (3 * (paperB line n : ℝ))) ^ 2 *
        Real.sqrt (paperB line n : ℝ) ≤
        (Real.exp (paperW line n) / ((1 / 4 : ℝ) * Real.exp (paperW line n / 4))) / 2 := by
      simpa [paperV, paperK] using hsupplyErr
    have h2 : (Real.exp (paperW line n) / ((1 / 4 : ℝ) * Real.exp (paperW line n / 4))) / 2 =
        paperV line n / ((1 / 4 : ℝ) * paperK line n) / 2 := rfl
    rw [h2] at h1
    linarith only [h1, hwidth]
  have hlg : 0 < paperC line n := paperC_pos line n
  have hlog : Real.log (paperB line n : ℝ) ≤ paperC line n := by
    have hBpos : (0 : ℝ) < (paperB line n : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by norm_num) hB2
    have h1 : Real.log (paperB line n : ℝ) ≤ paperW line n :=
      (Real.log_le_iff_le_exp hBpos).2 hBV
    unfold paperC
    linarith
  have hcard := cell_card_lower_of_primeBinSupply hK0 hsupply
    (A := 2) (B := paperB line n) (by norm_num) hB2 (lg := paperC line n) hlg hlog herr
  have hBge : paperV line n - 3 ≤ (paperB line n : ℝ) - 2 := by
    have hB := paperB_ge_V_sub_one line n
    linarith
  have hV6 : (6 : ℝ) ≤ paperV line n := (paperRegime line n).exp_ge_six
  have hmid : paperV line n / (4 * paperC line n) ≤
      ((paperB line n : ℝ) - 2) / (2 * paperC line n) := by
    have hCpos : 0 < paperC line n := paperC_pos line n
    have h4 : (0 : ℝ) < 4 * paperC line n := by nlinarith only [hCpos]
    have h2 : (0 : ℝ) < 2 * paperC line n := by nlinarith only [hCpos]
    rw [div_le_div_iff₀ h4 h2]
    nlinarith only [hBge, hV6, hCpos]
  calc
    paperV line n / (4 * paperC line n) ≤
        ((paperB line n : ℝ) - 2) / (2 * paperC line n) := hmid
    _ ≤ ((primeBin 2 (paperB line n)).card : ℝ) := hcard

/-- The guaranteed population `m` is at most the actual prime count. -/
theorem paperM_le_count (line : DirichletLZerosOnLine) (n : ℕ) :
    (paperM line n : ℝ) ≤ ((primeBin 2 (paperB line n)).card : ℝ) := by
  have hC := paperC_pos line n
  have hmle : (paperM line n : ℝ) ≤ paperV line n / (8 * paperC line n) := by
    unfold paperM
    exact Nat.floor_le (div_nonneg (paperV_pos line n).le
      (mul_nonneg (by norm_num) hC.le))
  have hstep : paperV line n / (8 * paperC line n) ≤
      paperV line n / (4 * paperC line n) := by
    exact div_le_div_of_nonneg_left (paperV_pos line n).le
      (by nlinarith only [hC]) (by nlinarith only [hC])
  exact hmle.trans (hstep.trans (paperBin_count_lower line n))

/-- The actual prime count is at most `V`. -/
theorem paperBin_count_le_V (line : DirichletLZerosOnLine) (n : ℕ) :
    ((primeBin 2 (paperB line n)).card : ℝ) ≤ paperV line n := by
  have hsub : primeBin 2 (paperB line n) ⊆ Finset.Ioc 2 (paperB line n) :=
    fun p hp => (Finset.mem_filter.mp hp).1
  have hcard : (primeBin 2 (paperB line n)).card ≤
      (Finset.Ioc 2 (paperB line n)).card := Finset.card_le_card hsub
  have hIoc : (Finset.Ioc 2 (paperB line n)).card = paperB line n - 2 := by
    simpa using Nat.card_Ioc 2 (paperB line n)
  rw [hIoc] at hcard
  have hle : ((paperB line n - 2 : ℕ) : ℝ) ≤ paperV line n := by
    have h1 : ((paperB line n - 2 : ℕ) : ℝ) ≤ (paperB line n : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    exact h1.trans (paperB_le_V line n)
  exact (by exact_mod_cast hcard : ((primeBin 2 (paperB line n)).card : ℝ) ≤
    ((paperB line n - 2 : ℕ) : ℝ)).trans hle

/-- The pool cardinality of the single-pattern certificate is the prime count. -/
theorem paperPool_card (line : DirichletLZerosOnLine) (n : ℕ) :
    ((numeratorPool (paperMassA line n) (paperMassB line n) (paperPatterns line n)).card : ℝ) =
      ((primeBin 2 (paperB line n)).card : ℝ) := by
  unfold numeratorPool paperPatterns
  rw [primeBinPatternProducts_card _ _ (paperMass_disjoint line n)]
  simp only [Finset.sum_singleton]
  rw [primeBinProducts_card]
  · simp [paperMassA, paperMassB]
  · intro i j hij
    exact paperMass_disjoint line n (Subtype.val_injective.ne hij)

/-! ### The mass and error inequalities of the numerator bin -/

theorem paperMass_num (line : DirichletLZerosOnLine) (n : ℕ) :
    paperV line n * paperRho line n ≤
      (paperPatterns line n).card * (paperM line n : ℝ) ^ 1 := by
  have hC := paperC_pos line n
  have hlin : 16 * paperC line n ≤ paperV line n := by
    have h := (paperRegime line n).linear
    simpa [paperV, paperC, mul_comm] using h
  have hfloor : paperV line n / (8 * paperC line n) < (paperM line n : ℝ) + 1 := by
    unfold paperM
    exact Nat.lt_floor_add_one _
  have hkey : paperV line n / (16 * paperC line n) ≤
      paperV line n / (8 * paperC line n) - 1 := by
    have h8 : (0 : ℝ) < 8 * paperC line n := by nlinarith only [hC]
    have h16 : (0 : ℝ) < 16 * paperC line n := by nlinarith only [hC]
    rw [div_sub_one (by nlinarith only [hC])]
    rw [div_le_div_iff₀ h16 h8]
    nlinarith only [hlin, hC]
  have hVrho : paperV line n * paperRho line n =
      paperV line n / (16 * paperC line n) := by
    unfold paperRho
    field_simp [hC.ne']
  rw [hVrho]
  have hcardpat : (paperPatterns line n).card = 1 := by simp [paperPatterns]
  rw [hcardpat]
  norm_num
  linarith

theorem paperError_scale (line : DirichletLZerosOnLine) (n : ℕ)
    (s : Finset ℕ) (hs : s ∈ paperPatterns line n) :
    paperX line n ≤ ∏ i ∈ s, (paperMassB line n i : ℝ) := by
  simp only [paperPatterns, Finset.mem_singleton] at hs
  subst s
  simp only [Finset.mem_singleton, Finset.prod_singleton]
  unfold paperX paperMassB
  simp only [↓reduceIte]
  have hB : (0 : ℝ) ≤ (paperB line n : ℝ) := Nat.cast_nonneg _
  linarith

/-- `1 + log (3 * floor V) ≤ 2 (1 + log V)`. -/
theorem paper_log_three_B_le (line : DirichletLZerosOnLine) (n : ℕ) :
    1 + Real.log (3 * (paperB line n : ℝ)) ≤ 2 * paperC line n := by
  have hB2 : 2 ≤ paperB line n := paperB_two_le line n
  have hBpos : (0 : ℝ) < (paperB line n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) hB2
  have hlog3 : Real.log 3 ≤ 1 + paperW line n := by
    have h : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      norm_num at this
      exact this
    have hW1 : 1 ≤ paperW line n := (paperRegime line n).one_le
    linarith
  have hlogB : Real.log (paperB line n : ℝ) ≤ paperW line n :=
    (Real.log_le_iff_le_exp hBpos).2 (by simpa [paperV] using paperB_le_V line n)
  have hWnn : 0 ≤ paperW line n := paperW_nonneg line n
  have hlogmul : Real.log (3 * (paperB line n : ℝ)) =
      Real.log 3 + Real.log (paperB line n : ℝ) :=
    Real.log_mul (by norm_num) hBpos.ne'
  unfold paperC
  rw [hlogmul]
  nlinarith only [hlog3, hlogB, hWnn]

theorem paperError_slot (line : DirichletLZerosOnLine) (n : ℕ)
    (s : Finset ℕ) (hs : s ∈ paperPatterns line n) (i : ℕ) (hi : i ∈ s) :
    2 * paperKmass line *
        (1 + Real.log (3 * ((1 : ℕ) : ℝ) * (paperMassB line n i : ℝ))) ^ 2 *
          (paperMassB line n i : ℝ) ≤
      paperU line n *
        ((primeBin (paperMassA line n i) (paperMassB line n i)).card : ℝ) := by
  simp only [paperPatterns, Finset.mem_singleton] at hs
  subst s
  simp only [Finset.mem_singleton] at hi
  subst i
  have hC := paperC_pos line n
  have hKm := paperKmass_nonneg line
  have hlog := paper_log_three_B_le line n
  have hbase_nn : 0 ≤ 1 + Real.log (3 * (paperB line n : ℝ)) := by
    have hlog3B : 0 ≤ Real.log (3 * (paperB line n : ℝ)) := by
      apply Real.log_nonneg
      have hB2 : 2 ≤ paperB line n := paperB_two_le line n
      have hB2' : (2 : ℝ) ≤ (paperB line n : ℝ) := by exact_mod_cast hB2
      nlinarith only [hB2']
    linarith
  have hsq : (1 + Real.log (3 * (paperB line n : ℝ))) ^ 2 ≤
      (2 * paperC line n) ^ 2 :=
    pow_le_pow_left₀ hbase_nn hlog 2
  have hstep1 : 2 * paperKmass line *
        (1 + Real.log (3 * (paperB line n : ℝ))) ^ 2 * (paperB line n : ℝ) ≤
      2 * paperKmass line * (2 * paperC line n) ^ 2 * (paperB line n : ℝ) := by
    have hcoef : 0 ≤ 2 * paperKmass line * (paperB line n : ℝ) := by positivity
    calc
      2 * paperKmass line * (1 + Real.log (3 * (paperB line n : ℝ))) ^ 2 *
          (paperB line n : ℝ) =
          (2 * paperKmass line * (paperB line n : ℝ)) *
            (1 + Real.log (3 * (paperB line n : ℝ))) ^ 2 := by ring
      _ ≤ (2 * paperKmass line * (paperB line n : ℝ)) *
            (2 * paperC line n) ^ 2 := mul_le_mul_of_nonneg_left hsq hcoef
      _ = 2 * paperKmass line * (2 * paperC line n) ^ 2 * (paperB line n : ℝ) := by ring
  have hcount := paperBin_count_lower line n
  have hCU : paperU line n = 64 * paperKmass line * (paperC line n) ^ 3 := rfl
  have hlower : 64 * paperKmass line * (paperC line n) ^ 3 *
        (paperV line n / (4 * paperC line n)) ≤
      paperU line n *
        ((primeBin (paperMassA line n 0) (paperMassB line n 0)).card : ℝ) := by
    rw [hCU]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa [paperMassA, paperMassB] using hcount
  have htarget : 2 * paperKmass line * (2 * paperC line n) ^ 2 * (paperB line n : ℝ) ≤
      64 * paperKmass line * (paperC line n) ^ 3 *
        (paperV line n / (4 * paperC line n)) := by
    have hBV := paperB_le_V line n
    have hcoef : 0 ≤ 8 * paperKmass line * (paperC line n) ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hBV hcoef
    calc
      2 * paperKmass line * (2 * paperC line n) ^ 2 * (paperB line n : ℝ) =
          8 * paperKmass line * (paperC line n) ^ 2 * (paperB line n : ℝ) := by ring
      _ ≤ 8 * paperKmass line * (paperC line n) ^ 2 * paperV line n := hmul
      _ ≤ 64 * paperKmass line * (paperC line n) ^ 3 *
            (paperV line n / (4 * paperC line n)) := by
        rw [show 64 * paperKmass line * (paperC line n) ^ 3 *
              (paperV line n / (4 * paperC line n)) =
            16 * paperKmass line * (paperC line n) ^ 2 * paperV line n by
          field_simp [hC.ne']
          ring]
        nlinarith only [show (0 : ℝ) ≤
          paperKmass line * (paperC line n) ^ 2 * paperV line n by
            exact mul_nonneg (mul_nonneg (paperKmass_nonneg line) (sq_nonneg _))
              (paperV_pos line n).le]
  simpa [paperMassA, paperMassB] using hstep1.trans (htarget.trans hlower)

theorem paperError_rel (line : DirichletLZerosOnLine) (n : ℕ) :
    paperU line n ^ 1 / Real.sqrt (paperX line n) ≤
      paperRho line n / (2 * paperEll line n) := by
  have hC := paperC_pos line n
  have hKm := paperKmass_nonneg line
  have hV6 : (6 : ℝ) ≤ paperV line n := (paperRegime line n).exp_ge_six
  have hB2 : 2 ≤ paperB line n := paperB_two_le line n
  have hXpos : 0 < paperX line n := by
    unfold paperX
    have : (0 : ℝ) < (paperB line n : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by norm_num) hB2
    linarith
  -- the polynomial `4096 K C^4` is at most `exp (W/2)`
  have hmass := (paperRegime line n).mass_small
  have hpolyC := (paperRegime line n).poly_sq
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hC_le : paperC line n ≤ 1 + Real.log 3 + paperW line n := by
    unfold paperC
    linarith
  have hCsq_le : (paperC line n) ^ 2 ≤ (1 + Real.log 3 + paperW line n) ^ 2 :=
    pow_le_pow_left₀ hC.le hC_le 2
  have hpolyC' : (paperC line n) ^ 2 ≤ Real.exp (1 / 4 * paperW line n) := by
    have h := hpolyC
    -- `paperC = 1 + W`
    simpa [paperC, div_eq_mul_inv, mul_comm] using h
  have hquart : 4096 * paperKmass line * (paperC line n) ^ 4 ≤
      Real.exp (1 / 2 * paperW line n) := by
    have h1 : 4096 * paperKmass line * (paperC line n) ^ 4 =
        (4096 * paperKmass line * (paperC line n) ^ 2) * (paperC line n) ^ 2 := by ring
    rw [h1]
    have hleft : 4096 * paperKmass line * (paperC line n) ^ 2 ≤
        4096 * paperKmass line * (1 + Real.log 3 + paperW line n) ^ 2 := by
      have hk : 0 ≤ 4096 * paperKmass line := by positivity
      exact mul_le_mul_of_nonneg_left hCsq_le hk
    have hleft' : 4096 * paperKmass line * (paperC line n) ^ 2 ≤
        Real.exp (1 / 4 * paperW line n) := by
      have hm := hmass
      -- `mass_small` is stated at `paperKmass`, `paperW`
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hleft.trans hm
    calc
      (4096 * paperKmass line * (paperC line n) ^ 2) * (paperC line n) ^ 2 ≤
          Real.exp (1 / 4 * paperW line n) * Real.exp (1 / 4 * paperW line n) :=
        mul_le_mul hleft' hpolyC' (sq_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (1 / 2 * paperW line n) := by
        rw [← Real.exp_add]
        congr 1
        ring
  -- `sqrt X >= exp(W/2)/2 >= 2048 K C^4`
  have hBge : paperV line n / 2 - 1 ≤ (paperB line n : ℝ) := by
    have hB := paperB_ge_V_sub_one line n
    linarith
  have hXge : paperV line n / 4 ≤ paperX line n := by
    unfold paperX
    have hB := paperB_ge_V_sub_one line n
    nlinarith only [hB, hV6]
  have hsqrt_ge : 2048 * paperKmass line * (paperC line n) ^ 4 ≤
      Real.sqrt (paperX line n) := by
    have h1 : Real.sqrt (paperV line n / 4) ≤ Real.sqrt (paperX line n) :=
      Real.sqrt_le_sqrt hXge
    have h2 : Real.sqrt (paperV line n / 4) = Real.exp (paperW line n / 2) / 2 := by
      rw [Real.sqrt_div (le_of_lt (paperV_pos line n)) 4]
      rw [show paperV line n = Real.exp (paperW line n) from rfl]
      rw [← Real.exp_half]
      norm_num
    have h3 : 2048 * paperKmass line * (paperC line n) ^ 4 ≤
        Real.exp (paperW line n / 2) / 2 := by
      have hq := hquart
      have hexp : Real.exp (1 / 2 * paperW line n) = Real.exp (paperW line n / 2) := by
        congr 1
        ring
      rw [hexp] at hq
      nlinarith only [hq]
    rw [h2] at h1
    exact h3.trans h1
  have hUle : paperU line n ≤ (1 / (32 * paperC line n)) * Real.sqrt (paperX line n) := by
    unfold paperU
    have hmul := mul_le_mul_of_nonneg_left hsqrt_ge
      (by positivity : (0 : ℝ) ≤ 1 / (32 * paperC line n))
    have heq : (1 / (32 * paperC line n)) * (2048 * paperKmass line * (paperC line n) ^ 4) =
        64 * paperKmass line * (paperC line n) ^ 3 := by
      field_simp [hC.ne']
      ring
    rw [← heq]
    exact hmul
  have hrho : paperRho line n / (2 * paperEll line n) = 1 / (32 * paperC line n) := by
    unfold paperRho paperEll
    field_simp [hC.ne']
    ring
  rw [hrho]
  have hU1 : paperU line n ^ 1 = paperU line n := pow_one _
  rw [hU1]
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hXpos)]
  exact hUle

theorem paperMass_size (line : DirichletLZerosOnLine) (n : ℕ) (s : Finset ℕ)
    (hs : s ∈ paperPatterns line n) : s.card = 1 := by
  simp only [paperPatterns, Finset.mem_singleton] at hs
  subst s
  simp

theorem paperMass_pop (line : DirichletLZerosOnLine) (n : ℕ) (s : Finset ℕ)
    (hs : s ∈ paperPatterns line n) (i : ℕ) (hi : i ∈ s) :
    paperM line n ≤ (primeBin (paperMassA line n i) (paperMassB line n i)).card := by
  simp only [paperPatterns, Finset.mem_singleton] at hs
  subst s
  simp only [Finset.mem_singleton] at hi
  subst i
  have h := paperM_le_count line n
  simp only [paperMassA, paperMassB, ↓reduceIte] at h ⊢
  exact_mod_cast h

theorem paperPool_upper (line : DirichletLZerosOnLine) (n : ℕ) :
    ((numeratorPool (paperMassA line n) (paperMassB line n) (paperPatterns line n)).card : ℝ) ≤
      paperV line n := by
  rw [paperPool_card line n]
  exact paperBin_count_le_V line n

theorem paperU_nonneg (line : DirichletLZerosOnLine) (n : ℕ) : 0 ≤ paperU line n := by
  unfold paperU
  exact mul_nonneg (mul_nonneg (by norm_num) (paperKmass_nonneg line)) (pow_nonneg (paperC_nonneg line n) 3)

theorem paperX_pos (line : DirichletLZerosOnLine) (n : ℕ) : 0 < paperX line n := by
  unfold paperX
  have hB2 : 2 ≤ paperB line n := paperB_two_le line n
  have hBpos : (0 : ℝ) < (paperB line n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) hB2
  linarith

/-- The mass/error data of the actual numerator bin. -/
noncomputable def paperMass (line : DirichletLZerosOnLine) :
    MassErrorInputs (paperW line) (paperEll line) (paperRho line) where
  K := paperKmass line
  K_nonneg := paperKmass_nonneg line
  q := fun _ => 1
  q_pos := by intro n; norm_num
  ell_eq := by intro n; simp [paperEll]
  rho_pos := paperRho_pos line
  A := paperMassA line
  B := paperMassB line
  patterns := paperPatterns line
  hdisj := paperMass_disjoint line
  hA := paperMassA_two line
  hAB := paperMassA_le_B line
  mass_k := fun _ => 1
  mass_m := paperM line
  mass_size := paperMass_size line
  mass_pop := paperMass_pop line
  mass_num := paperMass_num line
  error_U := paperU line
  error_X := paperX line
  error_U_nonneg := paperU_nonneg line
  error_X_pos := paperX_pos line
  error_scale := paperError_scale line
  error_slot := paperError_slot line
  pool_upper := paperPool_upper line
  error_rel := paperError_rel line

/-- `Nnum` is the actual root-progression count of the pool, at modulus `1`. -/
noncomputable def paperNumR (line : DirichletLZerosOnLine) : ∀ n : ℕ, (ZMod 1)ˣ :=
  fun _ => 1

noncomputable def paperNnum (line : DirichletLZerosOnLine) (n : ℕ) : ℝ :=
  (progressionCount (paperMassA line n) (paperMassB line n) (paperPatterns line n) 1
    (paperNumR line n) : ℝ)

theorem paperNnum_nonneg (line : DirichletLZerosOnLine) (n : ℕ) : 0 ≤ paperNnum line n :=
  Nat.cast_nonneg _

theorem paperNumCoprime (line : DirichletLZerosOnLine) (n m : ℕ)
    (hm : m ∈ numeratorPool (paperMassA line n) (paperMassB line n) (paperPatterns line n)) :
    m.Coprime 1 :=
  Nat.coprime_one_right m

theorem paperNnum_eq (line : DirichletLZerosOnLine) (n : ℕ) :
    paperNnum line n =
      (progressionCount ((paperMass line).A n) ((paperMass line).B n)
        ((paperMass line).patterns n) ((paperMass line).q n)
        (paperNumR line n) : ℝ) := by
  rfl

/-- The residue-class deviation at modulus `1` is zero, hence at most the
critical-line progression error. -/
theorem paperNumDeviation (line : DirichletLZerosOnLine) (n : ℕ) :
    |(progressionCount (paperMassA line n) (paperMassB line n) (paperPatterns line n) 1
        (paperNumR line n) : ℝ) -
      (coprimeCount (paperMassA line n) (paperMassB line n) (paperPatterns line n) 1 : ℝ) /
        (1 : ℕ).totient| ≤
      progressionError (paperKmass line) 1 (paperMassB line n) (paperPatterns line n) := by
  haveI : NeZero (1 : ℕ) := ⟨by norm_num⟩
  have htot : ((1 : ℕ).totient : ℝ) = 1 := by norm_num
  have hpc : progressionCount (paperMassA line n) (paperMassB line n) (paperPatterns line n) 1
      (paperNumR line n) =
      coprimeCount (paperMassA line n) (paperMassB line n) (paperPatterns line n) 1 := by
    unfold progressionCount coprimeCount
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro m hm
    constructor
    · intro _; exact Nat.coprime_one_right m
    · intro _; exact Subsingleton.elim _ _
  rw [hpc, htot]
  have hzero : (coprimeCount (paperMassA line n) (paperMassB line n) (paperPatterns line n) 1 : ℝ) -
      (coprimeCount (paperMassA line n) (paperMassB line n) (paperPatterns line n) 1 : ℝ) / 1 = 0 := by
    ring
  rw [hzero, abs_zero]
  exact progressionError_nonneg (paperKmass line) (paperKmass_nonneg line) 1
    (paperMassB line n) (paperPatterns line n)

/-! ## 5. The thin aggregate -/

/-- The number of retained thin marks: at least `K Ncell Nnum`, and at least
`K` so that `1/R ≤ 1/K`. -/
noncomputable def paperR (line : DirichletLZerosOnLine) (n : ℕ) : ℕ :=
  Nat.ceil (paperK line n * paperNcell line n * paperNnum line n) +
    Nat.ceil (paperK line n) + 1

/-- The retained marks `(1, b)` with `1 ≤ b ≤ R`. -/
noncomputable def paperS (line : DirichletLZerosOnLine) (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (paperR line n)).image (fun k : ℕ => ((1 : ℤ), (k : ℤ) + 1))

theorem paperR_pos (line : DirichletLZerosOnLine) (n : ℕ) : 0 < paperR line n := by
  unfold paperR
  omega

theorem paperS_card (line : DirichletLZerosOnLine) (n : ℕ) :
    (paperS line n).card = paperR line n := by
  unfold paperS
  rw [Finset.card_image_of_injective _ (fun a b h => by
    have h' : (a : ℤ) + 1 = (b : ℤ) + 1 := congrArg Prod.snd h
    have h'' : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast h'')]
  simp

theorem paperR_ge_K (line : DirichletLZerosOnLine) (n : ℕ) :
    paperK line n ≤ (paperR line n : ℝ) := by
  have hK : paperK line n ≤ (Nat.ceil (paperK line n) : ℝ) := Nat.le_ceil _
  have hle : Nat.ceil (paperK line n) ≤ paperR line n := by
    unfold paperR
    omega
  exact hK.trans (by exact_mod_cast hle)

theorem paperR_ge_retained (line : DirichletLZerosOnLine) (n : ℕ) :
    paperK line n * paperNcell line n * paperNnum line n ≤ (paperR line n : ℝ) := by
  have hval : 0 ≤ paperK line n * paperNcell line n * paperNnum line n :=
    mul_nonneg (mul_nonneg (paperK_pos line n).le (paperNcell_nonneg line n))
      (paperNnum_nonneg line n)
  have hceil := Nat.le_ceil (paperK line n * paperNcell line n * paperNnum line n)
  have hle : Nat.ceil (paperK line n * paperNcell line n * paperNnum line n) ≤
      paperR line n := by
    unfold paperR
    omega
  exact hceil.trans (by exact_mod_cast hle)

/-- The lattice box of the retained marks. -/
noncomputable def paperBox (line : DirichletLZerosOnLine) (n : ℕ) : LatticeBox where
  S := paperS line n
  q := 1
  q_pos := by norm_num
  lo := 0
  hi := (paperR line n : ℤ)
  lo_le_hi := by positivity
  bmin := 1
  bmin_pos := by norm_num
  L := (paperR line n : ℝ) + 1
  level_bound := by simp
  prim := by
    intro P hP
    unfold paperS at hP
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    exact isCoprime_one_left
  den_pos := by
    intro P hP
    unfold paperS at hP
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    simp
  box := by
    intro P hP
    unfold paperS at hP
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    have hkR : (k : ℤ) < (paperR line n : ℤ) := by exact_mod_cast Finset.mem_range.mp hk
    constructor <;> omega
  bmin_le := by
    intro P hP
    unfold paperS at hP
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    simp
  det_dvd := by
    intro P hP Q hQ
    simp

/-- The actual normalized diagonal fraction of the retained marks. -/
noncomputable def paperThin (line : DirichletLZerosOnLine) (n : ℕ) : ℝ :=
  1 / (paperR line n : ℝ)

theorem paperThin_pos (line : DirichletLZerosOnLine) (n : ℕ) : 0 < paperThin line n := by
  unfold paperThin
  exact div_pos zero_lt_one (by exact_mod_cast paperR_pos line n)

theorem paperThin_nonneg (line : DirichletLZerosOnLine) (n : ℕ) : 0 ≤ paperThin line n :=
  (paperThin_pos line n).le

theorem paperThinCutoff_pos (line : DirichletLZerosOnLine) (n : ℕ) :
    0 < thinCutoff (paperW line) (fun m => (paperBox line m).L) (paperRho line) n := by
  unfold thinCutoff
  have hL : 0 < (paperBox line n).L := by
    unfold paperBox
    simp only
    have : (0 : ℝ) ≤ (paperR line n : ℝ) := by exact_mod_cast Nat.zero_le _
    linarith
  have hW : 0 < 1 + paperW line n := by
    have := (paperRegime line n).one_le
    linarith
  have hD : 0 < paperRho line n := paperRho_pos line n
  have hK : 0 < paperK line n := paperK_pos line n
  have hKc : 0 < cellMesh (paperW line) n := by
    unfold cellMesh
    exact Real.exp_pos _
  exact mul_pos (div_pos (mul_pos (mul_pos (by norm_num) hL) hW) hD) hKc

theorem paperS_diag_subset_strip (line : DirichletLZerosOnLine) (n : ℕ) {X : ℝ}
    (hX : 0 ≤ X) :
    (paperS line n).image (fun P : ℤ × ℤ => (P, P)) ⊆
      stripPairSet (paperS line n) X := by
  rw [Finset.image_subset_iff]
  intro P hP
  rw [stripPairSet, Finset.mem_filter]
  constructor
  · change (P, P) ∈ (paperS line n ×ˢ paperS line n)
    rw [Finset.mem_product]
    exact ⟨hP, hP⟩
  · simp [det]
    exact hX

theorem paperStrip_card_ge (line : DirichletLZerosOnLine) (n : ℕ) :
    (paperR line n : ℝ) ≤
      ((stripPairSet (paperS line n)
        (denomScale (paperW line) n ^ 2 /
          thinCutoff (paperW line) (fun m => (paperR line m : ℝ) + 1) (paperRho line) n)).card : ℝ) := by
  have hX : 0 ≤ denomScale (paperW line) n ^ 2 /
      thinCutoff (paperW line) (fun m => (paperR line m : ℝ) + 1) (paperRho line) n :=
    div_nonneg (sq_nonneg _) (paperThinCutoff_pos line n).le
  have hsub := paperS_diag_subset_strip line n hX
  have hcard := Finset.card_le_card hsub
  have himg : ((paperS line n).image (fun P : ℤ × ℤ => (P, P))).card = paperR line n := by
    rw [Finset.card_image_of_injective _ (fun P Q h => congrArg Prod.fst h)]
    exact paperS_card line n
  rw [himg] at hcard
  exact_mod_cast hcard

/-- The thin aggregate data of the paper-regime construction. -/
noncomputable def paperThinData (line : DirichletLZerosOnLine) :
    ThinAggregateData (paperW line) (paperD line) (paperEll line) (paperRho line)
      (paperThin line) (paperNcell line) (paperNnum line) where
  box := paperBox line
  dens := paperRho line
  dens_pos := paperRho_pos line
  dens_le_one := by
    intro n
    unfold paperRho
    have hC1 : (1 : ℝ) ≤ paperC line n := by
      have := (paperRegime line n).one_le
      unfold paperC
      linarith
    have hpos : 0 < 16 * paperC line n := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith only [hC1]
  ell_eq := by intro n; simp [paperEll, paperBox]
  thin_le_pairFraction := by
    intro n
    have hcard := paperStrip_card_ge line n
    simp only [paperBox] at hcard ⊢
    simp only [paperS_card line n] at hcard ⊢
    have hthin : paperThin line n =
        (paperR line n : ℝ) / (paperR line n : ℝ) ^ 2 := by
      unfold paperThin
      have hR : (paperR line n : ℝ) ≠ 0 := by
        exact_mod_cast (paperR_pos line n).ne'
      field_simp [hR]
    rw [hthin]
    exact div_le_div_of_nonneg_right hcard (sq_nonneg _)
  retained_cell_count := by
    intro n
    unfold paperBox
    simp only
    rw [paperS_card line n]
    exact paperR_ge_retained line n
  const_le := by
    intro n
    unfold paperD paperRho
    field_simp
    exact le_rfl
  power_margin := by
    intro n
    have hC := paperC_pos line n
    have hpow := (paperRegime line n).power
    have hVK : paperV line n ^ 2 / paperK line n =
        Real.exp (7 / 4 * paperW line n) := by
      unfold paperV paperK
      rw [pow_two, ← Real.exp_add, ← Real.exp_sub]
      congr 1
      ring
    simp only [paperBox, paperRho]
    rw [show denomScale (paperW line) n = paperV line n from rfl]
    rw [show cellMesh (paperW line) n = paperK line n from rfl]
    rw [show (1 / (16 * paperC line n)) * paperV line n ^ 2 / paperK line n =
        (1 / (16 * paperC line n)) * (paperV line n ^ 2 / paperK line n) from by ring]
    rw [hVK]
    rw [show (1 / (16 * paperC line n)) * Real.exp (7 / 4 * paperW line n) =
        Real.exp (7 / 4 * paperW line n) / (16 * paperC line n) from by ring]
    rw [le_div_iff₀ (by positivity)]
    norm_num
    have hCeq : paperC line n = 1 + paperW line n := rfl
    have hgoal : 2 * (1 + paperW line n) * (16 * paperC line n) =
        32 * (1 + paperW line n) ^ 2 := by
      rw [hCeq]
      ring
    nlinarith only [hpow, hgoal]

/-! ## 6. The paper-regime certificate -/

/-- The `D^{O(1)}` exponent of the growing `W = max T (scale)^2`. -/
noncomputable def paperCW (line : DirichletLZerosOnLine) : ℝ :=
  max 3 (Real.log (paperT line) / scale 3)

/-- The reciprocal-density exponent `cρ = cW + log 32 / scale 3`. -/
noncomputable def paperCRho (line : DirichletLZerosOnLine) : ℝ :=
  paperCW line + Real.log 32 / scale 3

theorem paperT_ge_one (line : DirichletLZerosOnLine) : 1 ≤ paperT line :=
  (paperT_spec line (le_refl (paperT line))).one_le

theorem paperCW_ge_three (line : DirichletLZerosOnLine) : 3 ≤ paperCW line :=
  le_max_left _ _

theorem paperCW_nonneg (line : DirichletLZerosOnLine) : 0 ≤ paperCW line :=
  (by norm_num : (0 : ℝ) ≤ 3).trans (paperCW_ge_three line)

theorem paperCRho_nonneg (line : DirichletLZerosOnLine) : 0 ≤ paperCRho line := by
  have hlog : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
  have hs : 0 < scale 3 := scale_three_pos
  unfold paperCRho
  have : 0 ≤ Real.log 32 / scale 3 := div_nonneg hlog hs.le
  linarith [paperCW_nonneg line]

theorem scale_sq_le_exp (n : ℕ) (hn : 3 ≤ n) :
    (scale n) ^ 2 ≤ Real.exp (3 * scale n) := by
  have h3pos : 0 < scale 3 := scale_three_pos
  have hmono : scale 3 ≤ scale n := scale_mono_of_three_le (le_refl 3) hn
  have hx : 0 ≤ scale n := h3pos.le.trans hmono
  have h1 : 1 + scale n ≤ Real.exp (scale n) := by
    simpa [add_comm] using Real.add_one_le_exp (scale n)
  have hnn : 0 ≤ 1 + scale n := by linarith
  have hcube : (1 + scale n) ^ 3 ≤ (Real.exp (scale n)) ^ 3 :=
    pow_le_pow_left₀ hnn h1 3
  have hsq : (scale n) ^ 2 ≤ (1 + scale n) ^ 3 := by nlinarith only [hx]
  have hexp : (Real.exp (scale n)) ^ 3 = Real.exp (3 * scale n) := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc
    (scale n) ^ 2 ≤ (1 + scale n) ^ 3 := hsq
    _ ≤ (Real.exp (scale n)) ^ 3 := hcube
    _ = Real.exp (3 * scale n) := hexp

theorem paperW_upper (line : DirichletLZerosOnLine) :
    ∀ n, 3 ≤ n → paperW line n ≤ Real.exp (paperCW line * scale n) := by
  intro n hn
  have hs3 : 0 < scale 3 := scale_three_pos
  have hmono : scale 3 ≤ scale n := scale_mono_of_three_le (le_refl 3) hn
  have hTpos : 0 < paperT line := lt_of_lt_of_le zero_lt_one (paperT_ge_one line)
  have hlogT : Real.log (paperT line) ≤ paperCW line * scale 3 := by
    have hle : Real.log (paperT line) / scale 3 ≤ paperCW line := le_max_right _ _
    rw [div_le_iff₀ hs3] at hle
    linarith
  have hcWnn : 0 ≤ paperCW line := paperCW_nonneg line
  have hstep : Real.log (paperT line) ≤ paperCW line * scale n := by
    have := mul_le_mul_of_nonneg_left hmono hcWnn
    linarith
  have hT : paperT line ≤ Real.exp (paperCW line * scale n) := by
    calc
      paperT line = Real.exp (Real.log (paperT line)) :=
        (Real.exp_log hTpos).symm
      _ ≤ Real.exp (paperCW line * scale n) := Real.exp_le_exp.mpr hstep
  have hx : 0 ≤ scale n := by linarith [hs3, hmono]
  have h3x : 3 * scale n ≤ paperCW line * scale n :=
    mul_le_mul_of_nonneg_right (paperCW_ge_three line) hx
  have hsq : (scale n) ^ 2 ≤ Real.exp (3 * scale n) := scale_sq_le_exp n hn
  have hsq' : (scale n) ^ 2 ≤ Real.exp (paperCW line * scale n) :=
    hsq.trans (Real.exp_le_exp.mpr h3x)
  exact max_le hT hsq'

theorem paperW_dominates (line : DirichletLZerosOnLine) :
    ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, c * scale n ≤ paperW line n := by
  intro c hc
  filter_upwards [scale_grows.eventually_ge_atTop (max c 0)] with n hn
  have hc_le : c ≤ scale n := (le_max_left c 0).trans hn
  have hx : 0 ≤ scale n := (le_max_right c 0).trans hn
  calc
    c * scale n ≤ scale n * scale n := mul_le_mul_of_nonneg_right hc_le hx
    _ = (scale n) ^ 2 := by ring
    _ ≤ paperW line n := paperW_ge_scale_sq line n

theorem paperRho_inv_upper (line : DirichletLZerosOnLine) :
    ∀ n, 3 ≤ n → 1 / paperRho line n ≤ Real.exp (paperCRho line * scale n) := by
  intro n hn
  have hs3 : 0 < scale 3 := scale_three_pos
  have hmono : scale 3 ≤ scale n := scale_mono_of_three_le (le_refl 3) hn
  have hWge1 : 1 ≤ paperW line n := (paperRegime line n).one_le
  have hW := paperW_upper line n hn
  have hlog32 : 0 < Real.log 32 := Real.log_pos (by norm_num)
  have hcoef : 0 ≤ Real.log 32 / scale 3 := div_nonneg hlog32.le hs3.le
  have h1 : 16 * (1 + paperW line n) ≤ 32 * paperW line n := by nlinarith only [hWge1]
  have h2 : 32 * paperW line n ≤ 32 * Real.exp (paperCW line * scale n) :=
    mul_le_mul_of_nonneg_left hW (by norm_num)
  have h3 : 32 * Real.exp (paperCW line * scale n) ≤
      Real.exp (paperCRho line * scale n) := by
    have h32 : (32 : ℝ) = Real.exp (Real.log 32) := (Real.exp_log (by norm_num)).symm
    rw [h32, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold paperCRho
    have hle : Real.log 32 ≤ (Real.log 32 / scale 3) * scale n := by
      rw [show (Real.log 32 / scale 3) * scale n = (Real.log 32 * scale n) / scale 3 by ring]
      rw [le_div_iff₀ hs3]
      exact mul_le_mul_of_nonneg_left hmono hlog32.le
    nlinarith only [hle]
  have hrho : 1 / paperRho line n = 16 * (1 + paperW line n) := by
    unfold paperRho paperC
    field_simp
  rw [hrho]
  exact h1.trans (h2.trans h3)

/-- **The paper-regime `L18_4Certificate`.**  All data are explicit, `W` grows
like `(scale n)^2`, `cellK0` is the critical-line constant, the denominator cell
and numerator bin are actual prime bins, and the thin marks are explicit. -/
noncomputable def paperCertificate (line : DirichletLZerosOnLine) : L18_4Certificate where
  W := paperW line
  d := paperD line
  ell := paperEll line
  rho := paperRho line
  C := fun _ => 1
  M := fun _ => 1
  Econv := fun _ => 1
  S2 := paperS2 line
  Ncell := paperNcell line
  Nnum := paperNnum line
  thin := paperThin line
  cW := paperCW line
  cC := 0
  cM := 0
  cE := 0
  cd := 0
  cell := 0
  cρ := paperCRho line
  W_nonneg := paperW_nonneg line
  d_pos := by intro n; norm_num [paperD]
  ell_pos := by intro n; norm_num [paperEll]
  rho_pos := paperRho_pos line
  C_pos := by intro n; norm_num
  M_pos := by intro n; norm_num
  Econv_nonneg := by intro n; norm_num
  S2_nonneg := paperS2_nonneg line
  Ncell_nonneg := paperNcell_nonneg line
  Nnum_nonneg := paperNnum_nonneg line
  thin_nonneg := paperThin_nonneg line
  cW_nonneg := paperCW_nonneg line
  cC_nonneg := by norm_num
  cM_nonneg := by norm_num
  cE_nonneg := by norm_num
  cd_nonneg := by norm_num
  cell_nonneg := by norm_num
  cρ_nonneg := paperCRho_nonneg line
  W_upper := paperW_upper line
  C_upper := by intro n _; norm_num
  M_upper := by intro n _; norm_num
  Econv_upper := by intro n _; norm_num
  d_upper := by intro n _; norm_num [paperD]
  ell_upper := by intro n _; norm_num [paperEll]
  rho_inv_upper := paperRho_inv_upper line
  W_dominates := paperW_dominates line
  largeSieve := paperLargeSieve line
  hS2 := fun n => rfl
  cellData := paperCellData line
  hNcell := fun n => rfl
  cellK0 := paperK0 line
  cellK0_nonneg := paperK0_nonneg line
  cellSupply := cellSupply_of_supply (paperK0_nonneg line) (cellK0OfLine_supply line)
  cellSupplyFit := by
    intro n
    have hreg := (paperRegime line n).supply_small
    have hK0 := paperK0_nonneg line
    have hnonneg : 0 ≤ (1 + Real.log 3 + paperW line n) ^ 2 := sq_nonneg _
    have hcoef : 2 * paperD line n * paperK0 line ≤ 32 * paperK0 line := by
      unfold paperD
      nlinarith only [hK0]
    calc
      2 * paperD line n * paperK0 line * (1 + Real.log 3 + paperW line n) ^ 2
          ≤ (32 * paperK0 line) * (1 + Real.log 3 + paperW line n) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef hnonneg
      _ ≤ cellMesh (paperW line) n := by
        simpa [cellMesh, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hreg
  mass := paperMass line
  numR := paperNumR line
  numCoprime := paperNumCoprime line
  numEq := paperNnum_eq line
  numDeviation := paperNumDeviation line
  thinData := paperThinData line

/-- The literal certificate's `B = 2` slot bound. -/
theorem paperCertificate_slot_le (line : DirichletLZerosOnLine) {slots : C5LossSlots}
    (h : slots (C5Leaf.rationalGoodEnvironments) = (paperCertificate line).toInputs.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots (C5Leaf.rationalGoodEnvironments) n ≤ exp (-(2 : ℝ) * scale n) :=
  (paperCertificate line).slot_le h

/-- The literal certificate's `D^{-B}` deficit for every `B`. -/
theorem paperCertificate_subexpLoss (line : DirichletLZerosOnLine) :
    SubexpLoss (paperCertificate line).toInputs.loss :=
  (paperCertificate line).subexpLoss

theorem nonempty_L18_4Certificate_of_critical_line (line : DirichletLZerosOnLine) :
    Nonempty L18_4Certificate :=
  ⟨paperCertificate line⟩

/-! ## 7. The endpoint record without an L18.4 hypothesis -/

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedC5Full
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL20_4LeafAssembly
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL30
open Cogentic.RandomizedL34
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave27
open Cogentic.RandomizedPaperEndpointWave28
open Cogentic.RandomizedPaperEndpointWave29
open Cogentic.RandomizedPaperEndpointWave31
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule

/-- **The Wave-31 residual record with the `l18_4` field removed.**  The L18.4
certificate is no longer an input: it is the constructed
`paperCertificate line`.  Every other field is copied verbatim from
`PaperResidualFor31`, including the C5 loss adapter, which now refers to the
constructible certificate. -/
structure PaperResidualFor31GRH (line : DirichletLZerosOnLine)
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L19 certificate. -/
  l19 : Wave15L19Inputs
  /-- L20.2: interior concentration from the paper-mass saddle source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4: the sourced child-root-conditioned two-point data. -/
  l20_4 : Wave14L20_4Source
  /-- L21.2: the Riemann hypothesis and the central short-interval count. -/
  l21 : Wave27L21Inputs
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- L30 with the sharp count derived from Buchstab and parity. -/
  l30 : Wave31L30Inputs
  /-- L34 with the Stark field derived. -/
  l34 : Wave28L34Inputs
  /-- P1: the explicit `exp (o(H))`-cost prepass. -/
  p1 : SubexpPrepassInput
  /-- C1: the public congruence check (L1). -/
  c1 : C1Inputs E
  /-- C2: conditional hidden-sign uniformity. -/
  c2 : C2Inputs E
  /-- C3: the ideal/actual total-variation budget. -/
  c3 : C3Inputs E
  /-- C4: the expected public-work budget. -/
  c4 : C4Inputs E D
  /-- The concrete epoch family underlying the C5 certificate. -/
  concrete : ∀ n, 3 ≤ n → ConcreteEpochData n
  /-- Adapter: the ambient epoch is the concrete family's `toHardEpochData`. -/
  concrete_eq : ∀ n (hN : 3 ≤ n), E n hN = (concrete n hN).toHardEpochData
  /-- The C5 data assembled by `c5FullOfCount`. -/
  c5Data : Wave15C5Data concrete
  /-- Adapter: the concrete C5 loss is dominated by the Wave-31 ledger at the
  constructed L18.4 certificate. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave31Slots (paperCertificate line) l19 l20_2 l20_4 l21 l27_data
        l27_finish l30 l34 p1).total n

namespace PaperResidualFor31GRH

variable {line : DirichletLZerosOnLine}
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **Transport to the Wave-31 record.**  The only change is `l18_4`, which is
filled with the constructed `paperCertificate line`; the C5 adapter is unchanged
because `wave31Slots` receives the certificate as its first argument. -/
noncomputable def toPaperResidualFor31 (I : PaperResidualFor31GRH line E D) :
    PaperResidualFor31 E D where
  l18_4 := paperCertificate line
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
  l34 := I.l34
  p1 := I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5Data := I.c5Data
  loss_le := I.loss_le

/-- The transported certificate is the constructed one. -/
theorem toPaperResidualFor31_l18_4 (I : PaperResidualFor31GRH line E D) :
    (I.toPaperResidualFor31).l18_4 = paperCertificate line := rfl

/-- The transport leaves the C5 loss adapter unchanged. -/
theorem toPaperResidualFor31_loss_le (I : PaperResidualFor31GRH line E D)
    (n : ℕ) (hN : 3 ≤ n) :
    c5TotalLoss hN (I.concrete n hN) (I.c5Data.toC5 n hN) ≤
      (wave31Slots (paperCertificate line) I.l19 I.l20_2 I.l20_4 I.l21
        I.l27_data I.l27_finish I.l30 I.l34 I.p1).total n :=
  I.loss_le n hN

/-- The record is nonempty as a fully discharged input. -/
theorem nonempty_fullyDischargedInputs (I : PaperResidualFor31GRH line E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toPaperResidualFor31.toPaperResidualFor29.toFullyDischargedInputs⟩

end PaperResidualFor31GRH

/-- **The schedule-indexed form without an L18.4 hypothesis.** -/
abbrev PaperResidualFor31GRHSchedule (line : DirichletLZerosOnLine)
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor31GRH line (E s) D

/-- **The Wave-31 endpoint with L18.4 constructed from the critical line.**

Under `DirichletLZerosOnLine` there is one universal serialized factoring
algorithm such that, for every balanced epoch family `E` which at every valid
ceiling carries a `PaperResidualFor31GRH line (E s) D` record (i.e. the Wave-31
record *without* an L18.4 hypothesis), the kernel-checked driver outputs a
permutation of `n.primeFactorsList` with expected serialized bit cost eventually
at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum` in the same interval as Wave 31. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_grhCertificate
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor31GRH line (E s) D) →
      1.9839824118071388228 < balancedEnvelopeInfimum ∧
      balancedEnvelopeInfimum < 1.9839824118071388230 ∧
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound
          (balancedUniversalHard (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)))
          n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound
          (balancedUniversalHard (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)))
          n hn) (fun out => (out.2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ :=
    serialized_assembled_balancedEnvelopeInfimum_from_wave31Inputs line
  exact ⟨k, sound, fun E hI => hmain E fun s D hv =>
    (hI s D hv).toPaperResidualFor31⟩

/-! ## 8. Residual accounting -/

/-- The fields of `PaperResidualFor31GRH`; there is no `l18_4` field. -/
def paperResidualFieldNames : List String :=
  ["l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem paperResidualFieldNames_length : paperResidualFieldNames.length = 17 := rfl

/-- The record no longer carries an L18.4 hypothesis. -/
theorem paperResidual_no_l18_4 :
    paperResidualFieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- The remaining analytic residual list of the endpoint with the L18.4 entry
removed: the Wave-31 list minus `l18_4`. -/
def paperRemainingFieldNames : List String :=
  ["zetaRH", "localCount", "hbuchstab", "hparity",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "killMass", "curveBudget",
   "zeroFree", "cheb", "range", "beta0_le_half",
   "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

theorem paperRemainingFieldNames_length : paperRemainingFieldNames.length = 23 := rfl

theorem paperRemaining_no_l18_4 :
    paperRemainingFieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- **The L18.4 certificate is supplied, not assumed.**  Its two former
residuals (`W_dominates` and `cellSupply`) are both theorems here. -/
theorem paperCertificate_residuals_discharged (line : DirichletLZerosOnLine) :
    (∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, c * scale n ≤ (paperCertificate line).W n) ∧
      PrimeBinCellSupply (paperCertificate line).cellK0 :=
  ⟨paperW_dominates line, cellSupply_of_supply (paperK0_nonneg line) (cellK0OfLine_supply line)⟩

/-- **The constructed loss is genuinely positive**, not set to zero: the thin
fraction is `1/R` with `R` the explicit number of retained marks. -/
theorem paperCertificate_loss_pos (line : DirichletLZerosOnLine) (n : ℕ) :
    0 < (paperCertificate line).toInputs.loss n := by
  have hthin : 0 < (paperCertificate line).toInputs.thin n := by
    show 0 < paperThin line n
    exact paperThin_pos line n
  have hcell : 0 ≤ (paperCertificate line).toInputs.cellDeficit n := by
    unfold L18_4Inputs.cellDeficit
    exact mul_nonneg ((paperCertificate line).toInputs.K_pos n).le
      (div_nonneg ((paperCertificate line).toInputs.S2_nonneg n) (sq_nonneg _))
  unfold L18_4Inputs.loss
  linarith

/-! ## Axiom audit -/

#print axioms paperCertificate
#print axioms paperCertificate_slot_le
#print axioms paperCertificate_subexpLoss
#print axioms paperCertificate_loss_pos
#print axioms PaperResidualFor31GRH.toPaperResidualFor31
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_grhCertificate
#print axioms paperCertificate_residuals_discharged

end Cogentic.RandomizedL18_4
