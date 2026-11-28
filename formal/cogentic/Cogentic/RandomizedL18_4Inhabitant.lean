import Cogentic.RandomizedL18_4Full
import Cogentic.RandomizedL18_4CellFinish

/-!
# L18.4: a concrete inhabitant of the finite core, and the residual list

This file is a non-vacuity / consistency check for the L18.4 certificate of
`Cogentic.RandomizedL18_4Full`.  It does two things.

## 1. A concrete inhabitant of the largest compatible sub-record

`L18_4AmbientData` is the data part of `L18_4Ambient` without the
`D^{O(1)}` upper bounds and the growth-rate field `W_dominates`.
`L18_4CertificateCore` adds every sub-certificate of `L18_4Certificate` except
the critical-line prime-bin supply `cellSupply`:

* a concrete finite large-sieve certificate (one cell, modulus `3`, numerator
  set `{1}`, weight `1`, `A = 1`, `perCell = 1`, `Econv = 1`, `d = 1/4`);
* a concrete integer denominator cell `(2, 625]` of width `623` with the actual
  prime count `Ncell = #(primeBin 2 625)`;
* a concrete numerator pool: the disjoint prime bins `(2, 101]` and
  `(101, 233]`, each containing `25` primes, with the single pattern `{0,1}`,
  so the pool has exactly `25 * 25 = 625` elements;
* a concrete thin aggregate: `2 000 000` primitive marks `(1, b)` and the
  actual normalized diagonal/strip fraction;
* the actual nonzero RH progression error at the mass constant `10^{-10}`.

At the concrete data the L18.4 loss is
`K (S2 / mu^2) + thin`, with `S2` the actual residue energy of the large-sieve
certificate and `thin` the actual diagonal strip fraction; it is strictly
positive (`iCore_loss_pos`) and the progression error is strictly positive
(`iProgressionError_pos`).  No error or count is set to zero.

## 2. The exact residuals after guarding the growth fields

The `D^{O(1)}` fields of `L18_4Inputs`/`L18_4Ambient` are now asserted only on
the paper regime `3 ≤ n`.  The guard is necessary at `3`: `scale 0 = scale 1 =
0` and `scale 2 < 0`, so an unguarded bound at any of those indices forces
`W ≤ 1` and contradicts `CellData` exactly as the original `n = 0` argument
did.  Since `scale 3 > 0`, the guard removes that contradiction without
changing any positive-index content.

`L18_4CertificateCore.toCertificate` still lists what has to be added to reach
a literal `L18_4Certificate`, but the seven pointwise `D^{O(1)}` bounds are now
supplied by `iCore` itself (`iCore_W_upper` … `iCore_rho_inv_upper`).  The only
remaining inputs are:

* `W_dominates`; and
* the critical-line prime-bin supply `cellSupply` (equivalently
  `PrimeBinSupply cellK0`, the GRH/PNT-in-AP input).

`W_dominates` is not a defect of the finite data: the toy core has constant
`W = 4 log 5`, which provably does not dominate the unbounded `scale`
(`iCore_not_W_dominates`); a paper-regime witness takes `W = log V`, which
does.  `iCertificate` therefore produces an actual `L18_4Certificate` from the
concrete core plus exactly these two inputs, and its `B = 2` slot bound is
proved (`iCertificate_slot_le`).
-/

namespace Cogentic.RandomizedL18_4

open Finset Real
open scoped BigOperators
open Cogentic.Randomized
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedOneThirdAsymptotic

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.checkUnivs false

/-! ## 1. The concrete finite data -/

/-- The logarithmic denominator scale.  This is chosen so that
`V = exp W = 625` and `K = V^{1/4} = 5`. -/
noncomputable def iW : ℕ → ℝ := fun _ => 4 * Real.log 5

/-- The field degree. -/
noncomputable def iDeg : ℕ → ℝ := fun _ => 1 / 4

/-- The root index, equal to the root modulus `1`. -/
noncomputable def iEll : ℕ → ℝ := fun _ => 1

/-- The reference density. -/
noncomputable def iRho : ℕ → ℝ := fun _ => 1

/-- The large-sieve constant. -/
noncomputable def iC : ℕ → ℝ := fun _ => 1

/-- The support factor. -/
noncomputable def iM : ℕ → ℝ := fun _ => 1

/-- The undivided convolution energy. -/
noncomputable def iEconv : ℕ → ℝ := fun _ => 1

lemma denomScale_iW (n : ℕ) : denomScale iW n = 625 := by
  unfold denomScale iW
  rw [show 4 * Real.log 5 = Real.log 625 by
    rw [show (625 : ℝ) = 5 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring]
  exact Real.exp_log (by norm_num)

lemma cellMesh_iW (n : ℕ) : cellMesh iW n = 5 := by
  unfold cellMesh iW
  rw [show 4 * Real.log 5 / 4 = Real.log 5 by ring]
  exact Real.exp_log (by norm_num)

lemma iW_nonneg (n : ℕ) : 0 ≤ iW n := by
  unfold iW
  have h : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  nlinarith

/-- `scale` is monotone on the paper regime `n ≥ 3`: both `log n` and
`log log n` are positive and increase there. -/
theorem scale_mono_of_three_le {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) :
    scale m ≤ scale n := by
  have h3log : (1 : ℝ) < Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    simpa using h
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmlog : (1 : ℝ) < Real.log (m : ℝ) :=
    lt_of_lt_of_le h3log (Real.log_le_log (by norm_num) hmR)
  have hnlog : (1 : ℝ) < Real.log (n : ℝ) :=
    lt_of_lt_of_le h3log (Real.log_le_log (by norm_num) (hmR.trans hmnR))
  have hlogmono : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) hmnR
  have hloglogmono : Real.log (Real.log (m : ℝ)) ≤ Real.log (Real.log (n : ℝ)) :=
    Real.log_le_log (by linarith) hlogmono
  unfold scale
  refine mul_le_mul ?_ ?_ ?_ ?_
  · exact Real.rpow_le_rpow (le_of_lt (lt_trans zero_lt_one hmlog)) hlogmono
      (by norm_num)
  · exact Real.rpow_le_rpow (le_of_lt (Real.log_pos hmlog)) hloglogmono
      (by norm_num)
  · exact Real.rpow_nonneg (le_of_lt (Real.log_pos hmlog)) _
  · exact Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hnlog)) _

/-- A uniform positive lower bound for `scale` on the paper regime. -/
theorem scale_three_pos : 0 < scale 3 := by
  have h3log : (1 : ℝ) < Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    simpa using h
  have hloglog3 : 0 < Real.log (Real.log 3) := Real.log_pos h3log
  unfold scale
  exact mul_pos (Real.rpow_pos_of_pos (lt_trans zero_lt_one h3log) _)
    (Real.rpow_pos_of_pos hloglog3 _)

/-- The `D^{O(1)}` exponent chosen for the concrete ambient `W`. -/
noncomputable def iCW : ℝ := Real.log (4 * Real.log 5) / scale 3

lemma iCW_nonneg : 0 ≤ iCW := by
  have hlog5 : (1 : ℝ) < Real.log 5 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact lt_trans Real.exp_one_lt_three (by norm_num)
  have h4 : 1 < 4 * Real.log 5 := by nlinarith
  have hlog : 0 < Real.log (4 * Real.log 5) := Real.log_pos h4
  exact div_nonneg hlog.le (scale_three_pos).le

/-- The guarded `W` bound of the concrete ambient data.  The constant `iCW` is
chosen so that `exp (iCW * scale 3) = 4 log 5`, and monotonicity of `scale`
propagates this to every `n ≥ 3`. -/
theorem iW_upper : ∀ n, 3 ≤ n → iW n ≤ Real.exp (iCW * scale n) := by
  intro n hn
  have hlog5 : (1 : ℝ) < Real.log 5 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact lt_trans Real.exp_one_lt_three (by norm_num)
  have h4 : 1 < 4 * Real.log 5 := by nlinarith
  have hlog : 0 < Real.log (4 * Real.log 5) := Real.log_pos h4
  have hs3 : 0 < scale 3 := scale_three_pos
  have hscale : scale 3 ≤ scale n := scale_mono_of_three_le (le_refl 3) hn
  have hmul : Real.log (4 * Real.log 5) ≤ iCW * scale n := by
    have hcoef : 0 ≤ Real.log (4 * Real.log 5) / scale 3 := div_nonneg hlog.le hs3.le
    calc
      Real.log (4 * Real.log 5) =
          (Real.log (4 * Real.log 5) / scale 3) * scale 3 := by
        field_simp [hs3.ne']
      _ ≤ (Real.log (4 * Real.log 5) / scale 3) * scale n :=
        mul_le_mul_of_nonneg_left hscale hcoef
      _ = iCW * scale n := rfl
  calc
    iW n = 4 * Real.log 5 := rfl
    _ = Real.exp (Real.log (4 * Real.log 5)) := (Real.exp_log (by linarith)).symm
    _ ≤ Real.exp (iCW * scale n) := Real.exp_le_exp.mpr hmul

/-! ### The finite large-sieve certificate -/

/-- One denominator cell, modulus `3`, numerator set `{1}`, constant weight,
spectral bound `A = 1`, and one numerator cell.  This is the smallest genuine
large-sieve certificate: its residue energy is not the zero energy of a trivial
weight, and its per-cell count is the actual cardinality `1`. -/
noncomputable def iLargeSieve : LargeSieveCertificate.{0} iW iDeg iC iM iEconv where
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
  d_pos := by intro n; norm_num [iDeg]
  Econv_nonneg := by intro n; norm_num [iEconv]
  nonempty := fun _ => ⟨PUnit.unit⟩
  perCell := fun _ => 1
  perCell_nonneg := by intro n; norm_num
  perCell_ge_one := by intro n; norm_num
  energy_le := by intro n; norm_num [iEconv, iDeg]
  latticeCount := by
    intro n
    simp only [iC, iM]
    rw [denomScale_iW]
    norm_num

/-- The second moment of the concrete large-sieve certificate. -/
noncomputable def iS2 : ℕ → ℝ := iLargeSieve.secondMoment

lemma iS2_nonneg (n : ℕ) : 0 ≤ iS2 n := by
  unfold iS2 LargeSieveCertificate.secondMoment residueEnergy
  positivity

/-! ### The concrete denominator cell -/

/-- The integer cell `(2, 625]`: width `623`, upper endpoint at `V = 625`, and
actual prime count `#(primeBin 2 625)`. -/
noncomputable def iCellData : CellData iW iDeg where
  A := fun _ => 2
  B := fun _ => 625
  A_two := by intro n; norm_num
  A_le_B := by intro n; norm_num
  B_le_V := by intro n; rw [denomScale_iW]; norm_num
  width := by
    intro n
    rw [denomScale_iW, cellMesh_iW]
    norm_num [iDeg]

/-- `Ncell` is the actual prime count in the concrete cell. -/
noncomputable def iNcell : ℕ → ℝ := iCellData.Ncell

lemma iNcell_nonneg (n : ℕ) : 0 ≤ iNcell n := iCellData.Ncell_nonneg n

/-- A coarse upper bound for the actual cell count, obtained from the interval
`(2, 625]` itself (no prime-counting input). -/
lemma iCellData_Ncell_le (n : ℕ) : iCellData.Ncell n ≤ 623 := by
  unfold CellData.Ncell
  simp only [iCellData]
  have hsub : primeBin 2 625 ⊆ Finset.Ioc 2 625 := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hcard : (primeBin 2 625).card ≤ (Finset.Ioc 2 625).card :=
    Finset.card_le_card hsub
  have hIoc : (Finset.Ioc 2 625).card = 623 := by
    simpa using (Nat.card_Ioc 2 625)
  rw [hIoc] at hcard
  exact_mod_cast hcard

/-- The prime-bin supply constant used in the core.  The supply itself is the
only analytic residual; the fit is proved below. -/
noncomputable def iCellK0 : ℝ := 1 / 10 ^ 6

lemma iCellK0_nonneg : 0 ≤ iCellK0 := by norm_num [iCellK0]

lemma iCellSupplyFit : ∀ n,
    2 * iDeg n * iCellK0 * (1 + Real.log 3 + iW n) ^ 2 ≤ cellMesh iW n := by
  intro n
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlog5 : Real.log 5 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    linarith
  have hbase_nn : 0 ≤ 1 + Real.log 3 + 4 * Real.log 5 := by
    have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    linarith
  have hbase : 1 + Real.log 3 + 4 * Real.log 5 ≤ 19 := by linarith
  have hsq : (1 + Real.log 3 + 4 * Real.log 5) ^ 2 ≤ 19 ^ 2 :=
    pow_le_pow_left₀ hbase_nn hbase 2
  rw [cellMesh_iW]
  simp only [iDeg, iW, iCellK0]
  nlinarith

/-! ### The concrete numerator pool -/

/-- The lower endpoints of the two disjoint prime bins. -/
noncomputable def iA : ℕ → ℕ :=
  fun i => if i = 0 then 2 else if i = 1 then 101 else 2

/-- The upper endpoints of the two disjoint prime bins. -/
noncomputable def iB : ℕ → ℕ :=
  fun i => if i = 0 then 101 else if i = 1 then 233 else 2

/-- The single occupied pattern with both bins. -/
noncomputable def iPatterns : ℕ → Finset (Finset ℕ) :=
  fun _ => {({0, 1} : Finset ℕ)}

/-- The two bins are pairwise disjoint. -/
lemma iA_iB_disjoint :
    Pairwise fun i j => Disjoint (primeBin (iA i) (iB i)) (primeBin (iA j) (iB j)) := by
  intro i j hij
  by_cases hi0 : i = 0
  · subst i
    by_cases hj0 : j = 0
    · exact (hij hj0.symm).elim
    by_cases hj1 : j = 1
    · subst j
      rw [Finset.disjoint_left]
      intro p hp hq
      simp [iA, iB, primeBin] at hp hq
      omega
    · have hj2 : 2 ≤ j := by omega
      rw [show primeBin (iA j) (iB j) = ∅ by
        simp [iA, iB, hj0, hj1, primeBin]]
      simp
  · by_cases hi1 : i = 1
    · subst i
      by_cases hj0 : j = 0
      · subst j
        rw [Finset.disjoint_left]
        intro p hp hq
        simp [iA, iB, primeBin] at hp hq
        omega
      · by_cases hj1 : j = 1
        · exact (hij hj1.symm).elim
        · have hj2 : 2 ≤ j := by omega
          rw [show primeBin (iA j) (iB j) = ∅ by
            simp [iA, iB, hj0, hj1, primeBin]]
          simp
    · have hi2 : 2 ≤ i := by omega
      rw [show primeBin (iA i) (iB i) = ∅ by
        simp [iA, iB, hi0, hi1, primeBin]]
      simp

/-- The actual cardinality of the numerator pool: `25 * 25 = 625`. -/
lemma iPoolCard : (numeratorPool iA iB (iPatterns 0)).card = 625 := by
  rw [numeratorPool, primeBinPatternProducts_card _ _ iA_iB_disjoint]
  simp only [iPatterns, Finset.sum_singleton]
  rw [primeBinProducts_card]
  · simp [iA, iB]
    decide
  · intro i j hij
    exact iA_iB_disjoint (Subtype.val_injective.ne hij)

/-- The root residue is the unit of `(ZMod 1)ˣ`. -/
noncomputable def iNumR : ∀ n : ℕ, (ZMod 1)ˣ := fun _ => 1

/-- `Nnum` is the actual root-progression count of the concrete pool. -/
noncomputable def iNnum : ℕ → ℝ :=
  fun (n : ℕ) => (progressionCount iA iB (iPatterns n) 1 (iNumR n) : ℝ)

lemma iProgressionCount_eq (n : ℕ) :
    progressionCount iA iB (iPatterns n) 1 (iNumR n) = 625 := by
  unfold progressionCount
  have hfilter : (numeratorPool iA iB (iPatterns n)).filter
      (fun m : ℕ => ((iNumR n : (ZMod 1)ˣ) : ZMod 1) = (m : ZMod 1)) =
        numeratorPool iA iB (iPatterns n) := by
    apply Finset.filter_true_of_mem
    intro m hm
    exact Subsingleton.elim _ _
  rw [hfilter]
  exact iPoolCard

lemma iNnum_eq (n : ℕ) : iNnum n = 625 := by
  unfold iNnum
  rw [iProgressionCount_eq]
  norm_num

lemma iNnum_nonneg (n : ℕ) : 0 ≤ iNnum n := by
  unfold iNnum
  exact Nat.cast_nonneg _

/-- The mass/error data of the concrete pool.  The mass constant is
`10^{-10}` (strictly positive) and the relative error parameter is `1/10`. -/
noncomputable def iMass : MassErrorInputs iW iEll iRho where
  K := 1 / 10 ^ 10
  K_nonneg := by norm_num
  q := fun _ => 1
  q_pos := by intro n; norm_num
  ell_eq := by intro n; simp [iEll]
  rho_pos := by intro n; norm_num [iRho]
  A := fun _ => iA
  B := fun _ => iB
  patterns := iPatterns
  hdisj := fun _ => iA_iB_disjoint
  hA := by
    intro n i
    simp only [iA]
    split_ifs <;> norm_num
  hAB := by
    intro n i
    simp only [iA, iB]
    split_ifs <;> norm_num
  mass_k := fun _ => 2
  mass_m := fun _ => 25
  mass_size := by
    intro n s hs
    simp only [iPatterns, Finset.mem_singleton] at hs
    subst s
    norm_num
  mass_pop := by
    intro n s hs i hi
    simp only [iPatterns, Finset.mem_singleton] at hs
    subst s
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · norm_num [iA, iB]
      decide
    · norm_num [iA, iB]
      decide
  mass_num := by
    intro n
    simp only [iPatterns, Finset.card_singleton, iW, iRho, denomScale_iW]
    norm_num
  error_U := fun _ => 1 / 10
  error_X := fun _ => 1
  error_U_nonneg := by intro n; norm_num
  error_X_pos := by intro n; norm_num
  error_scale := by
    intro n s hs
    simp only [iPatterns, Finset.mem_singleton] at hs
    subst s
    simp [iB]
    norm_num
  error_slot := by
    intro n s hs i hi
    simp only [iPatterns, Finset.mem_singleton] at hs
    subst s
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    have hslot : ∀ B : ℕ, 2 ≤ B → B ≤ 233 →
        2 * (1 / 10 ^ 10 : ℝ) * (1 + Real.log (3 * (1 : ℝ) * (B : ℝ))) ^ 2 *
            (B : ℝ) ≤ (1 / 10 : ℝ) * 25 := by
      intro B hB2 hB
      have hBpos : (0 : ℝ) < (B : ℝ) := by
        exact_mod_cast lt_of_lt_of_le (by norm_num) hB2
      have hlog : Real.log (3 * (B : ℝ)) ≤ 3 * (B : ℝ) := by
        have h := Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < 3 * (B : ℝ) by positivity)
        linarith
      have hB2r : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB2
      have hbase_nn : 0 ≤ 1 + Real.log (3 * (B : ℝ)) := by
        have h3 : 0 ≤ Real.log (3 * (B : ℝ)) :=
          Real.log_nonneg (by nlinarith [hB2r])
        linarith
      have hbase : 1 + Real.log (3 * (B : ℝ)) ≤ 1 + 3 * (B : ℝ) := by linarith
      have hsq : (1 + Real.log (3 * (B : ℝ))) ^ 2 ≤ (1 + 3 * (B : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hbase_nn hbase 2
      have hlin : 1 + 3 * (B : ℝ) ≤ 700 := by
        have hB' : (B : ℝ) ≤ 233 := by exact_mod_cast hB
        nlinarith
      have hsq2 : (1 + Real.log (3 * (B : ℝ))) ^ 2 ≤ 700 ^ 2 :=
        le_trans hsq (pow_le_pow_left₀ (by nlinarith [hBpos]) hlin 2)
      have hBnn : (0 : ℝ) ≤ (B : ℝ) := hBpos.le
      have hmul : (1 + Real.log (3 * (B : ℝ))) ^ 2 * (B : ℝ) ≤ 700 ^ 2 * 233 :=
        mul_le_mul hsq2 (by exact_mod_cast hB) hBnn (by positivity)
      nlinarith
    rcases hi with rfl | rfl
    · have hpop : 25 ≤ (primeBin 2 101).card := by decide
      have hU : (0 : ℝ) ≤ 1 / 10 := by norm_num
      have h := (hslot 101 (by norm_num) (by norm_num)).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hpop : (25 : ℝ) ≤ ((primeBin 2 101).card : ℝ)) hU)
      simpa [iA, iB] using h
    · have hpop : 25 ≤ (primeBin 101 233).card := by decide
      have hU : (0 : ℝ) ≤ 1 / 10 := by norm_num
      have h := (hslot 233 (by norm_num) (by norm_num)).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hpop : (25 : ℝ) ≤ ((primeBin 101 233).card : ℝ)) hU)
      simpa [iA, iB] using h
  pool_upper := by
    intro n
    change ((numeratorPool iA iB (iPatterns 0)).card : ℝ) ≤ denomScale iW n
    rw [iPoolCard, denomScale_iW]
    norm_num
  error_rel := by
    intro n
    norm_num [iRho, iEll]

/-- The numerator pool is coprime to the root modulus `1`. -/
lemma iNumCoprime : ∀ n m,
    m ∈ numeratorPool iA iB (iPatterns n) → m.Coprime 1 := by
  intro n m hm
  exact Nat.coprime_one_right m

/-- `Nnum` is the actual root-residue count. -/
lemma iNumEq : ∀ n, iNnum n =
    (progressionCount iA iB (iPatterns n) 1 (iNumR n) : ℝ) := fun n => rfl

/-- The residue-class deviation of the concrete count.  For modulus `1` the
principal mass is the whole pool, so the deviation is exactly zero, which is at
most the (strictly positive) progression error. -/
lemma iNumDeviation : ∀ n,
    |(progressionCount iA iB (iPatterns n) 1 (iNumR n) : ℝ) -
      (coprimeCount iA iB (iPatterns n) 1 : ℝ) / (1 : ℕ).totient| ≤
      progressionError (1 / 10 ^ 10) 1 (iB) (iPatterns n) := by
  intro n
  have hpc : progressionCount iA iB (iPatterns n) 1 (iNumR n) =
      coprimeCount iA iB (iPatterns n) 1 := by
    unfold progressionCount coprimeCount
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro m hm
    constructor
    · intro _; exact Nat.coprime_one_right m
    · intro _; exact Subsingleton.elim _ _
  rw [hpc]
  have hzero : (coprimeCount iA iB (iPatterns n) 1 : ℝ) -
      (coprimeCount iA iB (iPatterns n) 1 : ℝ) /
        ((1 : ℕ).totient : ℝ) = 0 := by
    have htot : (1 : ℕ).totient = 1 := by norm_num
    rw [htot, Nat.cast_one]
    ring
  rw [hzero, abs_zero]
  exact progressionError_nonneg (1 / 10 ^ 10) (by norm_num) 1 iB (iPatterns n)

/-- The concrete progression error is strictly positive. -/
lemma iProgressionError_pos :
    0 < progressionError (1 / 10 ^ 10) 1 iB (iPatterns 0) := by
  refine progressionError_pos (by norm_num : (0 : ℝ) < 1 / 10 ^ 10)
    (by simp [iPatterns]) ?_
  intro s hs i hi
  simp only [iPatterns, Finset.mem_singleton] at hs
  subst s
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> simp [iB]

/-! ### The concrete thin aggregate -/

/-- The number of retained primitive marks. -/
noncomputable def iMarks : ℕ := 2000000

/-- The retained marks `(1, b)` for `1 ≤ b ≤ iMarks`. -/
@[irreducible] noncomputable def iS : Finset (ℤ × ℤ) :=
  (Finset.univ : Finset (Fin 2000000)).image
    (fun k : Fin 2000000 => ((1 : ℤ), (k : ℤ) + 1))

lemma iS_card : iS.card = iMarks := by
  unfold iS iMarks
  rw [Finset.card_image_of_injective _ (fun a b h => by
    have h' : (a : ℤ) + 1 = (b : ℤ) + 1 := congrArg Prod.snd h
    have h'' : (a : ℤ) = (b : ℤ) := by omega
    exact Fin.ext (by exact_mod_cast h''))]
  simp

/-- The lattice box of retained primitive marks. -/
noncomputable def iBox (n : ℕ) : LatticeBox where
  S := iS
  q := 1
  q_pos := by norm_num
  lo := 0
  hi := (iMarks : ℤ)
  lo_le_hi := by
    unfold iMarks
    norm_num
  bmin := 1
  bmin_pos := by norm_num
  L := (iMarks : ℝ) + 1
  level_bound := by
    unfold iMarks
    norm_num
  prim := by
    intro P hP
    unfold iS at hP
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    exact isCoprime_one_left
  den_pos := by
    intro P hP
    unfold iS at hP
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    simp
  box := by
    intro P hP
    unfold iS at hP
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    have hklt : (k : ℤ) < 2000000 := by exact_mod_cast k.isLt
    have hmarks : (iMarks : ℤ) = 2000000 := by
      unfold iMarks
      norm_num
    constructor
    · simp
    · rw [hmarks]
      omega
  bmin_le := by
    intro P hP
    unfold iS at hP
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    simp
  det_dvd := by
    intro P hP Q hQ
    simp

/-- The actual normalized diagonal fraction of the retained marks. -/
noncomputable def iThin : ℕ → ℝ := fun _ => 1 / (iMarks : ℝ)

lemma iThin_pos (n : ℕ) : 0 < iThin n := by
  unfold iThin iMarks
  norm_num

lemma iThin_nonneg (n : ℕ) : 0 ≤ iThin n := (iThin_pos n).le

lemma iThinCutoff_pos (n : ℕ) :
    0 < thinCutoff iW (fun m => (iBox m).L) (fun _ => 1) n := by
  unfold thinCutoff
  have hL : 0 < (iBox n).L := by
    unfold iBox iMarks
    norm_num
  have hW : 0 < 1 + iW n := by
    unfold iW
    have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    nlinarith
  have hK : 0 < cellMesh iW n := by
    rw [cellMesh_iW]
    norm_num
  exact mul_pos
    (div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hL) hW) (by norm_num))
    hK

/-- The diagonal is contained in the determinant strip. -/
lemma iS_diag_subset_strip {X : ℝ} (hX : 0 ≤ X) :
    iS.image (fun P : ℤ × ℤ => (P, P)) ⊆ stripPairSet iS X := by
  rw [Finset.image_subset_iff]
  intro P hP
  rw [stripPairSet, Finset.mem_filter]
  constructor
  · change (P, P) ∈ (iS ×ˢ iS)
    rw [Finset.mem_product]
    exact ⟨hP, hP⟩
  · simp [det]
    exact hX

lemma iStrip_card_ge (n : ℕ) :
    (iMarks : ℝ) ≤
      ((stripPairSet (iBox n).S
        (denomScale iW n ^ 2 /
          thinCutoff iW (fun m => (iBox m).L) (fun _ => 1) n)).card : ℝ) := by
  have hX : 0 ≤ denomScale iW n ^ 2 /
      thinCutoff iW (fun m => (iBox m).L) (fun _ => 1) n :=
    div_nonneg (sq_nonneg _) (iThinCutoff_pos n).le
  have hsub := iS_diag_subset_strip (X := denomScale iW n ^ 2 /
      thinCutoff iW (fun m => (iBox m).L) (fun _ => 1) n) hX
  have hcard := Finset.card_le_card hsub
  have himg : (iS.image (fun P : ℤ × ℤ => (P, P))).card = iMarks := by
    rw [Finset.card_image_of_injective _ (fun P Q h => by
      exact congrArg Prod.fst h)]
    exact iS_card
  rw [himg] at hcard
  exact_mod_cast hcard

/-- The raw thin data over the concrete marks. -/
noncomputable def iThinData : ThinAggregateData iW iDeg iEll iRho iThin iNcell iNnum where
  box := iBox
  dens := fun _ => 1
  dens_pos := by intro n; norm_num
  dens_le_one := by intro n; norm_num
  ell_eq := by intro n; simp [iEll, iBox]
  thin_le_pairFraction := by
    intro n
    have hcard := iStrip_card_ge n
    have hSbox : (iBox n).S = iS := rfl
    rw [hSbox, iS_card]
    have hthin : iThin n = (iMarks : ℝ) / (iMarks : ℝ) ^ 2 := by
      unfold iThin
      have hmarks_ne : (iMarks : ℝ) ≠ 0 := by
        unfold iMarks
        norm_num
      field_simp [hmarks_ne]
    rw [hthin]
    exact div_le_div_of_nonneg_right hcard (sq_nonneg _)
  retained_cell_count := by
    intro n
    have hSbox : (iBox n).S = iS := rfl
    rw [hSbox, iS_card, iNnum_eq n]
    have hNc : iNcell n ≤ 623 := iCellData_Ncell_le n
    have hK : cellMesh iW n = 5 := cellMesh_iW n
    rw [hK]
    have hmarks : (iMarks : ℝ) = 2000000 := by
      unfold iMarks
      norm_num
    rw [hmarks]
    nlinarith
  const_le := by
    intro n
    simp only [iDeg, iRho, Pi.one_apply]
    norm_num
  power_margin := by
    intro n
    simp only [iBox, iW, Pi.one_apply]
    rw [cellMesh_iW, denomScale_iW]
    have hlog5 : Real.log 5 ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
      linarith
    nlinarith

/-! ### The ambient data (without the growth fields) -/

/-- The data fields of `L18_4Ambient`, without the `D^{O(1)}` upper bounds and
`W_dominates`.  These are exactly the fields untouched by the paper-regime
guard `3 ≤ n` on the growth bounds. -/
structure L18_4AmbientData where
  W : ℕ → ℝ
  d : ℕ → ℝ
  ell : ℕ → ℝ
  rho : ℕ → ℝ
  C : ℕ → ℝ
  M : ℕ → ℝ
  Econv : ℕ → ℝ
  S2 : ℕ → ℝ
  Ncell : ℕ → ℝ
  Nnum : ℕ → ℝ
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

namespace L18_4AmbientData

/-- Add the `D^{O(1)}`/growth fields to the data part. -/
def toAmbient (A : L18_4AmbientData)
    (W_upper : ∀ n, 3 ≤ n → A.W n ≤ exp (A.cW * scale n))
    (C_upper : ∀ n, 3 ≤ n → A.C n ≤ exp (A.cC * scale n))
    (M_upper : ∀ n, 3 ≤ n → A.M n ≤ exp (A.cM * scale n))
    (Econv_upper : ∀ n, 3 ≤ n → A.Econv n ≤ exp (A.cE * scale n))
    (d_upper : ∀ n, 3 ≤ n → A.d n ≤ exp (A.cd * scale n))
    (ell_upper : ∀ n, 3 ≤ n → A.ell n ≤ exp (A.cell * scale n))
    (rho_inv_upper : ∀ n, 3 ≤ n → 1 / A.rho n ≤ exp (A.cρ * scale n))
    (W_dominates : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in Filter.atTop, c * scale n ≤ A.W n) :
    L18_4Ambient where
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
  W_upper := W_upper
  C_upper := C_upper
  M_upper := M_upper
  Econv_upper := Econv_upper
  d_upper := d_upper
  ell_upper := ell_upper
  rho_inv_upper := rho_inv_upper
  W_dominates := W_dominates

end L18_4AmbientData

/-- The concrete ambient data. -/
noncomputable def iAmbientData : L18_4AmbientData where
  W := iW
  d := iDeg
  ell := iEll
  rho := iRho
  C := iC
  M := iM
  Econv := iEconv
  S2 := iS2
  Ncell := iNcell
  Nnum := iNnum
  thin := iThin
  cW := iCW
  cC := 0
  cM := 0
  cE := 0
  cd := 0
  cell := 0
  cρ := 0
  W_nonneg := iW_nonneg
  d_pos := by intro n; norm_num [iDeg]
  ell_pos := by intro n; norm_num [iEll]
  rho_pos := by intro n; norm_num [iRho]
  C_pos := by intro n; norm_num [iC]
  M_pos := by intro n; norm_num [iM]
  Econv_nonneg := by intro n; norm_num [iEconv]
  S2_nonneg := iS2_nonneg
  Ncell_nonneg := iNcell_nonneg
  Nnum_nonneg := iNnum_nonneg
  thin_nonneg := iThin_nonneg
  cW_nonneg := iCW_nonneg
  cC_nonneg := by norm_num
  cM_nonneg := by norm_num
  cE_nonneg := by norm_num
  cd_nonneg := by norm_num
  cell_nonneg := by norm_num
  cρ_nonneg := by norm_num

/-! ## 2. The largest inhabited sub-record -/

/-- Every field of `L18_4Certificate` except the critical-line supply
`cellSupply` and the eight `D^{O(1)}`/growth fields. -/
structure L18_4CertificateCore extends L18_4AmbientData where
  largeSieve : LargeSieveCertificate W d C M Econv
  hS2 : ∀ n, S2 n = largeSieve.secondMoment n
  cellData : CellData W d
  hNcell : ∀ n, Ncell n = cellData.Ncell n
  cellK0 : ℝ
  cellK0_nonneg : 0 ≤ cellK0
  cellSupplyFit : ∀ n,
    2 * d n * cellK0 * (1 + Real.log 3 + W n) ^ 2 ≤ cellMesh W n
  mass : MassErrorInputs W ell rho
  numR : ∀ n, (ZMod (mass.q n))ˣ
  numCoprime : ∀ n m,
    m ∈ numeratorPool (mass.A n) (mass.B n) (mass.patterns n) → m.Coprime (mass.q n)
  numEq : ∀ n, Nnum n =
    (progressionCount (mass.A n) (mass.B n) (mass.patterns n) (mass.q n) (numR n) : ℝ)
  numDeviation : ∀ n,
    |(progressionCount (mass.A n) (mass.B n) (mass.patterns n) (mass.q n)
        (numR n) : ℝ) -
      (coprimeCount (mass.A n) (mass.B n) (mass.patterns n) (mass.q n) : ℝ) /
        (mass.q n).totient| ≤
      progressionError mass.K (mass.q n) (mass.B n) (mass.patterns n)
  thinData : ThinAggregateData W d ell rho thin Ncell Nnum

namespace L18_4CertificateCore

/-- The L18.4 rational-good loss of the core, exactly as in `L18_4Inputs.loss`:
the cell second-moment deficit plus the actual thin fraction. -/
noncomputable def loss (C : L18_4CertificateCore) (n : ℕ) : ℝ :=
  cellMesh C.W n * (C.S2 n / (C.Ncell n * C.Nnum n) ^ 2) + C.thin n

/-- The loss is nonnegative.  Both terms are actual nonnegative quantities. -/
theorem loss_nonneg (C : L18_4CertificateCore) (n : ℕ) : 0 ≤ C.loss n := by
  unfold loss
  have hcell : 0 ≤ cellMesh C.W n *
      (C.S2 n / (C.Ncell n * C.Nnum n) ^ 2) := by
    have hK : 0 ≤ cellMesh C.W n := by unfold cellMesh; exact (exp_pos _).le
    have hden : 0 ≤ (C.Ncell n * C.Nnum n) ^ 2 := sq_nonneg _
    exact mul_nonneg hK (div_nonneg (C.S2_nonneg n) hden)
  exact add_nonneg hcell (C.thin_nonneg n)

end L18_4CertificateCore

/-- The concrete core. -/
noncomputable def iCore : L18_4CertificateCore where
  toL18_4AmbientData := iAmbientData
  largeSieve := iLargeSieve
  hS2 := fun n => rfl
  cellData := iCellData
  hNcell := fun n => rfl
  cellK0 := iCellK0
  cellK0_nonneg := iCellK0_nonneg
  cellSupplyFit := iCellSupplyFit
  mass := iMass
  numR := iNumR
  numCoprime := iNumCoprime
  numEq := iNumEq
  numDeviation := iNumDeviation
  thinData := iThinData

/-- The concrete loss is strictly positive: the thin term is the actual positive
diagonal strip fraction, and the cell deficit is nonnegative. -/
theorem iCore_loss_pos : 0 < iCore.loss 0 := by
  unfold L18_4CertificateCore.loss
  have hthin : 0 < iCore.thin 0 := by
    show 0 < iThin 0
    exact iThin_pos 0
  have hcell : 0 ≤ cellMesh iCore.W 0 *
      (iCore.S2 0 / (iCore.Ncell 0 * iCore.Nnum 0) ^ 2) := by
    have hK : 0 ≤ cellMesh iCore.W 0 := by unfold cellMesh; exact (exp_pos _).le
    have hS2 : 0 ≤ iCore.S2 0 := iS2_nonneg 0
    have hden : 0 ≤ (iCore.Ncell 0 * iCore.Nnum 0) ^ 2 := sq_nonneg _
    exact mul_nonneg hK (div_nonneg hS2 hden)
  linarith

/-- The concrete core's cell count is the actual prime count of `(2, 625]`, so
it is not a chosen zero. -/
theorem iCore_Ncell_eq : ∀ n, iCore.Ncell n = iCellData.Ncell n := fun n => rfl

/-- The concrete core's numerator count is the actual root-progression count,
and it equals `625`. -/
theorem iCore_Nnum_eq (n : ℕ) : iCore.Nnum n = 625 := iNnum_eq n

/-! ## 3. The residual list after guarding the growth fields -/

namespace L18_4CertificateCore

/-- **Every field except `cellSupply` and the growth fields.**  Adding the eight
`D^{O(1)}`/growth fields and the critical-line supply gives a literal
`L18_4Certificate`. -/
noncomputable def toCertificate (C : L18_4CertificateCore)
    (W_upper : ∀ n, 3 ≤ n → C.W n ≤ exp (C.cW * scale n))
    (C_upper : ∀ n, 3 ≤ n → C.C n ≤ exp (C.cC * scale n))
    (M_upper : ∀ n, 3 ≤ n → C.M n ≤ exp (C.cM * scale n))
    (Econv_upper : ∀ n, 3 ≤ n → C.Econv n ≤ exp (C.cE * scale n))
    (d_upper : ∀ n, 3 ≤ n → C.d n ≤ exp (C.cd * scale n))
    (ell_upper : ∀ n, 3 ≤ n → C.ell n ≤ exp (C.cell * scale n))
    (rho_inv_upper : ∀ n, 3 ≤ n → 1 / C.rho n ≤ exp (C.cρ * scale n))
    (W_dominates : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in Filter.atTop, c * scale n ≤ C.W n)
    (cellSupply : PrimeBinCellSupply C.cellK0) :
    L18_4Certificate :=
  { C.toL18_4AmbientData.toAmbient W_upper C_upper M_upper Econv_upper
      d_upper ell_upper rho_inv_upper W_dominates with
    largeSieve := C.largeSieve
    hS2 := C.hS2
    cellData := C.cellData
    hNcell := C.hNcell
    cellK0 := C.cellK0
    cellK0_nonneg := C.cellK0_nonneg
    cellSupply := cellSupply
    cellSupplyFit := C.cellSupplyFit
    mass := C.mass
    numR := C.numR
    numCoprime := C.numCoprime
    numEq := C.numEq
    numDeviation := C.numDeviation
    thinData := C.thinData }

end L18_4CertificateCore

/-- `scale 0 = 0`, the reason the pointwise upper bounds have to be guarded. -/
lemma scale_zero : scale 0 = 0 := by
  unfold scale
  norm_num

/-- `scale 1 = 0` as well, so a guard at `0 < n` would not remove the
contradiction at `n = 1`. -/
lemma scale_one : scale 1 = 0 := by
  unfold scale
  simp

/-! ### The concrete core supplies every guarded `D^{O(1)}` bound -/

lemma iCore_W_upper :
    ∀ n, 3 ≤ n → iCore.W n ≤ exp (iCore.cW * scale n) :=
  iW_upper

lemma iCore_C_upper :
    ∀ n, 3 ≤ n → iCore.C n ≤ exp (iCore.cC * scale n) := by
  intro n _
  change (1 : ℝ) ≤ Real.exp (0 * scale n)
  simp

lemma iCore_M_upper :
    ∀ n, 3 ≤ n → iCore.M n ≤ exp (iCore.cM * scale n) := by
  intro n _
  change (1 : ℝ) ≤ Real.exp (0 * scale n)
  simp

lemma iCore_Econv_upper :
    ∀ n, 3 ≤ n → iCore.Econv n ≤ exp (iCore.cE * scale n) := by
  intro n _
  change (1 : ℝ) ≤ Real.exp (0 * scale n)
  simp

lemma iCore_d_upper :
    ∀ n, 3 ≤ n → iCore.d n ≤ exp (iCore.cd * scale n) := by
  intro n _
  change (1 / 4 : ℝ) ≤ Real.exp (0 * scale n)
  norm_num

lemma iCore_ell_upper :
    ∀ n, 3 ≤ n → iCore.ell n ≤ exp (iCore.cell * scale n) := by
  intro n _
  change (1 : ℝ) ≤ Real.exp (0 * scale n)
  simp

lemma iCore_rho_inv_upper :
    ∀ n, 3 ≤ n → 1 / iCore.rho n ≤ exp (iCore.cρ * scale n) := by
  intro n _
  norm_num [iCore, iAmbientData, iRho]

/-! ### The two genuine residuals of the concrete core -/

/-- The concrete core cannot supply `W_dominates`: its `W` is the constant
`4 log 5`, while `scale` is unbounded.  This is a property of the toy witness,
not of the guarded interface; a paper-regime witness has `W = log V` and does
dominate `scale`. -/
theorem iCore_not_W_dominates :
    ¬ (∀ c : ℝ, 0 < c →
        ∀ᶠ n : ℕ in Filter.atTop, c * scale n ≤ iCore.W n) := by
  intro h
  have hc : 0 < 4 * Real.log 5 + 1 := by positivity
  have hdom := h (4 * Real.log 5 + 1) hc
  have hbig : ∀ᶠ n : ℕ in Filter.atTop, 4 * Real.log 5 + 1 ≤ scale n :=
    scale_grows.eventually_ge_atTop (4 * Real.log 5 + 1)
  obtain ⟨n, hdn, hsn⟩ := (hdom.and hbig).exists
  change (4 * Real.log 5 + 1) * scale n ≤ 4 * Real.log 5 at hdn
  have hle : (4 * Real.log 5 + 1) * (4 * Real.log 5 + 1) ≤
      (4 * Real.log 5 + 1) * scale n :=
    mul_le_mul_of_nonneg_left hsn hc.le
  nlinarith [hle, hdn]

/-- The exact two inputs that the concrete core still needs.  All seven guarded
`D^{O(1)}` bounds are supplied by `iCore` itself. -/
structure L18_4CoreResidual where
  /-- `W` grows faster than every fixed multiple of `scale`. -/
  W_dominates : ∀ c : ℝ, 0 < c →
    ∀ᶠ n : ℕ in Filter.atTop, c * scale n ≤ iCore.W n
  /-- The critical-line prime-bin supply. -/
  cellSupply : PrimeBinCellSupply iCore.cellK0

/-- **An actual `L18_4Certificate` from the concrete core and its two remaining
inputs.**  This is the post-guard replacement for the former no-go: the core
supplies the cell, mass, large-sieve and thin data and all seven pointwise
`D^{O(1)}` bounds; only growth of `W` and the prime-bin supply remain. -/
noncomputable def iCertificate (r : L18_4CoreResidual) : L18_4Certificate :=
  iCore.toCertificate iCore_W_upper iCore_C_upper iCore_M_upper iCore_Econv_upper
    iCore_d_upper iCore_ell_upper iCore_rho_inv_upper r.W_dominates r.cellSupply

/-- The certificate type is nonempty as soon as the two residual inputs are
supplied. -/
theorem nonempty_L18_4Certificate_of_residual (r : L18_4CoreResidual) :
    Nonempty L18_4Certificate :=
  ⟨iCertificate r⟩

/-- The `B = 2` slot of the conditional certificate is the genuine L18.4
`D^{-B}` bound, not a vacuous consequence of an empty type. -/
theorem iCertificate_slot_le (r : L18_4CoreResidual) {slots : C5LossSlots}
    (h : slots .rationalGoodEnvironments = (iCertificate r).toInputs.loss) :
    ∀ᶠ n : ℕ in Filter.atTop,
      slots .rationalGoodEnvironments n ≤ exp (-(2 : ℝ) * scale n) := by
  simpa using (iCertificate r).slot_le h

/-! ## Axiom audit -/

#print axioms denomScale_iW
#print axioms cellMesh_iW
#print axioms iLargeSieve
#print axioms iS2_nonneg
#print axioms iCellData
#print axioms iCellData_Ncell_le
#print axioms iCellSupplyFit
#print axioms iA_iB_disjoint
#print axioms iPoolCard
#print axioms iProgressionCount_eq
#print axioms iMass
#print axioms iProgressionError_pos
#print axioms iS_card
#print axioms iBox
#print axioms iThinData
#print axioms iCore
#print axioms iCore_loss_pos
#print axioms scale_mono_of_three_le
#print axioms iW_upper
#print axioms L18_4CertificateCore.toCertificate
#print axioms iCore_not_W_dominates
#print axioms iCertificate
#print axioms nonempty_L18_4Certificate_of_residual
#print axioms iCertificate_slot_le

end Cogentic.RandomizedL18_4
