import Cogentic.RandomizedL18_4
import Cogentic.RandomizedPrimeBinProgression
import Cogentic.RandomizedPrimePatternProgression

/-!
# L18.4: the RH numerator count on a root-`ℓ` progression

`RandomizedL18_4.L18_4Inputs` assumes the paper-level numerator count

`denomScale W n * rho n / (2 * ell n) ≤ Nnum n`  (`cell_numerator_count`),

i.e. every denominator in a shrunken cell carries at least `V ρ / (2 ℓ)`
numerator points on the root-`ℓ` progression (KB G.3 p.107 and G.4;
`research/keybreak-balanced-ideal-pair-audit.md` §1).

This file does not assume that inequality.  It isolates the prime-bin
progression count that actually supplies it and proves the field from that
count:

1. **The numerator population.**  A finite union of occupied-bin patterns
   `primeBinPatternProducts A B patterns` inside the numerator interval.  Its
   size is at least the reference mass `V ρ` (`mass_lower`): in the notation of
   the audit, `ρ = S / X` is the reference density of the pattern support, and
   the numerator interval has length `X = V`.

2. **The RH progression estimate.**  For the root modulus `q = ℓ` and the root
   residue `r`, the number of pool elements congruent to `r` differs from the
   coprime principal mass `coprimeCount / φ(q)` by at most the explicit
   square-root error

   `∑ s ∈ patterns, ∏ i ∈ s, 2 K (1 + log (3 q Bᵢ))² √Bᵢ`

   (`deviation`).  This is exactly the residue-class statement of
   `PrimePatternProgressionBound`; `progressionDeviation_of_patternProgression`
   shows that the existing prime-bin progression count supplies it verbatim.
   The only remaining numerical input is that this error is at most half the
   reference count (`error_le`).

3. **The count is the lower bound.**  `reference_le_count` proves directly that
   the actual root-residue count is at least `V ρ / (2 ℓ)`.  `Nnum` is then
   identified with that count (`Nnum_eq_count`), not with a number chosen after
   the fact, and `numerator_count` rewrites the field onto the count.

From these three pieces the residue count is at least

`coprimeCount / φ(q) - error ≥ V ρ / ℓ - V ρ / (2 ℓ) = V ρ / (2 ℓ)`,

using only `φ(q) ≤ q = ℓ` and the coincidence of the pool with its coprime part.
This proves `cell_numerator_count`.  The reusable prime-bin inputs are
`PrimePatternProgressionBound` (and hence `PrimeBinProgressionBound`, or the
critical-line supply `primeBin_product_from_critical_line`).

Nothing here is a `sorry`, an `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL18_4

open Finset Real
open scoped BigOperators

open Cogentic.Randomized

/-! ## 1. The numerator pool and its progression count -/

/-- The integer numerator pool: all products obtained by choosing one prime from
each bin of an occupied-bin pattern, over the given family of patterns. -/
noncomputable def numeratorPool (A B : ℕ → ℕ) (patterns : Finset (Finset ℕ)) :
    Finset ℕ :=
  primeBinPatternProducts A B patterns

/-- The actual number of pool elements in the root residue `r` modulo `q`.  This
is the quantity the paper's numerator count lower-bounds. -/
noncomputable def progressionCount (A B : ℕ → ℕ) (patterns : Finset (Finset ℕ))
    (q : ℕ) (r : (ZMod q)ˣ) : ℕ :=
  ((numeratorPool A B patterns).filter
    (fun m : ℕ => (r : ZMod q) = (m : ZMod q))).card

/-- The number of pool elements coprime to the root modulus `q`.  When the bins
avoid the primes of `q` this is the whole pool; it is the principal mass in
`PrimePatternProgressionBound`. -/
noncomputable def coprimeCount (A B : ℕ → ℕ) (patterns : Finset (Finset ℕ))
    (q : ℕ) : ℕ :=
  ((numeratorPool A B patterns).filter (fun m : ℕ => m.Coprime q)).card

/-- The explicit square-root error of the prime-bin progression count at modulus
`q`: the product of the per-bin RH errors over each occupied-bin pattern,
summed over the patterns. -/
noncomputable def progressionError (K : ℝ) (q : ℕ) (B : ℕ → ℕ)
    (patterns : Finset (Finset ℕ)) : ℝ :=
  ∑ s ∈ patterns, ∏ i ∈ s,
    2 * K * (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 * Real.sqrt (B i : ℝ)

/-! ## 2. The RH progression estimate is the existing prime-bin count -/

/-- **`PrimePatternProgressionBound` is exactly the deviation field.**  For any
family of disjoint occupied bins, the residue count of the pattern products
deviates from the coprime principal mass by at most the explicit error
`progressionError K q B patterns`.  The modulus `K` is the one supplied by the
paper-level progression bound.  This shows that `NumeratorCountInputs.deviation`
is the existing prime-bin count and not an assumption of the conclusion. -/
theorem progressionDeviation_of_patternProgression
    (hprog : PrimePatternProgressionBound)
    {ι : Type} [DecidableEq ι] (A B : ι → ℕ) (patterns : Finset (Finset ι))
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) :
    ∃ K : ℝ, 0 ≤ K ∧
      |(((primeBinPatternProducts A B patterns).filter
            (fun m : ℕ => (r : ZMod q) = (m : ZMod q))).card : ℝ) -
          (((primeBinPatternProducts A B patterns).filter
            (fun m : ℕ => m.Coprime q)).card : ℝ) / (q.totient : ℝ)| ≤
        ∑ s ∈ patterns, ∏ i ∈ s,
          2 * K * (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
            Real.sqrt (B i : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := hprog
  refine ⟨K, hK, ?_⟩
  have h := hbound q r A B patterns hdisj hA hAB
  simpa only [Nat.cast_card] using h

/-- **The progression count from a critical line.**  The nonprincipal prime-count
estimate for `DirichletLZerosOnLine` gives the product bound, hence the bin
progression bound, hence the pattern progression bound.  This is the concrete
analytic supply behind `PrimePatternProgressionBound`. -/
theorem patternProgression_of_critical_line (line : DirichletLZerosOnLine) :
    PrimePatternProgressionBound :=
  primePattern_progression_of_bin_progression
    (primeBin_progression_of_product_bound (primeBin_product_from_critical_line line))

/-- **The deviation field from a critical line.**  Specializing
`progressionDeviation_of_patternProgression` to the critical-line supply removes
the abstract `PrimePatternProgressionBound` hypothesis. -/
theorem exists_deviation_of_critical_line (line : DirichletLZerosOnLine)
    {ι : Type} [DecidableEq ι] (A B : ι → ℕ) (patterns : Finset (Finset ι))
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) :
    ∃ K : ℝ, 0 ≤ K ∧
      |(((primeBinPatternProducts A B patterns).filter
            (fun m : ℕ => (r : ZMod q) = (m : ZMod q))).card : ℝ) -
          (((primeBinPatternProducts A B patterns).filter
            (fun m : ℕ => m.Coprime q)).card : ℝ) / (q.totient : ℝ)| ≤
        ∑ s ∈ patterns, ∏ i ∈ s,
          2 * K * (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
            Real.sqrt (B i : ℝ) :=
  progressionDeviation_of_patternProgression
    (patternProgression_of_critical_line line) A B patterns hdisj hA hAB q r

/-! ## 3. The numerator-count certificate -/

/-- **The explicit RH numerator-count inputs.**

`W` is `log V`, `ell` the root index, `rho` the reference density and `Nnum` the
per-denominator numerator count.  The structure carries:

* a family of disjoint prime bins `A B` and occupied-bin patterns `patterns`
  whose products form the numerator pool;
* the root modulus `q` with `q = ell` (`ell_eq`) and a root residue `r`;
* the reference mass bound `V ρ ≤ #pool` (`mass_lower`);
* the coprimality of the pool with `q` (`coprime_all`), so the principal mass in
  the progression bound is the whole pool;
* the identification of `Nnum` with the actual root-residue count
  (`Nnum_eq_count`);
* the explicit prime-bin progression deviation (`deviation`) with its error
  `progressionError`, and the numerical smallness of that error
  (`error_le`).

The inequality `V ρ / (2 ℓ) ≤ Nnum` is derived from these, not assumed. -/
structure NumeratorCountInputs (W ell rho Nnum : ℕ → ℝ) where
  /-- The prime-bin RH constant. -/
  K : ℝ
  /-- The prime-bin RH constant is nonnegative. -/
  K_nonneg : 0 ≤ K
  /-- The root modulus. -/
  q : ℕ → ℕ
  /-- The root modulus is positive. -/
  q_pos : ∀ n, 0 < q n
  /-- The root index `ℓ` is the root modulus. -/
  ell_eq : ∀ n, ell n = (q n : ℝ)
  /-- The reference density is positive. -/
  rho_pos : ∀ n, 0 < rho n
  /-- Lower endpoints of the prime bins. -/
  A : ℕ → ℕ → ℕ
  /-- Upper endpoints of the prime bins. -/
  B : ℕ → ℕ → ℕ
  /-- The occupied-bin patterns. -/
  patterns : ℕ → Finset (Finset ℕ)
  /-- The bins are pairwise disjoint at each stage. -/
  hdisj : ∀ n, Pairwise fun i j =>
    Disjoint (primeBin (A n i) (B n i)) (primeBin (A n j) (B n j))
  /-- Every bin starts at least at `2`. -/
  hA : ∀ n i, 2 ≤ A n i
  /-- Every bin is a genuine interval. -/
  hAB : ∀ n i, A n i ≤ B n i
  /-- The root residue. -/
  r : ∀ n, (ZMod (q n))ˣ
  /-- **Reference mass.**  The numerator pool has at least the reference mass
  `V ρ`. -/
  mass_lower : ∀ n,
    denomScale W n * rho n ≤ (numeratorPool (A n) (B n) (patterns n)).card
  /-- **Coprimality.**  Every numerator pool element is coprime to the root
  modulus, so the principal mass is the whole pool. -/
  coprime_all : ∀ n m,
    m ∈ numeratorPool (A n) (B n) (patterns n) → m.Coprime (q n)
  /-- **Identification with the count.**  `Nnum` is the actual number of pool
  elements in the root residue. -/
  Nnum_eq_count : ∀ n, Nnum n =
    (progressionCount (A n) (B n) (patterns n) (q n) (r n) : ℝ)
  /-- **RH progression deviation.**  The root-residue count differs from the
  coprime principal mass by at most the explicit prime-bin error. -/
  deviation : ∀ n,
    |(progressionCount (A n) (B n) (patterns n) (q n) (r n) : ℝ) -
      (coprimeCount (A n) (B n) (patterns n) (q n) : ℝ) / (q n).totient| ≤
      progressionError K (q n) (B n) (patterns n)
  /-- **Smallness of the RH error.**  The explicit error is at most half the
  reference numerator count. -/
  error_le : ∀ n,
    progressionError K (q n) (B n) (patterns n) ≤
      denomScale W n * rho n / (2 * ell n)

namespace NumeratorCountInputs

/-- **The actual progression count dominates the reference count.**

The count of numerator points in the root residue is
`coprimeCount / φ(q) - error` at least.  Since the pool is coprime to `q` and
`q = ℓ`, the principal mass is at least `V ρ / φ(q) ≥ V ρ / ℓ`; the explicit
error is at most `V ρ / (2 ℓ)`.  Hence the actual root-residue count is at
least `V ρ / (2 ℓ)`. -/
theorem reference_le_count {W ell rho Nnum : ℕ → ℝ}
    (N : NumeratorCountInputs W ell rho Nnum) (n : ℕ) :
    denomScale W n * rho n / (2 * ell n) ≤
      (progressionCount (N.A n) (N.B n) (N.patterns n) (N.q n) (N.r n) : ℝ) := by
  have hV : 0 < denomScale W n := by
    unfold denomScale
    exact exp_pos _
  have hrho : 0 < rho n := N.rho_pos n
  have hVR : 0 ≤ denomScale W n * rho n := mul_nonneg hV.le hrho.le
  have hq : 0 < (N.q n : ℝ) := by exact_mod_cast N.q_pos n
  have hell : 0 < ell n := by
    rw [N.ell_eq n]
    exact hq
  have hphi : 0 < (N.q n).totient := Nat.totient_pos.mpr (N.q_pos n)
  have hphiR : (0 : ℝ) < ((N.q n).totient : ℝ) := by exact_mod_cast hphi
  have hphi_leR : ((N.q n).totient : ℝ) ≤ (N.q n : ℝ) := by
    exact_mod_cast Nat.totient_le (N.q n)
  -- The pool is coprime to the root modulus.
  have hcop : coprimeCount (N.A n) (N.B n) (N.patterns n) (N.q n) =
      (numeratorPool (N.A n) (N.B n) (N.patterns n)).card := by
    unfold coprimeCount
    rw [Finset.filter_true_of_mem (fun m hm => N.coprime_all n m hm)]
  -- The deviation in terms of the total pool mass.
  have hdev :
      |(progressionCount (N.A n) (N.B n) (N.patterns n) (N.q n) (N.r n) : ℝ) -
        ((numeratorPool (N.A n) (N.B n) (N.patterns n)).card : ℝ) /
          ((N.q n).totient : ℝ)| ≤
        progressionError N.K (N.q n) (N.B n) (N.patterns n) := by
    have h := N.deviation n
    rw [hcop] at h
    exact h
  -- The reference mass is at most the pool size.
  have hmass : denomScale W n * rho n ≤
      ((numeratorPool (N.A n) (N.B n) (N.patterns n)).card : ℝ) :=
    N.mass_lower n
  -- Principal mass divided by `φ(q)` dominates `V ρ / φ(q)`.
  have h1 : denomScale W n * rho n / ((N.q n).totient : ℝ) ≤
      ((numeratorPool (N.A n) (N.B n) (N.patterns n)).card : ℝ) /
        ((N.q n).totient : ℝ) :=
    div_le_div_of_nonneg_right hmass hphiR.le
  -- `1 / φ(q) ≥ 1 / q`, so `V ρ / q ≤ V ρ / φ(q)`.
  have h2 : denomScale W n * rho n / (N.q n : ℝ) ≤
      denomScale W n * rho n / ((N.q n).totient : ℝ) :=
    div_le_div_of_nonneg_left hVR hphiR hphi_leR
  -- Rewrite the root modulus as `ℓ`.
  have h3 : denomScale W n * rho n / ell n ≤
      ((numeratorPool (N.A n) (N.B n) (N.patterns n)).card : ℝ) /
        ((N.q n).totient : ℝ) := by
    rw [N.ell_eq n]
    exact h2.trans h1
  -- The deviation gives `principal - error ≤ count`.
  have h4 : ((numeratorPool (N.A n) (N.B n) (N.patterns n)).card : ℝ) /
        ((N.q n).totient : ℝ) -
        progressionError N.K (N.q n) (N.B n) (N.patterns n) ≤
      (progressionCount (N.A n) (N.B n) (N.patterns n) (N.q n) (N.r n) : ℝ) := by
    have h := (abs_le.mp hdev).1
    linarith only [h]
  -- Combine the principal mass, the deviation and the error bound.
  have hhalf :
      denomScale W n * rho n / (2 * ell n) =
        denomScale W n * rho n / ell n -
          denomScale W n * rho n / (2 * ell n) := by
    have h2ell : (2 * ell n : ℝ) ≠ 0 := by positivity
    field_simp [hell.ne', h2ell]
    ring
  have hlow : denomScale W n * rho n / ell n -
      progressionError N.K (N.q n) (N.B n) (N.patterns n) ≤
      (progressionCount (N.A n) (N.B n) (N.patterns n) (N.q n) (N.r n) : ℝ) := by
    linarith only [h3, h4]
  have herr := N.error_le n
  linarith only [hhalf, hlow, herr]

/-- **`cell_numerator_count` from the RH progression count.**  Since `Nnum` is
the actual count, the count bound is exactly the field. -/
theorem numerator_count {W ell rho Nnum : ℕ → ℝ}
    (N : NumeratorCountInputs W ell rho Nnum) (n : ℕ) :
    denomScale W n * rho n / (2 * ell n) ≤ Nnum n := by
  rw [N.Nnum_eq_count n]
  exact N.reference_le_count n

/-- The count bound for every stage. -/
theorem numerator_count_all {W ell rho Nnum : ℕ → ℝ}
    (N : NumeratorCountInputs W ell rho Nnum) :
    ∀ n, denomScale W n * rho n / (2 * ell n) ≤ Nnum n :=
  fun n => N.numerator_count n

end NumeratorCountInputs

/-! ## 4. Replacement of the `L18_4Inputs.cell_numerator_count` field -/

namespace L18_4Inputs

variable (I : L18_4Inputs)

/-- **The `cell_numerator_count` field is reduced to `NumeratorCountInputs`.**
A certificate for the numerator data of `I` implies the inequality assumed by
its `cell_numerator_count` field. -/
theorem cell_numerator_count_of_inputs
    (N : NumeratorCountInputs I.W I.ell I.rho I.Nnum) :
    ∀ n, denomScale I.W n * I.rho n / (2 * I.ell n) ≤ I.Nnum n :=
  fun n => N.numerator_count n

/-- **Literal replacement of the `cell_numerator_count` proof field.**  All
other fields of `I` are kept; `cell_numerator_count` is derived from the
prime-bin progression count in `N` instead of being assumed. -/
noncomputable def replaceCellNumeratorCount
    (N : NumeratorCountInputs I.W I.ell I.rho I.Nnum) : L18_4Inputs :=
  { I with cell_numerator_count := fun n => N.numerator_count n }

/-- Replacing the numerator-count proof field does not change the count data or
the rational-good deficit. -/
@[simp] theorem replaceCellNumeratorCount_Nnum
    (N : NumeratorCountInputs I.W I.ell I.rho I.Nnum) :
    (I.replaceCellNumeratorCount N).Nnum = I.Nnum := rfl

/-- The replacement keeps the cell mean, since `Nnum` and `Ncell` are untouched. -/
@[simp] theorem replaceCellNumeratorCount_muCell
    (N : NumeratorCountInputs I.W I.ell I.rho I.Nnum) :
    (I.replaceCellNumeratorCount N).muCell = I.muCell := rfl

end L18_4Inputs

/-! ## Axiom audit -/

#print axioms progressionDeviation_of_patternProgression
#print axioms patternProgression_of_critical_line
#print axioms exists_deviation_of_critical_line
#print axioms NumeratorCountInputs.reference_le_count
#print axioms NumeratorCountInputs.numerator_count
#print axioms NumeratorCountInputs.numerator_count_all
#print axioms L18_4Inputs.cell_numerator_count_of_inputs
#print axioms L18_4Inputs.replaceCellNumeratorCount
#print axioms L18_4Inputs.replaceCellNumeratorCount_Nnum
#print axioms L18_4Inputs.replaceCellNumeratorCount_muCell

end Cogentic.RandomizedL18_4
