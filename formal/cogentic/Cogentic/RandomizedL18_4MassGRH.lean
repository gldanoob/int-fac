import Cogentic.RandomizedL18_4Mass
import Cogentic.RandomizedL18_4CellFinish

/-!
# L18.4: the mass/progression inputs from the critical line

`RandomizedL18_4Mass.MassErrorInputs` isolates the two numerical residuals of
the L18.4 numerator count behind the actual prime-bin pool:

* `mass_pop`, the lower population of every occupied bin;
* `error_slot`, the per-bin square-root error being dominated by the actual bin
  count.

Both are supplied by the critical-line prime-bin estimate.  This file proves
them from `DirichletLZerosOnLine`, and at the same time fixes the progression
constant of `PrimePatternProgressionBound` to an explicit value.

## 1. The explicit progression constant

`primePatternProgressionBound_of_criticalLine` gives

```
∃ K ≥ 0, ∀ q r A B patterns,
  |#{pool in r mod q} - #(pool coprime to q)/φ(q)|
    ≤ ∑ s ∈ patterns, ∏ i ∈ s, 2 K (1 + log (3 q Bᵢ))² √Bᵢ
```

with the concrete constant

```
massProgressionK line = max (the existing critical-line constant) 1.
```

The `max … 1` makes the constant *strictly positive*, so the resulting error is
never the zero error.  The bound `massProgressionK_deviation` is the same
orthogonality estimate as `PrimePatternProgressionBound`, restated at this fixed
constant; it is obtained from the existing critical-line bound by monotonicity
of the error in `K`.

## 2. The mass/error reduction

`MassGRHData` is `MassErrorInputs` with the two GRH-facing fields removed:

* `mass_pop` is replaced by the explicit width inequality
  `mass_m · 2 log B ≤ B - A`, which together with the critical-line supply gives
  `mass_m ≤ #(primeBin A B)`;
* `error_slot` is replaced by the explicit width inequality
  `4 log B · K (1 + log (3 q B))² B ≤ U (B - A)`
  together with the supply fit
  `K₀ (1 + log (3 B))² √B ≤ (B - A)/2`.

`toMassErrorInputs` proves both missing fields from
`primeBin_supply_of_critical_line` and `error_slot_of_primeBinSupply`.  Hence the
literal `MassErrorInputs.error_le`

```
progressionError (massProgressionK line) q B patterns
  ≤ denomScale W n * rho n / (2 * ell n)
```

is a theorem, not an input.  The residue-class deviation of
`NumeratorCountInputs` is also derived from `massProgressionK_deviation`, so no
part of the progression estimate is assumed.

## 3. Nonzero error

`massProgressionK_pos` proves the constant is positive.  Consequently, on any
stage with a nonempty occupied pattern and bins of size at least two,
`MassGRHData.progressionError_pos` proves the explicit error is strictly
positive.  The error is therefore genuinely nonzero, not a zero placeholder.

## 4. No missing PNT-in-AP input

The critical line already supplies both estimates needed here: the principal
theta estimate gives `PrimeBinSupply` (used for `mass_pop` and `error_slot`),
and the nonprincipal character estimate gives the product/progression bound
(used for the pattern deviation).  No separate PNT-in-AP hypothesis is required.
The only residual fields of `MassGRHData` are the finite counting/width
inequalities `mass_num`, `mass_pop_width`, `error_width`, `error_scale`,
`supply_fit`, `pool_upper` and `error_rel`; they contain no prime-count
asymptotic.

Nothing here is a `sorry`, an `axiom`, or a `native_decide`; no count, mass or
error is set to zero.
-/

namespace Cogentic.RandomizedL18_4

open Finset Real
open scoped BigOperators

open Cogentic.Randomized

set_option linter.style.haveILetI false

/-! ## 1. The explicit critical-line constant for the pattern progression -/

/-- The critical-line constant of `PrimePatternProgressionBound`, made strictly
positive.  The underlying constant is the one extracted from
`patternProgression_of_critical_line`; taking the maximum with `1` leaves the
estimate valid and records that the error term is nonzero. -/
noncomputable def massProgressionK (line : DirichletLZerosOnLine) : ℝ :=
  max (Classical.choose (patternProgression_of_critical_line line)) 1

/-- The explicit progression constant is nonnegative. -/
theorem massProgressionK_nonneg (line : DirichletLZerosOnLine) :
    0 ≤ massProgressionK line := by
  unfold massProgressionK
  exact le_trans (Classical.choose_spec (patternProgression_of_critical_line line)).1
    (le_max_left _ _)

/-- The explicit progression constant is strictly positive. -/
theorem massProgressionK_pos (line : DirichletLZerosOnLine) :
    0 < massProgressionK line := by
  unfold massProgressionK
  exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)

/-- The underlying critical-line constant is at most `massProgressionK line`. -/
theorem le_massProgressionK (line : DirichletLZerosOnLine) :
    Classical.choose (patternProgression_of_critical_line line) ≤
      massProgressionK line := by
  unfold massProgressionK
  exact le_max_left _ _

/-- Monotonicity of the explicit pattern-error sum in the constant, for an
arbitrary slot type. -/
theorem progressionError_sum_mono
    {K K' : ℝ} (hK : 0 ≤ K) (hKK' : K ≤ K')
    {ι : Type} (q : ℕ) (B : ι → ℕ) (patterns : Finset (Finset ι)) :
    (∑ s ∈ patterns, ∏ i ∈ s,
        2 * K * (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
          Real.sqrt (B i : ℝ)) ≤
      (∑ s ∈ patterns, ∏ i ∈ s,
        2 * K' * (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
          Real.sqrt (B i : ℝ)) := by
  refine Finset.sum_le_sum ?_
  intro s _
  refine Finset.prod_le_prod ?nonneg ?step
  · intro i _
    exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
      (Real.sqrt_nonneg _)
  · intro i _
    have h2 : 2 * K ≤ 2 * K' := by linarith
    have hg :
        0 ≤ (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
          Real.sqrt (B i : ℝ) :=
      mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h := mul_le_mul_of_nonneg_right h2 hg
    calc
      2 * K * (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
            Real.sqrt (B i : ℝ)
          = (2 * K) * ((1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
              Real.sqrt (B i : ℝ)) := by ring
      _ ≤ (2 * K') * ((1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
              Real.sqrt (B i : ℝ)) := h
      _ = 2 * K' * (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
              Real.sqrt (B i : ℝ) := by ring

/-- **The prime-pattern progression error bound at the explicit constant.** -/
theorem massProgressionK_bound (line : DirichletLZerosOnLine) :
    ∀ (q : ℕ) [NeZero q] (r : (ZMod q)ˣ)
      {ι : Type} [DecidableEq ι] (A B : ι → ℕ) (patterns : Finset (Finset ι)),
      Pairwise (fun i j =>
        Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
      (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
      |(((primeBinPatternProducts A B patterns).filter
            (fun m : ℕ => (r : ZMod q) = (m : ZMod q))).card : ℝ) -
          (((primeBinPatternProducts A B patterns).filter
            (fun m : ℕ => m.Coprime q)).card : ℝ) / (q.totient : ℝ)| ≤
        ∑ s ∈ patterns, ∏ i ∈ s,
          2 * massProgressionK line *
            (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 * Real.sqrt (B i : ℝ) := by
  intro q _ r ι _ A B patterns hdisj hA hAB
  obtain ⟨hK0, hbound⟩ :=
    Classical.choose_spec (patternProgression_of_critical_line line)
  have h := hbound q r A B patterns hdisj hA hAB
  exact h.trans
    (progressionError_sum_mono hK0 (le_massProgressionK line) q B patterns)

/-- **The critical-line pattern progression bound as a `Prop`.**  This is
`PrimePatternProgressionBound`, with the constant `massProgressionK line`
exhibited. -/
theorem primePatternProgressionBound_of_criticalLine
    (line : DirichletLZerosOnLine) : PrimePatternProgressionBound := by
  refine ⟨massProgressionK line, massProgressionK_nonneg line, ?_⟩
  intro q _ r ι _ A B patterns hdisj hA hAB
  exact massProgressionK_bound line q r A B patterns hdisj hA hAB

/-- The pattern progression bound specialized to the actual numerator pool
indexed by `ℕ`, in the `progressionError` notation of the L18.4 numerator. -/
theorem massProgressionK_deviation (line : DirichletLZerosOnLine)
    (A B : ℕ → ℕ) (patterns : Finset (Finset ℕ))
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) :
    |(((primeBinPatternProducts A B patterns).filter
          (fun m : ℕ => (r : ZMod q) = (m : ZMod q))).card : ℝ) -
        (((primeBinPatternProducts A B patterns).filter
          (fun m : ℕ => m.Coprime q)).card : ℝ) / (q.totient : ℝ)| ≤
      progressionError (massProgressionK line) q B patterns := by
  simpa only [progressionError] using
    massProgressionK_bound line q r A B patterns hdisj hA hAB

/-! ## 2. The prime-bin supply and the two mass/error fields -/

/-- The prime-bin supply constant extracted from the critical line. -/
noncomputable def massSupplyK (line : DirichletLZerosOnLine) : ℝ :=
  Classical.choose (primeBinSupply_of_critical_line line)

/-- The supply constant is nonnegative. -/
theorem massSupplyK_nonneg (line : DirichletLZerosOnLine) :
    0 ≤ massSupplyK line :=
  (Classical.choose_spec (primeBinSupply_of_critical_line line)).1

/-- The supply constant satisfies the finite prime-bin supply inequality. -/
theorem massSupplyK_supply (line : DirichletLZerosOnLine) :
    PrimeBinSupply (massSupplyK line) :=
  (Classical.choose_spec (primeBinSupply_of_critical_line line)).2

/-- **The bin population from the critical-line supply.**  If the supply error
fits in half the bin width and `m · 2 log B ≤ B - A`, then the bin contains at
least `m` primes. -/
theorem mass_pop_of_primeBinSupply {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hsupply : ∀ A B : ℕ, 2 ≤ A → A ≤ B →
      (B : ℝ) - (A : ℝ) -
          K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
        ((primeBin A B).card : ℝ) * Real.log (B : ℝ))
    {A B m : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B)
    (hsmall : K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
      ((B : ℝ) - (A : ℝ)) / 2)
    (hm : (m : ℝ) * (2 * Real.log (B : ℝ)) ≤ (B : ℝ) - (A : ℝ)) :
    m ≤ (primeBin A B).card := by
  have hB2 : 2 ≤ B := le_trans hA hAB
  have hB1 : (1 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hB2)
  have hlogpos : 0 < Real.log (B : ℝ) := Real.log_pos hB1
  have hcount :
      ((B : ℝ) - (A : ℝ)) / (2 * Real.log (B : ℝ)) ≤
        ((primeBin A B).card : ℝ) :=
    cell_card_lower_of_primeBinSupply hK0 hsupply hA hAB
      (lg := Real.log (B : ℝ)) hlogpos le_rfl hsmall
  have hml :
      (m : ℝ) ≤ ((B : ℝ) - (A : ℝ)) / (2 * Real.log (B : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  exact_mod_cast hml.trans hcount

/-- **The per-bin RH error slot from the critical line.**  The critical-line
supply gives the actual bin population; a width condition then dominates the
squared per-bin error. -/
theorem error_slot_of_criticalLine (line : DirichletLZerosOnLine) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧
      ∀ {q A B : ℕ} {K U : ℝ}, 0 ≤ U → 2 ≤ A → A ≤ B → 1 ≤ q →
        (4 * Real.log (B : ℝ) * K *
            (1 + Real.log (3 * (q : ℝ) * (B : ℝ))) ^ 2 * (B : ℝ) ≤
          U * ((B : ℝ) - (A : ℝ))) →
        (K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
          ((B : ℝ) - (A : ℝ)) / 2) →
        2 * K * (1 + Real.log (3 * (q : ℝ) * (B : ℝ))) ^ 2 * (B : ℝ) ≤
          U * ((primeBin A B).card : ℝ) := by
  obtain ⟨K0, hK0, hsupply⟩ := primeBinSupply_of_critical_line line
  refine ⟨K0, hK0, ?_⟩
  intro q A B K U hU hA hAB hq hwidth hsmall
  exact error_slot_of_primeBinSupply hK0 hU hsupply hA hAB hq hwidth hsmall

/-! ## 3. The mass/error bundle with the GRH fields discharged -/

/-- **The L18.4 mass/error data with the two GRH-facing fields reduced to
explicit width inequalities.**

Everything is as in `MassErrorInputs`, except that `mass_pop` and `error_slot`
are not assumed.  They are replaced by

* `mass_pop_width : mass_m · 2 log B ≤ B - A`, and
* `supply_fit` together with `error_width`, the two half-width conditions.

The constant of the progression error is the explicit `massProgressionK line`.
-/
structure MassGRHData (line : DirichletLZerosOnLine)
    (W ell rho : ℕ → ℝ) where
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
  /-- The uniform number of slots of a pattern. -/
  mass_k : ℕ → ℕ
  /-- The uniform lower population target of an occupied bin. -/
  mass_m : ℕ → ℕ
  /-- Every occupied pattern has `mass_k` slots. -/
  mass_size : ∀ n s, s ∈ patterns n → s.card = mass_k n
  /-- **The explicit population width.**  The target `mass_m` fits in the bin
  in `log B` units. -/
  mass_pop_width : ∀ n s, s ∈ patterns n → ∀ i ∈ s,
    (mass_m n : ℝ) * (2 * Real.log (B n i : ℝ)) ≤
      (B n i : ℝ) - (A n i : ℝ)
  /-- **Pattern-product population.** -/
  mass_num : ∀ n,
    denomScale W n * rho n ≤
      (patterns n).card * (mass_m n : ℝ) ^ (mass_k n)
  /-- The relative error parameter `U` of the product saving. -/
  error_U : ℕ → ℝ
  /-- The product scale `X` of the product saving. -/
  error_X : ℕ → ℝ
  /-- `U` is nonnegative. -/
  error_U_nonneg : ∀ n, 0 ≤ error_U n
  /-- `X` is positive. -/
  error_X_pos : ∀ n, 0 < error_X n
  /-- Every occupied pattern product has size at least `X`. -/
  error_scale : ∀ n s, s ∈ patterns n → error_X n ≤ ∏ i ∈ s, (B n i : ℝ)
  /-- **The supply fit.**  The critical-line supply error fits in half the bin
  width. -/
  supply_fit : ∀ n s, s ∈ patterns n → ∀ i ∈ s,
    massSupplyK line * (1 + Real.log (3 * (B n i : ℝ))) ^ 2 *
        Real.sqrt (B n i : ℝ) ≤
      ((B n i : ℝ) - (A n i : ℝ)) / 2
  /-- **The error width.**  The squared per-bin RH error is dominated by
  `U` times the bin width. -/
  error_width : ∀ n s, s ∈ patterns n → ∀ i ∈ s,
    4 * Real.log (B n i : ℝ) * massProgressionK line *
        (1 + Real.log (3 * (q n : ℝ) * (B n i : ℝ))) ^ 2 * (B n i : ℝ) ≤
      error_U n * ((B n i : ℝ) - (A n i : ℝ))
  /-- **Upper support count.** -/
  pool_upper : ∀ n,
    ((numeratorPool (A n) (B n) (patterns n)).card : ℝ) ≤ denomScale W n
  /-- **Numerical smallness of the relative error.** -/
  error_rel : ∀ n,
    error_U n ^ mass_k n / Real.sqrt (error_X n) ≤ rho n / (2 * ell n)

namespace MassGRHData

variable {line : DirichletLZerosOnLine} {W ell rho : ℕ → ℝ}

/-- **The actual bin population**, proved from the critical-line supply. -/
theorem mass_pop (G : MassGRHData line W ell rho) (n : ℕ)
    (s : Finset ℕ) (hs : s ∈ G.patterns n) (i : ℕ) (hi : i ∈ s) :
    G.mass_m n ≤ (primeBin (G.A n i) (G.B n i)).card :=
  mass_pop_of_primeBinSupply (massSupplyK_nonneg line)
    (massSupplyK_supply line) (G.hA n i) (G.hAB n i)
    (G.supply_fit n s hs i hi) (G.mass_pop_width n s hs i hi)

/-- **The per-bin RH error slot**, proved from the critical-line supply. -/
theorem error_slot (G : MassGRHData line W ell rho) (n : ℕ)
    (s : Finset ℕ) (hs : s ∈ G.patterns n) (i : ℕ) (hi : i ∈ s) :
    2 * massProgressionK line *
        (1 + Real.log (3 * (G.q n : ℝ) * (G.B n i : ℝ))) ^ 2 *
          (G.B n i : ℝ) ≤
      G.error_U n * ((primeBin (G.A n i) (G.B n i)).card : ℝ) :=
  error_slot_of_primeBinSupply (massSupplyK_nonneg line)
    (G.error_U_nonneg n) (massSupplyK_supply line) (G.hA n i) (G.hAB n i)
    (Nat.succ_le_of_lt (G.q_pos n))
    (G.error_width n s hs i hi) (G.supply_fit n s hs i hi)

/-- **The literal `MassErrorInputs`, with both GRH fields proved.** -/
noncomputable def toMassErrorInputs (G : MassGRHData line W ell rho) :
    MassErrorInputs W ell rho where
  K := massProgressionK line
  K_nonneg := massProgressionK_nonneg line
  q := G.q
  q_pos := G.q_pos
  ell_eq := G.ell_eq
  rho_pos := G.rho_pos
  A := G.A
  B := G.B
  patterns := G.patterns
  hdisj := G.hdisj
  hA := G.hA
  hAB := G.hAB
  mass_k := G.mass_k
  mass_m := G.mass_m
  mass_size := G.mass_size
  mass_pop := G.mass_pop
  mass_num := G.mass_num
  error_U := G.error_U
  error_X := G.error_X
  error_U_nonneg := G.error_U_nonneg
  error_X_pos := G.error_X_pos
  error_scale := G.error_scale
  error_slot := G.error_slot
  pool_upper := G.pool_upper
  error_rel := G.error_rel

/-- **The mass lower bound on the actual pool.** -/
theorem mass_lower (G : MassGRHData line W ell rho) (n : ℕ) :
    denomScale W n * rho n ≤
      ((numeratorPool (G.A n) (G.B n) (G.patterns n)).card : ℝ) :=
  (G.toMassErrorInputs).mass_lower n

/-- **`MassErrorInputs.error_le`, with the critical-line constant and the
critical-line bin supply.**  The explicit progression error is at most half the
reference count. -/
theorem error_le (G : MassGRHData line W ell rho) (n : ℕ) :
    progressionError (massProgressionK line) (G.q n) (G.B n) (G.patterns n) ≤
      denomScale W n * rho n / (2 * ell n) :=
  (G.toMassErrorInputs).error_le n

/-- The same field, written with the literal `MassErrorInputs` accessor. -/
theorem toMassErrorInputs_error_le (G : MassGRHData line W ell rho) (n : ℕ) :
    progressionError (massProgressionK line) (G.q n) (G.B n) (G.patterns n) ≤
      denomScale W n * rho n / (2 * ell n) :=
  MassErrorInputs.error_le G.toMassErrorInputs n

/-- The explicit progression error is nonnegative. -/
theorem error_nonneg (G : MassGRHData line W ell rho) (n : ℕ) :
    0 ≤ progressionError (massProgressionK line) (G.q n) (G.B n) (G.patterns n) :=
  progressionError_nonneg (massProgressionK line) (massProgressionK_nonneg line)
    (G.q n) (G.B n) (G.patterns n)

/-- **The residue-class deviation of the numerator count**, derived from the
prime-pattern progression bound rather than assumed. -/
theorem deviation (G : MassGRHData line W ell rho) (n : ℕ)
    (r : ∀ m, (ZMod (G.q m))ˣ) :
    |(progressionCount (G.A n) (G.B n) (G.patterns n) (G.q n) (r n) : ℝ) -
        (coprimeCount (G.A n) (G.B n) (G.patterns n) (G.q n) : ℝ) /
          (G.q n).totient| ≤
      progressionError (massProgressionK line) (G.q n) (G.B n) (G.patterns n) := by
  haveI : NeZero (G.q n) := ⟨(G.q_pos n).ne'⟩
  have h := massProgressionK_deviation line (G.A n) (G.B n) (G.patterns n)
    (G.hdisj n) (G.hA n) (G.hAB n) (G.q n) (r n)
  simpa only [progressionCount, coprimeCount, numeratorPool] using h

/-- **Assemble `NumeratorCountInputs` with the deviation from the critical
line.**  Only coprimality and the identification of `Nnum` with the actual
count remain explicit. -/
noncomputable def toNumeratorCountInputs (G : MassGRHData line W ell rho)
    (Nnum : ℕ → ℝ) (r : ∀ n, (ZMod (G.q n))ˣ)
    (coprime_all : ∀ n m,
      m ∈ numeratorPool (G.A n) (G.B n) (G.patterns n) → m.Coprime (G.q n))
    (Nnum_eq_count : ∀ n, Nnum n =
      (progressionCount (G.A n) (G.B n) (G.patterns n) (G.q n) (r n) : ℝ)) :
    NumeratorCountInputs W ell rho Nnum :=
  G.toMassErrorInputs.toNumeratorCountInputs Nnum r coprime_all Nnum_eq_count
    (fun n => G.deviation n r)

/-- **The L18.4 numerator count from the critical line.** -/
theorem numerator_count (G : MassGRHData line W ell rho)
    (Nnum : ℕ → ℝ) (r : ∀ n, (ZMod (G.q n))ˣ)
    (coprime_all : ∀ n m,
      m ∈ numeratorPool (G.A n) (G.B n) (G.patterns n) → m.Coprime (G.q n))
    (Nnum_eq_count : ∀ n, Nnum n =
      (progressionCount (G.A n) (G.B n) (G.patterns n) (G.q n) (r n) : ℝ))
    (n : ℕ) :
    denomScale W n * rho n / (2 * ell n) ≤ Nnum n :=
  (G.toNumeratorCountInputs Nnum r coprime_all Nnum_eq_count).numerator_count n

/-- **The progression error is genuinely nonzero.**  The explicit constant is
positive, and any nonempty occupied pattern with bins of size at least two
contributes a positive summand. -/
theorem progressionError_pos (G : MassGRHData line W ell rho) (n : ℕ)
    (hne : (G.patterns n).Nonempty) :
    0 < progressionError (massProgressionK line) (G.q n) (G.B n) (G.patterns n) :=
  Cogentic.RandomizedL18_4.progressionError_pos (massProgressionK_pos line) hne
    (fun _ _ i _ => le_trans (G.hA n i) (G.hAB n i))

/-- The progression error is not the zero error. -/
theorem progressionError_ne_zero (G : MassGRHData line W ell rho) (n : ℕ)
    (hne : (G.patterns n).Nonempty) :
    progressionError (massProgressionK line) (G.q n) (G.B n) (G.patterns n) ≠ 0 :=
  ne_of_gt (G.progressionError_pos n hne)

end MassGRHData

/-! ## Axiom audit -/

#print axioms massProgressionK_nonneg
#print axioms massProgressionK_pos
#print axioms le_massProgressionK
#print axioms progressionError_sum_mono
#print axioms massProgressionK_bound
#print axioms primePatternProgressionBound_of_criticalLine
#print axioms massProgressionK_deviation
#print axioms massSupplyK_nonneg
#print axioms massSupplyK_supply
#print axioms mass_pop_of_primeBinSupply
#print axioms error_slot_of_criticalLine
#print axioms MassGRHData.mass_pop
#print axioms MassGRHData.error_slot
#print axioms MassGRHData.toMassErrorInputs
#print axioms MassGRHData.mass_lower
#print axioms MassGRHData.error_le
#print axioms MassGRHData.toMassErrorInputs_error_le
#print axioms MassGRHData.error_nonneg
#print axioms MassGRHData.deviation
#print axioms MassGRHData.toNumeratorCountInputs
#print axioms MassGRHData.numerator_count
#print axioms MassGRHData.progressionError_pos
#print axioms MassGRHData.progressionError_ne_zero

end Cogentic.RandomizedL18_4
