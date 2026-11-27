import Cogentic.RandomizedL18_4Numerator
import Cogentic.RandomizedPrimeBinPatterns

/-!
# L18.4: the two numerical residuals of the numerator count

`RandomizedL18_4Numerator.NumeratorCountInputs` isolates the root-progression
count behind `L18_4Inputs.cell_numerator_count`.  It leaves two numerical
residuals:

1. `mass_lower : V ρ ≤ #(numeratorPool A B patterns)`, the reference mass bound;
2. `error_le : progressionError K q B patterns ≤ V ρ / (2 ℓ)`, the statement that
   the explicit RH square-root error is at most half the reference count.

This file proves both from the actual prime-bin pool, without setting either the
pool or the error to zero.

## The mass residual

`numeratorPool A B patterns` is the union of the prime products of the occupied
bins.  If every pattern has `k` slots and every occupied bin has at least `m`
primes, the existing `primeBinPatternProducts_card_lower` gives

`patterns.card * m ^ k ≤ #(numeratorPool A B patterns)`.

Hence `mass_lower` follows from the single explicit population inequality
`V ρ ≤ patterns.card * m ^ k` (`mass_lower_of_patternPopulation`).

## The error residual

The explicit error is a sum over patterns of products of the per-bin errors
`2 K (1 + log (3 q Bᵢ))² √Bᵢ`.  If

* every pattern has `k` slots,
* every pattern product has size at least `X`, and
* the *squared* per-bin error is at most `U` times the actual bin population,

then multiplying the per-bin estimates and using `√X ≤ ∏ √Bᵢ` gives

`progressionError K q B patterns ≤ (U ^ k / √X) * #(numeratorPool A B patterns)`

(`progressionError_le_relative`).  This is the same product saving that appears
in `RandomizedRelativePrefix.product_saving`, now applied directly to the
`progressionError` of `NumeratorCountInputs`.

The remaining numerical input is `U ^ k / √X ≤ ρ / (2 ℓ)` together with the
upper support count `#pool ≤ V` (the numerator interval has length `V`).  Then

`error ≤ (ρ / (2 ℓ)) * V = V ρ / (2 ℓ)`.

## The reduction structure

`MassErrorInputs W ell rho` carries exactly these counting hypotheses on the
actual pool.  It proves both residual fields and assembles a
`NumeratorCountInputs` once the remaining (already reduced) fields `coprime_all`,
`Nnum_eq_count` and `deviation` are supplied.  The deviation field is the
existing `PrimePatternProgressionBound` statement, exposed by
`RandomizedL18_4Numerator.progressionDeviation_of_patternProgression`.

Nothing here is a `sorry`, an `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL18_4

open Finset Real
open scoped BigOperators

open Cogentic.Randomized

/-! ## 1. The mass residual -/

/-- **`mass_lower` from the pattern population.**  If every occupied-bin pattern
has `k` slots and every occupied bin contains at least `m` primes, the actual
numerator pool has at least `patterns.card * m ^ k` elements.  Therefore it has
at least the reference mass whenever `V ρ ≤ patterns.card * m ^ k`.

The lower bound is the existing `primeBinPatternProducts_card_lower`; the only
numerical input is the displayed population inequality. -/
theorem mass_lower_of_patternPopulation
    (A B : ℕ → ℕ) (patterns : Finset (Finset ℕ))
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (k m : ℕ)
    (hsize : ∀ s ∈ patterns, s.card = k)
    (hpop : ∀ s ∈ patterns, ∀ i ∈ s, m ≤ (primeBin (A i) (B i)).card)
    {Vρ : ℝ} (hmass : Vρ ≤ (patterns.card : ℝ) * (m : ℝ) ^ k) :
    Vρ ≤ ((primeBinPatternProducts A B patterns).card : ℝ) := by
  have hlow := primeBinPatternProducts_card_lower A B hdisj patterns k m hsize hpop
  have hreal : (patterns.card : ℝ) * (m : ℝ) ^ k ≤
      ((primeBinPatternProducts A B patterns).card : ℝ) := by
    exact_mod_cast hlow
  exact hmass.trans hreal

/-! ## 2. The error residual -/

/-- **The explicit RH error relative to the actual pool.**

Let `Hᵢ = 2 K (1 + log (3 q Bᵢ))² √Bᵢ`.  If every pattern has `k` slots, every
pattern product has size at least `X`, and the squared per-bin error satisfies
`Hᵢ √Bᵢ ≤ U · #(binᵢ)`, then

`∑ₛ ∏_{i ∈ s} Hᵢ ≤ (U ^ k / √X) · #(numeratorPool A B patterns)`.

The proof is the product saving of `RandomizedRelativePrefix`:
`(∏ Hᵢ) √X ≤ ∏ (Hᵢ √Bᵢ) ≤ ∏ (U · #binᵢ) = U ^ k ∏ #binᵢ`, and the exact
cardinality of the pattern union rewrites `∑ₛ ∏ #binᵢ` as the pool size. -/
theorem progressionError_le_relative
    (A B : ℕ → ℕ) (patterns : Finset (Finset ℕ))
    {K U X : ℝ} {k q : ℕ}
    (hK : 0 ≤ K) (_hU : 0 ≤ U) (hX : 0 < X)
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hsize : ∀ s ∈ patterns, s.card = k)
    (hscale : ∀ s ∈ patterns, X ≤ ∏ i ∈ s, (B i : ℝ))
    (hslot : ∀ s ∈ patterns, ∀ i ∈ s,
      2 * K * (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 * (B i : ℝ) ≤
        U * ((primeBin (A i) (B i)).card : ℝ)) :
    progressionError K q B patterns ≤
      (U ^ k / Real.sqrt X) *
        ((primeBinPatternProducts A B patterns).card : ℝ) := by
  let H (i : ℕ) :=
    2 * K * (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 * Real.sqrt (B i : ℝ)
  have hH : ∀ i, 0 ≤ H i := by
    intro i
    dsimp only [H]
    have h2K : 0 ≤ 2 * K := by linarith
    exact mul_nonneg (mul_nonneg h2K (sq_nonneg _)) (Real.sqrt_nonneg _)
  have hterm (s : Finset ℕ) (hs : s ∈ patterns) :
      (∏ i ∈ s, H i) ≤ (U ^ k / Real.sqrt X) *
        ∏ i ∈ s, ((primeBin (A i) (B i)).card : ℝ) := by
    have hmul : (∏ i ∈ s, H i) * Real.sqrt X ≤
        U ^ k * ∏ i ∈ s, ((primeBin (A i) (B i)).card : ℝ) := by
      calc
        (∏ i ∈ s, H i) * Real.sqrt X
            ≤ (∏ i ∈ s, H i) * Real.sqrt (∏ i ∈ s, (B i : ℝ)) :=
              mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hscale s hs))
                (Finset.prod_nonneg fun i _ => hH i)
        _ = (∏ i ∈ s, H i) * ∏ i ∈ s, Real.sqrt (B i : ℝ) := by
              rw [Real.sqrt_prod s (fun _ _ => Nat.cast_nonneg _)]
        _ = ∏ i ∈ s, (H i * Real.sqrt (B i : ℝ)) :=
              (Finset.prod_mul_distrib).symm
        _ = ∏ i ∈ s,
              (2 * K * (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 * (B i : ℝ)) := by
              apply Finset.prod_congr rfl
              intro i _
              dsimp only [H]
              rw [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
        _ ≤ ∏ i ∈ s, (U * ((primeBin (A i) (B i)).card : ℝ)) :=
              Finset.prod_le_prod
                (fun i _ => mul_nonneg
                  (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * K) (sq_nonneg _))
                  (Nat.cast_nonneg _))
                (fun i hi => hslot s hs i hi)
        _ = U ^ k * ∏ i ∈ s, ((primeBin (A i) (B i)).card : ℝ) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, hsize s hs]
    rw [div_mul_eq_mul_div, le_div_iff₀ (Real.sqrt_pos.mpr hX)]
    exact hmul
  calc
    progressionError K q B patterns
        = ∑ s ∈ patterns, ∏ i ∈ s, H i := by
          simp only [progressionError, H]
    _ ≤ ∑ s ∈ patterns, (U ^ k / Real.sqrt X) *
          ∏ i ∈ s, ((primeBin (A i) (B i)).card : ℝ) :=
          Finset.sum_le_sum hterm
    _ = (U ^ k / Real.sqrt X) * ∑ s ∈ patterns,
          ∏ i ∈ s, ((primeBin (A i) (B i)).card : ℝ) := by
          rw [Finset.mul_sum]
    _ = (U ^ k / Real.sqrt X) *
          ((primeBinPatternProducts A B patterns).card : ℝ) := by
          congr 1
          rw [primeBinPatternProducts_card A B hdisj, Nat.cast_sum]
          apply Finset.sum_congr rfl
          intro s hs
          rw [primeBinProducts_card _ _
            (fun i j hij => hdisj (Subtype.val_injective.ne hij)), Nat.cast_prod,
            ← Finset.prod_coe_sort s
              (fun i => ((primeBin (A i) (B i)).card : ℝ))]

/-! ### The per-bin error slot from the prime-bin supply

The hypothesis `error_slot` of `MassErrorInputs` is the usual statement that the
RH square-root error is smaller than the actual bin population.  It is supplied
by the existing critical-line prime-bin supply: once the supply error fits in
half the bin width, `cell_card_lower_of_primeBinSupply` gives
`#bin ≥ (B - A) / (2 log B)`, and the width condition below then dominates the
squared per-bin error by `U · #bin`. -/

/-- **The per-bin error slot from a prime-bin supply.**  With
`lg = log B` and the supply error at most half the bin width, the bin contains
at least `(B - A) / (2 log B)` primes.  If additionally

`4 log B · K (1 + log (3 q B))² B ≤ U (B - A)`,

then the squared per-bin RH error is at most `U · #(primeBin A B)`. -/
theorem error_slot_of_primeBinSupply
    {K0 K U : ℝ} (hK0 : 0 ≤ K0) (hU : 0 ≤ U)
    (hsupply : ∀ A B : ℕ, 2 ≤ A → A ≤ B →
      (B : ℝ) - (A : ℝ) -
          K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
        ((primeBin A B).card : ℝ) * Real.log (B : ℝ))
    {q A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) (_hq : 1 ≤ q)
    (hwidth : 4 * Real.log (B : ℝ) * K *
        (1 + Real.log (3 * (q : ℝ) * (B : ℝ))) ^ 2 * (B : ℝ) ≤
      U * ((B : ℝ) - (A : ℝ)))
    (hsmall : K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
      ((B : ℝ) - (A : ℝ)) / 2) :
    2 * K * (1 + Real.log (3 * (q : ℝ) * (B : ℝ))) ^ 2 * (B : ℝ) ≤
      U * ((primeBin A B).card : ℝ) := by
  have hB2 : 2 ≤ B := le_trans hA hAB
  have hB1 : (1 : ℝ) < (B : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hB2)
  have hlogpos : 0 < Real.log (B : ℝ) := Real.log_pos hB1
  have hcount : ((B : ℝ) - (A : ℝ)) / (2 * Real.log (B : ℝ)) ≤
      ((primeBin A B).card : ℝ) :=
    cell_card_lower_of_primeBinSupply hK0 hsupply hA hAB (lg := Real.log (B : ℝ))
      hlogpos le_rfl hsmall
  have hmain : 2 * K * (1 + Real.log (3 * (q : ℝ) * (B : ℝ))) ^ 2 * (B : ℝ) ≤
      U * (((B : ℝ) - (A : ℝ)) / (2 * Real.log (B : ℝ))) := by
    have h2log : (0 : ℝ) < 2 * Real.log (B : ℝ) := by positivity
    rw [show U * (((B : ℝ) - (A : ℝ)) / (2 * Real.log (B : ℝ))) =
      U * ((B : ℝ) - (A : ℝ)) / (2 * Real.log (B : ℝ)) by ring]
    rw [le_div_iff₀ h2log]
    calc
      (2 * K * (1 + Real.log (3 * (q : ℝ) * (B : ℝ))) ^ 2 * (B : ℝ)) *
            (2 * Real.log (B : ℝ)) =
          4 * Real.log (B : ℝ) * K *
            (1 + Real.log (3 * (q : ℝ) * (B : ℝ))) ^ 2 * (B : ℝ) := by ring
      _ ≤ U * ((B : ℝ) - (A : ℝ)) := hwidth
  exact hmain.trans (mul_le_mul_of_nonneg_left hcount hU)

/-! ## 3. The two residuals bundled -/

/-- **The explicit counting inputs for the two L18.4 numerator residuals.**

The fields on `A`, `B`, `patterns` are the actual numerator pool.  The mass
fields are the uniform pattern population of `primeBinPatternProducts_card_lower`
(`mass_size`, `mass_pop`) plus the explicit population inequality `mass_num`.
The error fields are the relative product saving (`error_scale`, `error_slot`),
the support count `#pool ≤ V` (`pool_upper`), and the numerical smallness
`U ^ k / √X ≤ ρ / (2 ℓ)` (`error_rel`).

`mass_lower` and `error_le` below are the two residual fields of
`NumeratorCountInputs`. -/
structure MassErrorInputs (W ell rho : ℕ → ℝ) where
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
  /-- The uniform number of slots of a pattern. -/
  mass_k : ℕ → ℕ
  /-- The uniform lower population of an occupied bin. -/
  mass_m : ℕ → ℕ
  /-- Every occupied pattern has `mass_k` slots. -/
  mass_size : ∀ n s, s ∈ patterns n → s.card = mass_k n
  /-- Every occupied bin has at least `mass_m` primes. -/
  mass_pop : ∀ n s, s ∈ patterns n → ∀ i ∈ s,
    mass_m n ≤ (primeBin (A n i) (B n i)).card
  /-- **Pattern-product population.**  The reference mass is at most the uniform
  pattern population `#patterns · m ^ k`. -/
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
  /-- **The per-bin RH square-root error.**  The squared per-bin error is at most
  `U` times the actual bin population. -/
  error_slot : ∀ n s, s ∈ patterns n → ∀ i ∈ s,
    2 * K * (1 + Real.log (3 * (q n : ℝ) * (B n i : ℝ))) ^ 2 * (B n i : ℝ) ≤
      error_U n * ((primeBin (A n i) (B n i)).card : ℝ)
  /-- **Upper support count.**  The numerator interval has length `V`, so the
  actual pool has at most `V` elements. -/
  pool_upper : ∀ n,
    ((numeratorPool (A n) (B n) (patterns n)).card : ℝ) ≤ denomScale W n
  /-- **Numerical smallness of the relative error.**  The product-saving factor is
  at most `ρ / (2 ℓ)`. -/
  error_rel : ∀ n,
    error_U n ^ mass_k n / Real.sqrt (error_X n) ≤ rho n / (2 * ell n)

namespace MassErrorInputs

variable {W ell rho : ℕ → ℝ}

/-- **Residual 1.**  The actual numerator pool has at least the reference mass
`V ρ`. -/
theorem mass_lower (I : MassErrorInputs W ell rho) (n : ℕ) :
    denomScale W n * rho n ≤
      ((numeratorPool (I.A n) (I.B n) (I.patterns n)).card : ℝ) :=
  mass_lower_of_patternPopulation (I.A n) (I.B n) (I.patterns n) (I.hdisj n)
    (I.mass_k n) (I.mass_m n) (I.mass_size n) (I.mass_pop n) (I.mass_num n)

/-- **Residual 2.**  The explicit RH progression error is at most half the
reference count `V ρ / (2 ℓ)`. -/
theorem error_le (I : MassErrorInputs W ell rho) (n : ℕ) :
    progressionError I.K (I.q n) (I.B n) (I.patterns n) ≤
      denomScale W n * rho n / (2 * ell n) := by
  have hrel := progressionError_le_relative (I.A n) (I.B n) (I.patterns n)
    I.K_nonneg (I.error_U_nonneg n) (I.error_X_pos n) (I.hdisj n)
    (I.mass_size n) (I.error_scale n) (I.error_slot n)
  have hrel' : progressionError I.K (I.q n) (I.B n) (I.patterns n) ≤
      (I.error_U n ^ I.mass_k n / Real.sqrt (I.error_X n)) *
        ((numeratorPool (I.A n) (I.B n) (I.patterns n)).card : ℝ) := by
    simpa only [numeratorPool] using hrel
  have hell : 0 < ell n := by
    rw [I.ell_eq n]
    exact_mod_cast I.q_pos n
  have hnonneg : 0 ≤ rho n / (2 * ell n) :=
    div_nonneg (I.rho_pos n).le (mul_nonneg (by norm_num) hell.le)
  have hstep :
      (I.error_U n ^ I.mass_k n / Real.sqrt (I.error_X n)) *
          ((numeratorPool (I.A n) (I.B n) (I.patterns n)).card : ℝ) ≤
        (rho n / (2 * ell n)) * denomScale W n :=
    mul_le_mul (I.error_rel n) (I.pool_upper n) (Nat.cast_nonneg _) hnonneg
  calc
    progressionError I.K (I.q n) (I.B n) (I.patterns n)
        ≤ (I.error_U n ^ I.mass_k n / Real.sqrt (I.error_X n)) *
            ((numeratorPool (I.A n) (I.B n) (I.patterns n)).card : ℝ) := hrel'
    _ ≤ (rho n / (2 * ell n)) * denomScale W n := hstep
    _ = denomScale W n * rho n / (2 * ell n) := by ring

/-- **Assemble `NumeratorCountInputs` from the two residuals.**

The mass and error fields are `I.mass_lower` and `I.error_le`.  The remaining
fields are the already-reduced numerator data: coprimality of the pool with the
root modulus, the identification of `Nnum` with the root-residue count, and the
RH deviation, which is the `PrimePatternProgressionBound` statement exposed by
`progressionDeviation_of_patternProgression`. -/
noncomputable def toNumeratorCountInputs (I : MassErrorInputs W ell rho)
    (Nnum : ℕ → ℝ) (r : ∀ n, (ZMod (I.q n))ˣ)
    (coprime_all : ∀ n m,
      m ∈ numeratorPool (I.A n) (I.B n) (I.patterns n) → m.Coprime (I.q n))
    (Nnum_eq_count : ∀ n, Nnum n =
      (progressionCount (I.A n) (I.B n) (I.patterns n) (I.q n) (r n) : ℝ))
    (deviation : ∀ n,
      |(progressionCount (I.A n) (I.B n) (I.patterns n) (I.q n) (r n) : ℝ) -
        (coprimeCount (I.A n) (I.B n) (I.patterns n) (I.q n) : ℝ) /
          (I.q n).totient| ≤
        progressionError I.K (I.q n) (I.B n) (I.patterns n)) :
    NumeratorCountInputs W ell rho Nnum where
  K := I.K
  K_nonneg := I.K_nonneg
  q := I.q
  q_pos := I.q_pos
  ell_eq := I.ell_eq
  rho_pos := I.rho_pos
  A := I.A
  B := I.B
  patterns := I.patterns
  hdisj := I.hdisj
  hA := I.hA
  hAB := I.hAB
  r := r
  mass_lower := I.mass_lower
  coprime_all := coprime_all
  Nnum_eq_count := Nnum_eq_count
  deviation := deviation
  error_le := I.error_le

end MassErrorInputs

/-! ## 4. Feeding the residuals into the L18.4 slot -/

namespace L18_4Inputs

variable (I : L18_4Inputs)

/-- **The `cell_numerator_count` slot from the two residuals.**  Given the
counting data `MassErrorInputs` for the numerator pool, together with the
already-reduced coprimality, count identification and RH deviation fields, the
`L18_4Inputs` slot is rebuilt with `cell_numerator_count` derived from the actual
root-progression count.  This is the `NumeratorCountInputs` construction of
`RandomizedL18_4Numerator.replaceCellNumeratorCount`, with `mass_lower` and
`error_le` now proved. -/
noncomputable def replaceCellNumeratorCountOfMass
    (M : MassErrorInputs I.W I.ell I.rho) (r : ∀ n, (ZMod (M.q n))ˣ)
    (coprime_all : ∀ n m,
      m ∈ numeratorPool (M.A n) (M.B n) (M.patterns n) → m.Coprime (M.q n))
    (Nnum_eq_count : ∀ n, I.Nnum n =
      (progressionCount (M.A n) (M.B n) (M.patterns n) (M.q n) (r n) : ℝ))
    (deviation : ∀ n,
      |(progressionCount (M.A n) (M.B n) (M.patterns n) (M.q n) (r n) : ℝ) -
        (coprimeCount (M.A n) (M.B n) (M.patterns n) (M.q n) : ℝ) /
          (M.q n).totient| ≤
        progressionError M.K (M.q n) (M.B n) (M.patterns n)) :
    L18_4Inputs :=
  I.replaceCellNumeratorCount
    (M.toNumeratorCountInputs I.Nnum r coprime_all Nnum_eq_count deviation)

/-- The replacement leaves `Nnum` unchanged. -/
@[simp] theorem replaceCellNumeratorCountOfMass_Nnum
    (M : MassErrorInputs I.W I.ell I.rho) (r : ∀ n, (ZMod (M.q n))ˣ)
    (coprime_all : ∀ n m,
      m ∈ numeratorPool (M.A n) (M.B n) (M.patterns n) → m.Coprime (M.q n))
    (Nnum_eq_count : ∀ n, I.Nnum n =
      (progressionCount (M.A n) (M.B n) (M.patterns n) (M.q n) (r n) : ℝ))
    (deviation : ∀ n,
      |(progressionCount (M.A n) (M.B n) (M.patterns n) (M.q n) (r n) : ℝ) -
        (coprimeCount (M.A n) (M.B n) (M.patterns n) (M.q n) : ℝ) /
          (M.q n).totient| ≤
        progressionError M.K (M.q n) (M.B n) (M.patterns n)) :
    (I.replaceCellNumeratorCountOfMass M r coprime_all Nnum_eq_count deviation).Nnum =
      I.Nnum := rfl

end L18_4Inputs

/-! ## Axiom audit -/

#print axioms mass_lower_of_patternPopulation
#print axioms progressionError_le_relative
#print axioms error_slot_of_primeBinSupply
#print axioms MassErrorInputs.mass_lower
#print axioms MassErrorInputs.error_le
#print axioms MassErrorInputs.toNumeratorCountInputs
#print axioms L18_4Inputs.replaceCellNumeratorCountOfMass
#print axioms L18_4Inputs.replaceCellNumeratorCountOfMass_Nnum

end Cogentic.RandomizedL18_4
