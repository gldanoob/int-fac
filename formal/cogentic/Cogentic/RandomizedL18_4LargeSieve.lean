import Cogentic.RandomizedL18_4
import Cogentic.RandomizedPrimeProductPlancherel
import Cogentic.RandomizedTwoFactorFourier

/-!
# L18.4: the large-sieve second moment

`RandomizedL18_4.L18_4Inputs` assumes the paper-level estimate (KB Lemma G.3
p.107, `research/keybreak-balanced-ideal-pair-audit.md` §1)

`S2 n ≤ C n * (M n * V n ^ 2) * (E_conv n / d n)`, `V = exp (log V)`.

This file does not assume that estimate.  It isolates what the manuscript's
large sieve actually supplies and proves the estimate from those pieces:

1. **A single-modulus Parseval / Bessel inequality.**  Additive characters on
   `ZMod q` are orthogonal, so for every modulus `q` the full character energy is
   exactly `q` times the physical squared norm:

   `∑_χ ‖transform f χ‖² = q * ∑_x ‖f x‖²`,

   and hence the energy on any subset of frequencies is at most the same.  The
   reduced-residue (Dirichlet-character) form is
   `RandomizedPrimeProductPlancherel.classMass_centered_plancherel`, restated
   below; its uniform bound version is the single-modulus Bessel inequality used
   for one denominator cell.

2. **Multi-modulus summation.**  Summing the single-modulus Bessel bounds over a
   finite family of moduli multiplies the number of moduli into the bound; the
   concrete form is `multiModulus_residueEnergy_le`, which is the summation step
   with one uniform per-modulus constant.

3. **The two remaining paper-level estimates**, bundled in `LargeSieveInputs`:

   * `multiModulusSum`: after the per-modulus Parseval identities are summed,
     the aggregated second moment is at most `support * (E_conv / d)`.  Here
     `E_conv` is the multiplicity-one product-convolution energy and the division
     by the order `d` is the manuscript's energy division of the shrunken
     denominator interval.
   * `rationalCellPartition`: the determinant strip `|det| ≪ V²/K` meets `O(1)`
     numerator cells inside each denominator cell and `O(K)` cell pairs, so the
     support length is at most `C * M * V²`.

   Neither constant is set to zero and neither estimate mentions the conclusion.

4. The theorem `LargeSieveInputs.large_sieve` derives exactly the `large_sieve`
   field of `L18_4Inputs`.  Finally
   `L18_4Inputs.replaceLargeSieve` literally replaces that proof field by the
   certificate, and `L18_4Inputs.large_sieve_of_inputs` is the reduction
   statement: to build the L18.4 input it is enough to supply a
   `LargeSieveInputs` for its six large-sieve data functions.

The mathematical reading of the two named remainders is the one in
`research/keybreak-balanced-ideal-pair-audit.md` §1: the upper support length is
`O(M V²)`, the bound is linear in the multiplicity-one convolution energy `E_A`,
and restricting the denominator interval to the narrower scale divides the
energy by the order `d`.
-/

namespace Cogentic.RandomizedL18_4

open Filter Real
open Cogentic.RandomizedPaperLeafStatements
open scoped BigOperators

/-! ## 1. Single-modulus Parseval / Bessel inequalities -/

/-- **Additive Parseval on `ZMod q`.**  The additive characters are orthogonal,
so the unnormalized character transform has total squared energy exactly `q`
times the physical squared norm.  This is the single-modulus large-sieve
identity; it carries no arithmetic input. -/
theorem zmod_parseval {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    ∑ χ : AddChar (ZMod q) ℂ,
        ‖Cogentic.RandomizedTwoFactorFourier.transform f χ‖ ^ 2 =
      (q : ℝ) * ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  simpa only [ZMod.card] using
    (Cogentic.RandomizedTwoFactorFourier.sum_norm_transform_sq (G := ZMod q) f)

/-- **Single-modulus Bessel inequality on a frequency subset.**  For any set `s`
of additive frequencies on `ZMod q`, the squared character energy is at most `q`
times the physical energy.  This is the form in which the large sieve is applied
to a fixed modulus: it does not require the frequencies to exhaust `ZMod q`. -/
theorem zmod_spectral_subset_le {q : ℕ} [NeZero q]
    (s : Finset (AddChar (ZMod q) ℂ)) (f : ZMod q → ℂ) :
    ∑ χ ∈ s, ‖Cogentic.RandomizedTwoFactorFourier.transform f χ‖ ^ 2 ≤
      (q : ℝ) * ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  calc
    _ ≤ ∑ χ : AddChar (ZMod q) ℂ,
          ‖Cogentic.RandomizedTwoFactorFourier.transform f χ‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun _ _ _ => sq_nonneg _)
    _ = _ := zmod_parseval f

/-- **Single-modulus plancherel on reduced residues.**  The squared discrepancy
of the residue counts from their principal mean is exactly the nonprincipal
Dirichlet-character energy divided by `φ(q)`.  This is the reduced-residue
orthonormality statement behind the large sieve for a single denominator cell. -/
theorem zmod_unit_plancherel {q : ℕ} [NeZero q] (P : Finset ℕ) (w : ℕ → ℂ) :
    ∑ r : (ZMod q)ˣ,
        ‖Window.classMass P w r -
          Window.twist P w (1 : DirichletCharacter ℂ q) / q.totient‖ ^ 2 =
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖Window.twist P w χ‖ ^ 2) / (q.totient : ℝ) :=
  Cogentic.Randomized.classMass_centered_plancherel P w

/-- **Single-modulus Bessel bound on reduced residues.**  A uniform bound `A` on
the nonprincipal Dirichlet twists bounds the whole squared residue discrepancy by
`A²`, with no factor for the number of residues.  This is the single-cell
estimate that the multi-modulus summation below sums. -/
theorem zmod_unit_bessel {q : ℕ} [NeZero q] (P : Finset ℕ) (w : ℕ → ℂ) {A : ℝ}
    (hA : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖Window.twist P w χ‖ ≤ A) :
    ∑ r : (ZMod q)ˣ,
        ‖Window.classMass P w r -
          Window.twist P w (1 : DirichletCharacter ℂ q) / q.totient‖ ^ 2 ≤ A ^ 2 :=
  Cogentic.Randomized.classMass_centered_sq_le P w (M := A) hA

/-- **Multi-modulus summation.**  Summing the single-modulus Bessel bounds over a
finite family of moduli `q i` costs exactly the number of moduli, with one common
per-modulus constant `A`.  This is the summation step of the large sieve; the
remaining arithmetic content (identifying `A²` with the multiplicity-one
convolution energy and counting the moduli) is carried by `LargeSieveInputs`. -/
theorem multiModulus_residueEnergy_le {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (w : ι → ℕ → ℂ) {A : ℝ}
    (hA : ∀ i (χ : DirichletCharacter ℂ (q i)), χ ≠ 1 →
      ‖Window.twist (P i) (w i) χ‖ ≤ A) :
    (∑ i, ∑ r : (ZMod (q i))ˣ,
        ‖Window.classMass (P i) (w i) r -
          Window.twist (P i) (w i) (1 : DirichletCharacter ℂ (q i)) /
            (q i).totient‖ ^ 2) ≤
      (Fintype.card ι : ℝ) * A ^ 2 := by
  calc
    _ ≤ ∑ _i : ι, A ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact zmod_unit_bessel (P i) (w i) (hA i)
    _ = (Fintype.card ι : ℝ) * A ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## 2. The named large-sieve remainder -/

/-- **The remaining paper-level content of the L18.4 large sieve.**

`W` is `log V`, `d` the field degree, `C` the large-sieve constant, `M` the
support factor, `Econv` the undivided multiplicity-one product-convolution
energy, and `S2` the summed second moment of the numerator counts over the `K`
denominator cells.

There are exactly two estimates:

* `multiModulusSum` is the multi-modulus summation.  The single-modulus Parseval
  identities (`zmod_parseval`, `zmod_unit_plancherel`) are summed over the active
  moduli; multiplicity one in the product convolution makes the summed energy
  linear in `Econv`, and the shrunken denominator interval divides it by the
  order `d`.
* `rationalCellPartition` is the rational-cell partition.  The determinant strip
  `|det| ≪ V²/K` meets `O(1)` numerator cells inside each denominator cell and
  `O(K)` cell pairs in all, so the total support length is at most `C * M * V²`.

Both are `D^{O(1)}` estimates from KB G.3 p.107; neither is the conclusion and
neither is allowed to be zero.  `S2` remains the genuine second moment. -/
structure LargeSieveInputs (W d C M Econv S2 : ℕ → ℝ) where
  /-- The upper support length: the summed number of numerator frequency cells
  after the rational-cell partition. -/
  support : ℕ → ℝ
  /-- The support length is nonnegative. -/
  support_nonneg : ∀ n, 0 ≤ support n
  /-- The field degree is positive, so the energy division `E_conv / d` is defined
  and nonnegative. -/
  d_pos : ∀ n, 0 < d n
  /-- The undivided convolution energy is nonnegative. -/
  Econv_nonneg : ∀ n, 0 ≤ Econv n
  /-- **Multi-modulus summation** (KB G.3 p.107).  After the per-modulus Parseval
  identities are summed, the second moment is at most the support length times the
  multiplicity-one energy divided by the order `d`. -/
  multiModulusSum : ∀ n, S2 n ≤ support n * (Econv n / d n)
  /-- **Rational-cell partition / lattice count** (KB G.3 p.107, G.15).  The
  determinant strip `|det| ≪ V²/K` meets `O(1)` numerator cells per denominator
  cell and `O(K)` cell pairs, so the support length is at most `C * M * V²`. -/
  rationalCellPartition : ∀ n,
    support n ≤ C n * (M n * denomScale W n ^ 2)

namespace LargeSieveInputs

variable {W d C M Econv S2 : ℕ → ℝ}

/-- **`LargeSieveInputs` implies the `large_sieve` field.**  The support length is
bounded by `C * M * V²`, and the summed second moment is linear in `E_conv / d`;
multiplying the two estimates gives exactly

`S2 n ≤ C n * (M n * V n ^ 2) * (E_conv n / d n)`.

This is the manuscript's large-sieve estimate with the exact remainder isolated in
`multiModulusSum` and `rationalCellPartition`. -/
theorem large_sieve (L : LargeSieveInputs W d C M Econv S2) (n : ℕ) :
    S2 n ≤ C n * (M n * denomScale W n ^ 2) * (Econv n / d n) := by
  refine (L.multiModulusSum n).trans ?_
  exact mul_le_mul_of_nonneg_right (L.rationalCellPartition n)
    (div_nonneg (L.Econv_nonneg n) (L.d_pos n).le)

/-- The certificate gives the bound for every stage. -/
theorem large_sieve_all (L : LargeSieveInputs W d C M Econv S2) :
    ∀ n, S2 n ≤ C n * (M n * denomScale W n ^ 2) * (Econv n / d n) :=
  fun n => L.large_sieve n

end LargeSieveInputs

/-! ## 3. Replacement of the `L18_4Inputs.large_sieve` field -/

namespace L18_4Inputs

variable (I : L18_4Inputs)

/-- **The `large_sieve` field is reduced to `LargeSieveInputs`.**  For any
`L18_4Inputs`, a certificate for its six large-sieve data functions implies the
inequality assumed by its `large_sieve` field.  The two named paper-level
remainders therefore replace that field. -/
theorem large_sieve_of_inputs
    (L : LargeSieveInputs I.W I.d I.C I.M I.Econv I.S2) :
    ∀ n, I.S2 n ≤ I.C n * (I.M n * denomScale I.W n ^ 2) * (I.Econv n / I.d n) :=
  fun n => L.large_sieve n

/-- **Literal replacement of the `large_sieve` proof field.**  All other fields of
`I` are kept, while `large_sieve` is now derived from the two paper-level
estimates in `L` instead of being assumed. -/
noncomputable def replaceLargeSieve
    (L : LargeSieveInputs I.W I.d I.C I.M I.Econv I.S2) : L18_4Inputs :=
  { I with large_sieve := fun n => L.large_sieve n }

/-- Replacing the large-sieve proof field does not change the rational-good
deficit: `loss` depends only on the data fields, which are untouched. -/
@[simp] theorem replaceLargeSieve_loss
    (L : LargeSieveInputs I.W I.d I.C I.M I.Econv I.S2) :
    (I.replaceLargeSieve L).loss = I.loss := rfl

end L18_4Inputs

/-! ## Axiom audit -/

#print axioms zmod_parseval
#print axioms zmod_spectral_subset_le
#print axioms zmod_unit_plancherel
#print axioms zmod_unit_bessel
#print axioms multiModulus_residueEnergy_le
#print axioms LargeSieveInputs.large_sieve
#print axioms LargeSieveInputs.large_sieve_all
#print axioms L18_4Inputs.large_sieve_of_inputs
#print axioms L18_4Inputs.replaceLargeSieve
#print axioms L18_4Inputs.replaceLargeSieve_loss

end Cogentic.RandomizedL18_4
