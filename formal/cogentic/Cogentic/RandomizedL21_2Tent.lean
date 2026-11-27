import Cogentic.RandomizedL21_2Fourier
import Mathlib.Analysis.Fourier.ZMod

set_option linter.style.haveILetI false

/-!
# L21.2: the finite Plancherel / tent mean-square step

`Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs` keeps the mean-square
comparison

```
(1/N) * Σ_i deficit_i² ≤ lowTerm + middleTerm + tailTerm
```

as an abstract field `tentMeanSquare`, with an arbitrary finite discrepancy
profile `deficit : Fin N → ℝ`.

This file replaces `deficit` by an *actual* finite Fourier profile.  A profile
`TentProfile` carries

* a sampled centre count `N n` and a complex coefficient vector
  `coeff n : ZMod (N n) → ℂ`,
* a real frequency assignment `freq n : ZMod (N n) → ℝ`.

The discrepancy at the `i`-th sampled centre is the real part of the discrete
Fourier transform of `coeff`,

```
deficit n i = Re (𝓕 coeff n) (finEquiv i),
```

and the three frequency terms are the coefficient energies in the bands
`|t| ≤ 1`, `1 < |t| ≤ X³`, and `|t| > X³`.

The finite Plancherel identity on `ZMod N` (proved here from the orthogonality
of the standard additive character) gives

```
(1/N) Σ_i ‖𝓕 coeff_i‖² = Σ_j ‖coeff_j‖²,
```

so, using `(Re z)² ≤ ‖z‖²` and the band partition,

```
(1/N) Σ_i deficit_i² ≤ lowEnergy + middleEnergy + tailEnergy.
```

Thus `tentMeanSquare` is *proved*, with no abstract mean-square hypothesis and
no zero energy: the energy is the sum of the squared absolute values of the
actual coefficients.  The only remaining analytic inputs are the usual
frequency-band bounds `fourierLow`, `fourierMiddle`, `fourierTail`, together
with the Perron/Fourier-gap/density inputs inherited from the parent bundle.

The assembled reduction is
`L21_2TentInputs.toFourierInputs : L21_2TentInputs → L21_2FourierInputs`,
hence also the Perron/reduced/leaf/ledger chain.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2Tent

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedL21_2Fourier
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## Finite Plancherel on `ZMod N` -/

namespace DiscretePlancherel

variable {N : ℕ} [NeZero N]

/-- Orthogonality of the standard additive character, in the form needed for
the discrete Parseval identity. -/
theorem sum_stdAddChar_mul (b : ZMod N) :
    (∑ k : ZMod N, ZMod.stdAddChar (k * b)) =
      if b = 0 then (N : ℂ) else 0 := by
  simpa using AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar N)

/-- **Discrete Parseval identity.**  The unnormalised DFT multiplies the
sum of squared norms by `N`. -/
theorem dft_parseval (Ψ : ZMod N → ℂ) :
    (∑ k, Complex.normSq (ZMod.dft Ψ k)) =
      (N : ℝ) * ∑ j, Complex.normSq (Ψ j) := by
  have hconj (a : ZMod N) :
      (starRingEnd ℂ) (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
    rw [AddChar.map_neg_eq_inv, AddChar.inv_apply_eq_conj]
  have hchar (a b x : ZMod N) :
      ZMod.stdAddChar (a * x) * ZMod.stdAddChar (-(b * x)) =
        ZMod.stdAddChar ((a - b) * x) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have h : (∑ k, (Complex.normSq (ZMod.dft Ψ k) : ℂ)) =
      (N : ℂ) * ∑ j, (Complex.normSq (Ψ j) : ℂ) := by
    simp only [Complex.normSq_eq_conj_mul_self, ZMod.dft_apply]
    simp only [map_sum, smul_eq_mul]
    simp only [Finset.sum_mul, Finset.mul_sum]
    simp only [map_mul, hconj, neg_neg]
    calc
      (∑ x, ∑ x_1, ∑ x_2,
          ZMod.stdAddChar (x_2 * x) * (starRingEnd ℂ) (Ψ x_2) *
            (ZMod.stdAddChar (-(x_1 * x)) * Ψ x_1))
          = ∑ x_1, ∑ x_2, ∑ x,
              ZMod.stdAddChar (x_2 * x) * (starRingEnd ℂ) (Ψ x_2) *
                (ZMod.stdAddChar (-(x_1 * x)) * Ψ x_1) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro x_1 _
            exact Finset.sum_comm
      _ = ∑ x_1, ∑ x_2, ∑ x,
              ZMod.stdAddChar ((x_2 - x_1) * x) *
                ((starRingEnd ℂ) (Ψ x_2) * Ψ x_1) := by
            apply Finset.sum_congr rfl
            intro x_1 _
            apply Finset.sum_congr rfl
            intro x_2 _
            apply Finset.sum_congr rfl
            intro x _
            rw [← hchar]
            ring
      _ = ∑ x_1, ∑ x_2,
              (∑ x, ZMod.stdAddChar (x * (x_2 - x_1))) *
                ((starRingEnd ℂ) (Ψ x_2) * Ψ x_1) := by
            apply Finset.sum_congr rfl
            intro x_1 _
            apply Finset.sum_congr rfl
            intro x_2 _
            rw [← Finset.sum_mul]
            congr 1
            apply Finset.sum_congr rfl
            intro x _
            congr 1
            ring
      _ = ∑ x_1, ∑ x_2,
              (if x_2 - x_1 = 0 then (N : ℂ) else 0) *
                ((starRingEnd ℂ) (Ψ x_2) * Ψ x_1) := by
            apply Finset.sum_congr rfl
            intro x_1 _
            apply Finset.sum_congr rfl
            intro x_2 _
            have hsum : (∑ x, ZMod.stdAddChar (x * (x_2 - x_1))) =
                (if x_2 - x_1 = 0 then (N : ℂ) else 0) := by
              simpa using AddChar.sum_mulShift (x_2 - x_1)
                (ZMod.isPrimitive_stdAddChar N)
            rw [hsum]
      _ = ∑ x_1, ∑ x_2,
              (if x_2 = x_1 then (N : ℂ) else 0) *
                ((starRingEnd ℂ) (Ψ x_2) * Ψ x_1) := by
            simp only [sub_eq_zero]
      _ = ∑ x_1, ∑ x_2,
              (if x_2 = x_1 then (N : ℂ) *
                ((starRingEnd ℂ) (Ψ x_2) * Ψ x_1) else 0) := by
            apply Finset.sum_congr rfl
            intro x_1 _
            apply Finset.sum_congr rfl
            intro x_2 _
            split_ifs <;> ring
      _ = ∑ x_1, (N : ℂ) * ((starRingEnd ℂ) (Ψ x_1) * Ψ x_1) := by
            apply Finset.sum_congr rfl
            intro x_1 _
            rw [Finset.sum_ite_eq']
            simp
  exact_mod_cast h

/-- **Normalised Plancherel mean-square comparison.**  The mean square of the
real part of the DFT is bounded by the coefficient energy. -/
theorem dft_re_mean_square_le (Ψ : ZMod N → ℂ) :
    (1 / (N : ℝ)) * ∑ i, (ZMod.dft Ψ i).re ^ 2 ≤
      ∑ j, Complex.normSq (Ψ j) := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hpoint : ∀ i, (ZMod.dft Ψ i).re ^ 2 ≤ Complex.normSq (ZMod.dft Ψ i) := by
    intro i
    simpa [pow_two] using Complex.re_sq_le_normSq (ZMod.dft Ψ i)
  calc
    (1 / (N : ℝ)) * ∑ i, (ZMod.dft Ψ i).re ^ 2
        ≤ (1 / (N : ℝ)) * ∑ i, Complex.normSq (ZMod.dft Ψ i) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => hpoint i) (by positivity)
    _ = (1 / (N : ℝ)) * ((N : ℝ) * ∑ j, Complex.normSq (Ψ j)) := by
      rw [dft_parseval]
    _ = ∑ j, Complex.normSq (Ψ j) := by
      field_simp

/-- Reindex a sum over `Fin N` as a sum over `ZMod N`. -/
theorem sum_fin_eq_sum_zmod (f : ZMod N → ℝ) :
    (∑ i : Fin N, f (ZMod.finEquiv N i)) = ∑ j : ZMod N, f j :=
  Equiv.sum_comp (ZMod.finEquiv N).toEquiv f

end DiscretePlancherel

/-! ## The finite Fourier discrepancy profile -/

/-- A finite discrepancy profile: sampled centres indexed by `ZMod (N n)`, a
complex coefficient vector, and the real frequency attached to each coefficient. -/
structure TentProfile where
  /-- The dyadic centre bound `X`. -/
  X : ℕ → ℝ
  /-- The number of sampled centres, also the number of Fourier modes. -/
  N : ℕ → ℕ
  /-- The sample is nonempty. -/
  N_pos : ∀ n, 0 < N n
  /-- The Fourier coefficients of the smoothed-density discrepancy. -/
  coeff : (n : ℕ) → ZMod (N n) → ℂ
  /-- The real frequency `t` attached to each coefficient. -/
  freq : (n : ℕ) → ZMod (N n) → ℝ

namespace TentProfile

variable (P : TentProfile)

/-- The `NeZero` instance supplied by positivity of the sample size. -/
theorem neZero (n : ℕ) : NeZero (P.N n) :=
  ⟨(P.N_pos n).ne'⟩

/-- The discrete Fourier transform of the coefficient vector. -/
def dftCoeff (n : ℕ) : ZMod (P.N n) → ℂ :=
  letI := P.neZero n
  ZMod.dft (P.coeff n)

/-- The actual finite discrepancy at the `i`-th sampled centre: the real part
of the DFT coefficient. -/
def deficit (n : ℕ) (i : Fin (P.N n)) : ℝ :=
  letI := P.neZero n
  (ZMod.dft (P.coeff n) (ZMod.finEquiv (P.N n) i)).re

/-- The low-frequency band `|t| ≤ 1`. -/
def lowSet (n : ℕ) : Finset (ZMod (P.N n)) :=
  letI := P.neZero n
  Finset.univ.filter (fun j => |P.freq n j| ≤ 1)

/-- The complementary band `|t| > 1`. -/
def nonLowSet (n : ℕ) : Finset (ZMod (P.N n)) :=
  letI := P.neZero n
  Finset.univ.filter (fun j => ¬ |P.freq n j| ≤ 1)

/-- The middle-frequency band `1 < |t| ≤ X³`. -/
def middleSet (n : ℕ) : Finset (ZMod (P.N n)) :=
  letI := P.neZero n
  (P.nonLowSet n).filter (fun j => |P.freq n j| ≤ P.X n ^ 3)

/-- The high-frequency band `|t| > X³`. -/
def tailSet (n : ℕ) : Finset (ZMod (P.N n)) :=
  letI := P.neZero n
  (P.nonLowSet n).filter (fun j => ¬ |P.freq n j| ≤ P.X n ^ 3)

/-- The low-band coefficient energy. -/
def lowEnergy (P : TentProfile) (n : ℕ) : ℝ :=
  letI := P.neZero n
  ∑ j ∈ P.lowSet n, Complex.normSq (P.coeff n j)

/-- The middle-band coefficient energy. -/
def middleEnergy (P : TentProfile) (n : ℕ) : ℝ :=
  letI := P.neZero n
  ∑ j ∈ P.middleSet n, Complex.normSq (P.coeff n j)

/-- The high-band coefficient energy. -/
def tailEnergy (P : TentProfile) (n : ℕ) : ℝ :=
  letI := P.neZero n
  ∑ j ∈ P.tailSet n, Complex.normSq (P.coeff n j)

/-- The total coefficient energy `Σ_j ‖coeff_j‖²`. -/
def totalEnergy (P : TentProfile) (n : ℕ) : ℝ :=
  letI := P.neZero n
  ∑ j : ZMod (P.N n), Complex.normSq (P.coeff n j)

/-- The three frequency bands partition the modes, so their energies add up to
the total coefficient energy. -/
theorem energy_split (n : ℕ) :
    P.lowEnergy n + P.middleEnergy n + P.tailEnergy n = P.totalEnergy n := by
  letI := P.neZero n
  have h1 := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ZMod (P.N n)))
    (fun j => |P.freq n j| ≤ 1) (fun j => Complex.normSq (P.coeff n j))
  have h2 := Finset.sum_filter_add_sum_filter_not
    (P.nonLowSet n) (fun j => |P.freq n j| ≤ P.X n ^ 3)
    (fun j => Complex.normSq (P.coeff n j))
  have h1' : P.lowEnergy n + (∑ j ∈ P.nonLowSet n, Complex.normSq (P.coeff n j)) =
      P.totalEnergy n := by
    simpa only [lowEnergy, totalEnergy, lowSet, nonLowSet] using h1
  have h2' : P.middleEnergy n + P.tailEnergy n =
      ∑ j ∈ P.nonLowSet n, Complex.normSq (P.coeff n j) := by
    simpa only [middleEnergy, tailEnergy, middleSet, tailSet] using h2
  calc
    P.lowEnergy n + P.middleEnergy n + P.tailEnergy n
        = P.lowEnergy n + (P.middleEnergy n + P.tailEnergy n) := by ring
    _ = P.lowEnergy n + (∑ j ∈ P.nonLowSet n, Complex.normSq (P.coeff n j)) := by
      rw [h2']
    _ = P.totalEnergy n := h1'

/-- **The finite Plancherel / tent mean-square comparison.**  The normalized
mean square of the actual discrepancy profile is at most the total coefficient
energy, hence at most the sum of the low, middle and tail band energies. -/
theorem meanSquare_le_energy (n : ℕ) :
    (1 / (P.N n : ℝ)) * ∑ i : Fin (P.N n), (P.deficit n i) ^ 2 ≤
      P.lowEnergy n + P.middleEnergy n + P.tailEnergy n := by
  letI := P.neZero n
  rw [P.energy_split n]
  have hsum : (∑ i : Fin (P.N n), (P.deficit n i) ^ 2) =
      ∑ j : ZMod (P.N n), (ZMod.dft (P.coeff n) j).re ^ 2 := by
    simpa only [deficit] using
      DiscretePlancherel.sum_fin_eq_sum_zmod
        (fun j : ZMod (P.N n) => (ZMod.dft (P.coeff n) j).re ^ 2)
  rw [hsum]
  exact DiscretePlancherel.dft_re_mean_square_le (P.coeff n)

/-- The mean-square comparison in the exact form consumed by the tent
Chebyshev step. -/
theorem tentMeanSquare (n : ℕ) :
    (1 / (P.N n : ℝ)) * ∑ i : Fin (P.N n), (P.deficit n i) ^ 2 ≤
      P.lowEnergy n + P.middleEnergy n + P.tailEnergy n :=
  P.meanSquare_le_energy n

end TentProfile

/-! ## The tent bundle -/

/-- **L21.2 inputs with an explicit finite Fourier discrepancy profile.**
The fields are those of `L21_2FourierInputs`, except that `deficit` is no
longer arbitrary: it is the real part of the DFT of `profile.coeff`, and the
three frequency terms are the explicit band energies of `profile.coeff`.  The
mean-square field is therefore a theorem (`TentProfile.tentMeanSquare`). -/
structure L21_2TentInputs where
  /-- The finite discrepancy profile. -/
  profile : TentProfile
  /-- The stage-one constant `c` (the paper takes `c = 1/√2`). -/
  c : ℝ
  /-- Perron constant in the vertical error `O (v^{2/3} U^C)`. -/
  Kper : ℕ → ℝ
  /-- The absolute exponent `C` of the Perron/twisted-sum errors. -/
  Cper : ℝ
  /-- Exponent in `ε = e^{-a/3} U^{Ceps}`. -/
  Ceps : ℝ
  /-- The Fourier gap `μ̂ (t) - ν̂ (t)`. -/
  fourierGap : ℕ → ℝ → ℂ
  smoothCount : ℕ → ℝ
  /-- Exponent of the explicit polynomial factor `(1 + U)^{polyExp}`. -/
  polyExp : ℝ
  X_gt_one : ∀ n, 1 < profile.X n
  c_pos : 0 < c
  c_le_one : c ≤ 1
  /-- `log X ≥ 3` for every band. -/
  U_ge_three : ∀ n, 3 ≤ bandLog profile.X n
  Kper_nonneg : ∀ n, 0 ≤ Kper n
  Cper_ge_two : 2 ≤ Cper
  Ceps_nonneg : 0 ≤ Ceps
  polyExp_ge_three : 3 ≤ polyExp
  smoothCount_nonneg : ∀ n, 0 ≤ smoothCount n
  /-- **Perron at `Re s = 2/3`** (unchanged paper input). -/
  perronShift : ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c profile.X n → |t| ≤ profile.X n ^ 3 →
      ‖twistedPrimeSum v t - twistedMain v t‖ ≤
        Kper n * (v ^ (2 / 3 : ℝ) * (bandLog profile.X n) ^ Cper
          + v * (bandLog profile.X n) ^ Cper / profile.X n ^ 3
          + Real.sqrt v * (Real.log (2 * v)) ^ 2)
  /-- **The Perron constant is absolute.** -/
  Kper_bdd : ∃ K : ℝ, ∀ n, 3 * Kper n ≤ K
  /-- **Partial summation**: the Fourier gap is the Abel transform of the
  twisted error. -/
  fourierGap_eq_abel : ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
    fourierGap n t = abelGapOf profile.X c n t
  /-- The polynomial exponent absorbs the Abel boundary factor. -/
  Ceps_ge : Cper + 2 ≤ Ceps
  /-- `k = O (U^{1/2+o(1)})`, in the coarse form `k ≤ log X`. -/
  k_le_U : ∀ᶠ n : ℕ in atTop, kOf profile.X c n ≤ bandLog profile.X n
  /-- The lower band edge satisfies `e^a ≥ 2`. -/
  a_ge_log_two : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ aOf profile.X c n
  /-- `b ≤ B` eventually, the paper's prime-product cutoff below `B = c T_X`. -/
  b_le_B : ∀ᶠ n : ℕ in atTop, bOf profile.X c n ≤ logCutoff c profile.X n
  /-- **The density-normalization count** (unchanged paper input). -/
  densityNormalization : ∀ᶠ n : ℕ in atTop,
    Real.sqrt (profile.X n) *
        Real.exp (-(representationLog (kOf profile.X c) (spacingOf profile.X c)
          (bOf profile.X c) n)) ≤ smoothCount n
  /-- **Low frequency** (`|t| ≤ 1`). -/
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.lowEnergy n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate profile.X n)
  /-- **Middle frequency** (`1 < |t| ≤ X³`). -/
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.middleEnergy n ≤ Real.exp (-((1 / c) - δ) * paperRate profile.X n)
  /-- **High frequency** (`|t| > X³`). -/
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.tailEnergy n ≤ Real.exp (-δ * paperRate profile.X n)
  /-- **Two-scale separation**. -/
  U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog profile.X n
  /-- `log X ≤ exp (scale n)`. -/
  U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog profile.X n ≤ Real.exp (scale n)

namespace L21_2TentInputs

variable (T : L21_2TentInputs)

/-- The dyadic centre bound. -/
abbrev X (n : ℕ) : ℝ := T.profile.X n

/-- The sample size. -/
abbrev N (n : ℕ) : ℝ := T.profile.N n

/-- The actual finite discrepancy profile. -/
abbrev deficit (n : ℕ) (i : Fin (T.profile.N n)) : ℝ := T.profile.deficit n i

/-- The low-band energy. -/
abbrev lowTerm (n : ℕ) : ℝ := T.profile.lowEnergy n

/-- The middle-band energy. -/
abbrev middleTerm (n : ℕ) : ℝ := T.profile.middleEnergy n

/-- The tail-band energy. -/
abbrev tailTerm (n : ℕ) : ℝ := T.profile.tailEnergy n

/-- **`tentMeanSquare` from the explicit profile.**  This is the only field of
`L21_2FourierInputs` that was previously abstract; it is now proved from the
finite Plancherel identity and the band partition. -/
theorem tentMeanSquare :
    ∀ᶠ n : ℕ in atTop,
      (1 / (T.N n)) * ∑ i : Fin (T.profile.N n), (T.deficit n i) ^ 2 ≤
        T.lowTerm n + T.middleTerm n + T.tailTerm n :=
  Eventually.of_forall fun n => T.profile.meanSquare_le_energy n

/-- The tent bundle builds the Fourier bundle with the profile made explicit. -/
def toFourierInputs : L21_2FourierInputs where
  X := T.profile.X
  c := T.c
  Kper := T.Kper
  Cper := T.Cper
  Ceps := T.Ceps
  fourierGap := T.fourierGap
  smoothCount := T.smoothCount
  lowTerm := T.profile.lowEnergy
  middleTerm := T.profile.middleEnergy
  tailTerm := T.profile.tailEnergy
  polyExp := T.polyExp
  N := T.profile.N
  deficit := T.profile.deficit
  X_gt_one := T.X_gt_one
  c_pos := T.c_pos
  c_le_one := T.c_le_one
  U_ge_three := T.U_ge_three
  Kper_nonneg := T.Kper_nonneg
  Cper_ge_two := T.Cper_ge_two
  Ceps_nonneg := T.Ceps_nonneg
  polyExp_ge_three := T.polyExp_ge_three
  smoothCount_nonneg := T.smoothCount_nonneg
  lowTerm_nonneg := fun n => by
    letI := T.profile.neZero n
    exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (T.profile.coeff n j)
  middleTerm_nonneg := fun n => by
    letI := T.profile.neZero n
    exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (T.profile.coeff n j)
  tailTerm_nonneg := fun n => by
    letI := T.profile.neZero n
    exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (T.profile.coeff n j)
  N_pos := T.profile.N_pos
  perronShift := T.perronShift
  Kper_bdd := T.Kper_bdd
  fourierGap_eq_abel := T.fourierGap_eq_abel
  Ceps_ge := T.Ceps_ge
  k_le_U := T.k_le_U
  a_ge_log_two := T.a_ge_log_two
  b_le_B := T.b_le_B
  densityNormalization := T.densityNormalization
  fourierLow := T.fourierLow
  fourierMiddle := T.fourierMiddle
  fourierTail := T.fourierTail
  tentMeanSquare := T.tentMeanSquare
  U_dominates := T.U_dominates
  U_le_exp := T.U_le_exp

/-- The Perron bundle assembled from the tent inputs. -/
def toPerronInputs : L21_2PerronInputs := T.toFourierInputs.toPerronInputs

/-- The reduced L21.2 bundle. -/
def toReducedInputs : L21_2ReducedInputs := T.toPerronInputs.toReducedInputs

/-- The parent `L21_2Inputs`. -/
def toInputs : L21_2Inputs := T.toReducedInputs.toInputs

/-- The L21.2 `RatedLeaf`. -/
def toRatedLeaf : RatedLeaf := T.toReducedInputs.toRatedLeaf

/-- The `D^{-B}` form packaged as a `SubexpLeaf`. -/
def toSubexpLeaf : SubexpLeaf := T.toReducedInputs.toSubexpLeaf

theorem loss_nonneg (n : ℕ) : 0 ≤ T.toReducedInputs.loss n :=
  T.toReducedInputs.loss_nonneg n

theorem loss_le_paper :
    ∀ᶠ n : ℕ in atTop,
      T.toReducedInputs.loss n ≤ Real.exp (-((T.c / 64) * paperRate T.profile.X n)) :=
  T.toReducedInputs.loss_le_paper

theorem loss_le_ledger :
    ∀ᶠ n : ℕ in atTop,
      T.toReducedInputs.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  T.toReducedInputs.loss_le_ledger

/-- The `C5Leaf.ellipticExceptional` slot, when identified with this loss, is
eventually at most `exp (-2 * scale n)`. -/
theorem slot_le {slots : C5LossSlots}
    (h : slots .ellipticExceptional = T.toReducedInputs.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .ellipticExceptional n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  L21_2ReducedInputs.slot_le T.toReducedInputs h

/-- The eleven remaining leaves plus the tent inputs give the full paper
assumptions. -/
def paperAssumptions_of_tent
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (A : PaperAnalyticAssumptionsWithoutL21_2 E C) :
    PaperAnalyticAssumptions E C :=
  L21_2ReducedInputs.paperAssumptions_of_reduced T.toReducedInputs A

end L21_2TentInputs

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2Tent.DiscretePlancherel.dft_parseval
#print axioms Cogentic.RandomizedL21_2Tent.DiscretePlancherel.dft_re_mean_square_le
#print axioms Cogentic.RandomizedL21_2Tent.TentProfile.energy_split
#print axioms Cogentic.RandomizedL21_2Tent.TentProfile.meanSquare_le_energy
#print axioms Cogentic.RandomizedL21_2Tent.TentProfile.tentMeanSquare
#print axioms Cogentic.RandomizedL21_2Tent.L21_2TentInputs.tentMeanSquare
#print axioms Cogentic.RandomizedL21_2Tent.L21_2TentInputs.toFourierInputs
#print axioms Cogentic.RandomizedL21_2Tent.L21_2TentInputs.toPerronInputs
#print axioms Cogentic.RandomizedL21_2Tent.L21_2TentInputs.toReducedInputs
#print axioms Cogentic.RandomizedL21_2Tent.L21_2TentInputs.toInputs
#print axioms Cogentic.RandomizedL21_2Tent.L21_2TentInputs.toRatedLeaf
#print axioms Cogentic.RandomizedL21_2Tent.L21_2TentInputs.toSubexpLeaf
#print axioms Cogentic.RandomizedL21_2Tent.L21_2TentInputs.slot_le
#print axioms Cogentic.RandomizedL21_2Tent.L21_2TentInputs.paperAssumptions_of_tent

end Cogentic.RandomizedL21_2Tent
