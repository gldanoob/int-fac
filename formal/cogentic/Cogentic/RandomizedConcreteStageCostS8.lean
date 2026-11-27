import Cogentic.RandomizedConcreteStageCost
import Cogentic.RandomizedConcreteEpochCost
import Cogentic.RootSignCost
import Cogentic.ReconstructionCost
import Cogentic.ModularPowerCost

/-!
# Concrete stage cost for `S8` (square root / product check / field evaluation)

`Cogentic.RandomizedConcreteStageCost` instantiates the `S0` and `S7` slots of
the ten `StageCosts` fields of `RandomizedConcreteEpoch`.  This file instantiates
**one more** slot, `S8` (square root, product check and field evaluation), and
proves its polynomial bit-cost bound.  The remaining seven stages are
deliberately *not* claimed.

## The existing counters used

The concrete public work of `S8` is read off three counters that already exist
in the development; no new arithmetic primitive is postulated:

* **Field evaluation.**  `RandomizedRootSign.polynomial` / `atPoint` evaluate a
  homogeneous polynomial at a rational point through the homogeneous Horner
  recursion, and `atPoint_gates` bounds the gate count by
  `500 * (coeffs.length + 1) * (H + 1)^2`, where
  `H = 1 + (coeffs.length + 1) * (12 * W + 1)`.  The term `s8EvalCost` below is
  exactly this bound at the coefficient count and bit width selected from
  `inputBits`.
* **Root reconstruction.**  `RandomizedReconstruction.reconstructBits` produces
  the signed rational coordinates used to assemble the public root, and
  `reconstruct_bits` bounds its cost by
  `L^2 * (400 * (w + 3)^2) + L * (500 * w^2 + 1)` with `L = 2 * log₂ v + 1` and
  `w = |u| + v + Q + 3`.  `coordinateBudget h` is that bound at width `h`; the
  term `s8RootCost` is `coordinateBudget` at the input width.
* **Product check.**  `RandomizedModularPower.mulMod` multiplies two residues and
  reduces modulo the input, and `mulMod_spec` bounds one multiplication by
  `136 * d.length^2 + 3 * d.length`.  The term `s8MulBound` is that bound and
  `s8ProductCheckCost` charges one multiplication per label plus the final
  comparison, so the check `Y^2 ≡ ∏ A_i (mod N)` costs at most
  `(fieldCount + 1) * s8MulBound`.

Thus

```
s8Cost N = fieldCount N * (s8EvalCost N + s8RootCost N) + s8ProductCheckCost N
```

is a concrete `ℕ`-valued cost, and the proved polynomial bound is

```
s8Cost N ≤ 20000000 * (inputBits N)^6.
```

Consequently `s8Cost N ≤ exp (ε * scale N)` eventually for every `ε > 0`.

## Compatibility

The identification hypothesis `S8StageCostAgreement D` says that the concrete
epoch `D` really charges `s8Cost` at `S8`.  Under it:

* `s8_mean_le` discharges the C4 mean obligation at `S8` (the cost is
  deterministic);
* `s8StageC4Bound` packages the proved C4 slot as a `StageC4Bound`;
* `ConcreteC4Hypotheses.withS8` replaces the `S8` slot of an arbitrary
  `ConcreteC4Hypotheses` by the proved one, leaving the other nine stages as
  supplied by the caller.

No `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choose` is used.
-/

namespace Cogentic.RandomizedConcreteStageCostS8

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpochCost
open Cogentic.RandomizedConcreteStageCost
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.BinaryReconstruction
open Cogentic.BinaryRootSign
open Cogentic.BinaryModularPower
open Cogentic.BinaryPivot
open Cogentic.BinaryDivision
open Filter Real
open scoped BigOperators ENNReal

/-! ## Section 1: The concrete `S8` cost -/

/-- Number of field-evaluation tasks carried by `S8`: one per private label,
read off the input bit length. -/
def s8FieldCount (N : ℕ) : ℕ := inputBits N

/-- Number of homogeneous-polynomial coefficients handled by one evaluation. -/
def s8CoeffCount (N : ℕ) : ℕ := inputBits N

/-- Bit width of one evaluation argument. -/
def s8EvalWidth (N : ℕ) : ℕ := inputBits N + 1

/-- The intermediate height appearing in `BinaryRootSign.atPoint_gates`. -/
def s8EvalH (N : ℕ) : ℕ :=
  1 + (s8CoeffCount N + 1) * (12 * s8EvalWidth N + 1)

/-- Gate bound for one homogeneous field evaluation, copied from
`BinaryRootSign.atPoint_gates`. -/
def s8EvalCost (N : ℕ) : ℕ :=
  500 * (s8CoeffCount N + 1) * (s8EvalH N + 1) ^ 2

/-- Gate bound for one root reconstruction, copied from
`BinaryReconstruction.reconstruct_bits` (via `coordinateBudget`). -/
def s8RootCost (N : ℕ) : ℕ := coordinateBudget (inputBits N + 1)

/-- Gate bound for one modular multiplication, copied from
`BinaryModularPower.mulMod_spec`. -/
def s8MulBound (N : ℕ) : ℕ :=
  136 * (inputBits N) ^ 2 + 3 * inputBits N

/-- Product-check cost: one modular multiplication per label plus the final
comparison. -/
def s8ProductCheckCost (N : ℕ) : ℕ :=
  (s8FieldCount N + 1) * s8MulBound N

/-- Concrete `S8` cost: per field, one root reconstruction and one homogeneous
evaluation, followed by the product check. -/
def s8Cost (N : ℕ) : ℕ :=
  s8FieldCount N * (s8EvalCost N + s8RootCost N) + s8ProductCheckCost N

theorem s8Cost_nonneg (N : ℕ) : 0 ≤ s8Cost N := Nat.zero_le _

/-! ## Section 2: The polynomial bound -/

/-- The evaluation height is quadratic in the input width. -/
theorem s8EvalH_le (N : ℕ) :
    s8EvalH N ≤ 13 * (inputBits N + 1) ^ 2 := by
  unfold s8EvalH s8CoeffCount s8EvalWidth
  have hB : 1 ≤ inputBits N := inputBits_pos N
  nlinarith only [hB]

/-- The evaluation height plus one is at most `15 * (B + 1)^2`. -/
theorem s8EvalH_add_one_le (N : ℕ) :
    s8EvalH N + 1 ≤ 15 * (inputBits N + 1) ^ 2 := by
  have hB : 1 ≤ inputBits N := inputBits_pos N
  have h := s8EvalH_le N
  have hsq : 1 ≤ (inputBits N + 1) ^ 2 := by nlinarith only [hB]
  nlinarith only [h, hsq]

theorem pow_five_succ_le (B : ℕ) (hB : 1 ≤ B) :
    (B + 1) ^ 5 ≤ 32 * B ^ 5 := by
  have h : B + 1 ≤ 2 * B := by omega
  calc
    (B + 1) ^ 5 ≤ (2 * B) ^ 5 := Nat.pow_le_pow_left h 5
    _ = 32 * B ^ 5 := by ring

/-- One field evaluation costs at most `4 * 10^6 * B^5`. -/
theorem s8EvalCost_le (N : ℕ) :
    s8EvalCost N ≤ 4000000 * (inputBits N) ^ 5 := by
  have hB : 1 ≤ inputBits N := inputBits_pos N
  have hH : s8EvalH N + 1 ≤ 15 * (inputBits N + 1) ^ 2 :=
    s8EvalH_add_one_le N
  have hsq : (s8EvalH N + 1) ^ 2 ≤
      (15 * (inputBits N + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hH 2
  have hpow : (inputBits N + 1) ^ 5 ≤ 32 * (inputBits N) ^ 5 :=
    pow_five_succ_le (inputBits N) hB
  calc
    s8EvalCost N = 500 * (inputBits N + 1) * (s8EvalH N + 1) ^ 2 := by
      simp only [s8EvalCost, s8CoeffCount]
    _ ≤ 500 * (inputBits N + 1) * (15 * (inputBits N + 1) ^ 2) ^ 2 := by
      gcongr
    _ = 112500 * (inputBits N + 1) ^ 5 := by ring
    _ ≤ 112500 * (32 * (inputBits N) ^ 5) :=
      Nat.mul_le_mul_left _ hpow
    _ = 3600000 * (inputBits N) ^ 5 := by ring
    _ ≤ 4000000 * (inputBits N) ^ 5 :=
      Nat.mul_le_mul_right _ (by norm_num)

/-- The root-reconstruction budget is quartic in its width. -/
theorem coordinateBudget_le (h : ℕ) (hh : 1 ≤ h) :
    coordinateBudget h ≤ 345603 * h ^ 4 := by
  unfold coordinateBudget
  dsimp only
  have hL : 2 * h + 1 ≤ 3 * h := by omega
  have hw : 3 * h + 3 ≤ 6 * h := by omega
  have hw3 : 3 * h + 3 + 3 ≤ 9 * h := by omega
  have hL2 : (2 * h + 1) ^ 2 ≤ (3 * h) ^ 2 := Nat.pow_le_pow_left hL 2
  have hw2 : ((3 * h + 3) + 3) ^ 2 ≤ (9 * h) ^ 2 := Nat.pow_le_pow_left hw3 2
  have hw_orig : (3 * h + 3) ^ 2 ≤ (6 * h) ^ 2 := Nat.pow_le_pow_left hw 2
  have hfirst :
      (2 * h + 1) ^ 2 * (400 * ((3 * h + 3) + 3) ^ 2) ≤
        (3 * h) ^ 2 * (400 * (9 * h) ^ 2) := by
    gcongr
  have hsecond :
      (2 * h + 1) * (500 * (3 * h + 3) ^ 2 + 1) ≤
        (3 * h) * (500 * (6 * h) ^ 2 + 1) := by
    gcongr
  have hsix : 500 * (6 * h) ^ 2 + 1 ≤ 18001 * h ^ 2 := by
    have hh2 : 1 ≤ h ^ 2 := by nlinarith only [hh]
    nlinarith only [hh2]
  have h34 : h ^ 3 ≤ h ^ 4 := by
    calc
      h ^ 3 = h ^ 3 * 1 := (Nat.mul_one _).symm
      _ ≤ h ^ 3 * h := Nat.mul_le_mul_left _ hh
      _ = h ^ 4 := by ring
  calc
    (2 * h + 1) ^ 2 * (400 * ((3 * h + 3) + 3) ^ 2) +
        (2 * h + 1) * (500 * (3 * h + 3) ^ 2 + 1)
        ≤ (3 * h) ^ 2 * (400 * (9 * h) ^ 2) +
            (3 * h) * (500 * (6 * h) ^ 2 + 1) :=
          Nat.add_le_add hfirst hsecond
    _ ≤ (3 * h) ^ 2 * (400 * (9 * h) ^ 2) + (3 * h) * (18001 * h ^ 2) := by
      gcongr
    _ = 291600 * h ^ 4 + 54003 * h ^ 3 := by ring
    _ ≤ 291600 * h ^ 4 + 54003 * h ^ 4 :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ h34) _
    _ = 345603 * h ^ 4 := by ring

theorem s8RootCost_le (N : ℕ) :
    s8RootCost N ≤ 6000000 * (inputBits N) ^ 5 := by
  have hB : 1 ≤ inputBits N := inputBits_pos N
  have hh : 1 ≤ inputBits N + 1 := by omega
  have hroot := coordinateBudget_le (inputBits N + 1) hh
  have hpow : (inputBits N + 1) ^ 4 ≤ 16 * (inputBits N) ^ 4 := by
    have h : inputBits N + 1 ≤ 2 * inputBits N := by omega
    calc
      (inputBits N + 1) ^ 4 ≤ (2 * inputBits N) ^ 4 :=
        Nat.pow_le_pow_left h 4
      _ = 16 * (inputBits N) ^ 4 := by ring
  have hfour : (inputBits N) ^ 4 ≤ (inputBits N) ^ 5 := by
    calc
      (inputBits N) ^ 4 = (inputBits N) ^ 4 * 1 := (Nat.mul_one _).symm
      _ ≤ (inputBits N) ^ 4 * (inputBits N) :=
        Nat.mul_le_mul_left _ hB
      _ = (inputBits N) ^ 5 := by ring
  calc
    s8RootCost N = coordinateBudget (inputBits N + 1) := rfl
    _ ≤ 345603 * (inputBits N + 1) ^ 4 := hroot
    _ ≤ 345603 * (16 * (inputBits N) ^ 4) :=
      Nat.mul_le_mul_left _ hpow
    _ = 5529648 * (inputBits N) ^ 4 := by ring
    _ ≤ 6000000 * (inputBits N) ^ 4 :=
      Nat.mul_le_mul_right _ (by norm_num)
    _ ≤ 6000000 * (inputBits N) ^ 5 :=
      Nat.mul_le_mul_left _ hfour

theorem s8MulBound_le (N : ℕ) :
    s8MulBound N ≤ 139 * (inputBits N) ^ 2 := by
  unfold s8MulBound
  have hB : 1 ≤ inputBits N := inputBits_pos N
  nlinarith only [hB]

theorem s8ProductCheckCost_le (N : ℕ) :
    s8ProductCheckCost N ≤ 278 * (inputBits N) ^ 6 := by
  have hB : 1 ≤ inputBits N := inputBits_pos N
  have hmul := s8MulBound_le N
  have hfield : s8FieldCount N + 1 ≤ 2 * inputBits N := by
    unfold s8FieldCount
    omega
  have hthree : 278 * (inputBits N) ^ 3 ≤ 278 * (inputBits N) ^ 6 := by
    have h3 : (inputBits N) ^ 3 ≤ (inputBits N) ^ 6 := by
      calc
        (inputBits N) ^ 3 = (inputBits N) ^ 3 * 1 := (Nat.mul_one _).symm
        _ ≤ (inputBits N) ^ 3 * (inputBits N) ^ 3 :=
          Nat.mul_le_mul_left _ (one_le_pow₀ hB)
        _ = (inputBits N) ^ 6 := by ring
    exact Nat.mul_le_mul_left _ h3
  calc
    s8ProductCheckCost N = (s8FieldCount N + 1) * s8MulBound N := rfl
    _ ≤ (2 * inputBits N) * (139 * (inputBits N) ^ 2) :=
      Nat.mul_le_mul hfield hmul
    _ = 278 * (inputBits N) ^ 3 := by ring
    _ ≤ 278 * (inputBits N) ^ 6 := hthree

/-- **Polynomial bit-cost bound for `S8`.** -/
theorem s8Cost_le_poly (N : ℕ) :
    s8Cost N ≤ 20000000 * (inputBits N) ^ 6 := by
  have hB : 1 ≤ inputBits N := inputBits_pos N
  have heval := s8EvalCost_le N
  have hroot := s8RootCost_le N
  have hfield : s8FieldCount N ≤ inputBits N := le_rfl
  have hsum : s8EvalCost N + s8RootCost N ≤ 10000000 * (inputBits N) ^ 5 := by
    calc
      s8EvalCost N + s8RootCost N ≤
          4000000 * (inputBits N) ^ 5 + 6000000 * (inputBits N) ^ 5 :=
        Nat.add_le_add heval hroot
      _ = 10000000 * (inputBits N) ^ 5 := by ring
  have hmain : s8FieldCount N * (s8EvalCost N + s8RootCost N) ≤
      10000000 * (inputBits N) ^ 6 := by
    calc
      s8FieldCount N * (s8EvalCost N + s8RootCost N) ≤
          (inputBits N) * (10000000 * (inputBits N) ^ 5) :=
        Nat.mul_le_mul hfield hsum
      _ = 10000000 * (inputBits N) ^ 6 := by ring
  have hprod := s8ProductCheckCost_le N
  calc
    s8Cost N = s8FieldCount N * (s8EvalCost N + s8RootCost N) +
        s8ProductCheckCost N := rfl
    _ ≤ 10000000 * (inputBits N) ^ 6 + 278 * (inputBits N) ^ 6 :=
      Nat.add_le_add hmain hprod
    _ = 10000278 * (inputBits N) ^ 6 := by ring
    _ ≤ 20000000 * (inputBits N) ^ 6 :=
      Nat.mul_le_mul_right _ (by norm_num)

/-- The `S8` cost is eventually dominated by any positive exponential of the
one-third scale. -/
theorem eventually_s8Cost_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (s8Cost N : ℝ) ≤ exp (ε * scale N) := by
  filter_upwards [eventually_bitPoly_le_exp (A := 20000000) hε 6] with N hN
  have hcast : (s8Cost N : ℝ) ≤ 20000000 * ((N.log2 : ℝ) + 1) ^ 6 := by
    have h := s8Cost_le_poly N
    have h' : (s8Cost N : ℝ) ≤ ((20000000 * (inputBits N) ^ 6 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [inputBits] using h'
  exact hcast.trans hN

/-! ## Section 3: The cost is read off the existing counters -/

/-- The gate count of one homogeneous field evaluation is at most
`s8EvalCost`, uniformly over all coefficient lists and argument widths that fit
the `S8` parameter choice.  This is `BinaryRootSign.atPoint_gates` at the
selected width. -/
theorem atPoint_cost_le_s8EvalCost (N : ℕ) (A : List Bool) (z : SignedWord)
    (q : List Bool) (cs : List SignedWord)
    (hA : A.length ≤ s8EvalWidth N)
    (hz : z.digits.length ≤ s8EvalWidth N)
    (hq : q.length ≤ s8EvalWidth N)
    (hlen : cs.length ≤ s8CoeffCount N)
    (hcoeff : ∀ c ∈ cs, c.digits.length ≤ s8EvalWidth N) :
    (atPoint A z q cs).2 ≤ s8EvalCost N := by
  have h := atPoint_gates A z q cs (s8EvalWidth N) hA hz hq hcoeff
  dsimp only at h
  have hH : 1 + (cs.length + 1) * (12 * s8EvalWidth N + 1) ≤ s8EvalH N := by
    unfold s8EvalH
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (Nat.succ_le_succ hlen)) 1
  have hlen1 : cs.length + 1 ≤ s8CoeffCount N + 1 := by omega
  have hsq :
      (1 + (cs.length + 1) * (12 * s8EvalWidth N + 1) + 1) ^ 2 ≤
        (s8EvalH N + 1) ^ 2 := by
    apply Nat.pow_le_pow_left
    omega
  calc
    (atPoint A z q cs).2 ≤
        500 * (cs.length + 1) *
          (1 + (cs.length + 1) * (12 * s8EvalWidth N + 1) + 1) ^ 2 := h
    _ ≤ 500 * (s8CoeffCount N + 1) * (s8EvalH N + 1) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 500 hlen1) hsq
    _ = s8EvalCost N := rfl

/-- The gate count of root reconstruction is at most `s8RootCost`, uniformly
over all signed rational inputs whose coordinates fit the input width.  This is
`BinaryReconstruction.reconstruct_bits` at the selected width. -/
theorem reconstructBits_cost_le_s8RootCost (N : ℕ) (u : ℤ) (v Q : ℕ)
    (hp : 0 < v)
    (hu : u.natAbs.size ≤ inputBits N + 1)
    (hv : v.size ≤ inputBits N + 1)
    (hQ : Q.size ≤ inputBits N + 1)
    (hvlog : v.log2 ≤ inputBits N + 1) :
    (reconstructBits u v Q).2 ≤ s8RootCost N := by
  have h := reconstruct_bits u v Q hp
  obtain ⟨-, hcost⟩ := h
  let w := u.natAbs.size + v.size + Q.size + 3
  let L := 2 * v.log2 + 1
  let W := inputBits N + 1
  have hw : w ≤ 3 * W + 3 := by
    dsimp only [w, W]
    omega
  have hL : L ≤ 2 * W + 1 := by
    dsimp only [L, W]
    omega
  have hw3 : w + 3 ≤ (3 * W + 3) + 3 := by omega
  have hfirst :
      L ^ 2 * (400 * (w + 3) ^ 2) ≤
        (2 * W + 1) ^ 2 * (400 * ((3 * W + 3) + 3) ^ 2) := by
    apply Nat.mul_le_mul
    · exact Nat.pow_le_pow_left hL 2
    · exact Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left hw3 2)
  have hw2 : w ^ 2 ≤ (3 * W + 3) ^ 2 := Nat.pow_le_pow_left hw 2
  have hsecond :
      L * (500 * w ^ 2 + 1) ≤
        (2 * W + 1) * (500 * (3 * W + 3) ^ 2 + 1) := by
    apply Nat.mul_le_mul hL
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 500 hw2) 1
  have hsum := Nat.add_le_add hfirst hsecond
  have hbudget :
      (2 * W + 1) ^ 2 * (400 * ((3 * W + 3) + 3) ^ 2) +
          (2 * W + 1) * (500 * (3 * W + 3) ^ 2 + 1) =
        coordinateBudget W := by
    dsimp only [coordinateBudget, W]
  exact hcost.trans (hsum.trans_eq hbudget)

/-- The gate count of one modular multiplication is at most `s8MulBound`.  This
is `BinaryModularPower.mulMod_spec` at the selected width. -/
theorem mulMod_cost_le_s8MulBound (N : ℕ) (d x y : List Bool)
    (pos : 0 < value d) (hx : x.length ≤ d.length) (hy : y.length ≤ d.length)
    (hd : d.length ≤ s8FieldCount N) :
    (mulMod d x y).2 ≤ s8MulBound N := by
  have h := (mulMod_spec d x y pos hx hy).2.2
  have hd2 : d.length ^ 2 ≤ (s8FieldCount N) ^ 2 := Nat.pow_le_pow_left hd 2
  calc
    (mulMod d x y).2 ≤ 136 * d.length ^ 2 + 3 * d.length := h
    _ ≤ 136 * (s8FieldCount N) ^ 2 + 3 * s8FieldCount N := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left 136 hd2
      · exact Nat.mul_le_mul_left 3 hd
    _ = s8MulBound N := by
      unfold s8MulBound s8FieldCount
      ring

/-! ## Section 4: The `S8` stage cost and its identification hypothesis -/

section StageCost

/-- The concrete `S8` stage cost: square root / product check / field
evaluation, independent of the sampled coins and hidden labels. -/
def s8StageCost (Coins Label : Type) (N : ℕ) : StageCost N Coins Label :=
  fun _ => s8Cost N

@[simp] theorem s8StageCost_apply (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s8StageCost Coins Label N x = s8Cost N := rfl

theorem s8StageCost_nonneg (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    0 ≤ s8StageCost Coins Label N x := Nat.zero_le _

theorem s8StageCost_le_poly (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s8StageCost Coins Label N x ≤ 20000000 * (inputBits N) ^ 6 :=
  s8Cost_le_poly N

end StageCost

/-- Identification hypothesis: the concrete epoch `D` charges exactly the
deterministic `S8` cost of this file.  This is a modelling statement about
which epoch is being costed, not an analytic estimate. -/
structure S8StageCostAgreement {N : ℕ} (D : ConcreteEpochData N) : Prop where
  /-- `S8` is the square root / product check / field evaluation cost. -/
  s8 : ∀ x : D.Sample, D.stageCosts.s8 x = s8Cost N

namespace S8StageCostAgreement

variable {N : ℕ} {D : ConcreteEpochData N}

/-- The `S8` slot of the canonical single-epoch stage decomposition. -/
theorem stageDecomposition_cost_S8 (H : S8StageCostAgreement D) (x : D.Sample) :
    D.stageDecomposition.cost Stage.S8 x = s8Cost N := by
  change D.stageCosts.s8 x = s8Cost N
  exact H.s8 x

/-- The concrete `S8` work is charged to the epoch's public work. -/
theorem s8Cost_le_pubWork (H : S8StageCostAgreement D) (x : D.Sample) :
    s8Cost N ≤ D.toHardEpochData.pubWork x := by
  have hc : D.stageCosts.cost Stage.S8 x = s8Cost N := by
    change D.stageCosts.s8 x = s8Cost N
    exact H.s8 x
  have h := D.stageCost_le_pubWork Stage.S8 x
  rwa [hc] at h

end S8StageCostAgreement

/-- The family-level stage decomposition has the concrete `S8` cost in its `S8`
slot. -/
theorem familyStageDecomposition_cost_S8
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S8StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S8 n hN x = s8Cost n := by
  rw [familyStageDecomposition_cost]
  exact (H n).s8 x

/-- The family-level `S8` slot obeys the polynomial bound uniformly in `n`. -/
theorem familyStageDecomposition_cost_S8_le_poly
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S8StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S8 n hN x ≤
      20000000 * (inputBits n) ^ 6 := by
  rw [familyStageDecomposition_cost_S8 D H n hN x]
  exact s8Cost_le_poly n

/-! ## Section 5: Compatibility with `StageC4Bound` and `ConcreteC4Hypotheses` -/

/-- The `S8` mean cost is the deterministic value `s8Cost n`, so the C4 mean
obligation at `S8` is a theorem, not a hypothesis. -/
theorem s8_mean_le (D : ∀ n, ConcreteEpochData n)
    (H : ∀ n, S8StageCostAgreement (D n)) (n : ℕ) (hN : 3 ≤ n) :
    mean (concreteCostFamily D n hN).actual
        (fun x => ((D n).stageCosts.cost Stage.S8 x : ℝ≥0∞)) ≤
      ENNReal.ofReal (s8Cost n) := by
  change mean (D n).actual
      (fun x : (D n).Sample => ((D n).stageCosts.cost Stage.S8 x : ℝ≥0∞)) ≤
    ENNReal.ofReal (s8Cost n)
  have hfun : (fun x : (D n).Sample =>
      ((D n).stageCosts.cost Stage.S8 x : ℝ≥0∞)) = fun _ => (s8Cost n : ℝ≥0∞) := by
    funext x
    have hc : (D n).stageCosts.cost Stage.S8 x = s8Cost n := by
      change (D n).stageCosts.s8 x = s8Cost n
      exact (H n).s8 x
    rw [hc]
  rw [hfun, mean_const]
  exact le_of_eq (ENNReal.ofReal_natCast (s8Cost n)).symm

/-- **The `S8` C4 slot is discharged** with weight `s8Cost n` and any exponent
`c` with `0 < c < C`. -/
def s8StageC4Bound (D : ∀ n, ConcreteEpochData n) {C c : ℝ}
    (hc : 0 < c) (hcC : c < C) (H : ∀ n, S8StageCostAgreement (D n)) :
    StageC4Bound D C Stage.S8 where
  weight := fun n => (s8Cost n : ℝ)
  exponent := c
  exponent_lt := hcC
  mean_le := Filter.Eventually.of_forall fun n => s8_mean_le D H n
  weight_le := eventually_s8Cost_le_exp hc

/-- Weights for all ten stages with `S8` overridden by the concrete cost. -/
def overrideWeightS8 (W : Stage → ℕ → ℝ) : Stage → ℕ → ℝ
  | Stage.S8 => fun n => (s8Cost n : ℝ)
  | j => W j

/-- Exponents for all ten stages with `S8` overridden by the chosen exponent. -/
def overrideExponentS8 (c8 : ℝ) (c : Stage → ℝ) : Stage → ℝ
  | Stage.S8 => c8
  | j => c j

/-- **C4 compatibility: replace the `S8` slot by the proved one.**  Every other
stage is left exactly as supplied by `Hc4`; only the `S8` mean and weight data
are replaced by `s8_mean_le` and `eventually_s8Cost_le_exp`. -/
noncomputable def ConcreteC4Hypotheses.withS8
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (Hc4 : ConcreteC4Hypotheses D C)
    (H8 : ∀ n, S8StageCostAgreement (D n))
    {c8 : ℝ} (hc8 : 0 < c8) (h8C : c8 < C) :
    ConcreteC4Hypotheses D C where
  stageWeight := overrideWeightS8 Hc4.stageWeight
  stageExponent := overrideExponentS8 c8 Hc4.stageExponent
  exponent_lt := by
    intro j
    cases j with
    | S0 => simpa [overrideExponentS8] using Hc4.exponent_lt Stage.S0
    | S1 => simpa [overrideExponentS8] using Hc4.exponent_lt Stage.S1
    | S2 => simpa [overrideExponentS8] using Hc4.exponent_lt Stage.S2
    | S3 => simpa [overrideExponentS8] using Hc4.exponent_lt Stage.S3
    | S4 => simpa [overrideExponentS8] using Hc4.exponent_lt Stage.S4
    | S5 => simpa [overrideExponentS8] using Hc4.exponent_lt Stage.S5
    | S6 => simpa [overrideExponentS8] using Hc4.exponent_lt Stage.S6
    | S7 => simpa [overrideExponentS8] using Hc4.exponent_lt Stage.S7
    | S8 => simpa [overrideExponentS8] using h8C
    | S9 => simpa [overrideExponentS8] using Hc4.exponent_lt Stage.S9
  mean_le := by
    intro j
    cases j with
    | S0 => simpa [overrideWeightS8] using Hc4.mean_le Stage.S0
    | S1 => simpa [overrideWeightS8] using Hc4.mean_le Stage.S1
    | S2 => simpa [overrideWeightS8] using Hc4.mean_le Stage.S2
    | S3 => simpa [overrideWeightS8] using Hc4.mean_le Stage.S3
    | S4 => simpa [overrideWeightS8] using Hc4.mean_le Stage.S4
    | S5 => simpa [overrideWeightS8] using Hc4.mean_le Stage.S5
    | S6 => simpa [overrideWeightS8] using Hc4.mean_le Stage.S6
    | S7 => simpa [overrideWeightS8] using Hc4.mean_le Stage.S7
    | S8 =>
        simp only [overrideWeightS8]
        exact Filter.Eventually.of_forall fun n hN => s8_mean_le D H8 n hN
    | S9 => simpa [overrideWeightS8] using Hc4.mean_le Stage.S9
  weight_le := by
    intro j
    cases j with
    | S0 => simpa [overrideWeightS8, overrideExponentS8] using Hc4.weight_le Stage.S0
    | S1 => simpa [overrideWeightS8, overrideExponentS8] using Hc4.weight_le Stage.S1
    | S2 => simpa [overrideWeightS8, overrideExponentS8] using Hc4.weight_le Stage.S2
    | S3 => simpa [overrideWeightS8, overrideExponentS8] using Hc4.weight_le Stage.S3
    | S4 => simpa [overrideWeightS8, overrideExponentS8] using Hc4.weight_le Stage.S4
    | S5 => simpa [overrideWeightS8, overrideExponentS8] using Hc4.weight_le Stage.S5
    | S6 => simpa [overrideWeightS8, overrideExponentS8] using Hc4.weight_le Stage.S6
    | S7 => simpa [overrideWeightS8, overrideExponentS8] using Hc4.weight_le Stage.S7
    | S8 => simpa [overrideWeightS8, overrideExponentS8] using
        eventually_s8Cost_le_exp hc8
    | S9 => simpa [overrideWeightS8, overrideExponentS8] using Hc4.weight_le Stage.S9

/-! ## Section 6: Axiom audit -/

#print axioms s8Cost_le_poly
#print axioms eventually_s8Cost_le_exp
#print axioms atPoint_cost_le_s8EvalCost
#print axioms reconstructBits_cost_le_s8RootCost
#print axioms mulMod_cost_le_s8MulBound
#print axioms s8_mean_le
#print axioms s8StageC4Bound
#print axioms ConcreteC4Hypotheses.withS8

end Cogentic.RandomizedConcreteStageCostS8
