import Cogentic.RandomizedL27Weighted
import Mathlib.Tactic

/-!
# L27 Waterhouse at small primes: an explicit non-vacuity check

`Cogentic.RandomizedL27Waterhouse` states the weighted Deuring/Waterhouse
identity

`∑_{E/F_p, #E(F_p) = p+1-t} 1/#Aut(E) = H(4p - t²)`

as an abstract input, and `Cogentic.RandomizedL27Weighted` reduces its
left-hand side to a raw count of nonsingular Weierstrass equations divided by
the number of admissible variable changes.  This file evaluates both sides
explicitly for the smallest prime, `p = 3`, over `ZMod 3`, and proves the
identity for every trace with positive Frobenius discriminant.  It is a
non-vacuity check for the abstract development, not a general proof.

## What is computed

* `tupleFiberCount p j` is the number of nonsingular coefficient tuples
  `(a₁,a₂,a₃,a₄,a₆)` over `ZMod p` whose Weierstrass curve has exactly `j`
  projective points.  Its equality with `modelFiberCount p j` is proved by the
  coefficient equivalence, and `weightedCurveCount p j` is then the quotient
  of `tupleFiberCount p j` by `#VariableChange = (p-1)p³`.
* `classNumber D` counts reduced primitive positive definite binary quadratic
  forms of discriminant `-D`; `hurwitzClassNumber D` is the Hurwitz class number
  `H(D) = ∑_{d²|D} h(-D/d²)/w(-D/d²)`.
* For `p = 3` the seven nonempty trace fibers are `j = 1,…,7`, with
  `weightedCurveCount 3 j = 1/6, 1/2, 1/2, 2/3, 1/2, 1/2, 1/6`.  These are
  exactly `H(3), H(8), H(11), H(12), H(11), H(8), H(3)`.  The corresponding raw
  isomorphism-class counts, obtained by a separate orbit enumeration of the
  same finite model, are `1, 1, 1, 2, 1, 1, 1`; the raw counts are recorded here
  as a consistency check but are not used by the weighted identity.

`p = 5` and `p = 7` are computationally out of reach for kernel-level
`decide`/`norm_num` without `native_decide`: the p = 5 model has 3125 equations
and 25 affine points each, and a single fiber already costs minutes of kernel
reduction; p = 7 multiplies both factors.  The prime `p = 3` is the largest
prime for which the full identity is checked here in reasonable time.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

set_option linter.style.haveILetI false
set_option maxRecDepth 1000000

namespace Cogentic.RandomizedL27WaterhouseSmall

open scoped BigOperators
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL27Weighted
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27TraceClass

/-! ## 1. The computable coefficient model -/

/-- The five Weierstrass coefficients, as a tuple. -/
abbrev CoeffTuple (p : ℕ) : Type :=
  (ZMod p) × (ZMod p) × (ZMod p) × (ZMod p) × (ZMod p)

/-- The Weierstrass curve attached to a coefficient tuple. -/
def tupleCurve {p : ℕ} (x : CoeffTuple p) : WeierstrassCurve (ZMod p) :=
  WeierstrassCurve.mk x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- Nonsingularity of a coefficient tuple. -/
def TupleNonsing {p : ℕ} (x : CoeffTuple p) : Prop := (tupleCurve x).Δ ≠ 0

/-- The decidable nonsingularity test is the one used by the enumeration. -/
instance tupleNonsingDecidable {p : ℕ} (x : CoeffTuple p) : Decidable (TupleNonsing x) :=
  decidable_of_iff (¬ (tupleCurve x).Δ = 0) (by simp [TupleNonsing])

/-- The projective point count of the curve of a coefficient tuple, written as
an explicit polynomial equation so that kernel reduction does not have to unfold
the `WeierstrassCurve` structure. -/
def tuplePointCount (p : ℕ) [NeZero p] (x : CoeffTuple p) : ℕ :=
  (Finset.univ.filter (fun q : ZMod p × ZMod p =>
    q.2 ^ 2 + x.1 * q.1 * q.2 + x.2.2.1 * q.2 =
      q.1 ^ 3 + x.2.1 * q.1 ^ 2 + x.2.2.2.1 * q.1 + x.2.2.2.2)).card + 1

/-- The number of nonsingular coefficient tuples with exactly `j` points. -/
def tupleFiberCount (p : ℕ) [NeZero p] (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : CoeffTuple p =>
    TupleNonsing x ∧ tuplePointCount p x = j)).card

noncomputable instance instDecidableEquation (p : ℕ) (W : WeierstrassCurve (ZMod p))
    (x y : ZMod p) : Decidable (W.toAffine.Equation x y) := by
  unfold WeierstrassCurve.Affine.Equation
  infer_instance

lemma tuplePointCount_eq_curvePointCount (p : ℕ) [Fact p.Prime] [NeZero p]
    (x : CoeffTuple p) (h : TupleNonsing x) :
    tuplePointCount p x = curvePointCount p ⟨tupleCurve x, h⟩ := by
  unfold tuplePointCount curvePointCount
  have hfilter : (Finset.univ.filter (fun q : ZMod p × ZMod p =>
      q.2 ^ 2 + x.1 * q.1 * q.2 + x.2.2.1 * q.2 =
        q.1 ^ 3 + x.2.1 * q.1 ^ 2 + x.2.2.2.1 * q.1 + x.2.2.2.2)) =
      (Finset.univ.filter (fun q : ZMod p × ZMod p =>
        (tupleCurve x).toAffine.Equation q.1 q.2)) := by
    apply Finset.filter_congr
    intro q _
    rw [WeierstrassCurve.Affine.equation_iff]
    rfl
  rw [hfilter]

/-- The coefficient equivalence between Weierstrass curves and tuples. -/
def coeffEquiv (p : ℕ) : WeierstrassCurve (ZMod p) ≃ CoeffTuple p where
  toFun W := (W.a₁, W.a₂, W.a₃, W.a₄, W.a₆)
  invFun x := tupleCurve x
  left_inv W := by cases W; rfl
  right_inv x := by rcases x with ⟨a₁, a₂, a₃, a₄, a₆⟩; rfl

@[simp] lemma coeffEquiv_apply {p : ℕ} (W : WeierstrassCurve (ZMod p)) :
    coeffEquiv p W = (W.a₁, W.a₂, W.a₃, W.a₄, W.a₆) := rfl

@[simp] lemma tupleCurve_coeffEquiv {p : ℕ} (W : WeierstrassCurve (ZMod p)) :
    tupleCurve (coeffEquiv p W) = W := by cases W; rfl

@[simp] lemma tupleCurve_eta {p : ℕ} (W : WeierstrassCurve (ZMod p)) :
    tupleCurve (W.a₁, W.a₂, W.a₃, W.a₄, W.a₆) = W := by cases W; rfl

lemma tuplePointCount_coeffEquiv (p : ℕ) [Fact p.Prime] (W : CurveModel p) :
    tuplePointCount p (coeffEquiv p W.1) = curvePointCount p W := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let x := coeffEquiv p W.1
  have hx : TupleNonsing x := by
    simpa [x, TupleNonsing, CurveNonsingular] using W.2
  rw [tuplePointCount_eq_curvePointCount p x hx]
  rfl

/-- Curve models are coefficient tuples with nonvanishing discriminant. -/
def curveModelEquiv (p : ℕ) [Fact p.Prime] [NeZero p] :
    CurveModel p ≃ {x : CoeffTuple p // TupleNonsing x} where
  toFun W := ⟨coeffEquiv p W.1, by
    have h := W.2
    simpa [TupleNonsing, CurveNonsingular] using h⟩
  invFun x := ⟨tupleCurve x.1, x.2⟩
  left_inv W := by
    apply Subtype.ext
    simp [coeffEquiv, tupleCurve]
  right_inv x := by
    apply Subtype.ext
    rcases x with ⟨x, hx⟩
    simp [coeffEquiv, tupleCurve]

/-- `modelFiberCount` is the same count on coefficient tuples. -/
theorem modelFiberCount_eq_tupleFiberCount (p : ℕ) [Fact p.Prime] (j : ℕ) :
    modelFiberCount p j = tupleFiberCount p j := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [modelFiberCount, tupleFiberCount]
  rw [← Fintype.card_subtype (fun W : CurveModel p => curvePointCount p W = j)]
  rw [← Fintype.card_subtype
    (fun x : CoeffTuple p => TupleNonsing x ∧ tuplePointCount p x = j)]
  apply Fintype.card_congr
  refine
    { toFun := fun W => ⟨coeffEquiv p W.1.1, ?_⟩
      invFun := fun x => ⟨⟨tupleCurve x.1, x.2.1⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact ⟨by simpa [TupleNonsing, CurveNonsingular] using W.1.2,
      by rw [tuplePointCount_coeffEquiv p W.1]; exact W.2⟩
  · rw [← tuplePointCount_eq_curvePointCount p x.1 x.2.1]
    exact x.2.2
  · intro W
    apply Subtype.ext
    apply Subtype.ext
    simp [coeffEquiv, tupleCurve]
  · intro x
    apply Subtype.ext
    rcases x with ⟨x, hx⟩
    simp [coeffEquiv, tupleCurve]

/-- Variable changes are units times three field elements. -/
def variableChangeEquiv (p : ℕ) [NeZero p] :
    WeierstrassCurve.VariableChange (ZMod p) ≃
      (ZMod p)ˣ × ZMod p × ZMod p × ZMod p where
  toFun C := (C.u, C.r, C.s, C.t)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv C := by cases C; rfl
  right_inv x := by rcases x with ⟨u, r, s, t⟩; rfl

/-- The number of admissible variable changes is `(p-1)p³`. -/
theorem card_variableChange (p : ℕ) [Fact p.Prime] :
    Fintype.card (WeierstrassCurve.VariableChange (ZMod p)) = (p - 1) * p ^ 3 := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Fintype.card_congr (variableChangeEquiv p)]
  simp only [Fintype.card_prod, Fintype.card_units, ZMod.card]
  ring

/-- The classical weighted count, in terms of the explicit coefficient count. -/
theorem weightedCurveCount_eq_tupleFiberCount_div (p : ℕ) [Fact p.Prime] (j : ℕ) :
    weightedCurveCount p j =
      (tupleFiberCount p j : ℝ) / ((p - 1) * p ^ 3 : ℝ) := by
  have hden : (((p - 1) * p ^ 3 : ℕ) : ℝ) = ((p : ℝ) - 1) * (p : ℝ) ^ 3 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (Fact.out : p.Prime).one_le]
    norm_num
  rw [weightedCurveCount_eq_fiberSum, weightedFiberSum_eq_modelFiberCount_div,
    modelFiberCount_eq_tupleFiberCount, card_variableChange, hden]

/-! ## 2. Concrete Hurwitz class numbers -/

/-- The reduction predicate for a positive definite binary quadratic form. -/
def isReducedForm (a b c : ℤ) : Bool :=
  decide (0 < a ∧ a ≤ c ∧ (b.natAbs : ℤ) ≤ a ∧
    ((b.natAbs = a.natAbs ∨ a = c) → 0 ≤ b))

/-- The number of reduced primitive positive definite binary quadratic forms of
discriminant `-D`.  For `D ≡ 1, 2 (mod 4)` there are none.  The candidates are
enumerated by natural-number ranges and then cast to `ℤ`, so the definition is
computable and can be evaluated by `decide`. -/
def classNumber (D : ℕ) : ℕ :=
  if D % 4 == 1 || D % 4 == 2 then 0 else
    (((Finset.range D).product (Finset.range (2 * D + 1))).filter
      (fun ij : ℕ × ℕ =>
        let a : ℤ := (ij.1 : ℤ) + 1
        let b : ℤ := (ij.2 : ℤ) - (D : ℤ)
        let num := b ^ 2 + (D : ℤ)
        let den := 4 * a
        decide (den ∣ num) &&
          let c := num / den
          isReducedForm a b c &&
            decide (Int.gcd (Int.gcd a b) c = 1) &&
              decide (b ^ 2 - 4 * a * c = -(D : ℤ)))).card

/-- The unit weight of the order of discriminant `-D`. -/
def unitWeight (D : ℕ) : ℕ :=
  if D = 3 then 6 else if D = 4 then 4 else 2

/-- The Hurwitz class number `H(D)`, as a rational number. -/
def hurwitzClassNumber (D : ℕ) : ℚ :=
  ∑ d ∈ (Finset.range (D + 1)).filter (fun d => d ≠ 0 ∧ d * d ∣ D),
    (classNumber (D / (d * d)) : ℚ) / (unitWeight (D / (d * d)) : ℚ)

/-- The Hurwitz class number as a real-valued function of an integer
discriminant.  Only positive arguments occur in the Waterhouse identity. -/
def hurwitzH (D : ℤ) : ℝ :=
  if 0 < D then (hurwitzClassNumber D.toNat : ℝ) else 0

lemma hurwitzH_of_pos {D : ℤ} (h : 0 < D) :
    hurwitzH D = (hurwitzClassNumber D.toNat : ℝ) := by
  simp [hurwitzH, h]

/-! ### Evaluated class numbers and Hurwitz numbers -/

lemma classNumber_three : classNumber 3 = 1 := by decide
lemma classNumber_four : classNumber 4 = 1 := by decide
lemma classNumber_seven : classNumber 7 = 1 := by decide
lemma classNumber_eight : classNumber 8 = 1 := by decide
lemma classNumber_eleven : classNumber 11 = 1 := by decide
lemma classNumber_twelve : classNumber 12 = 1 := by decide
lemma classNumber_sixteen : classNumber 16 = 1 := by decide
lemma classNumber_nineteen : classNumber 19 = 1 := by decide
lemma classNumber_twenty : classNumber 20 = 2 := by decide
lemma classNumber_twentyfour : classNumber 24 = 2 := by decide
lemma classNumber_twentyseven : classNumber 27 = 1 := by decide
lemma classNumber_twentyeight : classNumber 28 = 1 := by decide

lemma classNumber_six : classNumber 6 = 0 := by decide
lemma classNumber_two : classNumber 2 = 0 := by decide
lemma classNumber_one : classNumber 1 = 0 := by decide
lemma classNumber_five : classNumber 5 = 0 := by decide

lemma unitWeight_one : unitWeight 1 = 2 := by norm_num [unitWeight]
lemma unitWeight_two : unitWeight 2 = 2 := by norm_num [unitWeight]
lemma unitWeight_three : unitWeight 3 = 6 := rfl
lemma unitWeight_four : unitWeight 4 = 4 := rfl
lemma unitWeight_five : unitWeight 5 = 2 := by norm_num [unitWeight]
lemma unitWeight_six : unitWeight 6 = 2 := by norm_num [unitWeight]
lemma unitWeight_seven : unitWeight 7 = 2 := by norm_num [unitWeight]
lemma unitWeight_eight : unitWeight 8 = 2 := by norm_num [unitWeight]
lemma unitWeight_eleven : unitWeight 11 = 2 := by norm_num [unitWeight]
lemma unitWeight_twelve : unitWeight 12 = 2 := by norm_num [unitWeight]
lemma unitWeight_sixteen : unitWeight 16 = 2 := by norm_num [unitWeight]
lemma unitWeight_nineteen : unitWeight 19 = 2 := by norm_num [unitWeight]
lemma unitWeight_twenty : unitWeight 20 = 2 := by norm_num [unitWeight]
lemma unitWeight_twentyfour : unitWeight 24 = 2 := by norm_num [unitWeight]
lemma unitWeight_twentyseven : unitWeight 27 = 2 := by norm_num [unitWeight]
lemma unitWeight_twentyeight : unitWeight 28 = 2 := by norm_num [unitWeight]

/-- The divisor set `{d : d² | D}` in the form used by `hurwitzClassNumber`. -/
lemma hurwitz_divisors_three :
    (Finset.range (3 + 1)).filter (fun d => d ≠ 0 ∧ d * d ∣ 3) = {1} := by
  decide

lemma hurwitz_divisors_four :
    (Finset.range (4 + 1)).filter (fun d => d ≠ 0 ∧ d * d ∣ 4) = {1, 2} := by
  decide

lemma hurwitz_divisors_eight :
    (Finset.range (8 + 1)).filter (fun d => d ≠ 0 ∧ d * d ∣ 8) = {1, 2} := by
  decide

lemma hurwitz_divisors_eleven :
    (Finset.range (11 + 1)).filter (fun d => d ≠ 0 ∧ d * d ∣ 11) = {1} := by
  decide

lemma hurwitz_divisors_twelve :
    (Finset.range (12 + 1)).filter (fun d => d ≠ 0 ∧ d * d ∣ 12) = {1, 2} := by
  decide

lemma hurwitz_divisors_sixteen :
    (Finset.range (16 + 1)).filter (fun d => d ≠ 0 ∧ d * d ∣ 16) = {1, 2, 4} := by
  decide

lemma hurwitz_divisors_nineteen :
    (Finset.range (19 + 1)).filter (fun d => d ≠ 0 ∧ d * d ∣ 19) = {1} := by
  decide

lemma hurwitz_divisors_twenty :
    (Finset.range (20 + 1)).filter (fun d => d ≠ 0 ∧ d * d ∣ 20) = {1, 2} := by
  decide

lemma hurwitz_divisors_twentyfour :
    (Finset.range (24 + 1)).filter (fun d => d ≠ 0 ∧ d * d ∣ 24) = {1, 2} := by
  decide

lemma hurwitz_divisors_twentyseven :
    (Finset.range (27 + 1)).filter (fun d => d ≠ 0 ∧ d * d ∣ 27) = {1, 3} := by
  decide

lemma hurwitz_divisors_twentyeight :
    (Finset.range (28 + 1)).filter (fun d => d ≠ 0 ∧ d * d ∣ 28) = {1, 2} := by
  decide

lemma hurwitzClassNumber_three : hurwitzClassNumber 3 = (1 / 6 : ℚ) := by
  rw [hurwitzClassNumber, hurwitz_divisors_three]
  norm_num [classNumber_three, unitWeight_three]

lemma hurwitzClassNumber_four : hurwitzClassNumber 4 = (1 / 4 : ℚ) := by
  rw [hurwitzClassNumber, hurwitz_divisors_four]
  norm_num [classNumber_four, classNumber_one, unitWeight_four, unitWeight_one]

lemma hurwitzClassNumber_eight : hurwitzClassNumber 8 = (1 / 2 : ℚ) := by
  rw [hurwitzClassNumber, hurwitz_divisors_eight]
  norm_num [classNumber_eight, classNumber_two, unitWeight_eight, unitWeight_two]

lemma hurwitzClassNumber_eleven : hurwitzClassNumber 11 = (1 / 2 : ℚ) := by
  rw [hurwitzClassNumber, hurwitz_divisors_eleven]
  norm_num [classNumber_eleven, unitWeight_eleven]

lemma hurwitzClassNumber_twelve : hurwitzClassNumber 12 = (2 / 3 : ℚ) := by
  rw [hurwitzClassNumber, hurwitz_divisors_twelve]
  norm_num [classNumber_twelve, classNumber_three, unitWeight_three,
    unitWeight_twelve]

lemma hurwitzClassNumber_sixteen : hurwitzClassNumber 16 = (3 / 4 : ℚ) := by
  rw [hurwitzClassNumber, hurwitz_divisors_sixteen]
  norm_num [classNumber_sixteen, classNumber_four, classNumber_one, unitWeight_four,
    unitWeight_sixteen, unitWeight_one]

lemma hurwitzClassNumber_nineteen : hurwitzClassNumber 19 = (1 / 2 : ℚ) := by
  rw [hurwitzClassNumber, hurwitz_divisors_nineteen]
  norm_num [classNumber_nineteen, unitWeight_nineteen]

lemma hurwitzClassNumber_twenty : hurwitzClassNumber 20 = (1 : ℚ) := by
  rw [hurwitzClassNumber, hurwitz_divisors_twenty]
  norm_num [classNumber_twenty, classNumber_five, unitWeight_twenty, unitWeight_five]

lemma hurwitzClassNumber_twentyfour : hurwitzClassNumber 24 = (1 : ℚ) := by
  rw [hurwitzClassNumber, hurwitz_divisors_twentyfour]
  norm_num [classNumber_twentyfour, classNumber_six, unitWeight_twentyfour,
    unitWeight_six]

lemma hurwitzClassNumber_twentyseven : hurwitzClassNumber 27 = (2 / 3 : ℚ) := by
  rw [hurwitzClassNumber, hurwitz_divisors_twentyseven]
  norm_num [classNumber_twentyseven, classNumber_three, unitWeight_three,
    unitWeight_twentyseven]

lemma hurwitzClassNumber_twentyeight : hurwitzClassNumber 28 = (1 : ℚ) := by
  rw [hurwitzClassNumber, hurwitz_divisors_twentyeight]
  norm_num [classNumber_twentyeight, classNumber_seven, unitWeight_twentyeight,
    unitWeight_seven]

lemma hurwitzH_three : hurwitzH 3 = (1 / 6 : ℝ) := by
  rw [hurwitzH_of_pos (D := 3) (by norm_num)]
  change ((hurwitzClassNumber 3 : ℚ) : ℝ) = (1 / 6 : ℝ)
  norm_num [hurwitzClassNumber_three]

lemma hurwitzH_eight : hurwitzH 8 = (1 / 2 : ℝ) := by
  rw [hurwitzH_of_pos (D := 8) (by norm_num)]
  change ((hurwitzClassNumber 8 : ℚ) : ℝ) = (1 / 2 : ℝ)
  norm_num [hurwitzClassNumber_eight]

lemma hurwitzH_eleven : hurwitzH 11 = (1 / 2 : ℝ) := by
  rw [hurwitzH_of_pos (D := 11) (by norm_num)]
  change ((hurwitzClassNumber 11 : ℚ) : ℝ) = (1 / 2 : ℝ)
  norm_num [hurwitzClassNumber_eleven]

lemma hurwitzH_twelve : hurwitzH 12 = (2 / 3 : ℝ) := by
  rw [hurwitzH_of_pos (D := 12) (by norm_num)]
  change ((hurwitzClassNumber 12 : ℚ) : ℝ) = (2 / 3 : ℝ)
  norm_num [hurwitzClassNumber_twelve]

/-! ## 3. The `p = 3` fiber counts -/

set_option maxRecDepth 1000000 in
lemma tupleFiberCount_three_one : tupleFiberCount 3 1 = 9 := by decide

set_option maxRecDepth 1000000 in
lemma tupleFiberCount_three_two : tupleFiberCount 3 2 = 27 := by decide

set_option maxRecDepth 1000000 in
lemma tupleFiberCount_three_three : tupleFiberCount 3 3 = 27 := by decide

set_option maxRecDepth 1000000 in
lemma tupleFiberCount_three_four : tupleFiberCount 3 4 = 36 := by decide

set_option maxRecDepth 1000000 in
lemma tupleFiberCount_three_five : tupleFiberCount 3 5 = 27 := by decide

set_option maxRecDepth 1000000 in
lemma tupleFiberCount_three_six : tupleFiberCount 3 6 = 27 := by decide

set_option maxRecDepth 1000000 in
lemma tupleFiberCount_three_seven : tupleFiberCount 3 7 = 9 := by decide

/-- The weighted curve count at a point order `j` for `p = 3`. -/
lemma weightedCurveCount_three_one : weightedCurveCount 3 1 = (1 / 6 : ℝ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [weightedCurveCount_eq_tupleFiberCount_div, tupleFiberCount_three_one]
  norm_num

lemma weightedCurveCount_three_two : weightedCurveCount 3 2 = (1 / 2 : ℝ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [weightedCurveCount_eq_tupleFiberCount_div, tupleFiberCount_three_two]
  norm_num

lemma weightedCurveCount_three_three : weightedCurveCount 3 3 = (1 / 2 : ℝ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [weightedCurveCount_eq_tupleFiberCount_div, tupleFiberCount_three_three]
  norm_num

lemma weightedCurveCount_three_four : weightedCurveCount 3 4 = (2 / 3 : ℝ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [weightedCurveCount_eq_tupleFiberCount_div, tupleFiberCount_three_four]
  norm_num

lemma weightedCurveCount_three_five : weightedCurveCount 3 5 = (1 / 2 : ℝ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [weightedCurveCount_eq_tupleFiberCount_div, tupleFiberCount_three_five]
  norm_num

lemma weightedCurveCount_three_six : weightedCurveCount 3 6 = (1 / 2 : ℝ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [weightedCurveCount_eq_tupleFiberCount_div, tupleFiberCount_three_six]
  norm_num

lemma weightedCurveCount_three_seven : weightedCurveCount 3 7 = (1 / 6 : ℝ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [weightedCurveCount_eq_tupleFiberCount_div, tupleFiberCount_three_seven]
  norm_num

lemma weightedCurveCount_three_one_toNat :
    weightedCurveCount 3 (Int.toNat 1) = (1 / 6 : ℝ) := by
  change weightedCurveCount 3 1 = (1 / 6 : ℝ)
  exact weightedCurveCount_three_one
lemma weightedCurveCount_three_two_toNat :
    weightedCurveCount 3 (Int.toNat 2) = (1 / 2 : ℝ) := by
  change weightedCurveCount 3 2 = (1 / 2 : ℝ)
  exact weightedCurveCount_three_two
lemma weightedCurveCount_three_three_toNat :
    weightedCurveCount 3 (Int.toNat 3) = (1 / 2 : ℝ) := by
  change weightedCurveCount 3 3 = (1 / 2 : ℝ)
  exact weightedCurveCount_three_three
lemma weightedCurveCount_three_four_toNat :
    weightedCurveCount 3 (Int.toNat 4) = (2 / 3 : ℝ) := by
  change weightedCurveCount 3 4 = (2 / 3 : ℝ)
  exact weightedCurveCount_three_four
lemma weightedCurveCount_three_five_toNat :
    weightedCurveCount 3 (Int.toNat 5) = (1 / 2 : ℝ) := by
  change weightedCurveCount 3 5 = (1 / 2 : ℝ)
  exact weightedCurveCount_three_five
lemma weightedCurveCount_three_six_toNat :
    weightedCurveCount 3 (Int.toNat 6) = (1 / 2 : ℝ) := by
  change weightedCurveCount 3 6 = (1 / 2 : ℝ)
  exact weightedCurveCount_three_six
lemma weightedCurveCount_three_seven_toNat :
    weightedCurveCount 3 (Int.toNat 7) = (1 / 6 : ℝ) := by
  change weightedCurveCount 3 7 = (1 / 6 : ℝ)
  exact weightedCurveCount_three_seven

/-! ## 4. The weighted Deuring/Waterhouse identity at `p = 3` -/

/-- **The weighted Deuring/Waterhouse identity over `F₃`.**  For every integral
trace `t` with positive Frobenius discriminant `12 - t²`, the weighted number of
curves over `F₃` with `3 + 1 - t` points is the Hurwitz class number
`H(12 - t²)`. -/
theorem waterhouseWeighted_three :
    WaterhouseWeighted 3 (by norm_num) hurwitzH := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro t ht
  have ht2 : t ^ 2 < 12 := by
    unfold traceDisc at ht
    norm_num at ht ⊢
    linarith
  have hlow : -3 ≤ t := by
    by_contra h
    have hle : t ≤ -4 := by omega
    nlinarith [sq_nonneg (t + 4)]
  have hhigh : t ≤ 3 := by
    by_contra h
    have hge : 4 ≤ t := by omega
    nlinarith [sq_nonneg (t - 4)]
  interval_cases t <;>
    norm_num [traceDisc, traceOrder] <;>
    norm_num [hurwitzH_three, hurwitzH_eight, hurwitzH_eleven, hurwitzH_twelve,
      weightedCurveCount_three_one, weightedCurveCount_three_two,
      weightedCurveCount_three_three, weightedCurveCount_three_four,
      weightedCurveCount_three_five, weightedCurveCount_three_six,
      weightedCurveCount_three_seven, weightedCurveCount_three_one_toNat,
      weightedCurveCount_three_two_toNat, weightedCurveCount_three_three_toNat,
      weightedCurveCount_three_four_toNat, weightedCurveCount_three_five_toNat,
      weightedCurveCount_three_six_toNat, weightedCurveCount_three_seven_toNat]

/-! ## Axiom audit -/

#print axioms modelFiberCount_eq_tupleFiberCount
#print axioms card_variableChange
#print axioms weightedCurveCount_eq_tupleFiberCount_div
#print axioms waterhouseWeighted_three

end Cogentic.RandomizedL27WaterhouseSmall
