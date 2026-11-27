import Cogentic.RandomizedL27TraceClass
import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# L27 Waterhouse: the finite curve count behind Deuring/Waterhouse

`Cogentic.RandomizedL27TraceClass` isolates the Deuring input as the one-sided
curve-count statement

`DeuringTraceCountLower p orderCount hurwitz`

on an abstract order count, and records that the exact form
`DeuringWaterhouseExactOrder` implies it.  This file goes one level down: it
builds the finite curve model over `F_p` and states the classical
Deuring/Waterhouse trace formula on it.

## The finite curve model

For a prime `p`, the model is the finite type of nonsingular Weierstrass
equations over `ZMod p`,

`W : Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆`,

modulo the admissible variable changes `(X,Y) ↦ (u²X + r, u³Y + u²sX + t)`.
The latter form the group `WeierstrassCurve.VariableChange (ZMod p)`, which acts
on equations.  The isomorphism classes are the orbits of this action, and the
stabilizer of `W` is its automorphism group.

Two counts are attached to the class of a curve:

* `rawCurveCount p j` — the number of isomorphism classes of curves whose
  projective point count is `j` (the affine solutions of the Weierstrass
  equation plus the point at infinity).  This is a natural number;
* `weightedCurveCount p j` — the same class count weighted by
  `1 / #Aut(E)`, the count used in the classical Deuring/Waterhouse theorem.

Both are finite cardinalities/sums, not hypotheses, and neither is set to
zero.

## The classical input

The classical theorem (Deuring, Waterhouse; see also Schoof's survey) is the
*weighted* identity

`∑_{E/F_p, #E(F_p) = p+1-t} 1/#Aut(E) = H(4p - t²)`,

which is `WaterhouseWeighted p hp hurwitz` below.  Its right-hand side is the
Hurwitz class number `H(-D)` of the Frobenius discriminant
`D = 4p - t² = traceDisc p t`; the function `hurwitz : ℤ → ℝ` is the same
abstract Hurwitz class number used throughout the L27 development.

Because every automorphism group has order at least one, the weighted count is
pointwise at most the raw class count.  Hence the classical weighted identity
implies the one-sided raw bound

`H(4p - t²) ≤ rawCurveCount p (p + 1 - t)`,

which is the smallest explicit curve-count input consumed by
`DeuringTraceCountLower`.  We prove that implication, and then reduce the
abstract `orderCount` of `L27_1Inputs` to the concrete model by the explicit
domination hypothesis `rawCurveCount ≤ orderCount`.

## Relation to `DeuringWaterhouseExactOrder`

The raw exact identity `rawCurveCount = H` is *not* the classical theorem: the
classical theorem counts with the automorphism weights.  We prove the precise
statement

`DeuringWaterhouseExactOrder p rawCurveOrderCount hurwitz ↔
   (weighted identity holds) ∧ (weighted count = raw count on every trace
   fiber)`.

Thus the exact order-level identity is isolated completely: it is the classical
weighted formula together with the extra assertion that the weights are
trivial on the relevant fiber.  The classical formula alone yields the
one-sided lower bound, which is exactly what the L27 reduction needs.

The extra assertion is not a consequence of the classical formula.  In odd
characteristic every elliptic curve has the hyperelliptic involution
`(X, Y) ↦ (X, -Y - a₁X - a₃)`, so every nonempty trace fiber has weighted count
strictly below its raw count (`weightedCurveCount_lt_rawCurveCount_of_nonempty`).
Hence the raw order-level exact identity fails on every nonempty
odd-characteristic fiber, while the weighted identity remains the correct
classical statement.

## Integration

`L27WaterhouseInputs` is the analogue of `L27TraceClassInputs` with the
Deuring field replaced by the prime hypothesis, the concrete weighted
Waterhouse identity, and the model-domination hypothesis.  It constructs
`L27TraceClassInputs` and re-exports the downstream L27.1 conclusions.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no class number,
curve count, or probability is set to zero.
-/

set_option linter.style.haveILetI false

namespace Cogentic.RandomizedL27Waterhouse

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27TraceClass
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The finite Weierstrass model over `ZMod p` -/

variable (p : ℕ) [Fact p.Prime]

/-- The five coefficients of a Weierstrass equation form a finite type. -/
instance instFintypeWeierstrassCurve : Fintype (WeierstrassCurve (ZMod p)) :=
  Fintype.ofInjective
    (fun W : WeierstrassCurve (ZMod p) => (W.a₁, W.a₂, W.a₃, W.a₄, W.a₆))
    (by
      intro W W' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h6⟩ := h
      ext <;> assumption)

/-- Coefficient-wise equality of Weierstrass equations. -/
instance instDecidableEqWeierstrassCurve : DecidableEq (WeierstrassCurve (ZMod p)) :=
  (Function.Injective.decidableEq
    (f := fun W : WeierstrassCurve (ZMod p) => (W.a₁, W.a₂, W.a₃, W.a₄, W.a₆))
    (by
      intro W W' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h6⟩ := h
      ext <;> assumption))

/-- A variable change is determined by `(u, r, s, t)`, hence finite. -/
instance instFintypeVariableChange :
    Fintype (WeierstrassCurve.VariableChange (ZMod p)) :=
  Fintype.ofInjective
    (fun C : WeierstrassCurve.VariableChange (ZMod p) => (C.u, C.r, C.s, C.t))
    (by
      intro C C' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      ext <;> simp_all)

/-- Coefficient-wise equality of variable changes. -/
instance instDecidableEqVariableChange :
    DecidableEq (WeierstrassCurve.VariableChange (ZMod p)) :=
  (Function.Injective.decidableEq
    (f := fun C : WeierstrassCurve.VariableChange (ZMod p) => (C.u, C.r, C.s, C.t))
    (by
      intro C C' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      ext <;> simp_all))

/-- Nonsingularity of a Weierstrass equation over the field `ZMod p`: its
discriminant does not vanish. -/
def CurveNonsingular (W : WeierstrassCurve (ZMod p)) : Prop := W.Δ ≠ 0

instance (W : WeierstrassCurve (ZMod p)) : Decidable (CurveNonsingular p W) :=
  inferInstanceAs (Decidable (W.Δ ≠ 0))

/-- Over a field, nonvanishing of the discriminant is exactly Mathlib's
`IsElliptic` condition. -/
theorem curveNonsingular_iff_isElliptic (W : WeierstrassCurve (ZMod p)) :
    CurveNonsingular p W ↔ W.IsElliptic := by
  rw [CurveNonsingular, WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]

/-- The finite type of nonsingular Weierstrass equations over `F_p`, i.e. the
elliptic curves presented by Weierstrass equations in the chosen coordinates. -/
abbrev CurveModel : Type := { W : WeierstrassCurve (ZMod p) // CurveNonsingular p W }

instance instFintypeCurveModel : Fintype (CurveModel p) := by
  unfold CurveModel
  infer_instance

instance instDecidableEqCurveModel : DecidableEq (CurveModel p) := by
  unfold CurveModel
  infer_instance

/-- Variable changes preserve nonsingularity. -/
instance instSMulCurveModel :
    SMul (WeierstrassCurve.VariableChange (ZMod p)) (CurveModel p) where
  smul C W := ⟨C • W.1, by
    have h := W.2
    rw [CurveNonsingular, WeierstrassCurve.variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero 12 (Units.ne_zero _)) h⟩

/-- The admissible variable changes act on nonsingular Weierstrass equations. -/
instance instMulActionCurveModel :
    MulAction (WeierstrassCurve.VariableChange (ZMod p)) (CurveModel p) where
  one_smul W := by
    apply Subtype.ext
    exact one_smul _ W.1
  mul_smul C C' W := by
    apply Subtype.ext
    exact mul_smul C C' W.1

/-- The orbit relation is decidable, since the group of variable changes is
finite and curve equality is decidable. -/
instance instDecidableRelOrbit :
    DecidableRel
      (MulAction.orbitRel (WeierstrassCurve.VariableChange (ZMod p)) (CurveModel p)) := by
  intro W W'
  show Decidable
    (W ∈ MulAction.orbit (WeierstrassCurve.VariableChange (ZMod p)) W')
  rw [MulAction.mem_orbit_iff]
  infer_instance

/-- The isomorphism classes of elliptic curves over `F_p`, as orbits of the
finite Weierstrass model under admissible variable changes. -/
abbrev CurveClass : Type :=
  Quotient
    (MulAction.orbitRel (WeierstrassCurve.VariableChange (ZMod p)) (CurveModel p))

instance instFintypeCurveClass : Fintype (CurveClass p) := by
  unfold CurveClass
  infer_instance

/-- The automorphism-group order of an isomorphism class, computed at the
chosen representative.  Stabilizer orders are invariant under the action, so
this is the order of `Aut(E)` of the class. -/
def classAutOrder (E : CurveClass p) : ℕ :=
  Nat.card
    (MulAction.stabilizer (WeierstrassCurve.VariableChange (ZMod p)) E.out)

/-- The automorphism order of the class of `W` is the stabilizer order of `W`.
This records that `classAutOrder` is independent of the chosen representative. -/
theorem classAutOrder_mk (W : CurveModel p) :
    classAutOrder p (Quotient.mk
      (MulAction.orbitRel (WeierstrassCurve.VariableChange (ZMod p)) (CurveModel p))
      W) =
      Nat.card
        (MulAction.stabilizer (WeierstrassCurve.VariableChange (ZMod p)) W) := by
  unfold classAutOrder
  have hout : Quotient.mk
      (MulAction.orbitRel (WeierstrassCurve.VariableChange (ZMod p)) (CurveModel p))
        (Quotient.mk
          (MulAction.orbitRel (WeierstrassCurve.VariableChange (ZMod p)) (CurveModel p))
          W).out =
      Quotient.mk
        (MulAction.orbitRel (WeierstrassCurve.VariableChange (ZMod p)) (CurveModel p)) W :=
    Quotient.out_eq _
  have hrel : MulAction.orbitRel (WeierstrassCurve.VariableChange (ZMod p))
      (CurveModel p) W
      (Quotient.mk
        (MulAction.orbitRel (WeierstrassCurve.VariableChange (ZMod p)) (CurveModel p))
        W).out := by
    apply Quotient.exact
    rw [hout]
  exact (Nat.card_congr
    (MulAction.stabilizerEquivStabilizerOfOrbitRel hrel).toEquiv).symm

/-! ## 2. The point count and the two curve counts -/

/-- Every affine point of a Weierstrass equation is decidable over `ZMod p`. -/
instance (W : CurveModel p) (x y : ZMod p) :
    Decidable (W.1.toAffine.Equation x y) := by
  unfold WeierstrassCurve.Affine.Equation
  infer_instance

/-- **The number of points of the elliptic curve `E` over `F_p`**: the affine
solutions of its Weierstrass equation plus the point at infinity.  For a
nonsingular Weierstrass equation this is exactly `#E(F_p)`. -/
def curvePointCount (W : CurveModel p) : ℕ :=
  (Finset.univ.filter
    (fun q : ZMod p × ZMod p => W.1.toAffine.Equation q.1 q.2)).card + 1

/-- An isomorphism class has a given number of points when some (equivalently,
every) representative does.  The existential form is invariant by definition
and avoids choosing coordinates on the class. -/
def classHasPointCount (E : CurveClass p) (j : ℕ) : Prop :=
  ∃ W : CurveModel p,
    Quotient.mk
      (MulAction.orbitRel (WeierstrassCurve.VariableChange (ZMod p)) (CurveModel p))
      W = E ∧ curvePointCount p W = j

instance (E : CurveClass p) (j : ℕ) : Decidable (classHasPointCount p E j) := by
  unfold classHasPointCount
  infer_instance


/-- **The raw finite curve count.**  The number of isomorphism classes of
nonsingular elliptic curves over `F_p` with exactly `j` points. -/
def rawCurveCount (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun E : CurveClass p => classHasPointCount p E j)).card

/-- **The weighted finite curve count.**  The number of isomorphism classes of
curves with `j` points, each weighted by the reciprocal automorphism order
`1 / #Aut(E)`.  This is the count appearing in the classical Deuring/Waterhouse
trace formula. -/
def weightedCurveCount (j : ℕ) : ℝ :=
  ∑ E : CurveClass p,
    if classHasPointCount p E j then 1 / (classAutOrder p E : ℝ) else 0

/-- An automorphism group contains the identity, so its order is at least one. -/
theorem classAutOrder_ge_one (E : CurveClass p) : 1 ≤ classAutOrder p E := by
  unfold classAutOrder
  have : Nonempty
      (MulAction.stabilizer (WeierstrassCurve.VariableChange (ZMod p)) E.out) :=
    ⟨1⟩
  exact Nat.card_pos

/-- Every class weight is at most one. -/
theorem classWeight_le_one (E : CurveClass p) :
    1 / (classAutOrder p E : ℝ) ≤ 1 := by
  have h1 : (0 : ℝ) < 1 := by norm_num
  have hle : (1 : ℝ) ≤ (classAutOrder p E : ℝ) := by
    exact_mod_cast classAutOrder_ge_one p E
  calc
    1 / (classAutOrder p E : ℝ) ≤ 1 / (1 : ℝ) :=
      one_div_le_one_div_of_le h1 hle
    _ = 1 := by norm_num

/-! ### The hyperelliptic involution

The negation map of the group law is an automorphism of every elliptic curve.
In the Weierstrass model it is the variable change
`(X, Y) ↦ (X, -Y - a₁X - a₃)`, whose parameters are
`(u, r, s, t) = (-1, 0, -a₁, -a₃)`.  It is nontrivial away from characteristic
`2`.  This is why the *weighted* order identity and the *raw* order identity
differ on every nonempty trace fiber. -/

/-- The hyperelliptic involution of a Weierstrass model, as an admissible
variable change. -/
def negAut (W : CurveModel p) : WeierstrassCurve.VariableChange (ZMod p) :=
  ⟨(-1 : (ZMod p)ˣ), 0, -W.1.a₁, -W.1.a₃⟩

/-- The hyperelliptic involution preserves the Weierstrass equation. -/
lemma negAut_smul_self (W : CurveModel p) : negAut p W • W.1 = W.1 := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;> simp [negAut] <;> ring

/-- In odd characteristic the hyperelliptic involution is not the identity. -/
lemma negAut_ne_one (hp2 : p ≠ 2) (W : CurveModel p) : negAut p W ≠ 1 := by
  intro h
  have hu : (-1 : (ZMod p)ˣ) = 1 := by
    have h' := congrArg
      (fun C : WeierstrassCurve.VariableChange (ZMod p) => C.u) h
    simpa [negAut, WeierstrassCurve.VariableChange.one_def] using h'
  have hval : (-1 : ZMod p) = 1 := by
    simpa using congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hu
  have h2 : (2 : ZMod p) = 0 := by
    linear_combination -hval
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
  have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hp_ge : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

/-- The hyperelliptic involution lies in the automorphism group. -/
lemma negAut_mem (W : CurveModel p) :
    negAut p W ∈
      MulAction.stabilizer (WeierstrassCurve.VariableChange (ZMod p)) W := by
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  exact negAut_smul_self p W

/-- Away from characteristic `2`, every elliptic curve has automorphism group of
order at least two. -/
theorem two_le_classAutOrder (hp2 : p ≠ 2) (E : CurveClass p) :
    2 ≤ classAutOrder p E := by
  unfold classAutOrder
  have hne : (⟨negAut p E.out, negAut_mem p E.out⟩ :
      MulAction.stabilizer (WeierstrassCurve.VariableChange (ZMod p)) E.out) ≠ 1 := by
    intro h
    apply negAut_ne_one p hp2 E.out
    exact congrArg Subtype.val h
  have : Nontrivial
      (MulAction.stabilizer (WeierstrassCurve.VariableChange (ZMod p)) E.out) :=
    ⟨⟨1, ⟨negAut p E.out, negAut_mem p E.out⟩, hne.symm⟩⟩
  rw [Nat.card_eq_fintype_card]
  have := Fintype.one_lt_card
    (α := MulAction.stabilizer (WeierstrassCurve.VariableChange (ZMod p)) E.out)
  omega

/-- The automorphism order is never one in odd characteristic. -/
theorem classAutOrder_ne_one (hp2 : p ≠ 2) (E : CurveClass p) :
    classAutOrder p E ≠ 1 := by
  have h := two_le_classAutOrder p hp2 E
  omega

/-- The raw count as a real sum of indicators. -/
theorem rawCurveCount_cast_eq_sum (j : ℕ) :
    (rawCurveCount p j : ℝ) =
      ∑ E : CurveClass p,
        if classHasPointCount p E j then (1 : ℝ) else 0 := by
  unfold rawCurveCount
  rw [Finset.card_filter]
  push_cast
  simp

/-- **The weighted count is at most the raw class count.**  Termwise, every
reciprocal automorphism order is at most one.  This is the only comparison
needed to pass from the classical weighted formula to the one-sided raw bound. -/
theorem weightedCurveCount_le_rawCurveCount (j : ℕ) :
    weightedCurveCount p j ≤ (rawCurveCount p j : ℝ) := by
  rw [rawCurveCount_cast_eq_sum]
  unfold weightedCurveCount
  apply Finset.sum_le_sum
  intro E _
  by_cases h : classHasPointCount p E j
  · simp only [h, if_true]
    exact classWeight_le_one p E
  · simp [h]

/-- A nontrivial automorphism makes the fiber sum strictly smaller than the raw
class count. -/
theorem weightedCurveCount_lt_rawCurveCount_of_nontrivial (j : ℕ)
    (E₀ : CurveClass p) (hE₀ : classHasPointCount p E₀ j)
    (hAut : classAutOrder p E₀ ≠ 1) :
    weightedCurveCount p j < (rawCurveCount p j : ℝ) := by
  have hlt : 1 / (classAutOrder p E₀ : ℝ) < 1 := by
    have h2 : (2 : ℝ) ≤ (classAutOrder p E₀ : ℝ) := by
      have h2n : 2 ≤ classAutOrder p E₀ := by
        have h1 : 1 ≤ classAutOrder p E₀ := classAutOrder_ge_one p E₀
        omega
      exact_mod_cast h2n
    calc
      1 / (classAutOrder p E₀ : ℝ) ≤ 1 / (2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) h2
      _ < 1 := by norm_num
  rw [rawCurveCount_cast_eq_sum]
  unfold weightedCurveCount
  refine Finset.sum_lt_sum (fun E _ => ?_) ⟨E₀, Finset.mem_univ E₀, ?_⟩
  · by_cases hE : classHasPointCount p E j
    · simp only [hE, if_true]
      exact classWeight_le_one p E
    · simp [hE]
  · simpa [hE₀] using hlt

/-- If every class in the fiber has trivial automorphism group, the weighted
count is exactly the raw class count. -/
theorem weightedCurveCount_eq_rawCurveCount_of_autOrder_one (j : ℕ)
    (h : ∀ E : CurveClass p, classHasPointCount p E j → classAutOrder p E = 1) :
    weightedCurveCount p j = (rawCurveCount p j : ℝ) := by
  rw [rawCurveCount_cast_eq_sum]
  unfold weightedCurveCount
  apply Finset.sum_congr rfl
  intro E _
  by_cases hE : classHasPointCount p E j
  · simp only [hE, if_true]
    rw [h E hE]
    norm_num
  · simp [hE]

/-- The weighted and raw counts agree precisely when every class in the fiber
has trivial automorphism group.  This is the exact measure of the gap between
the classical weighted identity and the raw exact identity. -/
theorem weightedCurveCount_eq_rawCurveCount_iff (j : ℕ) :
    weightedCurveCount p j = (rawCurveCount p j : ℝ) ↔
      ∀ E : CurveClass p, classHasPointCount p E j → classAutOrder p E = 1 := by
  constructor
  · intro h E hE
    by_contra hne
    have hlt := weightedCurveCount_lt_rawCurveCount_of_nontrivial p j E hE hne
    linarith
  · exact weightedCurveCount_eq_rawCurveCount_of_autOrder_one p j

/-- On a nonempty fiber in odd characteristic, the weighted count is strictly
smaller than the raw class count. -/
theorem weightedCurveCount_lt_rawCurveCount_of_nonempty (hp2 : p ≠ 2) (j : ℕ)
    (h : ∃ E : CurveClass p, classHasPointCount p E j) :
    weightedCurveCount p j < (rawCurveCount p j : ℝ) := by
  obtain ⟨E, hE⟩ := h
  exact weightedCurveCount_lt_rawCurveCount_of_nontrivial p j E hE
    (classAutOrder_ne_one p hp2 E)

/-- On a nonempty fiber in odd characteristic, weighted and raw counts differ. -/
theorem weightedCurveCount_ne_rawCurveCount_of_nonempty (hp2 : p ≠ 2) (j : ℕ)
    (h : ∃ E : CurveClass p, classHasPointCount p E j) :
    weightedCurveCount p j ≠ (rawCurveCount p j : ℝ) :=
  ne_of_lt (weightedCurveCount_lt_rawCurveCount_of_nonempty p hp2 j h)

/-! ## 3. The classical Deuring/Waterhouse input -/

/-- On the positive-discriminant part of the Hasse window, `traceOrder` is the
honest group order `p + 1 - t`. -/
theorem traceOrder_eq_of_pos_traceDisc {p : ℕ} {t : ℤ}
    (h : 0 < traceDisc p t) :
    (traceOrder p t : ℤ) = (p : ℤ) + 1 - t := by
  unfold traceOrder
  have hnonneg : (0 : ℤ) ≤ (p : ℤ) + 1 - t := by
    have := traceOrder_arg_nonneg h
    omega
  rw [Int.toNat_of_nonneg hnonneg]

/-- **The classical Deuring/Waterhouse trace formula**, stated on the concrete
weighted isomorphism-class count of §2: for every trace `t` with positive
Frobenius discriminant `4p - t²`, the weighted number of curves of trace `t` is
the Hurwitz class number `H(4p - t²)`.

This is the classical theorem, recorded as the single explicit input of this
file.  It is *weighted*: the raw class count is generally larger. -/
def WaterhouseWeighted (p : ℕ) (hp : p.Prime) (hurwitz : ℤ → ℝ) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ t : ℤ, 0 < traceDisc p t →
    weightedCurveCount p (traceOrder p t) = hurwitz (traceDisc p t)

/-- Explicit-prime wrapper around the raw class count. -/
def rawCurveCountAt (p : ℕ) (hp : p.Prime) (j : ℕ) : ℕ :=
  letI : Fact p.Prime := ⟨hp⟩
  rawCurveCount p j

/-- Explicit-prime wrapper around the weighted class count. -/
def weightedCurveCountAt (p : ℕ) (hp : p.Prime) (j : ℕ) : ℝ :=
  letI : Fact p.Prime := ⟨hp⟩
  weightedCurveCount p j

/-- The raw order count attached to the concrete curve model. -/
def rawCurveOrderCount (p : ℕ → ℕ) (hp : ∀ n, (p n).Prime) (n j : ℕ) : ℕ :=
  rawCurveCountAt (p n) (hp n) j

/-- The weighted order count attached to the concrete curve model. -/
def weightedCurveOrderCount (p : ℕ → ℕ) (hp : ∀ n, (p n).Prime) (n j : ℕ) : ℝ :=
  weightedCurveCountAt (p n) (hp n) j

/-- **The classical weighted formula gives the one-sided raw curve count.**  At
every positive Frobenius discriminant, the Hurwitz class number is at most the
number of raw isomorphism classes of curves with the corresponding trace. -/
theorem deuringTraceCountLower_rawCurve {p : ℕ → ℕ} (hp : ∀ n, (p n).Prime)
    {hurwitz : ℤ → ℝ} (h : ∀ n, WaterhouseWeighted (p n) (hp n) hurwitz) :
    DeuringTraceCountLower p (rawCurveOrderCount p hp) hurwitz := by
  intro n t ht
  letI : Fact ((p n).Prime) := ⟨hp n⟩
  have hW : weightedCurveCount (p n) (traceOrder (p n) t) =
      hurwitz (traceDisc (p n) t) := h n t ht
  have hle : weightedCurveCount (p n) (traceOrder (p n) t) ≤
      (rawCurveCount (p n) (traceOrder (p n) t) : ℝ) :=
    weightedCurveCount_le_rawCurveCount (p n) _
  rw [← hW]
  exact hle

/-- **The one-sided input for an abstract order count.**  If the concrete raw
curve count is dominated by `orderCount` at every order, then the classical
weighted formula yields `DeuringTraceCountLower p orderCount hurwitz`. -/
theorem deuringTraceCountLower_of_dominated_model {p : ℕ → ℕ}
    (hp : ∀ n, (p n).Prime) {orderCount : ℕ → ℕ → ℕ} {hurwitz : ℤ → ℝ}
    (h : ∀ n, WaterhouseWeighted (p n) (hp n) hurwitz)
    (hdom : ∀ n j, rawCurveOrderCount p hp n j ≤ orderCount n j) :
    DeuringTraceCountLower p orderCount hurwitz := by
  intro n t ht
  have hraw := deuringTraceCountLower_rawCurve hp h n t ht
  have hle : (rawCurveOrderCount p hp n (traceOrder (p n) t) : ℝ) ≤
      (orderCount n (traceOrder (p n) t) : ℝ) := by
    exact_mod_cast hdom n (traceOrder (p n) t)
  exact hraw.trans hle

/-! ## 4. Exact isolation of the raw order identity -/

/-- The extra condition under which the raw class count agrees with the
classical weighted count: on every trace fiber, weighted and raw coincide. -/
def WeightedEqualsRawOnTrace (p : ℕ → ℕ) (hp : ∀ n, (p n).Prime) : Prop :=
  ∀ n t, 0 < traceDisc (p n) t →
    weightedCurveOrderCount p hp n (traceOrder (p n) t) =
      (rawCurveOrderCount p hp n (traceOrder (p n) t) : ℝ)

/-- **The classical weighted identity plus weightedness of the fiber gives the
exact raw order identity.** -/
theorem deuringWaterhouseExactOrder_raw_of_weighted_eq {p : ℕ → ℕ}
    (hp : ∀ n, (p n).Prime) {hurwitz : ℤ → ℝ}
    (h : ∀ n, WaterhouseWeighted (p n) (hp n) hurwitz)
    (heq : WeightedEqualsRawOnTrace p hp) :
    DeuringWaterhouseExactOrder p (rawCurveOrderCount p hp) hurwitz := by
  intro n t ht
  letI : Fact ((p n).Prime) := ⟨hp n⟩
  have hw := h n t ht
  have hr := heq n t ht
  dsimp only [weightedCurveOrderCount, rawCurveOrderCount, rawCurveCountAt,
    weightedCurveCountAt] at hw hr ⊢
  rw [← hr, hw]

/-- **Reduction of the abstract `DeuringWaterhouseExactOrder`.**  If the abstract
order count is the raw finite curve count, then the classical weighted formula
plus weightedness on every trace fiber gives the exact order identity for the
abstract order count. -/
theorem deuringWaterhouseExactOrder_of_model {p : ℕ → ℕ}
    (hp : ∀ n, (p n).Prime) {orderCount : ℕ → ℕ → ℕ} {hurwitz : ℤ → ℝ}
    (h : ∀ n, WaterhouseWeighted (p n) (hp n) hurwitz)
    (heq : WeightedEqualsRawOnTrace p hp)
    (hmodel : ∀ n j, orderCount n j = rawCurveOrderCount p hp n j) :
    DeuringWaterhouseExactOrder p orderCount hurwitz := by
  intro n t ht
  rw [hmodel n (traceOrder (p n) t)]
  exact deuringWaterhouseExactOrder_raw_of_weighted_eq hp h heq n t ht

/-- Conversely, the exact raw identity together with the classical weighted
identity forces weightedness on every trace fiber. -/
theorem weighted_eq_raw_of_deuringWaterhouseExactOrder {p : ℕ → ℕ}
    (hp : ∀ n, (p n).Prime) {hurwitz : ℤ → ℝ}
    (h : ∀ n, WaterhouseWeighted (p n) (hp n) hurwitz)
    (hex : DeuringWaterhouseExactOrder p (rawCurveOrderCount p hp) hurwitz) :
    WeightedEqualsRawOnTrace p hp := by
  intro n t ht
  letI : Fact ((p n).Prime) := ⟨hp n⟩
  have hw := h n t ht
  have hx := hex n t ht
  dsimp only [weightedCurveOrderCount, rawCurveOrderCount, rawCurveCountAt,
    weightedCurveCountAt] at hw hx ⊢
  rw [hw, hx]

/-- **Exact isolation of `DeuringWaterhouseExactOrder`.**  Given the classical
weighted Deuring/Waterhouse formula, the raw order-level exact identity is
equivalent to the assertion that the weighted and raw counts agree on every
trace fiber.  Equivalently, by §2, every curve in the relevant fiber must have
trivial automorphism group; the classical theorem alone does not supply this. -/
theorem deuringWaterhouseExactOrder_raw_iff {p : ℕ → ℕ}
    (hp : ∀ n, (p n).Prime) {hurwitz : ℤ → ℝ}
    (h : ∀ n, WaterhouseWeighted (p n) (hp n) hurwitz) :
    DeuringWaterhouseExactOrder p (rawCurveOrderCount p hp) hurwitz ↔
      WeightedEqualsRawOnTrace p hp :=
  ⟨weighted_eq_raw_of_deuringWaterhouseExactOrder hp h,
    deuringWaterhouseExactOrder_raw_of_weighted_eq hp h⟩

/-- **The raw exact order identity fails on a nonempty odd-characteristic
fiber.**  If the classical weighted formula holds and the trace fiber of `t` is
nonempty, then the exact identity for the raw class count is false: the
hyperelliptic involution makes the weighted count strictly smaller. -/
theorem not_deuringWaterhouseExactOrder_raw_at (hp2 : p ≠ 2) {hurwitz : ℤ → ℝ}
    (h : WaterhouseWeighted p (Fact.out : p.Prime) hurwitz) (t : ℤ)
    (ht : 0 < traceDisc p t)
    (hne : ∃ E : CurveClass p, classHasPointCount p E (traceOrder p t)) :
    ¬ DeuringWaterhouseExactOrder (fun _ => p)
      (fun _ j => rawCurveCount p j) hurwitz := by
  intro hex
  have hEq : weightedCurveCount p (traceOrder p t) =
      (rawCurveCount p (traceOrder p t) : ℝ) := by
    have hw := h t ht
    have hx := hex 0 t ht
    rw [hw, hx]
  exact weightedCurveCount_ne_rawCurveCount_of_nonempty p hp2
    (traceOrder p t) hne hEq

/-! ## 5. The bundled input and its integration with L27 -/

/-- **The L27 Deuring input with the explicit finite curve count.**

Compared with `L27TraceClassInputs`, the Deuring field `trace_count_lower` is
replaced by three concrete statements:

* `p_prime` — the target is a prime (needed to speak of `F_p`);
* `waterhouse` — the classical *weighted* Deuring/Waterhouse trace formula on
  the finite isomorphism-class model of §1;
* `orderCount_dominates_raw` — the abstract order count dominates the raw
  finite class count at every order.

The other fields (`hurwitz`, the Siegel constant and bound, the discriminant
scale, the `j`-line stratification, and the small-prime prepass) are unchanged.
No count or class number is set to zero. -/
structure L27WaterhouseInputs (I : L27_1Inputs) where
  /-- The Hurwitz class number `H(-D)`. -/
  hurwitz : ℤ → ℝ
  /-- Siegel constant in `H(-D) ≥ c√D`. -/
  c : ℝ
  /-- Nondegeneracy fraction `D(p,j) ≥ θp` on smooth orders. -/
  θ : ℝ
  /-- The Siegel constant is positive. -/
  c_pos : 0 < c
  /-- The nondegeneracy fraction is positive. -/
  θ_pos : 0 < θ
  /-- The Hasse-scale constant is below the Siegel constant at scale `√θ`. -/
  kappa_le : I.κ ≤ c * Real.sqrt θ
  /-- Siegel's lower bound on Frobenius-trace discriminants. -/
  siegel_lower : HurwitzSiegelLowerTrace I.p hurwitz c
  /-- Smooth Frobenius discriminants retain a `θ`-fraction of the Hasse width. -/
  disc_scale : HurwitzDiscriminantScale I.p I.smooth θ
  /-- The target prime is prime, so the curve model is over a field. -/
  p_prime : ∀ n, (I.p n).Prime
  /-- The classical weighted Deuring/Waterhouse trace formula. -/
  waterhouse : ∀ n, WaterhouseWeighted (I.p n) (p_prime n) hurwitz
  /-- The abstract order count dominates the raw finite curve count. -/
  orderCount_dominates_raw : ∀ n j,
    rawCurveOrderCount I.p p_prime n j ≤ I.orderCount n j
  /-- The `j`-line stratification of the curves. -/
  j_invariant_strata : JInvariantStratification I.p I.orderCount I.orderTop
  /-- The target prime exceeds the two removed small primes. -/
  p_ge_four : ∀ n, 4 ≤ I.p n

namespace L27WaterhouseInputs

variable {I : L27_1Inputs}

/-- The one-sided Deuring trace count from the classical weighted formula. -/
theorem deuringTraceCountLower (D : L27WaterhouseInputs I) :
    DeuringTraceCountLower I.p I.orderCount D.hurwitz :=
  deuringTraceCountLower_of_dominated_model D.p_prime D.waterhouse
    D.orderCount_dominates_raw

/-- **Build `L27TraceClassInputs` from the concrete Waterhouse data.**  The
trace-class field is discharged by the classical weighted formula and the
model-domination hypothesis. -/
def toTraceClassInputs (D : L27WaterhouseInputs I) : L27TraceClassInputs I :=
  L27TraceClassInputs.ofLeaves D.hurwitz D.c_pos D.θ_pos D.kappa_le
    D.siegel_lower D.disc_scale D.deuringTraceCountLower D.j_invariant_strata
    D.p_ge_four

/-- The bundled `DeuringLenstraCounts` hypothesis of `L27_1Sub`. -/
theorem deuringLenstraCounts (D : L27WaterhouseInputs I) :
    DeuringLenstraCounts I :=
  D.toTraceClassInputs.deuringLenstraCounts

/-- The L27.1 ledger from the concrete Waterhouse data. -/
theorem reduced_ledger (D : L27WaterhouseInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  D.toTraceClassInputs.reduced_ledger hhasse h0 h1 h2 hstage hbudget hlog

/-- The manuscript-rate deficit bound from the concrete Waterhouse data. -/
theorem reduced_paper (D : L27WaterhouseInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  D.toTraceClassInputs.reduced_paper hhasse h0 h1 h2 hstage hbudget hlog

/-- The L27.1 `RatedLeaf` from the concrete Waterhouse data. -/
def toRatedLeaf (D : L27WaterhouseInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) : RatedLeaf :=
  D.toTraceClassInputs.toRatedLeaf hhasse h0 h1 h2 hstage hbudget hlog

/-- The `C5` slot `exp (-2H)` from the concrete Waterhouse data. -/
theorem slot (D : L27WaterhouseInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop,
      (D.toRatedLeaf hhasse h0 h1 h2 hstage hbudget hlog).loss n ≤
        Real.exp (-(2 : ℝ) * scale n) :=
  D.toTraceClassInputs.slot hhasse h0 h1 h2 hstage hbudget hlog

end L27WaterhouseInputs

/-- **The full reduction from the concrete Waterhouse data.**  The prime
hypothesis, the classical weighted Deuring/Waterhouse formula, the
model-domination hypothesis, the analytic Hurwitz leaves, the `j`-line
stratification, and the small-prime prepass imply both bundled `L27_1Sub`
hypotheses and both deficit conclusions. -/
theorem reduction_of_waterhouse {I : L27_1Inputs}
    (D : L27WaterhouseInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  reduction_of_traceClass D.toTraceClassInputs hhasse h0 h1 h2 hstage hbudget hlog

/-- The Deuring half of the capstone from the concrete Waterhouse data. -/
theorem deuringLenstraCounts_of_waterhouse {I : L27_1Inputs}
    (D : L27WaterhouseInputs I) : DeuringLenstraCounts I :=
  D.deuringLenstraCounts

/-! ## Axiom audit -/

#print axioms curveNonsingular_iff_isElliptic
#print axioms classAutOrder_mk
#print axioms traceOrder_eq_of_pos_traceDisc
#print axioms classAutOrder_ge_one
#print axioms classWeight_le_one
#print axioms negAut_smul_self
#print axioms negAut_ne_one
#print axioms negAut_mem
#print axioms two_le_classAutOrder
#print axioms classAutOrder_ne_one
#print axioms rawCurveCount_cast_eq_sum
#print axioms weightedCurveCount_le_rawCurveCount
#print axioms weightedCurveCount_lt_rawCurveCount_of_nontrivial
#print axioms weightedCurveCount_eq_rawCurveCount_of_autOrder_one
#print axioms weightedCurveCount_eq_rawCurveCount_iff
#print axioms weightedCurveCount_lt_rawCurveCount_of_nonempty
#print axioms weightedCurveCount_ne_rawCurveCount_of_nonempty
#print axioms deuringTraceCountLower_rawCurve
#print axioms deuringTraceCountLower_of_dominated_model
#print axioms deuringWaterhouseExactOrder_raw_of_weighted_eq
#print axioms deuringWaterhouseExactOrder_of_model
#print axioms weighted_eq_raw_of_deuringWaterhouseExactOrder
#print axioms deuringWaterhouseExactOrder_raw_iff
#print axioms not_deuringWaterhouseExactOrder_raw_at
#print axioms L27WaterhouseInputs.deuringTraceCountLower
#print axioms L27WaterhouseInputs.toTraceClassInputs
#print axioms L27WaterhouseInputs.deuringLenstraCounts
#print axioms L27WaterhouseInputs.reduced_ledger
#print axioms L27WaterhouseInputs.reduced_paper
#print axioms L27WaterhouseInputs.toRatedLeaf
#print axioms L27WaterhouseInputs.slot
#print axioms reduction_of_waterhouse
#print axioms deuringLenstraCounts_of_waterhouse

end

end Cogentic.RandomizedL27Waterhouse
