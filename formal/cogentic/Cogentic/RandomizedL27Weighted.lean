import Cogentic.RandomizedL27Waterhouse
import Mathlib.GroupTheory.GroupAction.CardCommute

/-!
# L27 Weighted: the finite weighted Deuring/Waterhouse identity

`Cogentic.RandomizedL27Waterhouse` states the classical weighted
Deuring/Waterhouse trace formula as an abstract input

`WaterhouseWeighted p hp hurwitz`,

where the left-hand side is the finite sum over isomorphism classes of elliptic
curves over `F_p` of `1 / #Aut(E)`.  This file does not assume that formula.
Instead it reduces it to the smallest explicit finite weighted identity on the
concrete `CurveModel`/`CurveClass` model of `RandomizedL27Waterhouse.lean`.

The main structural observation is the orbit-stabiliser double count.  For a
finite group `G` acting on a finite type `X`, the weighted sum over the orbit
space with weights `1 / #Stab(x)` is the cardinality of `X` divided by the
cardinality of `G`:

`∑_{orbit O} 1 / #Stab(O) = #X / #G`.

Applied to the action of the admissible variable changes on nonsingular
Weierstrass equations, this turns the weighted isomorphism-class count into a
raw count of Weierstrass equations:

`weightedCurveCount p j = # { W : CurveModel p // #W(F_p) = j } / #VariableChange`.

Consequently the classical weighted identity is equivalent to the explicit
finite identity

`# { W : CurveModel p // #W(F_p) = p + 1 - t } /
      #VariableChange = H(4p - t²)`

for every trace `t` with positive Frobenius discriminant.  The right-hand side
is unchanged; only the left-hand side has been made a count of honest finite
Weierstrass equations instead of a quotient weighted by automorphism orders.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no curve count or
class number is set to zero.
-/

set_option linter.style.haveILetI false

namespace Cogentic.RandomizedL27Weighted

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27TraceClass
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The orbit-stabiliser weighted count -/

/-- **Orbit-stabiliser double count.**  For a finite group `G` acting on a
finite type `X`, the sum over the orbit space of the reciprocal stabiliser
orders is `#X / #G`.

This is the groupoid-cardinality form of the class formula.  It is the finite
combinatorial content behind the weights `1 / #Aut(E)` in the Deuring/Waterhouse
formula. -/
theorem sum_inv_card_stabilizer_eq_card_div_card_group
    (G X : Type*) [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [DecidableRel (MulAction.orbitRel G X)]
    [∀ x : X, Fintype (MulAction.stabilizer G x)] :
    (∑ E : Quotient (MulAction.orbitRel G X),
        1 / (Fintype.card (MulAction.stabilizer G E.out) : ℝ)) =
      (Fintype.card X : ℝ) / (Fintype.card G : ℝ) := by
  classical
  have hcard : ∀ E : Quotient (MulAction.orbitRel G X),
      Fintype.card (MulAction.orbit G E.out) *
        Fintype.card (MulAction.stabilizer G E.out) = Fintype.card G :=
    fun E => MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) E.out
  have hterm : ∀ E : Quotient (MulAction.orbitRel G X),
      1 / (Fintype.card (MulAction.stabilizer G E.out) : ℝ) =
        (Fintype.card (MulAction.orbit G E.out) : ℝ) / (Fintype.card G : ℝ) := by
    intro E
    have hstab : (0 : ℝ) < (Fintype.card (MulAction.stabilizer G E.out) : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨1⟩
    have horbit : (0 : ℝ) < (Fintype.card (MulAction.orbit G E.out) : ℝ) := by
      have hne : Nonempty (MulAction.orbit G E.out) :=
        ⟨⟨E.out, MulAction.mem_orbit_self E.out⟩⟩
      exact_mod_cast Fintype.card_pos_iff.mpr hne
    have hgroup : (0 : ℝ) < (Fintype.card G : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨1⟩
    have hmul : (Fintype.card (MulAction.orbit G E.out) : ℝ) *
        (Fintype.card (MulAction.stabilizer G E.out) : ℝ) =
        (Fintype.card G : ℝ) := by
      exact_mod_cast hcard E
    rw [div_eq_div_iff hstab.ne' hgroup.ne']
    rw [one_mul, hmul]
  calc
    (∑ E : Quotient (MulAction.orbitRel G X),
        1 / (Fintype.card (MulAction.stabilizer G E.out) : ℝ)) =
        ∑ E : Quotient (MulAction.orbitRel G X),
          (Fintype.card (MulAction.orbit G E.out) : ℝ) / (Fintype.card G : ℝ) :=
      Finset.sum_congr rfl fun E _ => hterm E
    _ = (∑ E : Quotient (MulAction.orbitRel G X),
          (Fintype.card (MulAction.orbit G E.out) : ℝ)) / (Fintype.card G : ℝ) := by
      rw [Finset.sum_div]
    _ = (Fintype.card X : ℝ) / (Fintype.card G : ℝ) := by
      congr 1
      have hsigma : Fintype.card X =
          ∑ E : Quotient (MulAction.orbitRel G X),
            Fintype.card (MulAction.orbit G E.out) := by
        rw [Fintype.card_congr (MulAction.selfEquivSigmaOrbits G X),
          Fintype.card_sigma]
      exact_mod_cast hsigma.symm

/-- A proposition invariant under a group action has the same truth value on
every element of an orbit. -/
theorem iff_of_mem_orbit {G X : Type*} [Group G] [MulAction G X]
    {Q : X → Prop} (hQ : ∀ (g : G) (x : X), Q (g • x) ↔ Q x)
    {x y : X} (h : y ∈ MulAction.orbit G x) : Q y ↔ Q x := by
  rw [MulAction.mem_orbit_iff] at h
  obtain ⟨g, rfl⟩ := h
  exact hQ g x

/-- The reciprocal stabiliser order is the orbit size divided by the group
order, by orbit-stabiliser. -/
theorem inv_card_stabilizer_eq_card_orbit_div_card_group
    (G X : Type*) [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [∀ b : X, Fintype (MulAction.stabilizer G b)]
    [∀ b : X, Fintype (MulAction.orbit G b)] :
    ∀ b : X,
      1 / (Fintype.card (MulAction.stabilizer G b) : ℝ) =
        (Fintype.card (MulAction.orbit G b) : ℝ) / (Fintype.card G : ℝ) := by
  classical
  intro b
  have hstab : (0 : ℝ) < (Fintype.card (MulAction.stabilizer G b) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨1⟩
  have hgroup : (0 : ℝ) < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨1⟩
  have hmul : (Fintype.card (MulAction.orbit G b) : ℝ) *
      (Fintype.card (MulAction.stabilizer G b) : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) b
  rw [div_eq_div_iff hstab.ne' hgroup.ne']
  rw [one_mul, hmul]

/-- The first component of the orbit decomposition is the class map. -/
lemma selfEquivSigmaOrbits_fst {G X : Type*} [Group G] [MulAction G X] (x : X) :
    (MulAction.selfEquivSigmaOrbits G X x).1 =
      Quotient.mk (MulAction.orbitRel G X) x := by
  simp [MulAction.selfEquivSigmaOrbits, MulAction.selfEquivSigmaOrbits']
  rfl

/-- **Filtered orbit-stabiliser double count.**  For a group-invariant predicate
`Q`, the sum over the orbit space of `1 / #Stab` restricted to the orbits meeting
`Q` is the number of elements satisfying `Q`, divided by the group order. -/
theorem sum_ite_invariant_eq_card_filter_div_card_group
    (G X : Type*) [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [DecidableRel (MulAction.orbitRel G X)]
    [∀ x : X, Fintype (MulAction.stabilizer G x)]
    [∀ x : X, Fintype (MulAction.orbit G x)]
    (Q : X → Prop) [DecidablePred Q]
    (hQ : ∀ (g : G) (x : X), Q (g • x) ↔ Q x) :
    (∑ E : Quotient (MulAction.orbitRel G X),
        if Q E.out then 1 / (Fintype.card (MulAction.stabilizer G E.out) : ℝ) else 0) =
      ((Finset.univ.filter Q).card : ℝ) / (Fintype.card G : ℝ) := by
  classical
  let e := MulAction.selfEquivSigmaOrbits G X
  have hcard : ((Finset.univ.filter Q).card : ℝ) =
      ∑ x : X, if Q x then (1 : ℝ) else 0 := by
    rw [Finset.card_filter]
    push_cast
    simp
  have htransfer : (∑ x : X, if Q x then (1 : ℝ) else 0) =
      ∑ E : Quotient (MulAction.orbitRel G X),
        ∑ z : MulAction.orbit G E.out,
          (if Q (e.symm ⟨E, z⟩) then (1 : ℝ) else 0) := by
    rw [← Equiv.sum_comp e.symm]
    rw [Fintype.sum_sigma]
  have horbit_count :
      (∑ E : Quotient (MulAction.orbitRel G X),
          if Q E.out then (Fintype.card (MulAction.orbit G E.out) : ℝ) else 0) =
        ((Finset.univ.filter Q).card : ℝ) := by
    rw [hcard, htransfer]
    apply Finset.sum_congr rfl
    intro E _
    have hconst : ∀ z : MulAction.orbit G E.out, Q (e.symm ⟨E, z⟩) ↔ Q E.out := by
      intro z
      have hmem : e.symm ⟨E, z⟩ ∈ MulAction.orbit G E.out := by
        have hmk : Quotient.mk (MulAction.orbitRel G X) (e.symm ⟨E, z⟩) = E := by
          have h := congrArg Sigma.fst (Equiv.apply_symm_apply e ⟨E, z⟩)
          rw [selfEquivSigmaOrbits_fst] at h
          exact h
        have hmem' : e.symm ⟨E, z⟩ ∈ MulAction.orbitRel.Quotient.orbit E :=
          (MulAction.orbitRel.Quotient.mem_orbit).mpr hmk
        rwa [MulAction.orbitRel.Quotient.orbit_eq_orbit_out E Quotient.out_eq'] at hmem'
      exact iff_of_mem_orbit hQ hmem
    by_cases hE : Q E.out
    · have hz : ∀ z : MulAction.orbit G E.out, Q (e.symm ⟨E, z⟩) :=
        fun z => (hconst z).mpr hE
      simp [hE, hz]
    · have hz : ∀ z : MulAction.orbit G E.out, ¬ Q (e.symm ⟨E, z⟩) :=
        fun z h => hE ((hconst z).mp h)
      simp [hE, hz]
  calc
    (∑ E : Quotient (MulAction.orbitRel G X),
        if Q E.out then 1 / (Fintype.card (MulAction.stabilizer G E.out) : ℝ) else 0) =
        ∑ E : Quotient (MulAction.orbitRel G X),
          (if Q E.out then (Fintype.card (MulAction.orbit G E.out) : ℝ) else 0) /
            (Fintype.card G : ℝ) := by
      apply Finset.sum_congr rfl
      intro E _
      by_cases hE : Q E.out
      · simp only [hE, if_true]
        exact inv_card_stabilizer_eq_card_orbit_div_card_group G X E.out
      · simp [hE]
    _ = (∑ E : Quotient (MulAction.orbitRel G X),
          if Q E.out then (Fintype.card (MulAction.orbit G E.out) : ℝ) else 0) /
            (Fintype.card G : ℝ) := by
      rw [Finset.sum_div]
    _ = ((Finset.univ.filter Q).card : ℝ) / (Fintype.card G : ℝ) := by
      rw [horbit_count]

/-! ## 2. The point count is an isomorphism invariant -/

variable (p : ℕ) [Fact p.Prime]

/-- The coordinate change `(X, Y) ↦ (u²X + r, u³Y + u²sX + t)` attached to an
admissible variable change. -/
def coordChange (C : WeierstrassCurve.VariableChange (ZMod p))
    (q : ZMod p × ZMod p) : ZMod p × ZMod p :=
  ((C.u : ZMod p) ^ 2 * q.1 + C.r,
    (C.u : ZMod p) ^ 3 * q.2 + (C.u : ZMod p) ^ 2 * C.s * q.1 + C.t)

/-- **The Weierstrass equation after a variable change.**  A point `q` satisfies
the transformed equation iff its coordinate change satisfies the original
equation.  This is the affine form of the standard change-of-coordinates
identity, with the harmless factor `u⁶` removed. -/
lemma equation_coordChange (C : WeierstrassCurve.VariableChange (ZMod p))
    (W : WeierstrassCurve (ZMod p)) (q : ZMod p × ZMod p) :
    (C • W).toAffine.Equation q.1 q.2 ↔
      W.toAffine.Equation (coordChange p C q).1 (coordChange p C q).2 := by
  rw [WeierstrassCurve.Affine.equation_iff', WeierstrassCurve.Affine.equation_iff']
  have hu : (C.u : ZMod p) ≠ 0 := C.u.ne_zero
  have key : (C.u : ZMod p) ^ 6 *
      (q.2 ^ 2 + (C • W).a₁ * q.1 * q.2 + (C • W).a₃ * q.2 -
        (q.1 ^ 3 + (C • W).a₂ * q.1 ^ 2 + (C • W).a₄ * q.1 + (C • W).a₆)) =
      ((coordChange p C q).2 ^ 2 + W.a₁ * (coordChange p C q).1 * (coordChange p C q).2 +
        W.a₃ * (coordChange p C q).2 -
        ((coordChange p C q).1 ^ 3 + W.a₂ * (coordChange p C q).1 ^ 2 +
          W.a₄ * (coordChange p C q).1 + W.a₆)) := by
    simp only [coordChange, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆,
      Units.val_inv_eq_inv_val]
    field_simp
    ring
  constructor
  · intro h
    rw [← key, h, mul_zero]
  · intro h
    have h0 : (C.u : ZMod p) ^ 6 *
        (q.2 ^ 2 + (C • W).a₁ * q.1 * q.2 + (C • W).a₃ * q.2 -
          (q.1 ^ 3 + (C • W).a₂ * q.1 ^ 2 + (C • W).a₄ * q.1 + (C • W).a₆)) = 0 := by
      rw [key, h]
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 6 hu)

/-- The coordinate change of the inverse variable change inverts the coordinate
change. -/
lemma coordChange_inv_apply (C : WeierstrassCurve.VariableChange (ZMod p))
    (q : ZMod p × ZMod p) :
    coordChange p C⁻¹ (coordChange p C q) = q := by
  ext <;>
    simp only [coordChange, WeierstrassCurve.VariableChange.inv_def,
      Units.val_inv_eq_inv_val] <;>
    field_simp <;>
    ring

/-- The coordinate change of `C` inverts the coordinate change of `C⁻¹`. -/
lemma coordChange_apply_inv_apply (C : WeierstrassCurve.VariableChange (ZMod p))
    (q : ZMod p × ZMod p) :
    coordChange p C (coordChange p C⁻¹ q) = q := by
  simpa using coordChange_inv_apply p C⁻¹ q

/-- **The point count is invariant under admissible variable changes.** -/
theorem curvePointCount_smul (C : WeierstrassCurve.VariableChange (ZMod p))
    (W : CurveModel p) :
    curvePointCount p (C • W) = curvePointCount p W := by
  have h : (Finset.univ.filter (fun q : ZMod p × ZMod p =>
        (C • W).1.toAffine.Equation q.1 q.2)).card =
      (Finset.univ.filter (fun q : ZMod p × ZMod p =>
        W.1.toAffine.Equation q.1 q.2)).card := by
    apply Finset.card_bij (fun q _ => coordChange p C q)
    · intro q hq
      rw [Finset.mem_filter] at hq ⊢
      exact ⟨Finset.mem_univ _,
        (equation_coordChange p C W.1 q).mp hq.2⟩
    · intro q₁ hq₁ q₂ hq₂ h
      have := congrArg (coordChange p C⁻¹) h
      simpa only [coordChange_inv_apply] using this
    · intro q hq
      refine ⟨coordChange p C⁻¹ q, ?_, ?_⟩
      · rw [Finset.mem_filter] at hq ⊢
        refine ⟨Finset.mem_univ _, (equation_coordChange p C W.1 _).mpr ?_⟩
        simpa only [coordChange_apply_inv_apply] using hq.2
      · exact coordChange_apply_inv_apply p C q
  simp only [curvePointCount, h]

/-! ## 3. The explicit finite weighted identity -/

/-- The weighted count of isomorphism classes with exactly `j` points, written
as a sum over the nonempty fiber.  This is the smallest explicit finite weighted
sum attached to the curve model. -/
def weightedFiberSum (j : ℕ) : ℝ :=
  ∑ E ∈ Finset.univ.filter (fun E : CurveClass p => classHasPointCount p E j),
    (classAutOrder p E : ℝ)⁻¹

/-- The raw count of nonsingular Weierstrass equations with exactly `j` points. -/
def modelFiberCount (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun W : CurveModel p => curvePointCount p W = j)).card

/-- The weighted class count is the sum over the nonempty fiber. -/
theorem weightedCurveCount_eq_fiberSum (j : ℕ) :
    weightedCurveCount p j = weightedFiberSum p j := by
  unfold weightedCurveCount weightedFiberSum
  rw [Finset.sum_filter]
  simp [one_div]

/-- The class fiber of an equation is its point-count fiber. -/
theorem classHasPointCount_mk_iff (W : CurveModel p) (j : ℕ) :
    classHasPointCount p (Quotient.mk
      (MulAction.orbitRel (WeierstrassCurve.VariableChange (ZMod p)) (CurveModel p))
      W) j ↔ curvePointCount p W = j := by
  constructor
  · rintro ⟨W', hW', hcount⟩
    have hrel : MulAction.orbitRel (WeierstrassCurve.VariableChange (ZMod p))
        (CurveModel p) W' W := Quotient.exact hW'
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨C, hC⟩ := hrel
    rw [← hC, curvePointCount_smul] at hcount
    exact hcount
  · intro h
    exact ⟨W, rfl, h⟩

/-- **The weighted class count is a raw equation count divided by the group
order.**  Orbit-stabiliser turns the automorphism weights `1/#Aut` into a
division by the number of admissible variable changes. -/
theorem weightedFiberSum_eq_modelFiberCount_div (j : ℕ) :
    weightedFiberSum p j = (modelFiberCount p j : ℝ) /
      (Fintype.card (WeierstrassCurve.VariableChange (ZMod p)) : ℝ) := by
  classical
  let Q : CurveModel p → Prop := fun W => curvePointCount p W = j
  have hQ : ∀ (C : WeierstrassCurve.VariableChange (ZMod p)) (W : CurveModel p),
      Q (C • W) ↔ Q W := by
    intro C W
    change curvePointCount p (C • W) = j ↔ curvePointCount p W = j
    rw [curvePointCount_smul]
  have hclass : ∀ E : CurveClass p, classHasPointCount p E j ↔ Q E.out := by
    intro E
    have h := classHasPointCount_mk_iff p E.out j
    simpa [Q, Quotient.out_eq] using h
  have hsum : weightedFiberSum p j =
      ∑ E : CurveClass p, if Q E.out then 1 / (classAutOrder p E : ℝ) else 0 := by
    unfold weightedFiberSum
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro E _
    by_cases h : classHasPointCount p E j
    · have hQout : Q E.out := (hclass E).mp h
      simp [h, hQout]
    · have hQout : ¬ Q E.out := fun hq => h ((hclass E).mpr hq)
      simp [h, hQout]
  have hsum' : (∑ E : CurveClass p,
        if Q E.out then 1 / (classAutOrder p E : ℝ) else 0) =
      ∑ E : CurveClass p,
        if Q E.out then
          1 / (Fintype.card (MulAction.stabilizer
            (WeierstrassCurve.VariableChange (ZMod p)) E.out) : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro E _
    by_cases h : Q E.out
    · simp only [h, if_true]
      rw [classAutOrder, Nat.card_eq_fintype_card]
    · simp [h]
  have horbit := sum_ite_invariant_eq_card_filter_div_card_group
    (WeierstrassCurve.VariableChange (ZMod p)) (CurveModel p) Q hQ
  rw [hsum, hsum', horbit]
  simp [modelFiberCount, Q]

/-- **The classical weighted identity, stated on the nonempty fiber sum.**
This is the smallest explicit finite weighted sum form of
`WaterhouseWeighted`: the sum runs only over isomorphism classes with the
prescribed trace, and each summand is the reciprocal automorphism order. -/
def WaterhouseWeightedFiberSum (p : ℕ) (hp : p.Prime) (hurwitz : ℤ → ℝ) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ t : ℤ, 0 < traceDisc p t →
    weightedFiberSum p (traceOrder p t) = hurwitz (traceDisc p t)

/-- **The classical weighted identity, stated as a raw count of Weierstrass
equations.**  The left-hand side is the number of nonsingular equations with
the prescribed trace, divided by the number of admissible variable changes.
This is the finite identity obtained after applying orbit-stabiliser; it has no
quotient types and no reciprocal automorphism weights in its summands. -/
def WaterhouseWeightedModelCount (p : ℕ) (hp : p.Prime) (hurwitz : ℤ → ℝ) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ t : ℤ, 0 < traceDisc p t →
    (modelFiberCount p (traceOrder p t) : ℝ) /
        (Fintype.card (WeierstrassCurve.VariableChange (ZMod p)) : ℝ) =
      hurwitz (traceDisc p t)

/-- `WaterhouseWeighted` is exactly the finite fiber-sum identity. -/
theorem waterhouseWeighted_iff_fiberSum (p : ℕ) (hp : p.Prime) (hurwitz : ℤ → ℝ) :
    WaterhouseWeighted p hp hurwitz ↔ WaterhouseWeightedFiberSum p hp hurwitz := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold WaterhouseWeighted WaterhouseWeightedFiberSum
  constructor <;> intro h t ht
  · rw [← weightedCurveCount_eq_fiberSum]
    exact h t ht
  · rw [weightedCurveCount_eq_fiberSum]
    exact h t ht

/-- `WaterhouseWeighted` is exactly the explicit raw equation-count identity. -/
theorem waterhouseWeighted_iff_modelCount (p : ℕ) (hp : p.Prime) (hurwitz : ℤ → ℝ) :
    WaterhouseWeighted p hp hurwitz ↔ WaterhouseWeightedModelCount p hp hurwitz := by
  rw [waterhouseWeighted_iff_fiberSum]
  letI : Fact p.Prime := ⟨hp⟩
  unfold WaterhouseWeightedFiberSum WaterhouseWeightedModelCount
  constructor <;> intro h t ht
  · rw [weightedFiberSum_eq_modelFiberCount_div]
    exact h t ht
  · rw [weightedFiberSum_eq_modelFiberCount_div]
    exact h t ht

/-- The finite fiber-sum identity gives the classical weighted identity. -/
theorem waterhouseWeighted_of_fiberSum {p : ℕ} {hp : p.Prime} {hurwitz : ℤ → ℝ}
    (h : WaterhouseWeightedFiberSum p hp hurwitz) :
    WaterhouseWeighted p hp hurwitz :=
  (waterhouseWeighted_iff_fiberSum p hp hurwitz).mpr h

/-- The explicit raw equation-count identity gives the classical weighted
identity. -/
theorem waterhouseWeighted_of_modelCount {p : ℕ} {hp : p.Prime} {hurwitz : ℤ → ℝ}
    (h : WaterhouseWeightedModelCount p hp hurwitz) :
    WaterhouseWeighted p hp hurwitz :=
  (waterhouseWeighted_iff_modelCount p hp hurwitz).mpr h

end

end Cogentic.RandomizedL27Weighted
