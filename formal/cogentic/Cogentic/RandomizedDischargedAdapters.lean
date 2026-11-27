import Cogentic.RandomizedPaperEndpointDischarged
import Cogentic.RandomizedConcreteEpochChecks
import Cogentic.RandomizedConcreteEpochCost
import Cogentic.RandomizedC5Full

/-!
# Concrete adapters for the discharged paper endpoint

`Cogentic.RandomizedPaperEndpointDischarged.DischargedPaperEndpointInputs` keeps
three adapters explicit besides the eight remaining paper leaves, the decomposed
L18.4/L19 inputs, C1–C4, and the W45 `C5FullInputs` certificate:

1. `concrete` — the concrete epoch family on which the C5 certificate lives;
2. `concrete_eq` — the ambient `HardEpochData` family is that concrete family
   packaged by `ConcreteEpochData.toHardEpochData`;
3. `loss_le` — the concrete C5.a–e loss is dominated by the paper ledger.

This file discharges (1) and (2) definitionally for the canonical concrete
family, and reduces (3) to a single explicit numerical inequality between

* the eight-term concrete C5 loss
  `pool + survivor + descent + chebotarev + oddDegree + valuation + hensel + coupling`
  (the W31 C5.d algebra total loss is split into its four leaf losses), and
* the twelve-term paper ledger
  `l18_4 + l19.4 + l19.5 + l19.6 + l20.2 + l20.4 + l21.2 + l27.1 + l30 + l34 + l4/l25/l36 + p1`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no loss is set to
zero: every slot is the genuine projection of the corresponding input record.
-/

namespace Cogentic.RandomizedDischargedAdapters

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpoch.ConcreteEpochChecks
open Cogentic.RandomizedConcreteEpochCost
open Cogentic.RandomizedC5Full
open Cogentic.RandomizedC5Algebra
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperL18_4
open Cogentic.RandomizedPaperLeafStatements
open Filter Real
open scoped BigOperators ENNReal

set_option warn.classDefReducibility false

/-! ## Section 1: The concrete family and the `concrete` / `concrete_eq` adapters -/

/-- The ambient `HardEpochData` family attached to a family of concrete epochs.
This is exactly `ConcreteEpochChecks.concreteEpochFamily`, named here so that the
adapter statements read independently of the checks file. -/
noncomputable def concreteHardFamily
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n) : ∀ n, 3 ≤ n → HardEpochData n :=
  concreteEpochFamily D

/-- **The `concrete_eq` adapter, proved for the canonical concrete family.**
For `E = concreteHardFamily D` and `concrete = D` the ambient epoch is
definitionally the packaged concrete epoch. -/
theorem concrete_eq_concreteHardFamily
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n) :
    ∀ n hN, concreteHardFamily D n hN = (D n hN).toHardEpochData :=
  fun _ _ => rfl

/-- The same adapter for the cost-file packaging of a `n`-only concrete family.
`concreteCostFamily D` is definitionally `(D n).toHardEpochData`. -/
theorem concrete_eq_concreteCostFamily
    (D : ∀ n, ConcreteEpochData n) :
    ∀ n hN, concreteCostFamily D n hN = (D n).toHardEpochData :=
  fun _ _ => rfl

/-! ## Section 2: `loss_le` reduced to explicit sums -/

/-- The concrete C5.a–e loss, with the C5.d algebra total split into the four
L34–L37 sub-losses.  This is the left-hand side of the remaining numerical
adapter, with every structure projection made explicit. -/
noncomputable def c5ExpandedLoss {n : ℕ} (hN : 3 ≤ n) (C : ConcreteEpochData n)
    (I : @C5FullInputs n C (sampleFintype hN C)) : ℝ :=
  letI := sampleFintype hN C
  I.abc.pool.loss + I.survivor.loss + I.descent.loss +
    I.algebra.chebotarevLoss + I.algebra.oddDegreeLoss +
    I.algebra.valuationLoss + I.algebra.henselLoss + I.coupling.loss

/-- The concrete C5 total loss is the expanded eight-term loss. -/
theorem c5TotalLoss_eq_expanded {n : ℕ} (hN : 3 ≤ n) (C : ConcreteEpochData n)
    (I : @C5FullInputs n C (sampleFintype hN C)) :
    c5TotalLoss hN C I = c5ExpandedLoss hN C I := by
  simp only [c5TotalLoss, c5ExpandedLoss, C5FullInputs.totalLoss,
    C5AlgebraInputs.totalLoss]
  ring

/-- The paper ledger `dischargedSlots`, written as the explicit twelve-term sum of
the decomposed L18.4/L19 losses and the eight remaining paper-leaf losses. -/
theorem dischargedSlots_total_eq
    (l18_4 : L18_4Inputs) (l19 : L19Inputs)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_1 : RatedLeaf) (l30 : SubexpLeaf)
    (l34 : RatedLeaf) (l4_l25_l36 : AlgebraicLeaf) (p1 : P1Leaf) (n : ℕ) :
    (dischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
        l4_l25_l36 p1).total n =
      l18_4.loss n + l19.poisson.loss n + l19.zeroMode.loss n +
        l19.thin.loss n + l20_2.loss n + l20_4.loss n + l21_2.loss n +
        l27_1.loss n + l30.loss n + l34.loss n + l4_l25_l36.loss n +
        p1.loss n := by
  simp (config := { decide := true }) [C5LossSlots.total, allC5Leaves,
    dischargedSlots]
  ring

/-- **The `loss_le` adapter in its smallest explicit form.**  The C5 field of the
discharged inputs follows from the single numerical inequality between the
eight-term concrete loss and the twelve-term paper ledger. -/
theorem loss_le_of_expanded
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n)
    (l18_4 : L18_4Inputs) (l19 : L19Inputs)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_1 : RatedLeaf) (l30 : SubexpLeaf)
    (l34 : RatedLeaf) (l4_l25_l36 : AlgebraicLeaf) (p1 : P1Leaf)
    (c5 : ∀ n hN, @C5FullInputs n (D n hN) (sampleFintype hN (D n hN)))
    (h : ∀ n hN,
      c5ExpandedLoss hN (D n hN) (c5 n hN) ≤
        (dischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
          l4_l25_l36 p1).total n) :
    ∀ n hN,
      c5TotalLoss hN (D n hN) (c5 n hN) ≤
        (dischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
          l4_l25_l36 p1).total n := by
  intro n hN
  rw [c5TotalLoss_eq_expanded]
  exact h n hN

/-- **`loss_le` is equivalent to the expanded inequality.**  The adapter field is
not merely implied by the eight-term/twelve-term inequality: it is equivalent to
it, so the numerical content of the adapter is exactly that inequality. -/
theorem loss_le_iff_expanded
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n)
    (l18_4 : L18_4Inputs) (l19 : L19Inputs)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_1 : RatedLeaf) (l30 : SubexpLeaf)
    (l34 : RatedLeaf) (l4_l25_l36 : AlgebraicLeaf) (p1 : P1Leaf)
    (c5 : ∀ n hN, @C5FullInputs n (D n hN) (sampleFintype hN (D n hN))) :
    (∀ n hN,
      c5TotalLoss hN (D n hN) (c5 n hN) ≤
        (dischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
          l4_l25_l36 p1).total n) ↔
    (∀ n hN,
      c5ExpandedLoss hN (D n hN) (c5 n hN) ≤
        (dischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
          l4_l25_l36 p1).total n) := by
  constructor
  · intro h n hN
    rw [← c5TotalLoss_eq_expanded (hN := hN) (C := D n hN) (I := c5 n hN)]
    exact h n hN
  · exact loss_le_of_expanded D l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30
      l34 l4_l25_l36 p1 c5

/-- **`loss_le` is equivalent to the fully explicit twelve-term inequality.**
This is the smallest explicit form: the eight concrete C5.a–e losses on the left,
the twelve genuine paper-ledger losses on the right, with no structure
projection or ledger combinator left folded. -/
theorem loss_le_iff_explicit
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n)
    (l18_4 : L18_4Inputs) (l19 : L19Inputs)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_1 : RatedLeaf) (l30 : SubexpLeaf)
    (l34 : RatedLeaf) (l4_l25_l36 : AlgebraicLeaf) (p1 : P1Leaf)
    (c5 : ∀ n hN, @C5FullInputs n (D n hN) (sampleFintype hN (D n hN))) :
    (∀ n hN,
      c5TotalLoss hN (D n hN) (c5 n hN) ≤
        (dischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
          l4_l25_l36 p1).total n) ↔
    (∀ n hN,
      c5ExpandedLoss hN (D n hN) (c5 n hN) ≤
        l18_4.loss n + l19.poisson.loss n + l19.zeroMode.loss n +
          l19.thin.loss n + l20_2.loss n + l20_4.loss n + l21_2.loss n +
          l27_1.loss n + l30.loss n + l34.loss n + l4_l25_l36.loss n +
          p1.loss n) := by
  rw [loss_le_iff_expanded D l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30
    l34 l4_l25_l36 p1 c5]
  constructor
  · intro h n hN
    simpa only [dischargedSlots_total_eq] using h n hN
  · intro h n hN
    simpa only [dischargedSlots_total_eq] using h n hN

/-! ## Section 3: `DischargedPaperEndpointInputs` from concrete inputs -/

/-- **Concrete `DischargedPaperEndpointInputs`.**  The three adapters are
supplied as follows: `concrete := D`; `concrete_eq` is the definitional identity
`concrete_eq_concreteHardFamily`; and `loss_le` is obtained from the explicit
eight-term/twelve-term inequality `hloss`.  Everything else is exactly the C1–C4
records, the W45 C5 certificate, the eight remaining paper leaves, and the
decomposed L18.4/L19 inputs. -/
noncomputable def dischargedInputsOfConcrete
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n) (C : ℝ)
    (l18_4 : L18_4Inputs) (l19 : L19Inputs)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_1 : RatedLeaf) (l30 : SubexpLeaf)
    (l34 : RatedLeaf) (l4_l25_l36 : AlgebraicLeaf) (p1 : P1Leaf)
    (c1 : C1Inputs (concreteHardFamily D))
    (c2 : C2Inputs (concreteHardFamily D))
    (c3 : C3Inputs (concreteHardFamily D))
    (c4 : C4Inputs (concreteHardFamily D) C)
    (c5 : ∀ n hN, @C5FullInputs n (D n hN) (sampleFintype hN (D n hN)))
    (hloss : ∀ n hN,
      c5ExpandedLoss hN (D n hN) (c5 n hN) ≤
        (dischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
          l4_l25_l36 p1).total n) :
    DischargedPaperEndpointInputs (concreteHardFamily D) C where
  l18_4 := l18_4
  l19 := l19
  l20_2 := l20_2
  l20_4 := l20_4
  l21_2 := l21_2
  l27_1 := l27_1
  l30 := l30
  l34 := l34
  l4_l25_l36 := l4_l25_l36
  p1 := p1
  c1 := c1
  c2 := c2
  c3 := c3
  c4 := c4
  concrete := D
  concrete_eq := concrete_eq_concreteHardFamily D
  c5 := c5
  loss_le := loss_le_of_expanded D l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30
    l34 l4_l25_l36 p1 c5 hloss

/-- **Concrete C1/C2/C3/C4 constructor.**  C1 and C2 are proved from the
concrete global-product identity and hidden-sign symmetry (`W12`); C3 and C4 are
the direct-sampler and stagewise-work records of `W13`.  The only numerical
input left is the explicit eight-term/twelve-term loss inequality. -/
noncomputable def dischargedInputsOfConcreteCost
    (D : ∀ n, ConcreteEpochData n) (C : ℝ)
    (l18_4 : L18_4Inputs) (l19 : L19Inputs)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_1 : RatedLeaf) (l30 : SubexpLeaf)
    (l34 : RatedLeaf) (l4_l25_l36 : AlgebraicLeaf) (p1 : P1Leaf)
    (hglobal : ∀ n, (D n).GlobalProductIdentity)
    (huniform : ∀ n, (D n).HiddenSignSymmetry)
    (H3 : ConcreteC3Hypotheses D) (H4 : ConcreteC4Hypotheses D C)
    (c5 : ∀ n hN, @C5FullInputs n (D n) (sampleFintype hN (D n)))
    (hloss : ∀ n hN,
      c5ExpandedLoss hN (D n) (c5 n hN) ≤
        (dischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
          l4_l25_l36 p1).total n) :
    DischargedPaperEndpointInputs (concreteCostFamily D) C where
  l18_4 := l18_4
  l19 := l19
  l20_2 := l20_2
  l20_4 := l20_4
  l21_2 := l21_2
  l27_1 := l27_1
  l30 := l30
  l34 := l34
  l4_l25_l36 := l4_l25_l36
  p1 := p1
  c1 := c1Inputs_concreteEpoch (fun n _ => D n) (fun n _ => hglobal n)
  c2 := c2Inputs_concreteEpoch (fun n _ => D n) (fun n _ => huniform n)
  c3 := c3Inputs D H3
  c4 := c4Inputs D H4
  concrete := fun n _ => D n
  concrete_eq := concrete_eq_concreteCostFamily D
  c5 := c5
  loss_le := loss_le_of_expanded (fun n _ => D n) l18_4 l19 l20_2 l20_4
    l21_2 l27_1 l30 l34 l4_l25_l36 p1 c5 hloss

/-! ## Section 4: The `hitMass` bridge and endpoint corollaries -/

/-- The `hitMass` bridge produced by the concrete construction is the discharged
`hitMass_of_inputs` applied to the explicit loss inequality. -/
theorem hitMass_of_concrete
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n) (C : ℝ)
    (l18_4 : L18_4Inputs) (l19 : L19Inputs)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_1 : RatedLeaf) (l30 : SubexpLeaf)
    (l34 : RatedLeaf) (l4_l25_l36 : AlgebraicLeaf) (p1 : P1Leaf)
    (c1 : C1Inputs (concreteHardFamily D))
    (c2 : C2Inputs (concreteHardFamily D))
    (c3 : C3Inputs (concreteHardFamily D))
    (c4 : C4Inputs (concreteHardFamily D) C)
    (c5 : ∀ n hN, @C5FullInputs n (D n hN) (sampleFintype hN (D n hN)))
    (hloss : ∀ n hN,
      c5ExpandedLoss hN (D n hN) (c5 n hN) ≤
        (dischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
          l4_l25_l36 p1).total n) :
    ∀ n (hN : 3 ≤ n), HardInput n →
      (1 / 4 : ℝ) - (dischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1
        l30 l34 l4_l25_l36 p1).total n ≤
        (((concreteHardFamily D n hN).ideal.toOuterMeasure
          {x | observe (concreteHardFamily D n hN).trace x ∈
            (concreteHardFamily D n hN).good}).toReal) := by
  intro n hN hhard
  let I : DischargedPaperEndpointInputs (concreteHardFamily D) C :=
    dischargedInputsOfConcrete D C l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30
      l34 l4_l25_l36 p1 c1 c2 c3 c4 c5 hloss
  have h := I.hitMass_of_inputs n hN hhard
  rw [I.toPaperAnalyticAssumptions_slots] at h
  dsimp only [I] at h
  exact h

/-! ## Axiom audit -/

#print axioms concreteHardFamily
#print axioms concrete_eq_concreteHardFamily
#print axioms concrete_eq_concreteCostFamily
#print axioms c5ExpandedLoss
#print axioms c5TotalLoss_eq_expanded
#print axioms dischargedSlots_total_eq
#print axioms loss_le_of_expanded
#print axioms loss_le_iff_expanded
#print axioms loss_le_iff_explicit
#print axioms dischargedInputsOfConcrete
#print axioms dischargedInputsOfConcreteCost
#print axioms hitMass_of_concrete

end Cogentic.RandomizedDischargedAdapters
