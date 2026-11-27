import Cogentic.RandomizedPaperLeafStatements
import Cogentic.RandomizedL18_4

/-!
# Replacing the L18.4 leaf by its explicit cell-count inputs

`RandomizedPaperLeafStatements.PaperAnalyticAssumptions` has one opaque field
`l18_4 : SubexpLeaf`.  `RandomizedL18_4.L18_4Inputs` decomposes that leaf into
the large-sieve/second-moment estimate, the RH cell counts, the rational-cell
partition, and the thin-pair fraction, and proves the resulting `SubexpLoss`
(hence the `SubexpLeaf`).

This file lets a caller supply the eleven remaining paper leaves separately and
the L18.4 inputs explicitly, then reassemble the full paper-assumption record.
It is a thin composition layer; it does not prove any of the remaining leaves.
-/

namespace Cogentic.RandomizedPaperL18_4

open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedL18_4

/-- The paper assumptions with the L18.4 leaf removed.  The other eleven
fields are exactly those of `PaperAnalyticAssumptions`. -/
structure PaperAnalyticAssumptionsWithoutL18_4
    (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ) where
  l19_4 : SubexpLeaf
  l19_5 : SubexpLeaf
  l19_6 : SubexpLeaf
  l20_2 : ConcentrationLeaf
  l20_4 : SubexpLeaf
  l21_2 : RatedLeaf
  l27_1 : RatedLeaf
  l30 : SubexpLeaf
  l34 : RatedLeaf
  l4_l25_l36 : AlgebraicLeaf
  p1 : P1Leaf

/-- Reassemble the full paper assumptions from the eleven remaining leaves and
an explicit L18.4 leaf. -/
def PaperAnalyticAssumptionsWithoutL18_4.toPaper
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptionsWithoutL18_4 E C) (l18_4 : SubexpLeaf) :
    PaperAnalyticAssumptions E C where
  l18_4 := l18_4
  l19_4 := P.l19_4
  l19_5 := P.l19_5
  l19_6 := P.l19_6
  l20_2 := P.l20_2
  l20_4 := P.l20_4
  l21_2 := P.l21_2
  l27_1 := P.l27_1
  l30 := P.l30
  l34 := P.l34
  l4_l25_l36 := P.l4_l25_l36
  p1 := P.p1

/-- The eleven remaining leaves plus the decomposed L18.4 inputs give the full
paper assumptions. -/
noncomputable def paperAssumptions_of_L18_4Inputs
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptionsWithoutL18_4 E C) (L : L18_4Inputs) :
    PaperAnalyticAssumptions E C :=
  P.toPaper L.toSubexpLeaf

#print axioms PaperAnalyticAssumptionsWithoutL18_4.toPaper
#print axioms paperAssumptions_of_L18_4Inputs

end Cogentic.RandomizedPaperL18_4
