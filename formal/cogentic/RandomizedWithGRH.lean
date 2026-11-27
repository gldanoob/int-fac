import Main
import Cogentic.RandomizedPrimeBinProgression
import Cogentic.RandomizedPrimeBinSupply

namespace Cogentic.Randomized

/-- Uniform character cancellation for products drawn from sharp prime intervals. -/
theorem primeBin_product : PrimeBinProductBound :=
  primeBin_product_from_critical_line LFunction_eq_zero_re

/-- Uniform prime supply for the individual sharp intervals. -/
theorem primeBin_supply : PrimeBinSupplyBound :=
  primeBin_supply_from_critical_line LFunction_eq_zero_re

/-- Counts of the distinct product integers in each invertible residue class. -/
theorem primeBin_progression : PrimeBinProgressionBound :=
  primeBin_progression_of_product_bound primeBin_product

end Cogentic.Randomized

#print axioms Cogentic.Randomized.primeBin_product
#print axioms Cogentic.Randomized.primeBin_supply
#print axioms Cogentic.Randomized.primeBin_progression
