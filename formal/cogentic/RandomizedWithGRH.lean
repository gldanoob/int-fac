import Main
import Cogentic.RandomizedPrimeBinProgression
import Cogentic.RandomizedPrimeBinSupply
import Cogentic.RandomizedRelativePrefix
import Cogentic.RandomizedPreprocessingCost

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

/-- Uniform character bounds for sharp prefixes of one prime-bin product pattern. -/
theorem primeBin_product_prefix : PrimeBinProductPrefixBound :=
  primeBin_product_prefix_from_critical_line LFunction_eq_zero_re

/-- The sharp prefix bound relative to the actual product population. -/
theorem primeBin_relative_prefix : PrimeBinRelativePrefixBound :=
  primeBin_relative_prefix_from_critical_line LFunction_eq_zero_re

/-- One fixed generator cutoff certifies all preprocessing decisions and
their polynomial bit cost throughout the recursive factoring algorithm. -/
theorem factoring_preprocessing :
    ∃ k : ℕ, ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n ∧
      (RandomizedPreprocessing.run k n).2 ≤ (10000*(k+1))^32*(n.log2+2)^32 :=
  RandomizedPreprocessing.of_critical_line LFunction_eq_zero_re

end Cogentic.Randomized

#print axioms Cogentic.Randomized.primeBin_product
#print axioms Cogentic.Randomized.primeBin_supply
#print axioms Cogentic.Randomized.primeBin_progression

#print axioms Cogentic.Randomized.primeBin_product_prefix
#print axioms Cogentic.Randomized.primeBin_relative_prefix

#print axioms Cogentic.Randomized.factoring_preprocessing
