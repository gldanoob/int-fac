import TwoThirdsCost
import TwoThirdsRank
import TwoThirdsWindow
import Cogentic.FixedSchedule
import Cogentic.AffineValuations
import Cogentic.ReconstructedOrder
import Cogentic.SearchSaturation
import Cogentic.WindowProgression
import Cogentic.WindowSaddle
import Cogentic.TotalFactor
import Cogentic.BinaryIrreducible
import Cogentic.EliminationBounds
import Cogentic.ConstructionHeight
import Cogentic.ArchSolve
import Cogentic.EliminationUnits
import Cogentic.Pivot
import Cogentic.SaddleLocation
import Lean.Util.CollectAxioms

/-! Fail the build if any of these public deductions acquires an additional axiom. -/
open Lean Elab Command in
run_cmd
  let endpoints := #[``Cogentic.Window.uniform_psi_from_critical_line,
    ``Cogentic.Window.clean_progression_error, ``Cogentic.Window.fixed_principal_prime_band,
    ``Cogentic.Window.prime_saddle_nonresonance, ``Cogentic.Window.saddle_pair_covariance_bernoulli,
    ``Cogentic.Window.prime_saddle_exists, ``Cogentic.Window.principal_product_off_center,
    ``Cogentic.Window.principal_euler_frequency_bound, ``Cogentic.Window.saddle_integral_edgeworth,
    ``Cogentic.Window.principal_euler_saddle_mass, ``Cogentic.Window.poisson_exponent_expansion,
    ``Cogentic.Construction.box_inputGuard, ``Cogentic.computed_field_unit_minor,
    ``Cogentic.certified_archimedean_reconstruction, ``Cogentic.RootLogs.markLog_error,
    ``Cogentic.Concrete.total_factorization, ``Cogentic.Concrete.tryDivisor_succeeds,
    ``Cogentic.stageTwo_height, ``Cogentic.Concrete.factor_of_box_coverage, ``Cogentic.Concrete.search_with_minor_choices,
    ``Cogentic.Elimination.stageTwo_verified, ``Cogentic.TryPair.saturated_size,
    ``Cogentic.bounded_clean_affine_pivot_minor, ``Cogentic.Marking.retained_iff, ``Cogentic.clean_affine_unit_minor,
    ``Cogentic.reconstructed_order_hits, ``Cogentic.search_saturation,
    ``Cogentic.Fixed.fixed_factorization, ``Cogentic.Fixed.search_calls_leading]
  for endpoint in endpoints do
    for a in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Theorem {endpoint} depends on unexpected axiom {a}"
