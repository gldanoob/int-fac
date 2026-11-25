import TwoThirdsCost
import TwoThirdsRank
import TwoThirdsWindow
import Cogentic.FixedSchedule
import Cogentic.AffineValuations
import Cogentic.ReconstructedOrder
import Cogentic.SearchSaturation
import Cogentic.WindowProgression
import Cogentic.WindowSaddle
import Cogentic.Marking
import Cogentic.PrincipalBand
import Lean.Util.CollectAxioms

/-! Fail the build if any of these public deductions acquires an additional axiom. -/
open Lean Elab Command in
run_cmd
  let endpoints := #[``Cogentic.Window.uniform_psi_from_critical_line,
    ``Cogentic.Window.clean_progression_error, ``Cogentic.Window.fixed_principal_prime_band,
    ``Cogentic.Window.principal_euler_saddle_mass, ``Cogentic.Window.poisson_exponent_expansion,
    ``Cogentic.Marking.retained_iff, ``Cogentic.clean_affine_unit_minor,
    ``Cogentic.reconstructed_order_hits, ``Cogentic.search_saturation,
    ``Cogentic.Fixed.fixed_factorization, ``Cogentic.Fixed.search_calls_leading]
  for endpoint in endpoints do
    for a in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Theorem {endpoint} depends on unexpected axiom {a}"
