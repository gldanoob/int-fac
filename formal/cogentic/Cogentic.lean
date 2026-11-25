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
import Cogentic.PrincipalResidue
import Cogentic.SaddleComparison
import Cogentic.GaussianJoint
import Cogentic.ConstructedFields
import Cogentic.ColumnAccuracy
import Cogentic.UnitMinor
import Cogentic.TargetUnits
import Cogentic.FieldSpecialization
import Cogentic.VerifiedCandidate
import Cogentic.SearchScale
import Cogentic.RankCoverage
import Cogentic.MarkDensity
import Cogentic.ProgressionCorrection
import Cogentic.GaussianGeometry
import Cogentic.SaddleConstructionScale
import Cogentic.RelativeAffine
import Cogentic.MarkTilts
import Cogentic.FixedPairCovariance
import Cogentic.ForcedRows
import Cogentic.CleanArithmetic
import Cogentic.GramPositivity
import Cogentic.ModelRank
import Cogentic.CellPairMoment
import Cogentic.DivisorCovariance
import Cogentic.PolynomialRetained
import Cogentic.ObservedScalar
import Cogentic.SmoothFamilies
import Cogentic.RetainedNullity
import Cogentic.JointSmoothBulk
import Cogentic.BackSubstitutionWork
import Cogentic.ModularPowerCost
import Cogentic.BinaryPivotCost
import Cogentic.AdmissionMoments
import Cogentic.TwoFieldRetentionLoss
import Cogentic.NearSmoothUpper
import Cogentic.NearPairVariance
import Cogentic.SquareDivisorPairs
import Cogentic.PolynomialExceptions
import Cogentic.MomentRows
import Cogentic.LogArithmeticCost
import Cogentic.MinorEnumerationCost
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
    ``Cogentic.Window.full_principal_mass, ``Cogentic.Window.neighboring_rankin_saddles,
    ``Cogentic.Window.fixed_full_principal_mass, ``Cogentic.Window.fixed_central_mass_lower,
    ``Cogentic.Window.fixed_relative_principal_mass, ``Cogentic.Window.fixed_character_relative,
    ``Cogentic.Construction.constructed_class_relative, ``Cogentic.Construction.scalar_progression_relative,
    ``Cogentic.Construction.grid_cells_have_marks, ``Cogentic.Construction.weighted_constructed_marks,
    ``Cogentic.Construction.weighted_pair_gamma, ``Cogentic.Construction.centered_pair_bound,
    ``Cogentic.Construction.centered_cell_pair_moment, ``Cogentic.Construction.PrescribedRows.box_witness,
    ``Cogentic.Construction.PrescribedRows.admission_probability,
    ``Cogentic.Construction.PrescribedRows.smooth_probability_lower, ``Cogentic.Construction.many_smooth_at_marks,
    ``Cogentic.Construction.many_smooth_in_grid_cell, ``Cogentic.Marking.avoids_badRows_iff_coprime,
    ``Cogentic.Construction.one_singular_slope, ``Cogentic.Construction.boxed_singular_slope_mass,
    ``Cogentic.Construction.PrescribedRows.boxed_ordinary_singular_loss,
    ``Cogentic.Construction.PrescribedRows.smooth_probability_margin,
    ``Cogentic.Construction.PrescribedRows.smooth_probability_avoid,
    ``Cogentic.Construction.PrescribedRows.joint_smooth_probability,
    ``Cogentic.Construction.PrescribedRows.joint_bulk_nominal,
    ``Cogentic.Construction.many_coprime_smooth_at_marks, ``Cogentic.Construction.many_retained_at_marks,
    ``Cogentic.Construction.cell_retained_kernel, ``Cogentic.Construction.constructed_columns_injective,
    ``Cogentic.Construction.retained_column_rank_bound, ``Cogentic.Construction.PrescribedRows.smooth_probability_avoid_sharp,
    ``Cogentic.Construction.PrescribedRows.boxed_ordinary_singular_loss_sharp,
    ``Cogentic.Construction.PrescribedRows.compatible_iff_listed, ``Cogentic.Construction.twoField_admission_moments,
    ``Cogentic.Construction.twoField_shared_or_singular_loss, ``Cogentic.Construction.PrescribedRows.joint_smooth_upper,
    ``Cogentic.Construction.cell_smooth_relative_close, ``Cogentic.Construction.twoField_score_error, ``Cogentic.Construction.twoField_simultaneous_box,
    ``Cogentic.Construction.fixed_square_prime_loss, ``Cogentic.Construction.cell_near_indicator_covariance,
    ``Cogentic.BinaryPivot.stageTwo_pivot_gates, ``Cogentic.BinaryModularPower.verify_exponent_iff,
    ``Cogentic.BinaryModularPower.fermatGuards_spec, ``Cogentic.BinaryModularPower.power_gates,
    ``Cogentic.BinaryDivision.divide_naturals, ``Cogentic.BinaryDivision.solve_normalization_gates,
    ``Cogentic.Elimination.solve_forward_remainder_bound, ``Cogentic.Elimination.solve_fill_bits_work,
    ``Cogentic.Elimination.solve_integer_family_bits,
    ``Cogentic.Window.fixed_divisibility_covariance, ``Cogentic.Construction.observed_second_scalar,
    ``Cogentic.Construction.PrescribedRows.first_probability, ``Cogentic.Construction.PrescribedRows.second_probability,
    ``Cogentic.Construction.first_polynomial_exceptional, ``Cogentic.Construction.coefficient_outside_weight,
    ``Cogentic.Construction.retained_from_polynomial_events, ``Cogentic.centered_bounds_of_local_entries,
    ``Cogentic.Elimination.solve_cross_product_bits, ``Cogentic.Elimination.solve_back_substitution_height,
    ``Cogentic.ArchNumerics.log_partial_fraction_height, ``Cogentic.MinorEnumeration.fixed_selection_visits,
    ``Cogentic.Window.mark_prime_weight, ``Cogentic.Window.omitted_prime_mass_uniform,
    ``Cogentic.Window.fixed_central_insertions, ``Cogentic.Window.fixed_all_shift_upper,
    ``Cogentic.Window.affine_gaussian_reduced, ``Cogentic.Window.marked_prime_classMass,
    ``Cogentic.Construction.one_point_window, ``Cogentic.Construction.two_point_window,
    ``Cogentic.Window.clean_residue_saddle_input,
    ``Cogentic.Window.eventual_fixed_saddle_wings, ``Cogentic.Window.fixed_band_power_savings,
    ``Cogentic.Window.fixed_middle_savings, ``Cogentic.Window.two_point_coprime_correction,
    ``Cogentic.Window.fixed_construction_window, ``Cogentic.Window.two_point_schedule_widths,
    ``Cogentic.Window.coefficient_fiber_crt, ``Cogentic.Window.polynomial_conditional_probability,
    ``Cogentic.Window.polynomial_first_probability, ``Cogentic.Window.root_conditioned_joint_probability,
    ``Cogentic.Construction.box_inputGuard, ``Cogentic.Construction.stageOne_succeeds,
    ``Cogentic.Construction.constructed_field_places, ``Cogentic.Construction.constructed_mark_logs,
    ``Cogentic.Construction.constructed_column_accuracy, ``Cogentic.constructed_target_observation,
    ``Cogentic.Construction.mark_density_from_critical_line, ``Cogentic.fixed_exponent_fits,
    ``Cogentic.Construction.MarkRing.order_from_affine_classes,
    ``Cogentic.computed_field_unit_minor, ``Cogentic.computed_helmert_unit_minor,
    ``Cogentic.ArchPrecision.fixed_selected_reconstruction, ``Cogentic.ArchPrecision.projected_mark_precision,
    ``Cogentic.Concrete.candidate_of_minor, ``Cogentic.Concrete.tryDivisor_of_coverage,
    ``Cogentic.Concrete.candidate_count_L_two_thirds,
    ``Cogentic.Concrete.fast_split_of_box_rank,
    ``Cogentic.fixed_nominal_grid_energy, ``Cogentic.stable_gram_deletion,
    ``Cogentic.Construction.retained_true_log_error, ``Cogentic.fixed_centered_model_margin,
    ``Cogentic.retained_norm_coordinates,
    ``Cogentic.twoFieldGram_of_perpendicular, ``Cogentic.positiveMarkCore_of_perpendicular,
    ``Cogentic.positiveMarkCore_of_centered_moments,
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
