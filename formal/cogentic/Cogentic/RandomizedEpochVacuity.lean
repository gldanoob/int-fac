import Cogentic.RandomizedEpochAssembly

/-!
# Vacuity check for `HardEpochAsymptoticBound`

A zero-work epoch whose transcript data picks a square root by `Classical.choose`
satisfies `HardEpochAsymptoticBound _ 0`. The interface therefore does not charge
the computation of `publicRoot`, and the end-to-end theorem specialised to this
epoch would claim expected cost `exp(ε · scale n)` for every `ε > 0`.
-/

namespace Cogentic.RandomizedEpochAssembly.Vacuity

open Cogentic.RandomizedEpochSuccess Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedHiddenLabels Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedCostedFactorLaw Cogentic.RandomizedOneThirdAsymptotic
open Filter Real
open scoped ENNReal

noncomputable def squareSet (N : ℕ) [NeZero N] : Finset (ZMod N)ˣ :=
  Finset.univ.image fun u => u ^ 2

noncomputable def oracleEpoch (N : ℕ) (hN : 3 ≤ N) : HardEpochData N :=
  haveI : NeZero N := ⟨by omega⟩
  { Coins := Unit
    Label := Unit
    Public := (ZMod N)ˣ
    ideal := PMF.uniformOfFintype _
    actual := PMF.uniformOfFintype _
    trace := fun _ s => s ()
    good := squareSet N
    data := fun t =>
      { labels := {()}
        multiplicity := fun _ => 1
        publicRoot := Classical.choose (Finset.mem_image.mp t.2)
        privateIndex := ()
        mem_labels := Finset.mem_singleton_self _
        odd_multiplicity := odd_one }
    pubWork := fun _ => 0 }

theorem uniform_eq (α : Type) [Fintype α] [Nonempty α] (a b : α) :
    PMF.uniformOfFintype α a = PMF.uniformOfFintype α b := by
  rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]

theorem oracleEpoch_bound : HardEpochAsymptoticBound oracleEpoch 0 := by
  refine hardEpochAsymptoticBound_of_const_hit oracleEpoch (c := 1 / 2) (by norm_num) ?_
  intro δ hδ
  refine Filter.Eventually.of_forall fun n hN _ _ _ => ?_
  have : NeZero n := ⟨by omega⟩
  refine ⟨?_, ?_, 0, 1, 0, zero_le_one, ?_, (exp_pos _).le, ?_, ?_, by norm_num⟩
  · -- CongruenceCheck: (h ())^2 = publicRoot^2, and publicRoot^2 = observed square
    intro t x hx
    have hspec := Classical.choose_spec (Finset.mem_image.mp t.2)
    show (∏ i ∈ ({()} : Finset Unit), x.2 i ^ 1) ^ 2 =
      (Classical.choose (Finset.mem_image.mp t.2)) ^ 2
    rw [hspec.2, ← hx, Finset.prod_singleton, pow_one]
    rfl
  · -- HiddenUniform: the ideal law is uniform
    intro t x y _ _ _ _
    show (PMF.uniformOfFintype (Unit × (Unit → (ZMod n)ˣ))) x =
      (PMF.uniformOfFintype (Unit × (Unit → (ZMod n)ˣ))) y
    exact uniform_eq (Unit × (Unit → (ZMod n)ˣ)) x y
  · -- zero public work
    simp [oracleEpoch, mean]
  · -- every transcript is good
    have hall : {x : (oracleEpoch n hN).Sample |
        observe (oracleEpoch n hN).trace x ∈ (oracleEpoch n hN).good} = Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact Finset.mem_image.mpr ⟨x.2 (), Finset.mem_univ _, rfl⟩
    rw [hall, (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)]
    simp
  · -- ideal = actual, so TV = 0
    simp [pmfTotalVariation, oracleEpoch]

/-- The end-to-end theorem applied to the oracle epoch: an `L_N[1/3, ε]` bound for
every `ε > 0`, i.e. coefficient zero. -/
theorem oracle_end_to_end (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (RandomizedSerializedDriver.serializedFactor k sound
            (RandomizedInputDriver.epochHard (epochLaw oracleEpoch)
              (epochAttempt oracleEpoch)) n hn)
          (fun out => (out.2 : ℝ≥0∞)) ≤ ENNReal.ofReal (exp ((0 + ε) * scale n)) := by
  obtain ⟨k, sound, h⟩ := serialized_assembled_epoch_from_critical_line line
  exact ⟨k, sound, (h oracleEpoch le_rfl oracleEpoch_bound).2⟩

#print axioms oracleEpoch_bound
#print axioms oracle_end_to_end

end Cogentic.RandomizedEpochAssembly.Vacuity
