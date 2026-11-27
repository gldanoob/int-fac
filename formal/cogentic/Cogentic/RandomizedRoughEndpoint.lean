import Cogentic.RandomizedEpochAssembly
import Cogentic.RandomizedSmallPrimePrepass
import Cogentic.RandomizedEpochOutput

/-!
# End-to-end randomized factoring with the hard epoch required only on rough inputs

The existing end-to-end theorem `RandomizedEpochAssembly.serialized_assembled_epoch_from_critical_line`
requires `HardEpochAsymptoticBound E C` on every hard input. Blueprint §0.2 observes that the
analytic epoch bound is only available on `B`-rough inputs (all prime factors larger than the
direct-class-sampler threshold `B = roughThreshold n = exp((log n)^(2/3))`); hard inputs with a
small prime factor must instead be routed to a prepass.

This file restates the endpoint in that shape:

* `HardEpochStepBound E C δ n` is the per-input part of `HardEpochAsymptoticBound E C` at fixed
  `δ` (the part quantified over `hN : 3 ≤ n`).
* `HardEpochRoughBound E C` is `HardEpochStepBound E C δ n` required only on
  `IsRough (roughThreshold n) n`, for every `δ > 0` and eventually in `n`.
* `rough_epoch_ratio_eventually` turns the rough-branch step bound into the exact per-input
  work/success ratio needed by the serialized driver.
* `combined_rough_epoch_ratio_eventually` combines the trial-division prepass with the rough
  main epoch, using `RandomizedSmallPrimePrepass.combined_epoch_asymptotic_logB`.
* `factor_expected_from_rough_epoch` is the driver-level theorem.

The trial-division prepass must scan up to `roughThreshold n = exp((log n)^(2/3))`, which is
*not* `exp(o(scale n))` (`scale n = (log n)^(1/3) (log log n)^(2/3)`); `trialPrepass_mean_work_le_exp`
only proves the bound for a cutoff `≤ exp(ε * scale n)` for every `ε > 0`. Consequently the
sub-exponential cost of the prepass is kept as the explicit hypothesis `hPreWork` in the main
theorem. The *splitting* behaviour of the small-prime branch is fully discharged by the counted
trial-division prepass (`trialPrepass_success_prob_one`), not assumed.

A second theorem, `factor_expected_from_affordable_prepass_and_rough_epoch`, uses a cutoff for
which that cost bound *is* proved by `trialPrepass_mean_work_le_exp`; the inputs whose smallest
prime factor lies between that cutoff and `roughThreshold n` are then exposed as the explicit
remaining "medium band" hypothesis `hMedium`.
-/

namespace Cogentic.RandomizedRoughEndpoint

open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochKernel
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedSmallPrimePrepass
open Cogentic.RandomizedVerifiedHiddenSplit
open Filter Real
open scoped ENNReal Topology

/-! ## The per-input step bound and its rough-branch restriction -/

/-- The per-input part of `HardEpochAsymptoticBound E C` at fixed `δ`: everything that the
asymptotic bound asserts on a single input `n`, uniformly over the proof `hN : 3 ≤ n`. -/
def HardEpochStepBound (E : ∀ n, 3 ≤ n → HardEpochData n) (C δ : ℝ) (n : ℕ) : Prop :=
  ∀ (hN : 3 ≤ n), Odd n → ¬n.Prime → ¬IsPrimePow n →
    (E n hN).CongruenceCheck ∧
    (E n hN).HiddenUniform ∧
    ∃ W_pub γ ε : ℝ,
      0 ≤ γ ∧
      mean (E n hN).actual (fun x => ((E n hN).pubWork x : ℝ≥0∞)) ≤ ENNReal.ofReal W_pub ∧
      W_pub ≤ exp ((C + δ / 2) * scale n) ∧
      γ ≤ ((E n hN).ideal.toOuterMeasure
        {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal ∧
      pmfTotalVariation (E n hN).ideal (E n hN).actual ≤ ε ∧
      exp (-(δ / 4) * scale n) ≤ γ / 2 - ε

/-- The same asymptotic bound, required only on `roughThreshold n`-rough hard inputs. -/
def HardEpochRoughBound (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ) : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    IsRough (roughThreshold n) n → HardEpochStepBound E C δ n

/-- Unfolding check: the old global bound is the un-restricted step bound. -/
theorem hardEpochAsymptoticBound_iff_step
    (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ) :
    HardEpochAsymptoticBound E C ↔
      ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, HardEpochStepBound E C δ n := by
  unfold HardEpochAsymptoticBound HardEpochStepBound
  rfl

/-- Integer trial-division cutoff reaching `roughThreshold n`. -/
noncomputable def roughCutoff (n : ℕ) : ℕ :=
  ⌊roughThreshold n⌋₊ + 1

theorem roughThreshold_le_roughCutoff (n : ℕ) :
    roughThreshold n ≤ (roughCutoff n : ℝ) := by
  have h := Nat.lt_floor_add_one (roughThreshold n)
  calc
    roughThreshold n ≤ (⌊roughThreshold n⌋₊ : ℝ) + 1 := h.le
    _ = ((⌊roughThreshold n⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
    _ = (roughCutoff n : ℝ) := by rfl

theorem eventually_roughThreshold_le_roughCutoff :
    ∀ᶠ n : ℕ in atTop, roughThreshold n ≤ (roughCutoff n : ℝ) :=
  Filter.Eventually.of_forall roughThreshold_le_roughCutoff

/-! ## Rough-branch ratio bound

This is `RandomizedEpochAssembly.assembled_epoch_ratio_eventually` with the global
`HardEpochAsymptoticBound` hypothesis replaced by `HardEpochRoughBound`; the conclusion is
therefore only asserted on `roughThreshold n`-rough inputs. -/

theorem rough_epoch_ratio_eventually
    (E : ∀ n, 3 ≤ n → HardEpochData n) {C : ℝ} (hC : 0 ≤ C)
    (hbound : HardEpochRoughBound E C) :
    ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n → IsRough (roughThreshold n) n →
        ∃ W S : ℝ, 0 < S ∧
          mean (epochLaw E n) (fun a => ((epochAttempt E n a).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
          S ≤ (((epochLaw E n).map (epochAttempt E n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
          W / S ≤ exp ((C + δ) * scale n) := by
  intro δ hδ
  filter_upwards [hbound δ hδ, eventually_ge_atTop (3 : ℕ),
    scale_grows.eventually_ge_atTop 0,
    eventually_trialBudget_add_two_le_exp (show 0 < δ / 2 by positivity),
    eventually_bitPoly_le_exp (A := 2) (show 0 < δ / 4 by positivity) 0]
    with n hn hN hscale htrial htwo ho hp hpow hrough
  simp only [pow_zero, mul_one] at htwo
  obtain ⟨hcheck, huniform, W_pub, γ, ε, hγ₀, hpub, hWpub, hγ, hTV, hSexp⟩ :=
    hn hrough hN ho hp hpow
  let W : ℝ := max 0 W_pub + ((trialBudget n + 2 : ℕ) : ℝ)
  let S : ℝ := γ / 2 - ε
  have hSpos : 0 < S := (exp_pos _).trans_le hSexp
  have hwork :
      mean (epochLaw E n) (fun a => ((epochAttempt E n a).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W := by
    rw [epochLaw_of_le E hN, mean_map]
    exact (E n hN).assembledAttempt_mean_work_le hN hpub
  have hhit :
      S ≤ (((epochLaw E n).map (epochAttempt E n)).toOuterMeasure {o | o.1 ≠ none}).toReal := by
    rw [epochLaw_of_le E hN, PMF.map_comp, epochAttempt_embed]
    exact (E n hN).assembledAttempt_hit_prob_ge hN ho hpow hcheck huniform hγ₀ hγ hTV
  have hWle : W ≤ exp ((C + 3 * δ / 4) * scale n) := by
    have hmax : max 0 W_pub ≤ exp ((C + δ / 2) * scale n) :=
      max_le (exp_pos _).le hWpub
    have htr : ((trialBudget n + 2 : ℕ) : ℝ) ≤ exp ((C + δ / 2) * scale n) :=
      htrial.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hscale))
    calc
      W ≤ 2 * exp ((C + δ / 2) * scale n) := by dsimp [W]; linarith only [hmax, htr]
      _ ≤ exp ((δ / 4) * scale n) * exp ((C + δ / 2) * scale n) :=
          mul_le_mul_of_nonneg_right htwo (exp_pos _).le
      _ = exp ((C + 3 * δ / 4) * scale n) := by
          rw [← exp_add]
          congr 1
          ring
  have hratio : W / S ≤ exp ((C + δ) * scale n) := by
    have hWnn : 0 ≤ W := add_nonneg (le_max_left 0 W_pub) (Nat.cast_nonneg _)
    calc
      W / S ≤ exp ((C + 3 * δ / 4) * scale n) / exp (-(δ / 4) * scale n) :=
        div_le_div₀ (exp_pos _).le hWle (exp_pos _) hSexp
      _ = exp ((C + δ) * scale n) := by
        rw [← exp_sub]
        congr 1
        ring
  exact ⟨W, S, hSpos, hwork, hhit, hratio⟩

/-! ## Discharging the small-prime branch with counted trial division

The next lemma shows that the prepass succeeds with probability `1` on every hard input having
a prime factor at most `Thr n`, provided the trial-division cutoff `T n` reaches `Thr n`. The
main-epoch work bound in the disjunction is never used in that case (`S_pre = 1`). -/

theorem trialPrepass_small_branch
    (E : ∀ n, 3 ≤ n → HardEpochData n) {C : ℝ}
    (Thr : ℕ → ℝ) (T : ℕ → ℕ)
    (hST : ∀ᶠ n : ℕ in atTop, Thr n ≤ (T n : ℝ)) :
    ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n → HasSmallPrimeFactor (Thr n) n →
        ∃ S_pre : ℝ, 0 < S_pre ∧
          S_pre ≤ (((trialPrepassEpoch n).map (trialPrepassAttempt T n)).toOuterMeasure
            {o | o.1 ≠ none}).toReal ∧
          1 / S_pre ≤ exp (δ * scale n) ∧
          (1 ≤ S_pre ∨
            mean (epochLaw E n) (fun b => ((epochAttempt E n b).2 + 1 : ℕ)) + 1 ≤
              ENNReal.ofReal (exp ((C + δ) * scale n))) := by
  intro δ hδ
  filter_upwards [hST, scale_grows.eventually_ge_atTop 0] with n hSTn hs
  intro _ho hp _hpp hsmall
  obtain ⟨p, hp_mem, hp_le⟩ := hsmall
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hn0 : n ≠ 0 := (Nat.mem_primeFactors.mp hp_mem).2.2
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
  have hn2 : 2 ≤ n := hp_prime.two_le.trans (Nat.le_of_dvd hnpos hdvd)
  have hsmallT : HasSmallPrimeFactor ((T n : ℕ) : ℝ) n :=
    ⟨p, hp_mem, hp_le.trans hSTn⟩
  have hsucc := trialPrepass_success_prob_one (B := T n) hn2 hp hsmallT
  have hsucc' : (((trialPrepassEpoch n).map (trialPrepassAttempt T n)).toOuterMeasure
      {o | o.1 ≠ none}) = 1 := by
    simpa [trialPrepassEpoch, trialPrepassAttempt] using hsucc
  refine ⟨1, one_pos, ?_, ?_, Or.inl le_rfl⟩
  · rw [hsucc', ENNReal.toReal_one]
  · rw [one_div_one]
    exact Real.one_le_exp (mul_nonneg hδ.le hs)

/-! ## Combined prepass + rough epoch ratio theorem -/

theorem combined_rough_epoch_ratio_eventually
    (E : ∀ n, 3 ≤ n → HardEpochData n) {C : ℝ} (hC : 0 ≤ C)
    (hPreWork : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
      mean (trialPrepassEpoch n)
        (fun a => ((trialPrepassAttempt roughCutoff n a).2 + 1 : ℕ)) + 1 ≤
        ENNReal.ofReal (exp (ε * scale n)))
    (hbound : HardEpochRoughBound E C) :
    ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
        ∃ W S : ℝ, 0 < S ∧
          mean (combEpoch (trialPrepassEpoch n) (epochLaw E n))
            (fun ab => ((combAttempt (trialPrepassAttempt roughCutoff n) (epochAttempt E n) ab).2 +
              1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
          S ≤ (((combEpoch (trialPrepassEpoch n) (epochLaw E n)).map
            (combAttempt (trialPrepassAttempt roughCutoff n) (epochAttempt E n))).toOuterMeasure
            {o | o.1 ≠ none}).toReal ∧
          W / S ≤ exp ((C + δ) * scale n) :=
  combined_epoch_asymptotic_logB
    (fun n => trialPrepassEpoch n) (fun n => trialPrepassAttempt roughCutoff n)
    (epochLaw E) (epochAttempt E) hC hPreWork
    (trialPrepass_small_branch E roughThreshold roughCutoff
      eventually_roughThreshold_le_roughCutoff)
    (rough_epoch_ratio_eventually E hC hbound)

/-! ## Driver-level theorem with the hard epoch only on rough inputs -/

theorem factor_expected_from_rough_epoch (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
      ∀ (E : ∀ n, 3 ≤ n → HardEpochData n) {C : ℝ}, 0 ≤ C →
        (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
          Odd n → ¬n.Prime → ¬IsPrimePow n →
          mean (trialPrepassEpoch n)
            (fun a => ((trialPrepassAttempt roughCutoff n a).2 + 1 : ℕ)) + 1 ≤
            ENNReal.ofReal (exp (ε * scale n))) →
        HardEpochRoughBound E C →
        (∀ n (hn : 2 ≤ n) bits,
          bits ∈ (outputBits k sound
            (epochHard (fun n => combEpoch (trialPrepassEpoch n) (epochLaw E n))
              (fun n => combAttempt (trialPrepassAttempt roughCutoff n) (epochAttempt E n)))
            n hn).support →
          ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
        ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
          mean (serializedFactor k sound
            (epochHard (fun n => combEpoch (trialPrepassEpoch n) (epochLaw E n))
              (fun n => combAttempt (trialPrepassAttempt roughCutoff n) (epochAttempt E n)))
            n hn) (fun out => (out.2 : ℝ≥0∞)) ≤
            ENNReal.ofReal (exp ((C + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ := serialized_epoch_from_critical_line line
  refine ⟨k, sound, fun E C hC hPreWork hbound => ?_⟩
  exact hmain
    (fun n => combEpoch (trialPrepassEpoch n) (epochLaw E n))
    (fun n => combAttempt (trialPrepassAttempt roughCutoff n) (epochAttempt E n))
    hC (combined_rough_epoch_ratio_eventually E hC hPreWork hbound)

/-! ## Variant with a prepass whose cost is proved

The theorem above keeps the sub-exponential cost of trial division up to `roughThreshold n` as
an explicit hypothesis, because that cutoff is larger than `exp(ε * scale n)`. The variant here
uses an *affordable* cutoff `T n` with `T n ≤ exp(ε * scale n)` for every `ε > 0`, so
`trialPrepass_mean_work_le_exp` proves the prepass work bound. What remains is exactly the
"medium band": hard inputs that are `T n`-rough but not `roughThreshold n`-rough, i.e. inputs
whose smallest prime factor lies in `(T n, roughThreshold n]`. For those inputs the main epoch
ratio is exposed as `hMedium`; the small-prime branch and the `roughThreshold`-rough branch are
both discharged. -/

theorem combined_affordable_prepass_rough_epoch_ratio_eventually
    (E : ∀ n, 3 ≤ n → HardEpochData n) {C : ℝ} (hC : 0 ≤ C)
    (T : ℕ → ℕ)
    (hT : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (T n : ℝ) ≤ exp (ε * scale n))
    (hMedium : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
      IsRough (T n : ℝ) n → ¬IsRough (roughThreshold n) n →
        ∃ W S : ℝ, 0 < S ∧
          mean (epochLaw E n) (fun a => ((epochAttempt E n a).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
          S ≤ (((epochLaw E n).map (epochAttempt E n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
          W / S ≤ exp ((C + δ) * scale n))
    (hbound : HardEpochRoughBound E C) :
    ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
        ∃ W S : ℝ, 0 < S ∧
          mean (combEpoch (trialPrepassEpoch n) (epochLaw E n))
            (fun ab => ((combAttempt (trialPrepassAttempt T n) (epochAttempt E n) ab).2 +
              1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
          S ≤ (((combEpoch (trialPrepassEpoch n) (epochLaw E n)).map
            (combAttempt (trialPrepassAttempt T n) (epochAttempt E n))).toOuterMeasure
            {o | o.1 ≠ none}).toReal ∧
          W / S ≤ exp ((C + δ) * scale n) := by
  refine combined_epoch_asymptotic (fun n => (T n : ℝ))
    (fun n => trialPrepassEpoch n) (fun n => trialPrepassAttempt T n)
    (epochLaw E) (epochAttempt E) hC ?_ ?_ ?_
  · intro ε hε
    exact (trialPrepass_mean_work_le_exp hT ε hε).mono
      (fun n hn _ _ _ => hn)
  · exact trialPrepass_small_branch E (fun n => (T n : ℝ)) T
      (Filter.Eventually.of_forall fun n => le_rfl)
  · intro δ hδ
    have hR := rough_epoch_ratio_eventually E hC hbound δ hδ
    have hM := hMedium δ hδ
    filter_upwards [hR, hM] with n hnR hnM
    intro ho hp hpp hroughT
    by_cases hRt : IsRough (roughThreshold n) n
    · exact hnR ho hp hpp hRt
    · exact hnM ho hp hpp hroughT hRt

theorem factor_expected_from_affordable_prepass_and_rough_epoch
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
      ∀ (E : ∀ n, 3 ≤ n → HardEpochData n) {C : ℝ}, 0 ≤ C →
        ∀ (T : ℕ → ℕ),
          (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (T n : ℝ) ≤ exp (ε * scale n)) →
          (∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
            Odd n → ¬n.Prime → ¬IsPrimePow n →
            IsRough (T n : ℝ) n → ¬IsRough (roughThreshold n) n →
              ∃ W S : ℝ, 0 < S ∧
                mean (epochLaw E n) (fun a => ((epochAttempt E n a).2 + 1 : ℕ)) + 1 ≤
                  ENNReal.ofReal W ∧
                S ≤ (((epochLaw E n).map (epochAttempt E n)).toOuterMeasure
                  {o | o.1 ≠ none}).toReal ∧
                W / S ≤ exp ((C + δ) * scale n)) →
          HardEpochRoughBound E C →
          (∀ n (hn : 2 ≤ n) bits,
            bits ∈ (outputBits k sound
              (epochHard (fun n => combEpoch (trialPrepassEpoch n) (epochLaw E n))
                (fun n => combAttempt (trialPrepassAttempt T n) (epochAttempt E n)))
              n hn).support →
            ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
          ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
            mean (serializedFactor k sound
              (epochHard (fun n => combEpoch (trialPrepassEpoch n) (epochLaw E n))
                (fun n => combAttempt (trialPrepassAttempt T n) (epochAttempt E n)))
              n hn) (fun out => (out.2 : ℝ≥0∞)) ≤
              ENNReal.ofReal (exp ((C + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ := serialized_epoch_from_critical_line line
  refine ⟨k, sound, fun E C hC T hT hMedium hbound => ?_⟩
  exact hmain
    (fun n => combEpoch (trialPrepassEpoch n) (epochLaw E n))
    (fun n => combAttempt (trialPrepassAttempt T n) (epochAttempt E n))
    hC (combined_affordable_prepass_rough_epoch_ratio_eventually E hC T hT hMedium hbound)

/-- Factor-level (pre-serialization) form, obtained directly from
`RandomizedSmallPrimePrepass.factor_expected_from_prepass_and_rough_epoch`. -/
theorem factor_expected_from_rough_epoch_factor_level (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
      ∀ (E : ∀ n, 3 ≤ n → HardEpochData n) {C : ℝ}, 0 ≤ C →
        (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
          Odd n → ¬n.Prime → ¬IsPrimePow n →
          mean (trialPrepassEpoch n)
            (fun a => ((trialPrepassAttempt roughCutoff n a).2 + 1 : ℕ)) + 1 ≤
            ENNReal.ofReal (exp (ε * scale n))) →
        HardEpochRoughBound E C →
        ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
          mean (factor k sound
            (epochHard (fun n => combEpoch (trialPrepassEpoch n) (epochLaw E n))
              (fun n => combAttempt (trialPrepassAttempt roughCutoff n) (epochAttempt E n)))
            n hn) (fun out => (out.2 : ℝ≥0∞)) ≤
            ENNReal.ofReal (exp ((C + ε) * scale n)) := by
  obtain ⟨k, prep⟩ := RandomizedPreprocessing.of_critical_line line
  refine ⟨k, fun n hn => (prep n hn).1, fun E C hC hPreWork hbound => ?_⟩
  exact factor_expected_from_prepass_and_rough_epoch k prep roughThreshold
    (fun n => trialPrepassEpoch n) (fun n => trialPrepassAttempt roughCutoff n)
    (epochLaw E) (epochAttempt E) hC hPreWork
    (trialPrepass_small_branch E roughThreshold roughCutoff
      eventually_roughThreshold_le_roughCutoff)
    (rough_epoch_ratio_eventually E hC hbound)

#print axioms hardEpochAsymptoticBound_iff_step
#print axioms roughThreshold_le_roughCutoff
#print axioms rough_epoch_ratio_eventually
#print axioms trialPrepass_small_branch
#print axioms combined_rough_epoch_ratio_eventually
#print axioms factor_expected_from_rough_epoch
#print axioms combined_affordable_prepass_rough_epoch_ratio_eventually
#print axioms factor_expected_from_affordable_prepass_and_rough_epoch
#print axioms factor_expected_from_rough_epoch_factor_level

end Cogentic.RandomizedRoughEndpoint
