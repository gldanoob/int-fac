import Cogentic.RandomizedSplitWork
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Cogentic.RandomizedOneThirdAsymptotic

open Filter Real
open scoped BigOperators

/-- The natural-log scale in the exponent of (L_N[1/3,c]). -/
noncomputable def scale (n : ℕ) : ℝ :=
  (log n) ^ (1/3 : ℝ) * (log (log n)) ^ (2/3 : ℝ)

private theorem log_grows : Tendsto (fun n : ℕ => log n) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem scale_grows : Tendsto scale atTop atTop :=
  ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp log_grows).atTop_mul_atTop₀
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/3)).comp (tendsto_log_atTop.comp log_grows))

/-- The logarithm of a polynomial in the input length is negligible on this scale. -/
theorem logLog_isLittleO_scale :
    Asymptotics.IsLittleO atTop (fun n : ℕ => log (log n)) scale := by
  refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
  have small :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp_tendsto log_grows).def hε
  filter_upwards [small, log_grows.eventually_ge_atTop 1,
    (tendsto_log_atTop.comp log_grows).eventually_ge_atTop 1] with n hs hlog hloglog
  have hpow : 0 ≤ (log n) ^ (1/3 : ℝ) := rpow_nonneg (by linarith) _
  have hfactor : 1 ≤ (log (log n)) ^ (2/3 : ℝ) := one_le_rpow hloglog (by norm_num)
  have hle : (log n) ^ (1/3 : ℝ) ≤ scale n := le_mul_of_one_le_right hpow hfactor
  change ‖log (log n)‖ ≤ ε * ‖(log n) ^ (1/3 : ℝ)‖ at hs
  rw [Real.norm_of_nonneg hpow] at hs
  rw [Real.norm_of_nonneg (hpow.trans hle)]
  exact hs.trans (mul_le_mul_of_nonneg_left hle hε.le)

private theorem eventually_affine_logLog_le {ε : ℝ} (hε : 0 < ε)
    (a b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop, a + b * log (log n) ≤ ε * scale n := by
  have hδ : 0 < ε / (2 * (b + 1)) := by positivity
  filter_upwards [scale_grows.eventually_ge_atTop (max 0 (a / (ε / 2))),
    logLog_isLittleO_scale.def hδ,
    (tendsto_log_atTop.comp log_grows).eventually_ge_atTop 1] with n hscale hlog hn
  have hscale₀ : 0 ≤ scale n := (le_max_left ..).trans hscale
  have ha := (div_le_iff₀ (show 0 < ε / 2 by positivity)).mp ((le_max_right ..).trans hscale)
  change 1 ≤ log (log n) at hn
  change ‖log (log n)‖ ≤ _ at hlog
  rw [Real.norm_of_nonneg hscale₀, Real.norm_of_nonneg (zero_le_one.trans hn)] at hlog
  have hcoeff : b * (ε / (2 * (b + 1))) ≤ ε / 2 := by
    calc
      _ ≤ (b + 1) * (ε / (2 * (b + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = _ := by field_simp
  calc
    _ ≤ (ε / 2) * scale n + b * ((ε / (2 * (b + 1))) * scale n) :=
      add_le_add (by simpa [mul_comm] using ha) (mul_le_mul_of_nonneg_left hlog hb)
    _ ≤ ε * scale n := by
      rw [← mul_assoc, ← add_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) hscale₀

/-- Every fixed polynomial in the binary input length fits in any positive exponent slack. -/
theorem eventually_bitPoly_le_exp {ε A : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, A * ((n.log2 : ℝ) + 1) ^ k ≤ exp (ε * scale n) := by
  let B := 1 + 1 / log 2
  let D := max 1 A * B ^ k
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := mul_pos (zero_lt_one.trans_le (le_max_left ..)) (pow_pos hB _)
  filter_upwards [log_grows.eventually_ge_atTop 1,
    eventually_affine_logLog_le hε (log D) k (Nat.cast_nonneg k)] with n hn hbudget
  have hlog : 0 < log n := zero_lt_one.trans_le hn
  have hbits : (n.log2 : ℝ) + 1 ≤ B * log n := by
    have h := Real.log2_le_logb n
    rw [Real.logb] at h
    dsimp [B]
    rw [add_mul, one_mul, one_div_mul_eq_div]
    linarith only [hn, h]
  calc
    _ ≤ max 1 A * (B * log n) ^ k := by
      gcongr
      exact le_max_right _ _
    _ = D * (log n) ^ k := by rw [mul_pow, ← mul_assoc]
    _ = exp (log D + (k : ℝ) * log (log n)) := by
      rw [← log_pow, exp_add, exp_log hD, exp_log (pow_pos hlog _)]
    _ ≤ _ := exp_le_exp.mpr hbudget

/-- The complete binary recursion changes the one-third exponent by arbitrarily little. -/
theorem eventually_work_le_exp {E T : ℕ → ℝ} {c ε : ℝ} (hε : 0 < ε)
    (hlocal : ∀ᶠ n : ℕ in atTop, T n ≤ exp (c * scale n))
    (hwork : ∀ n, 2 ≤ n → E n ≤ (2 * (n.log2 : ℝ) - 1) * T n) :
    ∀ᶠ n : ℕ in atTop, E n ≤ exp ((c + ε) * scale n) := by
  filter_upwards [hlocal, eventually_ge_atTop 2,
    eventually_bitPoly_le_exp (A := 2) hε 1] with n hT hn hp
  have hlog : (1 : ℝ) ≤ n.log2 := by
    exact_mod_cast (Nat.le_log2 (show n ≠ 0 by omega)).mpr (show 2 ^ 1 ≤ n by simpa using hn)
  have hpoly : 2 * (n.log2 : ℝ) - 1 ≤ exp (ε * scale n) := by
    simp only [pow_one] at hp
    linarith only [hp]
  calc
    _ ≤ (2 * (n.log2 : ℝ) - 1) * T n := hwork n hn
    _ ≤ (2 * (n.log2 : ℝ) - 1) * exp (c * scale n) :=
      mul_le_mul_of_nonneg_left hT (by linarith only [hlog])
    _ ≤ exp (ε * scale n) * exp (c * scale n) :=
      mul_le_mul_of_nonneg_right hpoly (exp_pos _).le
    _ = _ := by rw [← exp_add, add_mul, add_comm (c * scale n)]

/-- Lift eventual local charges through a proper-split recurrence. A monotone
majorant covers the finitely many sizes below the asymptotic threshold. -/
theorem eventually_work_le_exp_of_recurrence {E T : ℕ → ℝ}
    (split : ∀ n, 2 ≤ n → ¬n.Prime → RandomizedSplitWork.SplitLaw n)
    (hE : ∀ n, 0 ≤ E n) (hprime : ∀ n, n.Prime → E n ≤ T n)
    (hrec : ∀ n (hn : 2 ≤ n) (hp : ¬n.Prime),
      E n ≤ T n + (split n hn hp).expectedChildCharge E)
    {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (hlocal : ∀ᶠ n : ℕ in atTop, T n ≤ exp (c * scale n)) :
    ∀ᶠ n : ℕ in atTop, E n ≤ exp ((c + ε) * scale n) := by
  classical
  have tail := hlocal.and ((log_grows.eventually_ge_atTop 1).and
    (eventually_ge_atTop (2 : ℕ)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp tail
  let K := ∑ n ∈ Finset.range N, |T n|
  let major (n : ℕ) := max K (exp (c * scale (max n N)))
  have hmono : Monotone major := by
    intro a b hab
    have ha := (hN _ (le_max_right a N)).2
    have hlog : log (max a N : ℕ) ≤ log (max b N : ℕ) :=
      log_le_log (by exact_mod_cast (show 0 < max a N by omega))
        (by exact_mod_cast (max_le_max_right N hab))
    have hscale : scale (max a N) ≤ scale (max b N) := by
      unfold scale
      apply mul_le_mul
      · exact rpow_le_rpow (zero_le_one.trans ha.1) hlog (by norm_num)
      · exact rpow_le_rpow (log_nonneg ha.1)
          (log_le_log (zero_lt_one.trans_le ha.1) hlog) (by norm_num)
      · exact rpow_nonneg (log_nonneg ha.1) _
      · exact rpow_nonneg ((zero_le_one.trans ha.1).trans hlog) _
    exact max_le_max_left K (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hscale hc))
  have hmajor (n : ℕ) : T n ≤ major n := by
    by_cases hn : N ≤ n
    · have h : T n ≤ exp (c * scale (max n N)) := by
        simpa only [max_eq_left hn] using (hN n hn).1
      exact h.trans (le_max_right ..)
    · have h := Finset.single_le_sum (f := fun n => |T n|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (lt_of_not_ge hn))
      exact (le_abs_self _).trans (h.trans (le_max_left ..))
  have hδ : 0 < ε/2 := by positivity
  have hmajor_exp : ∀ᶠ n : ℕ in atTop, major n ≤ exp ((c + ε/2) * scale n) := by
    filter_upwards [eventually_ge_atTop N, scale_grows.eventually_ge_atTop 0,
      eventually_bitPoly_le_exp (A := K) hδ 0] with n hn hs hk
    simp only [pow_zero, mul_one] at hk
    apply max_le
    · exact hk.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hs))
    · rw [max_eq_left hn]
      exact exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hs)
  rw [show c + ε = (c + ε/2) + ε/2 by ring]
  exact eventually_work_le_exp hδ hmajor_exp
    (RandomizedSplitWork.expected_work_le_log2 E major split hE hmono
      (fun n hp => (hprime n hp).trans (hmajor n))
      (fun n hn hp => (hrec n hn hp).trans (add_le_add (hmajor n) le_rfl)))

/-- For a single work function dominated by each member of a parameter family
up to a fixed polynomial overhead, the family can approach the endpoint with
the parameter chosen before taking the input limit. -/
theorem eventually_work_le_exp_of_approximants {ι : Type*} {C : ℝ}
    (hC : 0 ≤ C) (work : ℕ → ℝ) (charge : ι → ℕ → ℝ)
    (cost overhead : ι → ℝ) (degree : ι → ℕ)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ i, cost i ≤ C + δ)
    (hcharge : ∀ i, ∀ᶠ n : ℕ in atTop, charge i n ≤ exp (cost i * scale n))
    (hpoly : ∀ i, ∀ᶠ n : ℕ in atTop,
      work n ≤ overhead i * ((n.log2 : ℝ) + 1) ^ (degree i) * max 1 (charge i n)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, work n ≤ exp ((C + ε) * scale n) := by
  intro ε hε
  have hδ : 0 < ε/2 := by positivity
  obtain ⟨i, hi⟩ := happrox (ε/2) hδ
  filter_upwards [hcharge i, hpoly i, scale_grows.eventually_ge_atTop 0,
    eventually_bitPoly_le_exp (A := max 0 (overhead i)) hδ (degree i)] with n hn hw hs hp
  have hbound : max 1 (charge i n) ≤ exp ((C + ε/2) * scale n) :=
    max_le (one_le_exp (mul_nonneg (by linarith) hs))
      (hn.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hi hs)))
  calc
    _ ≤ max 0 (overhead i) * ((n.log2 : ℝ) + 1) ^ (degree i) * max 1 (charge i n) := by
      refine hw.trans ?_
      gcongr
      exact le_max_right ..
    _ ≤ exp (ε/2 * scale n) * exp ((C + ε/2) * scale n) := by
      exact mul_le_mul hp hbound (zero_le_one.trans (le_max_left ..)) (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

/-- A work bound at the one-third scale bounds the number of bits needed to
write the work budget. The constant may depend on a fixed algorithm index. -/
theorem eventually_log_charge_le_bitLength {T : ℕ → ℝ} {c : ℝ} (a : ℝ)
    (hT : ∀ᶠ n : ℕ in atTop, T n ≤ exp (c * scale n)) :
    ∃ B > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      a + log (2 + max 1 (T n)) ≤ B * ((n.log2 : ℝ) + 1) := by
  let B := max 0 (a + log 3) + max 0 c * log 2 + 1
  have hc : 0 ≤ max 0 c := le_max_left ..
  have hB : 0 < B := by
    dsimp [B]
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (le_max_left ..) (mul_nonneg hc (log_nonneg (by norm_num)))) zero_lt_one
  refine ⟨B, hB, ?_⟩
  filter_upwards [hT, log_grows.eventually_ge_atTop 1, eventually_ge_atTop (2 : ℕ)]
    with n hn hlog hn₂
  have hs : 0 ≤ scale n := mul_nonneg (rpow_nonneg (zero_le_one.trans hlog) _)
    (rpow_nonneg (log_nonneg hlog) _)
  have hlogs : log (log n) ≤ log n := by
    linarith only [log_le_sub_one_of_pos (zero_lt_one.trans_le hlog)]
  have hscale : scale n ≤ log n := by
    unfold scale
    calc
      _ ≤ (log n) ^ (1/3 : ℝ) * (log n) ^ (2/3 : ℝ) :=
        mul_le_mul_of_nonneg_left (rpow_le_rpow (log_nonneg hlog) hlogs (by norm_num))
          (by positivity)
      _ = _ := by rw [← rpow_add (zero_lt_one.trans_le hlog)]; norm_num
  have hbits : 1 ≤ (n.log2 : ℝ) + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) n.log2]
  have hlogbits : log n ≤ ((n.log2 : ℝ) + 1) * log 2 := by
    calc
      _ ≤ log ((2 : ℝ) ^ (n.log2 + 1)) :=
        log_le_log (by exact_mod_cast (show 0 < n by omega))
          (by exact_mod_cast (Nat.lt_log2_self (n := n)).le)
      _ = _ := by rw [log_pow, Nat.cast_add, Nat.cast_one]
  have hcap : max 1 (T n) ≤ exp (max 0 c * scale n) :=
    max_le (one_le_exp (mul_nonneg hc hs))
      (hn.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right ..) hs)))
  have hlogcap : log (2 + max 1 (T n)) ≤ log 3 + max 0 c * scale n := by
    calc
      _ ≤ log (3 * exp (max 0 c * scale n)) := by
        apply log_le_log (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 + 1)
          (add_le_add le_rfl (le_max_left ..)))
        linarith only [hcap, one_le_exp (mul_nonneg hc hs)]
      _ = _ := by rw [log_mul (by norm_num) (exp_ne_zero _), log_exp]
  calc
    _ ≤ (a + log 3) + max 0 c * scale n := by linarith only [hlogcap]
    _ ≤ max 0 (a + log 3) * ((n.log2 : ℝ) + 1) +
        max 0 c * (((n.log2 : ℝ) + 1) * log 2) :=
      add_le_add ((le_max_right ..).trans (le_mul_of_one_le_right (le_max_left ..) hbits))
        (mul_le_mul_of_nonneg_left (hscale.trans hlogbits) hc)
    _ ≤ _ := by dsimp [B]; nlinarith only [hbits]

/-- The same fixed-index transfer allows polynomial charge in the bit length
of the work budget, as used for the phase counters of a restart scheduler. -/
theorem eventually_work_le_exp_of_approximants_logCharge {ι : Type*} {C : ℝ}
    (hC : 0 ≤ C) (work : ℕ → ℝ) (charge : ι → ℕ → ℝ)
    (cost overhead offset : ι → ℝ) (degree counterDegree : ι → ℕ)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ i, cost i ≤ C + δ)
    (hcharge : ∀ i, ∀ᶠ n : ℕ in atTop, charge i n ≤ exp (cost i * scale n))
    (hpoly : ∀ i, ∀ᶠ n : ℕ in atTop,
      work n ≤ overhead i * ((n.log2 : ℝ) + 1) ^ (degree i) *
        (max 1 (offset i + log (2 + max 1 (charge i n)))) ^ (counterDegree i) *
        max 1 (charge i n)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, work n ≤ exp ((C + ε) * scale n) := by
  choose B hB hlog using fun i => eventually_log_charge_le_bitLength (offset i) (hcharge i)
  refine eventually_work_le_exp_of_approximants hC work charge cost
    (fun i => max 0 (overhead i) * (B i + 1) ^ (counterDegree i))
    (fun i => degree i + counterDegree i) happrox hcharge fun i => ?_
  filter_upwards [hpoly i, hlog i] with n hw hbound
  let x := (n.log2 : ℝ) + 1
  have hx : 1 ≤ x := by dsimp [x]; linarith only [Nat.cast_nonneg (α := ℝ) n.log2]
  have htotal : max 1 (offset i + log (2 + max 1 (charge i n))) ≤ (B i + 1) * x := by
    rw [add_mul, one_mul]
    have hb : 0 ≤ B i * x := mul_nonneg (hB i).le (zero_le_one.trans hx)
    exact max_le (by linarith only [hb, hx]) (by linarith only [hbound, hx])
  calc
    _ ≤ max 0 (overhead i) * x ^ (degree i) * ((B i + 1) * x) ^ (counterDegree i) *
        max 1 (charge i n) := by
      refine hw.trans ?_
      gcongr
      exact le_max_right ..
    _ = _ := by change _ = (_ * x ^ (_ + _)) * _; rw [mul_pow, pow_add]; ring

#print axioms logLog_isLittleO_scale
#print axioms eventually_bitPoly_le_exp
#print axioms eventually_work_le_exp
#print axioms eventually_work_le_exp_of_recurrence
#print axioms eventually_work_le_exp_of_approximants
#print axioms eventually_log_charge_le_bitLength
#print axioms eventually_work_le_exp_of_approximants_logCharge

end Cogentic.RandomizedOneThirdAsymptotic
