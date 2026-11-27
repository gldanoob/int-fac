import Cogentic.RandomizedFactorSerialization
import Cogentic.RandomizedInputDriver
import Cogentic.RandomizedOneThirdAsymptotic

namespace Cogentic.RandomizedSerializedDriver

open RandomizedCostedFactorLaw RandomizedFactorSerialization
open RandomizedInputDriver RandomizedOneThirdAsymptotic Filter Real
open scoped ENNReal

/-- Reserve this charge for all recursive copying, including copying the
binary prime at each leaf. Charge the actual number of framed output bits
separately. -/
def copyAllowance (n : ℕ) : ℕ :=
  (2 * n.log2 - 1) * (3 * n.log2)

theorem copies_le_allowance {n : ℕ} (run : TwoThirdsFactor.Run n) :
    (collect run).2 ≤ copyAllowance n := by
  refine (collect_spec run).2.trans (run.work_bound _ ?_)
  intro a ha han
  have ha0 : a ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  exact Nat.mul_le_mul_left 3 ((Nat.le_log2 hn0).mpr ((Nat.log2_self_le ha0).trans han))

def outputBudget (n : ℕ) : ℕ :=
  copyAllowance n + (6 * n.log2 + 1)

theorem outputBudget_le (n : ℕ) : outputBudget n ≤ 6 * (n.log2 + 1) ^ 2 := by
  have h : copyAllowance n ≤ 6 * n.log2 ^ 2 := by
    calc
      _ ≤ (2 * n.log2) * (3 * n.log2) :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = _ := by ring
  unfold outputBudget
  nlinarith only [h, Nat.zero_le n.log2]

private def chargeOutput (n : ℕ) (out : List ℕ × ℕ) : List Bool × ℕ :=
  let frame := serialize (out.1.map Nat.bits)
  (frame.1, out.2 + (copyAllowance n + frame.2))

/-- On each execution keep the joint output and charged work. The extra charge
is the actual final framing length plus a deterministic allowance for the
copy work of any realized recursive tree on this input. -/
noncomputable def serializedFactor (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (hard : HardKernel) (n : ℕ) (hn : 2 ≤ n) : PMF (List Bool × ℕ) :=
  (factor k sound hard n hn).map (chargeOutput n)

noncomputable def outputBits (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (hard : HardKernel) (n : ℕ) (hn : 2 ≤ n) : PMF (List Bool) :=
  (serializedFactor k sound hard n hn).map Prod.fst

variable (k : ℕ)
variable (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
variable (hard : HardKernel)

theorem outputBits_decode (n : ℕ) (hn : 2 ≤ n) :
    (outputBits k sound hard n hn).map decodeFactors =
      (factor k sound hard n hn).map (fun out => some out.1) := by
  simp [outputBits, serializedFactor, chargeOutput, PMF.map_comp, Function.comp_def,
    decodeFactors_serialize]

theorem outputBits_support_correct {n : ℕ} (hn : 2 ≤ n) {bits : List Bool}
    (hbits : bits ∈ (outputBits k sound hard n hn).support) :
    ∃ xs : List ℕ, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList := by
  rw [outputBits, PMF.mem_support_map_iff] at hbits
  obtain ⟨_, hout, rfl⟩ := hbits
  rw [serializedFactor, PMF.mem_support_map_iff] at hout
  obtain ⟨out, hout, rfl⟩ := hout
  exact ⟨out.1, decodeFactors_serialize _, factor_support_correct k sound hard hn hout⟩

private theorem frameBudget_le {n : ℕ} (hn : 2 ≤ n) {xs : List ℕ}
    (hx : xs.Perm n.primeFactorsList) :
    (serialize (xs.map Nat.bits)).2 ≤ 6 * n.log2 + 1 := by
  have hp : xs.prod = n := hx.prod_eq.trans (Nat.prod_primeFactorsList (by omega))
  have hmin : ∀ a ∈ xs, 2 ≤ a :=
    fun a ha => (Nat.prime_of_mem_primeFactorsList (hx.mem_iff.mp ha)).two_le
  have hlen : xs.length ≤ n.log2 :=
    (Nat.le_log2 (by omega : n ≠ 0)).mpr ((List.pow_card_le_prod xs 2 hmin).trans_eq hp)
  have hbits := RandomizedSplitVerification.factor_list_bits_le_twice_log2 xs hmin
  have hs : List.length ∘ Nat.bits = Nat.size := funext Nat.size_eq_bits_len
  rw [hp] at hbits
  rw [(serialize_spec _).2, List.length_map, List.map_map, hs]
  omega

/-- The serializer and copying add at most this deterministic overhead to
expected work. The estimate remains valid for arbitrary joint laws of
factorization outcomes and costs satisfying the driver's support theorem. -/
theorem serializedFactor_mean_le {n : ℕ} (hn : 2 ≤ n) :
    mean (serializedFactor k sound hard n hn) (fun out => out.2) ≤
      mean (factor k sound hard n hn) (fun out => out.2) + outputBudget n := by
  rw [serializedFactor, mean_map, ← mean_const (factor k sound hard n hn)
    (outputBudget n : ℝ≥0∞), ← mean_add]
  unfold mean
  refine ENNReal.tsum_le_tsum fun out => ?_
  by_cases hout : out ∈ (factor k sound hard n hn).support
  · have frame := frameBudget_le hn (factor_support_correct k sound hard hn hout)
    apply mul_le_mul_right
    change ((out.2 + (copyAllowance n + (serialize (out.1.map Nat.bits)).2) : ℕ) : ℝ≥0∞) ≤
      (out.2 : ℝ≥0∞) + (outputBudget n : ℝ≥0∞)
    rw [← Nat.cast_add]
    exact Nat.cast_le.mpr (Nat.add_le_add_left
      (Nat.add_le_add_left frame (copyAllowance n)) out.2)
  · have hzero : factor k sound hard n hn out = 0 := by
      by_contra h
      exact hout ((PMF.mem_support_iff _ _).mpr h)
    simp [hzero]

/-- Any exponent for the counted input driver persists after serialization
and recursive list copying. -/
theorem serializedFactor_expected_eventually {C : ℝ} (hC : 0 ≤ C)
    (hbase : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
      mean (factor k sound hard n hn) (fun out => out.2) ≤
        ENNReal.ofReal (exp ((C + ε) * scale n))) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
      mean (serializedFactor k sound hard n hn) (fun out => out.2) ≤
        ENNReal.ofReal (exp ((C + ε) * scale n)) := by
  intro ε hε
  have hδ : 0 < ε / 2 := by positivity
  filter_upwards [hbase (ε / 2) hδ, eventually_bitPoly_le_exp (A := 6) hδ 2,
    eventually_bitPoly_le_exp (A := 2) hδ 0, scale_grows.eventually_ge_atTop 0] with
    n hmean hpoly htwo hscale hn
  simp only [pow_zero, mul_one] at htwo
  have hcost : (outputBudget n : ℝ) ≤ exp ((C + ε / 2) * scale n) := calc
    _ ≤ 6 * ((n.log2 : ℝ) + 1) ^ 2 := by exact_mod_cast outputBudget_le n
    _ ≤ exp ((ε / 2) * scale n) := hpoly
    _ ≤ exp ((C + ε / 2) * scale n) :=
      exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hscale)
  have hcharge : (outputBudget n : ℝ≥0∞) ≤
      ENNReal.ofReal (exp ((C + ε / 2) * scale n)) := by
    simpa using ENNReal.ofReal_le_ofReal hcost
  calc
    _ ≤ ENNReal.ofReal (exp ((C + ε / 2) * scale n)) +
        ENNReal.ofReal (exp ((C + ε / 2) * scale n)) :=
      (serializedFactor_mean_le k sound hard hn).trans (add_le_add (hmean hn) hcharge)
    _ = ENNReal.ofReal (2 * exp ((C + ε / 2) * scale n)) := by
      rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le, two_mul]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ exp ((ε / 2) * scale n) * exp ((C + ε / 2) * scale n) :=
          mul_le_mul_of_nonneg_right htwo (exp_pos _).le
        _ = _ := by rw [← exp_add]; congr 1; ring

#print axioms copies_le_allowance
#print axioms outputBits_decode
#print axioms outputBits_support_correct
#print axioms serializedFactor_mean_le
#print axioms serializedFactor_expected_eventually

end Cogentic.RandomizedSerializedDriver
