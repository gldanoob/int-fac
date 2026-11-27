import Cogentic.PowerScanCost
import Cogentic.RandomizedSplitWork
import TwoThirdsFactor

namespace Cogentic.RandomizedSplitVerification

open BinaryDivision
open scoped ArithmeticFunction.Omega Classical

/-- Check a candidate divisor on canonical input words and retain the
quotient word if the candidate is proper and the remainder is zero.
The counter uses the existing Boolean-gate model. -/
def verify (n d : ℕ) : Option (List Bool) × ℕ :=
  let proper := BinarySplitter.proper n.bits d.bits
  if proper.1 then
    let out := divide d.bits n.bits
    let zero := BinaryPowerScan.leBits out.remainder []
    (if zero.1 then some out.quotient else none, proper.2 + out.gates + zero.2 + 2)
  else (none, proper.2 + 1)

/-- Guard, restoring division, remainder check and two branch gates. -/
def verifierBudget (n : ℕ) : ℕ :=
  n.size * (20 * n.size + 1) + 28 * n.size + 4

theorem verify_spec {n d : ℕ} (hn : 0 < n) (hwidth : d.size ≤ n.size) :
    (verify n d).1.map value = (if TwoThirdsSearch.ProperDivisor n d then some (n / d) else none) ∧
      (verify n d).2 ≤ verifierBudget n := by
  have hpos : 0 < value n.bits := by simpa using hn
  have hb : d.bits.length ≤ n.bits.length := by simpa only [Nat.size_eq_bits_len] using hwidth
  obtain ⟨hproper, hproperCost⟩ := BinarySplitter.proper_spec n.bits d.bits hpos hb
  simp only [value_bits, Nat.size_eq_bits_len] at hproper hproperCost
  by_cases hp : 1 < d ∧ d < n
  · have hpass := hproper.mpr hp
    let out := divide d.bits n.bits
    let zero := BinaryPowerScan.leBits out.remainder []
    have hd : 0 < d := by omega
    obtain ⟨hquot, hrem, hcost⟩ := divide_naturals n d hd
    change value out.quotient = n / d at hquot
    change value out.remainder = n % d at hrem
    obtain ⟨hdivWidth, hremLen, _, _, _⟩ := divide_spec d.bits n.bits (by simpa using hd)
    obtain ⟨hzero, hzeroCost⟩ := BinaryPowerScan.leBits_spec out.remainder []
    change (zero.1 = true ↔ value out.remainder ≤ value []) at hzero
    have hcheck : zero.1 = true ↔ d ∣ n := by
      simpa only [value, hrem, Nat.le_zero, Nat.dvd_iff_mod_eq_zero] using hzero
    have hzeroBound : zero.2 ≤ 14 * n.size + 1 := by
      change out.width = d.bits.length + n.bits.length at hdivWidth
      change out.remainder.length ≤ out.width at hremLen
      simp only [Nat.size_eq_bits_len] at hdivWidth
      have hcost' : zero.2 = 7 * out.remainder.length + 1 := by
        simpa only [List.length_nil, max_zero] using hzeroCost
      omega
    have hdivBound : out.gates ≤ n.size * (20 * n.size + 1) :=
      hcost.trans (Nat.mul_le_mul_left _ (by omega))
    unfold verify
    rw [if_pos hpass]
    change (if zero.1 then some out.quotient else none).map value = _ ∧
      (BinarySplitter.proper n.bits d.bits).2 + out.gates + zero.2 + 2 ≤ _
    refine ⟨?_, ?_⟩
    · by_cases hdvd : d ∣ n
      · simp [hcheck.mpr hdvd, TwoThirdsSearch.ProperDivisor, hp.1, hp.2, hdvd, hquot]
      · have hz := Bool.eq_false_iff.mpr (fun he => hdvd (hcheck.mp he))
        simp [hz, TwoThirdsSearch.ProperDivisor, hdvd]
    · rw [hproperCost]
      unfold verifierBudget
      omega
  · have hfail : ¬ (BinarySplitter.proper n.bits d.bits).1 = true := fun h => hp (hproper.mp h)
    have hnot : ¬ TwoThirdsSearch.ProperDivisor n d := fun h => hp ⟨h.1, h.2.1⟩
    unfold verify
    rw [if_neg hfail, if_neg hnot]
    simp only [Option.map_none, true_and, hproperCost, verifierBudget]
    omega

/-- Each outcome of the abstract split law passes the concrete checker,
which reconstructs the second factor at the stated gate cost. -/
theorem splitLaw_outcome_verifies {n : ℕ} (s : RandomizedSplitWork.SplitLaw n)
    (p : ↥s.outcomes) :
    (verify n p.val.1).1.map value = some p.val.2 ∧ (verify n p.val.1).2 ≤ verifierBudget n := by
  obtain ⟨ha, hb, hab⟩ := s.proper p.val p.property
  have hlt : p.val.1 < n :=
    (lt_mul_of_one_lt_right (by omega : 0 < p.val.1) (by omega : 1 < p.val.2)).trans_eq hab
  have hdiv : p.val.1 ∣ n := ⟨p.val.2, hab.symm⟩
  have hd : TwoThirdsSearch.ProperDivisor n p.val.1 := ⟨by omega, hlt, hdiv⟩
  have hq : n / p.val.1 = p.val.2 := calc
    _ = (p.val.1 * p.val.2) / p.val.1 := congrArg (fun a => a / p.val.1) hab.symm
    _ = _ := Nat.mul_div_cancel_left _ (by omega)
  simpa only [if_pos hd, hq] using verify_spec (by omega : 0 < n) (Nat.size_le_size hlt.le)

/-- Counting bit lengths of a list of positive factors costs at most one
bit per factor beyond the binary logarithm of their product. -/
theorem factor_list_bits_le (xs : List ℕ) (hpos : ∀ x ∈ xs, 0 < x) :
    (xs.map Nat.size).sum ≤ xs.prod.log2 + xs.length := by
  have hsum : (xs.map Nat.size).sum = (xs.map Nat.log2).sum + xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := hpos x (by simp)
      have hxs : ∀ y ∈ xs, 0 < y := fun y hy => hpos y (by simp [hy])
      have h1 := Nat.size_le.mpr (Nat.lt_log2_self (n := x))
      have h2 := Nat.lt_size.mpr (Nat.log2_self_le hx.ne')
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih hxs]
      omega
  have hp : xs.prod ≠ 0 := by
    intro h
    exact (Nat.lt_irrefl 0) (hpos 0 (List.prod_eq_zero_iff.mp h))
  have hpow : 2 ^ (xs.map Nat.log2).sum ≤ xs.prod := by
    clear hsum hp
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := hpos x (by simp)
      have hxs : ∀ y ∈ xs, 0 < y := fun y hy => hpos y (by simp [hy])
      simp only [List.map_cons, List.sum_cons, Nat.pow_add, List.prod_cons]
      exact Nat.mul_le_mul (Nat.log2_self_le hx.ne') (ih hxs)
  rw [hsum]
  exact Nat.add_le_add_right ((Nat.le_log2 hp).mpr hpow) _

/-- A factor-list frontier of any complete or partial decomposition has
total binary width at most twice the logarithm of its product. -/
theorem factor_list_bits_le_twice_log2 (xs : List ℕ) (hmin : ∀ x ∈ xs, 2 ≤ x) :
    (xs.map Nat.size).sum ≤ 2 * xs.prod.log2 := by
  have hpos : ∀ x ∈ xs, 0 < x := fun x hx => Nat.zero_lt_two.trans_le (hmin x hx)
  have hp : xs.prod ≠ 0 := by
    intro h
    exact (Nat.lt_irrefl 0) (hpos 0 (List.prod_eq_zero_iff.mp h))
  have hlen := (Nat.le_log2 hp).mpr (List.pow_card_le_prod xs 2 hmin)
  exact (factor_list_bits_le xs hpos).trans (by omega)

theorem primeListLaw_output_bitlength
    (split : ∀ n, 2 ≤ n → ¬n.Prime → RandomizedSplitWork.SplitLaw n)
    {n : ℕ} (hn : 2 ≤ n) {xs : List ℕ}
    (hxs : xs ∈ (RandomizedSplitWork.primeListLaw split n hn).support) :
    ((xs.map Nat.bits).map List.length).sum ≤ n.log2 + Ω n := by
  obtain ⟨hprod, hprime⟩ := RandomizedSplitWork.primeListLaw_support_correct split hn hxs
  have hlen := (RandomizedSplitWork.primeListLaw_support_perm split hn hxs).length_eq
  have hbits : List.length ∘ Nat.bits = Nat.size := funext Nat.size_eq_bits_len
  rw [List.map_map, hbits, ArithmeticFunction.cardFactors_apply, ← hlen, ← hprod]
  exact factor_list_bits_le xs (fun p hp => (hprime p hp).pos)

/-- The deterministic call-count invariant also bounds the sum of local
verification budgets over any realized decomposition tree. -/
theorem verifierBudget_work_le {n : ℕ} (run : TwoThirdsFactor.Run n) :
    run.work verifierBudget ≤ (2 * n.log2 - 1) * verifierBudget n := by
  apply run.work_bound
  intro a _ ha
  unfold verifierBudget
  have hs := Nat.size_le_size ha
  gcongr

theorem verifierBudget_le_quadratic {n : ℕ} (hn : 0 < n) :
    verifierBudget n ≤ 53 * n.size ^ 2 := by
  have hs : 1 ≤ n.size := Nat.size_pos.mpr hn
  have hsq : n.size ≤ n.size * n.size := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n.size hs
  unfold verifierBudget
  nlinarith only [hs, hsq]

#print axioms verify_spec
#print axioms splitLaw_outcome_verifies
#print axioms factor_list_bits_le
#print axioms factor_list_bits_le_twice_log2
#print axioms primeListLaw_output_bitlength
#print axioms verifierBudget_work_le
#print axioms verifierBudget_le_quadratic

end Cogentic.RandomizedSplitVerification
