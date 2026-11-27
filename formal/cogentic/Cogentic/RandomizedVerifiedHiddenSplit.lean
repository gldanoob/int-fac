import Cogentic.RandomizedHiddenOutputLaw
import Cogentic.RandomizedHiddenSplitLaw
import Cogentic.RandomizedSplitVerification

namespace Cogentic.RandomizedVerifiedHiddenSplit

open RandomizedHiddenLabels RandomizedSignCount RandomizedOddSplit
open RandomizedHiddenOutputLaw RandomizedHiddenSplitLaw RandomizedSplitVerification
open BinaryDivision BinaryModularPower
open scoped ENNReal

private theorem singletonMem : () ∈ ({()} : Finset Unit) := by simp

private def singletonRoot (N : ℕ) :
    SquareFiber (labelProduct ({()} : Finset Unit) (fun _ => 1) (fun _ => (1 : (ZMod N)ˣ))) :=
  ⟨1, by simp [labelProduct]⟩

private theorem singletonRatio {N : ℕ} (x : SquareFiber (1 : (ZMod N)ˣ)) :
    compareRoot (singletonRoot N)
      (replacementOutput {()} (fun _ => 1) (fun _ => 1) () singletonMem x) = x := by
  apply Subtype.ext
  simp [compareRoot, singletonRoot, replacementOutput, labelProduct]
  rfl

private def ratioTrial {N : ℕ} (x : SquareFiber (1 : (ZMod N)ˣ)) : Option (ProperPair N) :=
  hiddenSplitTrial {()} (fun _ => 1) (fun _ => 1) singletonMem (singletonRoot N) x

private theorem ratioTrial_accepts {N : ℕ} (x : SquareFiber (1 : (ZMod N)ˣ)) :
    ratioTrial x ≠ none ↔ 1 < splitGcd x ∧ splitGcd x < N := by
  simpa only [ratioTrial, singletonRatio] using
    hiddenSplitTrial_accepts {()} (fun _ => 1) (fun _ => 1) singletonMem (singletonRoot N) x

private theorem ratioTrial_pair {N : ℕ} (x : SquareFiber (1 : (ZMod N)ˣ))
    (outcome : ProperPair N) (h : ratioTrial x = some outcome) :
    outcome.val = (splitGcd x, N / splitGcd x) := by
  simpa only [singletonRatio] using
    hiddenSplitTrial_pair {()} (fun _ => 1) (fun _ => 1) singletonMem (singletonRoot N) x outcome h

/-- Subtract one from the canonical ratio, take its gcd with the modulus, and
check the resulting divisor and quotient. Work starts at the represented ratio. -/
def verifiedTrial {N : ℕ} (x : SquareFiber (1 : (ZMod N)ˣ)) : Option (ℕ × ℕ) × ℕ :=
  let difference := subtract N.size ((x.val : ZMod N).val.bits) [true] false
  let g := gcdBits difference.digits N.bits
  let d := value g.1
  let checked := verify N d
  (checked.1.map (fun q => (d, value q)), difference.gates + g.2 + checked.2)

/-- Gate budget for the post-ratio subtraction, gcd, and verifier. -/
def trialBudget (N : ℕ) : ℕ := 7 * N.size + gcdBudget N.size + verifierBudget N

private theorem verifiedTrial_spec {N : ℕ} (hN : 3 ≤ N) (x : SquareFiber (1 : (ZMod N)ˣ)) :
    (verifiedTrial x).1 = (ratioTrial x).map Subtype.val ∧ (verifiedTrial x).2 ≤ trialBudget N := by
  classical
  have : NeZero N := ⟨by omega⟩
  have : Fact (1 < N) := ⟨by omega⟩
  let r := (x.val : ZMod N).val
  have hr : 1 ≤ r := Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr (Units.ne_zero x.val))
  have hlt : r < N := ZMod.val_lt _
  let dif := subtract N.size r.bits [true] false
  have hlen : [true].length ≤ N.size := Nat.size_pos.mpr (by omega)
  obtain ⟨hwidth, hsubGate, hsub⟩ :=
    subtract_spec N.size r.bits [true] false
      (by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hlt.le) hlen
  change dif.digits.length = N.size at hwidth
  change dif.gates = 7 * N.size at hsubGate
  change value dif.digits + 1 + 0 = value r.bits + 2 ^ N.size * dif.borrow.toNat at hsub
  rw [value_bits] at hsub
  have hdif : value dif.digits = r - 1 := by
    have hbound := value_lt dif.digits
    rw [hwidth] at hbound
    cases hb : dif.borrow <;> simp [hb] at hsub <;> omega
  let g := gcdBits dif.digits N.bits
  have ⟨hg, _, hgGate⟩ := gcdBits_spec dif.digits N.bits N.size hwidth.le
    (by simp only [Nat.size_eq_bits_len, le_refl])
  have hgval : value g.1 = splitGcd x := by
    simpa only [g, hdif, value_bits, splitGcd, r] using hg
  have hgate : g.2 ≤ gcdBudget N.size := by
    have hdiffWidth : (value dif.digits).size ≤ N.size := by
      rw [hdif]
      exact Nat.size_le_size (by omega)
    have hc := (Elimination.gcdWithCount_le (value dif.digits) (value N.bits)).trans
      (Nat.mul_le_mul_left 2 hdiffWidth)
    exact hgGate.trans (by unfold gcdBudget; gcongr)
  let d := splitGcd x
  have hdvd : d ∣ N := Nat.gcd_dvd_right _ _
  have hdle : d ≤ N := Nat.le_of_dvd (by omega) hdvd
  obtain ⟨hver, hvGate⟩ := verify_spec (d := d) (by omega : 0 < N) (Nat.size_le_size hdle)
  change (Option.map (fun q => (value g.1, value q)) (verify N (value g.1)).1) = _ ∧
    dif.gates + g.2 + (verify N (value g.1)).2 ≤ _
  rw [hgval]
  change (Option.map (fun q => (d, value q)) (verify N d).1) = _ ∧
    dif.gates + g.2 + (verify N d).2 ≤ _
  refine ⟨?_, by unfold trialBudget; omega⟩
  have hvmap : (verify N d).1.map (fun q => (d, value q)) =
      ((verify N d).1.map value).map (Prod.mk d) := by
    rw [Option.map_map]
    rfl
  rw [hvmap, hver]
  cases ht : ratioTrial x with
  | none =>
    have hnot : ¬ TwoThirdsSearch.ProperDivisor N d := fun h =>
      (ratioTrial_accepts x).mpr ⟨h.1, h.2.1⟩ ht
    simp [hnot]
  | some pair =>
    have hproper := (ratioTrial_accepts x).mp (by simp [ht])
    have hvalid : TwoThirdsSearch.ProperDivisor N d := ⟨hproper.1, hproper.2, hdvd⟩
    simp [hvalid, ratioTrial_pair x pair ht, d]

variable {Coins Label Public : Type*} [DecidableEq Label] {N : ℕ}

/-- The charged divisor result on a positive-probability public transcript.
The label-coordinate mass symmetry is required before looking at the ratio. -/
theorem conditional_verified_split (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (input : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public) (transcript : Public)
    (labels : Finset Label) (multiplicity : Label → ℕ) (publicRoot : (ZMod N)ˣ)
    {i : Label} (hi : i ∈ labels) (hodd : Odd (multiplicity i))
    (hseen : ∃ x ∈ {x | observe trace x = transcript}, x ∈ input.support)
    (hcheck : ∀ x, observe trace x = transcript →
      (labelProduct labels multiplicity x.2) ^ 2 = publicRoot ^ 2)
    (huniform : ∀ x y, observe trace x = transcript → x.1 = y.1 →
      (x.2 i) ^ 2 = (y.2 i) ^ 2 → (∀ j, j ≠ i → x.2 j = y.2 j) → input x = input y) :
    let trial := (input.filter {x | observe trace x = transcript} hseen).map
      (fun x => verifiedTrial (comparisonRatio labels multiplicity publicRoot x.2))
    (trial.toOuterMeasure {outcome | outcome.1 ≠ none}).toReal =
      1 - 2 / (2 : ℝ)^N.primeFactors.card ∧
    ∀ outcome ∈ trial.support, outcome.2 ≤ trialBudget N ∧
      ∀ pair, outcome.1 = some pair → 2 ≤ pair.1 ∧ 2 ≤ pair.2 ∧ pair.1 * pair.2 = N := by
  classical
  have : NeZero N := ⟨by omega⟩
  have : Nonempty (SquareFiber (1 : (ZMod N)ˣ)) := ⟨⟨1, rfl⟩⟩
  let roots := (input.filter {x | observe trace x = transcript} hseen).map
    (fun x => comparisonRatio labels multiplicity publicRoot x.2)
  have hoddOne : Odd (1 : ℕ) := by decide
  have hu : roots =
      uniformHiddenRoot {()} (fun _ => 1) (fun _ => 1) singletonMem (singletonRoot N) hN ho hoddOne := by
    unfold roots
    rw [comparisonRatio_uniform input trace transcript labels multiplicity publicRoot
      hi hodd hseen hcheck huniform]
    unfold PMF.uniformOfFintype uniformHiddenRoot
    congr 1
    ext x
    simp
  have hmass := hiddenSplitLaw_acceptance {()} (fun _ => 1) (fun _ => 1) singletonMem
    (singletonRoot N) hN ho hnot hoddOne roots hu
  change ((roots.map ratioTrial).toOuterMeasure {outcome | outcome ≠ none}).toReal = _ at hmass
  have htrial := PMF.map_comp
    (fun x : Coins × (Label → (ZMod N)ˣ) => comparisonRatio labels multiplicity publicRoot x.2)
    (p := input.filter {x | observe trace x = transcript} hseen) (g := verifiedTrial)
  simp only [Function.comp_def] at htrial
  change (((input.filter {x | observe trace x = transcript} hseen).map
    (fun x => verifiedTrial (comparisonRatio labels multiplicity publicRoot x.2))).toOuterMeasure
    {outcome | outcome.1 ≠ none}).toReal = _ ∧ _
  rw [← htrial]
  refine ⟨?_, ?_⟩
  · rw [PMF.toOuterMeasure_map_apply] at hmass ⊢
    have hevent : verifiedTrial ⁻¹' {outcome : Option (ℕ × ℕ) × ℕ | outcome.1 ≠ none} =
        ratioTrial ⁻¹' {outcome : Option (ProperPair N) | outcome ≠ none} := by
      ext x
      change (verifiedTrial x).1 ≠ none ↔ ratioTrial x ≠ none
      rw [(verifiedTrial_spec hN x).1]
      cases ratioTrial x <;> simp
    rwa [hevent]
  · intro outcome hout
    obtain ⟨x, _, rfl⟩ := PMF.mem_support_map_iff _ _ _ |>.mp hout
    obtain ⟨hvalue, hcost⟩ := verifiedTrial_spec hN x
    refine ⟨hcost, fun pair heq => ?_⟩
    rw [hvalue] at heq
    cases h : ratioTrial x with
    | none => simp [h] at heq
    | some out =>
      have hv : out.val = pair := by simpa [h] using heq
      exact hv ▸ out.property

#print axioms conditional_verified_split

end Cogentic.RandomizedVerifiedHiddenSplit
