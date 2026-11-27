import Cogentic.RandomizedSplitVerification

namespace Cogentic.RandomizedFactorSerialization

open scoped ArithmeticFunction.Omega

private def writeWord : List Bool → List Bool → List Bool × ℕ
  | [], tail => (false :: tail, 1)
  | bit :: bits, tail =>
    let out := writeWord bits tail
    (true :: bit :: out.1, out.2 + 2)

/-- Write an explicit stream terminator, a start and end marker per word,
and an escape bit before each payload bit. The counter charges each write. -/
def serialize : List (List Bool) → List Bool × ℕ
  | [] => ([false], 1)
  | word :: words =>
    let tail := serialize words
    let head := writeWord word tail.1
    (true :: head.1, head.2 + tail.2 + 1)

private def readWord : List Bool → Option (List Bool × List Bool)
  | false :: tail => some ([], tail)
  | true :: bit :: bits => (readWord bits).map (fun (word, tail) => (bit :: word, tail))
  | _ => none

private def readWords : ℕ → List Bool → Option (List (List Bool))
  | 0, _ => none
  | _ + 1, [false] => some []
  | fuel + 1, true :: bits =>
    match readWord bits with
    | none => none
    | some (word, tail) => (readWords fuel tail).map (word :: ·)
  | _ + 1, _ => none

/-- Decode one complete framed stream. Its bit length is sufficient fuel. -/
def decode (bits : List Bool) : Option (List (List Bool)) :=
  readWords bits.length bits

def decodeFactors (bits : List Bool) : Option (List ℕ) :=
  (decode bits).map (List.map BinaryDivision.value)

private theorem writeWord_spec (word tail : List Bool) :
    (writeWord word tail).1.length = 2 * word.length + 1 + tail.length ∧
      (writeWord word tail).2 = 2 * word.length + 1 := by
  induction word with
  | nil => simp [writeWord, Nat.add_comm]
  | cons bit bits ih =>
    simp only [writeWord, List.length_cons, ih.1, ih.2]
    omega

theorem serialize_spec (words : List (List Bool)) :
    (serialize words).1.length = 2 * (words.map List.length).sum + 2 * words.length + 1 ∧
      (serialize words).2 = 2 * (words.map List.length).sum + 2 * words.length + 1 := by
  induction words with
  | nil => simp [serialize]
  | cons word words ih =>
    have h := writeWord_spec word (serialize words).1
    simp only [serialize, List.length_cons, List.map_cons, List.sum_cons, h.1, h.2, ih.1, ih.2]
    omega

private theorem readWord_writeWord (word tail : List Bool) :
    readWord (writeWord word tail).1 = some (word, tail) := by
  induction word with
  | nil => rfl
  | cons bit bits ih => simp [writeWord, readWord, ih]

private theorem readWords_serialize (words : List (List Bool)) (fuel : ℕ)
    (hf : words.length < fuel) : readWords fuel (serialize words).1 = some words := by
  induction words generalizing fuel with
  | nil => cases fuel with
    | zero => simp at hf
    | succ fuel => rfl
  | cons word words ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have ht : words.length < fuel := Nat.lt_of_succ_lt_succ hf
      simp [serialize, readWords, readWord_writeWord, ih fuel ht]

theorem decode_serialize (words : List (List Bool)) : decode (serialize words).1 = some words := by
  apply readWords_serialize
  have h := (serialize_spec words).1
  omega

theorem decodeFactors_serialize (xs : List ℕ) :
    decodeFactors (serialize (xs.map Nat.bits)).1 = some xs := by
  simp only [decodeFactors, decode_serialize, Option.map_some, List.map_map, Function.comp_def,
    BinaryDivision.value_bits, List.map_id']

private def copyWord : List Bool → List Bool × ℕ
  | [] => ([], 0)
  | bit :: bits => let tail := copyWord bits; (bit :: tail.1, tail.2 + 1)

private theorem copyWord_spec (word : List Bool) :
    (copyWord word).1 = word ∧ (copyWord word).2 = word.length := by
  induction word with
  | nil => exact ⟨rfl, rfl⟩
  | cons bit bits ih => simp [copyWord, ih.1, ih.2]

/-- Copy each left-hand word and its list link onto the shared right-hand
suffix. The counter charges one per payload bit and one per copied link. -/
def copyAppend : List (List Bool) → List (List Bool) → List (List Bool) × ℕ
  | [], right => (right, 0)
  | word :: words, right =>
    let head := copyWord word
    let tail := copyAppend words right
    (head.1 :: tail.1, head.2 + tail.2 + 1)

theorem copyAppend_spec (left right : List (List Bool)) :
    (copyAppend left right).1 = left ++ right ∧
      (copyAppend left right).2 = (left.map List.length).sum + left.length := by
  induction left with
  | nil => simp [copyAppend]
  | cons word words ih =>
    obtain ⟨hword, hcost⟩ := copyWord_spec word
    simp only [copyAppend, hword, hcost, ih.1, ih.2, List.cons_append,
      List.length_cons, List.map_cons, List.sum_cons, true_and]
    omega

/-- A uniform per-node allowance for copying a recursively produced left list. -/
def mergeBudget (n : ℕ) : ℕ := 3 * n.log2

private theorem log2_mono_of_pos {a n : ℕ} (ha : 0 < a) (han : a ≤ n) :
    a.log2 ≤ n.log2 :=
  (Nat.le_log2 (ha.trans_le han).ne').mpr ((Nat.log2_self_le ha.ne').trans han)

private theorem run_two_le {n : ℕ} (run : TwoThirdsFactor.Run n) : 2 ≤ n := by
  induction run with
  | prime _ hp => exact hp.1
  | split l r hl hr =>
    exact hl.trans (Nat.le_mul_of_pos_right _ (by omega))

private theorem wordStats {n : ℕ} (run : TwoThirdsFactor.Run n) :
    2 ≤ n ∧ ((run.factors.map Nat.bits).map List.length).sum ≤ 2 * n.log2 ∧
      run.factors.length ≤ n.log2 := by
  obtain ⟨hp, hprime⟩ := run.correct
  have hmin : ∀ x ∈ run.factors, 2 ≤ x := fun x hx => (hprime x hx).1
  have hn := run_two_le run
  refine ⟨hn, ?_, (Nat.le_log2 (by omega : n ≠ 0)).mpr ?_⟩
  · have hbits : List.length ∘ Nat.bits = Nat.size := funext Nat.size_eq_bits_len
    rw [List.map_map, hbits]
    have h := RandomizedSplitVerification.factor_list_bits_le_twice_log2 _ hmin
    rw [hp] at h
    exact h
  · exact (List.pow_card_le_prod _ 2 hmin).trans_eq hp

/-- Copy each leaf word and concatenate the two recursively produced lists
using the same charged left-copy operation at each split. -/
def collect : {n : ℕ} → TwoThirdsFactor.Run n → List (List Bool) × ℕ
  | _, .prime p _ =>
    let word := copyWord p.bits
    ([word.1], word.2 + 1)
  | _, .split l r =>
    let left := collect l
    let right := collect r
    let out := copyAppend left.1 right.1
    (out.1, left.2 + right.2 + out.2)

theorem collect_spec {n : ℕ} (run : TwoThirdsFactor.Run n) :
    (collect run).1 = run.factors.map Nat.bits ∧ (collect run).2 ≤ run.work mergeBudget := by
  induction run with
  | prime p hp =>
    obtain ⟨hword, hcost⟩ := copyWord_spec p.bits
    have hs := Nat.size_le.mpr (Nat.lt_log2_self (n := p))
    rw [← Nat.size_eq_bits_len] at hs
    have hl : 1 ≤ p.log2 := (Nat.le_log2 (by have := hp.1; omega : p ≠ 0)).mpr hp.1
    simp only [collect, hword, hcost, TwoThirdsFactor.Run.factors, List.map_cons, List.map_nil,
      TwoThirdsFactor.Run.work, mergeBudget, true_and]
    omega
  | @split a b l r hl hr =>
    have ⟨ha, habits, halength⟩ := wordStats l
    have hb := (wordStats r).1
    have hlog := log2_mono_of_pos (show 0 < a by omega)
      (Nat.le_mul_of_pos_right a (show 0 < b by omega))
    obtain ⟨hwords, hcost⟩ := copyAppend_spec (l.factors.map Nat.bits) (r.factors.map Nat.bits)
    simp only [collect, hwords, hl.1, hr.1, TwoThirdsFactor.Run.factors, List.map_append,
      TwoThirdsFactor.Run.work, true_and, hcost, List.length_map, mergeBudget]
    have hleft := hl.2
    have hright := hr.2
    omega

/-- The final stream of a supported prime list decodes to that list and
adds only a linear output-write charge. -/
theorem primeListLaw_serialize
    (split : ∀ n, 2 ≤ n → ¬n.Prime → RandomizedSplitWork.SplitLaw n)
    {n : ℕ} (hn : 2 ≤ n) {xs : List ℕ}
    (hxs : xs ∈ (RandomizedSplitWork.primeListLaw split n hn).support) :
    let out := serialize (xs.map Nat.bits)
    decodeFactors out.1 = some xs ∧ out.1.length = out.2 ∧ out.2 ≤ 6 * n.log2 + 1 := by
  obtain ⟨hlen, hcost⟩ := serialize_spec (xs.map Nat.bits)
  refine ⟨decodeFactors_serialize xs, hlen.trans hcost.symm, ?_⟩
  rw [hcost, List.length_map]
  have hbits := RandomizedSplitVerification.primeListLaw_output_bitlength split hn hxs
  have hcount := RandomizedSplitWork.cardFactors_le_log2 n
  have hprimeCount : xs.length = Ω n :=
    (RandomizedSplitWork.primeListLaw_support_perm split hn hxs).length_eq
  omega

/-- Copy the complete factor list and serialize it. The counter is the
sum of the recursive copy/link charges and the framed output writes. -/
def emit {n : ℕ} (run : TwoThirdsFactor.Run n) : List Bool × ℕ :=
  let words := collect run
  let out := serialize words.1
  (out.1, words.2 + out.2)

theorem emit_spec {n : ℕ} (run : TwoThirdsFactor.Run n) :
    decodeFactors (emit run).1 = some run.factors ∧
      (emit run).2 ≤ (2 * n.log2 - 1) * (3 * n.log2) + (6 * n.log2 + 1) := by
  obtain ⟨hwords, hcopies⟩ := collect_spec run
  have hwork : run.work mergeBudget ≤ (2 * n.log2 - 1) * (3 * n.log2) := by
    apply run.work_bound
    intro a ha han
    exact Nat.mul_le_mul_left 3 (log2_mono_of_pos (by omega) han)
  have ⟨_, hbits, hcount⟩ := wordStats run
  have hwrites := (serialize_spec (run.factors.map Nat.bits)).2
  rw [List.length_map] at hwrites
  simp only [emit, hwords, decodeFactors_serialize, true_and, hwrites]
  omega

#print axioms serialize_spec
#print axioms decode_serialize
#print axioms decodeFactors_serialize
#print axioms copyAppend_spec
#print axioms collect_spec
#print axioms primeListLaw_serialize
#print axioms emit_spec

end Cogentic.RandomizedFactorSerialization
