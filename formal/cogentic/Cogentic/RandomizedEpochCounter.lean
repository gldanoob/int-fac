import Cogentic.RandomizedCappedTape
import Cogentic.RandomizedTrialFallback

namespace Cogentic.RandomizedEpochCounter

open BinaryDivision RandomizedCappedEpoch

/-- Subtract one across the entire stored word. The borrow is also the zero test. -/
def decrement (width : ℕ) (counter : List Bool) : Difference :=
  subtract width counter [] true

/-- The subtractor uses seven gates per bit and one branch gate for its borrow. -/
def checkBudget (width : ℕ) : ℕ := 7 * width + 1

theorem decrement_spec (width : ℕ) (counter : List Bool) (hwidth : counter.length = width) :
    let d := decrement width counter
    d.digits.length = width ∧ d.gates + 1 = checkBudget width ∧
    (d.borrow = true ↔ value counter = 0) ∧
    (d.borrow = false → value d.digits + 1 = value counter) := by
  obtain ⟨hlen, hgate, hval⟩ := subtract_spec width counter [] true hwidth.le (by simp)
  let d := decrement width counter
  change d.digits.length = width at hlen
  change d.gates = 7 * width at hgate
  change value d.digits + 0 + 1 = value counter + 2 ^ width * d.borrow.toNat at hval
  have hsmall := value_lt d.digits
  rw [hlen] at hsmall
  refine ⟨hlen, by rw [hgate, checkBudget], ?_, ?_⟩
  · cases h : d.borrow <;> simp [h] at hval ⊢ <;> omega
  · intro h
    change d.borrow = false at h
    rw [h] at hval
    simpa using hval

structure CounterResult (β : Type*) where
  result : β
  work : ℕ
  remaining : List Bool

/-- Run on a finite tape. An exhausted counter does not read the tape.
The tape is advanced by taking its tail, and `work` records gate charges. -/
def runCounter {α β : Type*} (attempt : α → Option β × ℕ) (fallback : Unit → β × ℕ)
    (width : ℕ) (counter : List Bool) (tape : List α) : CounterResult β :=
  let d := decrement width counter
  if d.borrow then
    let b := fallback ()
    ⟨b.1, d.gates + 1 + b.2, counter⟩
  else
    match tape with
    | [] =>
      let b := fallback ()
      ⟨b.1, d.gates + 1 + b.2, counter⟩
    | a :: tail =>
      let q := attempt a
      match q.1 with
      | some b => ⟨b, d.gates + 1 + (q.2 + 1), d.digits⟩
      | none =>
        let next := runCounter attempt fallback width d.digits tail
        ⟨next.result, d.gates + 1 + (q.2 + 1) + next.work, next.remaining⟩
termination_by structural tape

/-- Specification of how many blocks are read by the capped tape interpreter. -/
def tapeAttempts {α β : Type*} (attempt : α → Option β × ℕ) : List α → ℕ
  | [] => 0
  | a :: tape =>
    match (attempt a).1 with
    | some _ => 1
    | none => 1 + tapeAttempts attempt tape

theorem tapeAttempts_of_misses {α β : Type*} (attempt : α → Option β × ℕ)
    (tape : List α) (misses : ∀ a ∈ tape, (attempt a).1 = none) :
    tapeAttempts attempt tape = tape.length := by
  induction tape with
  | nil => rfl
  | cons a tail ih =>
    rw [tapeAttempts, misses a (by simp), ih (fun x hx => misses x (List.mem_cons_of_mem _ hx))]
    simp [Nat.add_comm]

/-- The original tape interpreter with the fixed-width charge attached to each
attempt and to the final exhausted-counter branch. -/
def chargedTape {α β : Type*} (attempt : α → Option β × ℕ) (fallback : Unit → β × ℕ)
    (width : ℕ) (tape : List α) : β × ℕ :=
  runTape (fun a => ((attempt a).1, checkBudget width + (attempt a).2))
    (fun u => ((fallback u).1, checkBudget width + (fallback u).2)) tape.length tape.get

/-- The bit counter returns the same outcome as the capped interpreter and
accounts for exactly the number of blocks it reads. Every live attempt and the
final zero test, when reached, pay the charge at the original width. -/
theorem runCounter_spec {α β : Type*} (attempt : α → Option β × ℕ)
    (fallback : Unit → β × ℕ) (width : ℕ) (counter : List Bool) (tape : List α)
    (hwidth : counter.length = width) (htape : value counter = tape.length) :
    let out := runCounter attempt fallback width counter tape
    out.result = (runTape attempt fallback tape.length tape.get).1 ∧
    (out.result, out.work) = chargedTape attempt fallback width tape ∧
    out.remaining.length = width ∧
    value out.remaining + tapeAttempts attempt tape = value counter := by
  induction tape generalizing counter with
  | nil =>
    obtain ⟨_, hgate, hzero, _⟩ := decrement_spec width counter hwidth
    have hb := hzero.mpr htape
    rw [runCounter]
    simp [hb, hgate, runTape, chargedTape, tapeAttempts, hwidth, htape]
  | cons a tail ih =>
    let d := decrement width counter
    obtain ⟨hlen, hgate, hzero, hpred⟩ := decrement_spec width counter hwidth
    have hb : d.borrow = false := Bool.eq_false_iff.mpr (fun h => by
      have hz := hzero.mp h
      simp [hz] at htape)
    have hnext := hpred hb
    have htail : value d.digits = tail.length := by
      change value d.digits + 1 = value counter at hnext
      simp only [List.length_cons] at htape
      omega
    rw [runCounter]
    cases hresult : (attempt a).1 with
    | some b =>
      simp [show (decrement width counter).borrow = false from hb, runTape, chargedTape,
        hresult, hgate, hlen, tapeAttempts, hnext, Nat.add_assoc]
    | none =>
      obtain ⟨hresultTail, hchargeTail, hwidthTail, hremainingTail⟩ := ih d.digits hlen htail
      simp only [show (decrement width counter).borrow = false from hb, Bool.false_eq_true,
        ↓reduceIte, hresult, chargedTape, List.length_cons, runTape, List.get_cons_zero,
        List.get_cons_succ', tapeAttempts]
      change (runCounter attempt fallback width d.digits tail).result = _ ∧ _
      refine ⟨hresultTail, ?_, hwidthTail, ?_⟩
      · let next := runCounter attempt fallback width d.digits tail
        let old := chargedTape attempt fallback width tail
        change (next.result, d.gates + 1 + ((attempt a).2 + 1) + next.work) =
          (old.1, checkBudget width + (attempt a).2 + 1 + old.2)
        change (next.result, next.work) = old at hchargeTail
        rw [← hchargeTail]
        have hd : d.gates + 1 = checkBudget width := hgate
        simp [hd, Nat.add_assoc]
      · change value (runCounter attempt fallback width d.digits tail).remaining +
          (1 + tapeAttempts attempt tail) = value counter
        rw [Nat.add_comm 1 (tapeAttempts attempt tail), ← Nat.add_assoc, hremainingTail]
        exact hnext

/-- The cap's canonical bits have the prescribed value and use at most the
existing linear width bound. Live iterations also branch on the attempt result. -/
theorem initializedCounter_spec (n : ℕ) :
    value (RandomizedTrialFallback.cap n).bits = RandomizedTrialFallback.cap n ∧
    checkBudget (RandomizedTrialFallback.cap n).bits.length + 1 ≤ 28 * n.size + 156 := by
  refine ⟨value_bits _, ?_⟩
  have hwidth : (RandomizedTrialFallback.cap n).bits.length ≤ 4 * n.size + 22 := by
    rw [Nat.size_eq_bits_len]
    exact RandomizedTrialFallback.cap_size_le n
  unfold checkBudget
  calc
    _ ≤ 7 * (4 * n.size + 22) + 1 + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 7 hwidth) 1) 1
    _ = _ := by ring

#print axioms decrement_spec
#print axioms runCounter_spec
#print axioms initializedCounter_spec

end Cogentic.RandomizedEpochCounter
