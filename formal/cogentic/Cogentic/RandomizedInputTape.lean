import Cogentic.RandomizedInputDriver
import Cogentic.RandomizedTotalEpochSplit

namespace Cogentic.RandomizedInputTape

open RandomizedCostedFactorLaw RandomizedEpochKernel RandomizedInputDriver

/-- An epoch block is addressed by its node's binary path and retry index.
The current input selects the block type. -/
abbrev Tape (α : ℕ → Type*) := List Bool → (n : ℕ) → ℕ → α n

abbrev HardSplitter (α : ℕ → Type*) :=
  ∀ n : ℕ, 2 ≤ n → Odd n → ¬n.Prime → ¬IsPrimePow n → (ℕ → α n) → SplitOutcome n

/-- Execute a supplied hard epoch on its node-local tape, followed by
counted trial division if the finite retry budget is exhausted. -/
def epochHard {α : ℕ → Type*} (attempt : ∀ n, α n → Option (Factors n) × ℕ) :
    HardSplitter α :=
  fun n hn _ hp _ tape => RandomizedTotalEpochSplit.splitFrom hn hp (attempt n) tape

variable {α : ℕ → Type*}
variable (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
variable (hard : HardSplitter α)

private def dispatch (n : ℕ) (hn : 2 ≤ n) (work : ℕ) (tape : ℕ → α n) :
    (r : RandomizedPreprocessing.Result) → r.Sound n → Branch n
  | .prime, hp => .prime work hp
  | .split d, hd => .split (verifiedEasySplit n d hn hd work)
  | .hard, hs =>
    let s := hard n hn hs.1 hs.2.1 hs.2.2 tape
    .split {s with work := work + s.work}

/-- Interpret the result of the counted input checks. Only the hard branch
reads blocks from its node's tape. -/
def decision (n : ℕ) (hn : 2 ≤ n) (tape : ℕ → α n) : Branch n :=
  let prep := RandomizedPreprocessing.run k n
  dispatch hard n hn prep.2 tape prep.1 (sound n hn)

/-- Run the binary recursion from a node address, using the same input tape
with a distinct address for each child. Paths are stored in reverse order. -/
def factorFrom (tape : Tape α) (n : ℕ) (hn : 2 ≤ n) (path : List Bool) : List ℕ × ℕ :=
  match decision k sound hard n hn (tape path n) with
  | .prime work _ => ([n], work)
  | .split s =>
    let a := factorFrom tape s.left s.left_ge (false :: path)
    let b := factorFrom tape s.right s.right_ge (true :: path)
    (a.1 ++ b.1, s.work + a.2 + b.2)
termination_by n
decreasing_by all_goals first | exact s.left_lt | exact s.right_lt

theorem factorFrom_correct (tape : Tape α) (n : ℕ) (hn : 2 ≤ n) (path : List Bool) :
    let out := factorFrom k sound hard tape n hn path
    out.1.prod = n ∧ ∀ p ∈ out.1, p.Prime := by
  induction n using Nat.strong_induction_on generalizing path with
  | h n ih =>
    dsimp only
    rw [factorFrom]
    cases h : decision k sound hard n hn (tape path n) with
    | prime work hp => simp [hp]
    | split s =>
      obtain ⟨hl, hpl⟩ := ih s.left s.left_lt s.left_ge (false :: path)
      obtain ⟨hr, hpr⟩ := ih s.right s.right_lt s.right_ge (true :: path)
      dsimp only
      refine ⟨?_, ?_⟩
      · rw [List.prod_append, hl, hr, s.product]
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hpl p hp
        · exact hpr p hp

/-- Counted factoring on the prescribed tape from the root address. -/
def factor (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    (tape : Tape α) (n : ℕ) (hn : 2 ≤ n) : List ℕ × ℕ :=
  factorFrom k sound (epochHard attempt) tape n hn []

/-- Every tape produces the prime factor multiset of the input, including
tapes that miss on every candidate epoch. -/
theorem factor_correct (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    (tape : Tape α) (n : ℕ) (hn : 2 ≤ n) :
    (factor k sound attempt tape n hn).1.Perm n.primeFactorsList :=
  (factorFrom_correct k sound (epochHard attempt) tape n hn []).elim Nat.primeFactorsList_unique

#print axioms factorFrom_correct
#print axioms factor_correct

end Cogentic.RandomizedInputTape
