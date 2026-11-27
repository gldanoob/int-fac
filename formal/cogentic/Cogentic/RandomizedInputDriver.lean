import Cogentic.RandomizedPreprocessing
import Cogentic.RandomizedSplitVerification
import Cogentic.RandomizedCostedFactorLaw

namespace Cogentic.RandomizedInputDriver

open RandomizedCostedFactorLaw
open scoped ENNReal

abbrev HardKernel := ∀ n : ℕ, 2 ≤ n → Odd n → ¬ n.Prime → ¬ IsPrimePow n → PMF (SplitOutcome n)

inductive Branch (n : ℕ) where
  | prime (work : ℕ) (isPrime : n.Prime)
  | split (out : SplitOutcome n)

variable (k : ℕ)
variable (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
variable (hard : HardKernel)

private def easySplit (n d : ℕ) (hn : 2 ≤ n) (hd : TwoThirdsSearch.ProperDivisor n d)
    (front : ℕ) : SplitOutcome n :=
  let check := RandomizedSplitVerification.verify n d
  let q := (check.1.map BinaryDivision.value).getD 0
  have hq : q = n/d := by
    have h := (RandomizedSplitVerification.verify_spec (by omega : 0 < n)
      (Nat.size_le_size hd.2.1.le)).1
    simpa [q, check, if_pos hd] using congrArg (fun x : Option ℕ => x.getD 0) h
  have heq : d * q = n := by rw [hq, Nat.mul_div_cancel' hd.2.2]
  have hq2 : 2 ≤ q := by
    by_contra! h
    have hlt := hd.2.1
    rcases (by omega : q = 0 ∨ q = 1) with h0 | h1
    · simp [h0] at heq
      omega
    · simp [h1] at heq
      omega
  ⟨d, q, front + check.2, hd.1, hq2, heq⟩

private noncomputable def dispatch (n : ℕ) (hn : 2 ≤ n) (work : ℕ) :
    (result : RandomizedPreprocessing.Result) → result.Sound n → PMF (Branch n)
  | .prime, hp => PMF.pure (.prime work hp)
  | .split d, hd => PMF.pure (.split (easySplit n d hn hd work))
  | .hard, hs =>
    (hard n hn hs.1 hs.2.1 hs.2.2).map fun s =>
      .split {s with work := work + s.work}

/-- Dispatch on the result of the counted deterministic precheck. Only the
odd composite, non-prime-power branch requests the hard-input sampler. -/
noncomputable def decision (n : ℕ) (hn : 2 ≤ n) : PMF (Branch n) :=
  let prep := RandomizedPreprocessing.run k n
  dispatch hard n hn prep.2 prep.1 (sound n hn)

private theorem decision_eq_dispatch {n : ℕ} (hn : 2 ≤ n) {r : RandomizedPreprocessing.Result}
    (h : (RandomizedPreprocessing.run k n).1 = r) (hs : r.Sound n) :
    decision k sound hard n hn = dispatch hard n hn (RandomizedPreprocessing.run k n).2 r hs := by
  subst r
  rfl

/-- The driver always runs the executable precheck before interpreting a
branch. Its semantic recursion decreases on both returned factors. -/
noncomputable def factor (n : ℕ) (hn : 2 ≤ n) : PMF (List ℕ × ℕ) :=
  (decision k sound hard n hn).bind fun
    | .prime work _ => PMF.pure ([n], work)
    | .split s =>
      (factor s.left s.left_ge).bind fun a =>
        (factor s.right s.right_ge).map fun b =>
          (a.1 ++ b.1, s.work + a.2 + b.2)
termination_by n
decreasing_by all_goals first | exact s.left_lt | exact s.right_lt

private def getSplit {n : ℕ} (h : ¬n.Prime) : Branch n → SplitOutcome n
  | .prime _ hp => (h hp).elim
  | .split s => s

noncomputable def splitter : SplitKernel :=
  fun n hn hp => (decision k sound hard n hn).map (getSplit hp)

include sound in
private theorem precheck_prime {n : ℕ} (hn : 2 ≤ n) (hp : n.Prime) :
    (RandomizedPreprocessing.run k n).1 = .prime := by
  have hs := sound n hn
  cases h : (RandomizedPreprocessing.run k n).1 with
  | prime => rfl
  | split d =>
    rw [h] at hs
    obtain ⟨hle, hlt, hd⟩ := hs
    rcases (Nat.dvd_prime hp).mp hd with hc | hc <;> omega
  | hard =>
    rw [h] at hs
    exact (hs.2.1 hp).elim

/-- Agreement with the charged factor-and-work law gives the driver its
support and expectation theorems without charging an oracle primality test. -/
theorem factor_eq (n : ℕ) (hn : 2 ≤ n) :
    factor k sound hard n hn =
      factorLaw (splitter k sound hard) (fun a => (RandomizedPreprocessing.run k a).2) n hn := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hp : n.Prime
    · rw [factorLaw_of_prime _ _ hn hp, factor]
      have hc := precheck_prime k sound hn hp
      simp only [decision_eq_dispatch k sound hard hn hc hp, dispatch, PMF.pure_bind]
    · rw [factorLaw_of_composite _ _ hn hp, factor, splitter, PMF.bind_map]
      congr 1
      funext b
      cases b with
      | prime _ h => exact (hp h).elim
      | split s =>
        simp only [getSplit, Function.comp_apply, ih s.left s.left_lt s.left_ge,
          ih s.right s.right_lt s.right_ge]

theorem factor_support_correct {n : ℕ} (hn : 2 ≤ n) {out : List ℕ × ℕ}
    (hout : out ∈ (factor k sound hard n hn).support) : out.1.Perm n.primeFactorsList := by
  rw [factor_eq] at hout
  exact factorLaw_support_perm _ _ hn hout

/-- A hard-call estimate transfers through the counted precheck and through
the binary verification and division on the easy branch. -/
theorem splitter_mean_le (B : ℕ → ℝ≥0∞)
    (hB : ∀ n (hn : 2 ≤ n) (ho : Odd n) (hp : ¬n.Prime) (hpow : ¬IsPrimePow n),
      mean (hard n hn ho hp hpow) (fun s => s.work) ≤ B n)
    (n : ℕ) (hn : 2 ≤ n) (hp : ¬ n.Prime) :
    mean (splitter k sound hard n hn hp) (fun s => s.work) ≤
      ((RandomizedPreprocessing.run k n).2 : ℝ≥0∞) + RandomizedSplitVerification.verifierBudget n + B n := by
  have hs := sound n hn
  rw [splitter, mean_map]
  cases h : (RandomizedPreprocessing.run k n).1 with
  | prime =>
    rw [h] at hs
    exact (hp hs).elim
  | split d =>
    rw [h] at hs
    obtain ⟨_, hcost⟩ := RandomizedSplitVerification.verify_spec (by omega : 0 < n)
      (Nat.size_le_size hs.2.1.le)
    simp only [decision_eq_dispatch k sound hard hn h hs, dispatch, mean_pure, getSplit,
      easySplit, Nat.cast_add]
    calc
      _ ≤ ((RandomizedPreprocessing.run k n).2 : ℝ≥0∞) +
          RandomizedSplitVerification.verifierBudget n :=
        add_le_add le_rfl (Nat.cast_le.mpr hcost)
      _ ≤ _ := le_add_right le_rfl
  | hard =>
    rw [h] at hs
    simp only [decision_eq_dispatch k sound hard hn h hs, dispatch, mean_map, getSplit,
      Nat.cast_add, mean_add, mean_const]
    calc
      _ ≤ ((RandomizedPreprocessing.run k n).2 : ℝ≥0∞) + B n :=
        add_le_add le_rfl (hB n hn hs.1 hs.2.1 hs.2.2)
      _ ≤ _ := add_le_add (le_add_right le_rfl) le_rfl

end Cogentic.RandomizedInputDriver

#print axioms Cogentic.RandomizedInputDriver.factor_eq
#print axioms Cogentic.RandomizedInputDriver.splitter_mean_le
