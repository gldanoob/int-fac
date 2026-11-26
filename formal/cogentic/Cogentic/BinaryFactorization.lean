import Cogentic.DriverBitCost

namespace Cogentic.Companion
open Concrete TwoThirdsFactor TwoThirdsSearch TwoThirdsFinish CompanionSplitCost Real Filter

/-- The four-coordinate and target scans stop at their actual return points.
Quotients and output writes are charged by the binary tree traversal. -/
def nodeTrace (split : Splitter) (k n : ℕ) : ℕ :=
  (if 2≤n then (BinaryPowerScan.run n.bits).2+(BinaryPowerScan.computedBase n.bits).2 else 0) +
    (commonWork k n - BinaryRecursion.nodeBudget n) + fallbackWork split k n +
    (if h : ReachesSearch k n then traceSearchWork n h.1+saturationWork n h.1 else 0) +
    backendWork split k n

private theorem node_trace_le (split : Splitter) (k n : ℕ) :
    nodeTrace split k n+BinaryRecursion.nodeBudget n ≤
      guardedLocalWork k n+driverWork split k n+backendWork split k n := by
  have paid : BinaryRecursion.nodeBudget n ≤ commonWork k n := by
    dsimp only [commonWork]; omega
  simp only [nodeTrace,guardedLocalWork,driverWork]
  by_cases h : ReachesSearch k n
  · simp only [h,if_true,dif_pos]
    have bound := (search_trace_spec n h.1).2
    omega
  · simp only [h,if_false,dif_neg]; omega

private theorem tree_trace_le (split : Splitter) (k : ℕ) {n : ℕ} (t : Run n) :
    t.work (nodeTrace split k) + t.work BinaryRecursion.nodeBudget ≤
      t.work (fun a => guardedLocalWork k a+driverWork split k a+backendWork split k a) := by
  induction t with
  | prime p _ => exact node_trace_le split k p
  | @split a b l r hl hr =>
    have head := node_trace_le split k (a*b)
    simp only [Run.work]
    omega

/-- Factor words with their aggregate bit charge on the same recursion tree.
The accumulator produces each prime word once, including repetitions. -/
def factorWords (split : Splitter) (k : ℕ)
    (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1))))
    (n : ℕ) (hn : 2≤n) : List (List Bool) × ℕ :=
  let tree := factor (fun a h => totalStepWith (fun x hx _ => tryDivisorWith x hx (fun m => (split x m).1))
    k a h (gen a h)) n hn
  let out := BinaryRecursion.emit tree []
  (out.1,tree.work (nodeTrace split k) + out.2)

theorem factor_words_of_dense_hits (line : DirichletLZerosOnLine)
    (split : Splitter) {C₁ A : ℝ} (hc : 0≤C₁) (ha : 0≤A) (spec : SplitterSpec split C₁ A) :
    ∃ (k : ℕ) (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
      (∀ n (hn : 2≤n),
        let primes := (factorWords split k gen n hn).1.map BinaryDivision.value
        primes.prod=n ∧ (∀ p∈primes, p.Prime) ∧ (∀ p, p.Prime → ∀ j, p^j∣n ↔ j≤primes.count p)) ∧
      ((∀ᶠ n : ℕ in atTop, ReachesSearch k n → DenseBoxHits n) →
        ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop, ∀ hn : 2≤n,
          ((factorWords split k gen n hn).2:ℝ) ≤ exp ((max 6528665845 (C₁+12*A+131117)+ε)*scale n)) := by
  obtain ⟨k,gen,finish⟩ := factor_tree_of_accounted_stages line split hc ha spec
  let tree (n : ℕ) (hn : 2≤n) := factor (fun a h => totalStepWith
    (fun x hx _ => tryDivisorWith x hx (fun m => (split x m).1)) k a h (gen a h)) n hn
  refine ⟨k,gen,?_,?_⟩
  · intro n hn
    let t := tree n hn
    have words := (BinaryRecursion.emit_spec t []).1
    change (BinaryRecursion.emit t []).1=_ at words
    simp only [List.append_nil] at words
    change let primes := (BinaryRecursion.emit t []).1.map BinaryDivision.value
           primes.prod=n ∧ (∀ p∈primes, p.Prime) ∧ (∀ p, p.Prime → ∀ j, p^j∣n ↔ j≤primes.count p)
    simp only [words,List.map_map,Function.comp_def,BinaryDivision.value_bits,List.map_id_fun]
    exact ⟨t.correct.1,fun p hp => Nat.prime_def.mpr (t.correct.2 p hp),
      fun p hp => t.multiplicity (Nat.prime_def.mp hp)⟩
  · intro hits ε pos
    filter_upwards [finish hits ε pos] with n bound hn
    let t := tree n hn
    have emitted := (BinaryRecursion.emit_spec t []).2
    have work := (Nat.add_le_add_left emitted (t.work (nodeTrace split k))).trans (tree_trace_le split k t)
    exact (Nat.cast_le.mpr work).trans (bound hn)

end Cogentic.Companion

#print axioms Cogentic.Companion.factor_words_of_dense_hits
