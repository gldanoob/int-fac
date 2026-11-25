import Cogentic.Elimination
import Cogentic.FixedSchedule
import Cogentic.ReconstructedOrder

namespace Cogentic.TryPair

open TwoThirdsSearch

/-- Data still supplied by the CRT polynomial construction at one grid point.
    All size parameters, the common root and the target prime come from the loop. -/
structure PairData where
  leading : ℕ
  factorBase : List ℕ
  marks : List ℕ
  first : List ℤ
  second : List ℤ

abbrev Construct := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → PairData
abbrev Archimedean := (s : Marking.Input) → (rel : Marking.Relations) →
  Elimination.IntegerFamily rel.marks.length → Option (Fin (2*s.degree-2) → ℚ)

def fixedInput (n g : ℕ) (pair : PairData) : Marking.Input :=
  let b := n.log2+1
  { n := n, m := Fixed.rootBase n, degree := Fixed.d b, leading := pair.leading
    A := Fixed.A b, B := Fixed.B b, L₀ := b, K₁ := Fixed.K₁ b, target := g
    factorBase := pair.factorBase, marks := pair.marks, first := pair.first, second := pair.second }

def localBits (s : Marking.Input) (rel : Marking.Relations) :=
  64*s.degree^3*(rel.rows.length+1)*s.L₀

def denominatorCap (s : Marking.Input) (rel : Marking.Relations) : ℕ :=
  2^(3*s.degree*(rel.rows.length+1)*s.L₀)

def finish (arch : Archimedean) (s : Marking.Input) (rel : Marking.Relations)
    (lattice : Elimination.IntegerFamily rel.marks.length) : Option Proposal := do
  if lattice.free < rel.marks.length ∧ 2*s.degree-2 ≤ lattice.free then
    let approx ← arch s rel lattice
    reconstructedProposal approx (denominatorCap s rel) lattice.scale
      (min (localBits s rel) (Fixed.precision (s.n.log2+1)))
  else none

/-- Fixed parameters, sparse mark collection, fraction-free elimination, the
    archimedean solve, and exact continued-fraction order reconstruction. -/
def attempt (build : Construct) (arch : Archimedean) (n : ℕ) : TwoThirdsSearch.TryPair :=
  Elimination.trySolved (fun g a b c d => fixedInput n g (build n g a b c d)) (finish arch)

private theorem reconstruction_bound {k Q e bits out : ℕ} {x : Fin k → ℚ}
    (eq : reconstructedProposal x Q e bits = some (.exponent out)) : out ≤ 2^bits := by
  unfold reconstructedProposal at eq
  obtain ⟨m,_,produced⟩ := Option.bind_eq_some_iff.mp eq
  split at produced
  next bounded => cases produced; exact bounded
  next _ => cases produced

/-- The splitter's exponent-size hypothesis now follows from the actual
    reconstruction guard at each candidate, independently of search coverage. -/
theorem attempt_bound (build : Construct) (arch : Archimedean) (n g a b c d e : ℕ)
    (hit : attempt build arch n g a b c d = some (.exponent e)) :
    e ≤ 2^Fixed.precision (n.log2+1) := by
  let s := fixedInput n g (build n g a b c d)
  change ((Marking.stageOne s).bind (fun rel => (Elimination.stageTwo rel).bind (finish arch s rel))) =
    some (.exponent e) at hit
  obtain ⟨rel,_,hit⟩ := Option.bind_eq_some_iff.mp hit
  obtain ⟨lattice,_,hit⟩ := Option.bind_eq_some_iff.mp hit
  unfold finish at hit
  split at hit
  next yes =>
    obtain ⟨x,_,hit⟩ := Option.bind_eq_some_iff.mp hit
    exact (reconstruction_bound hit).trans (Nat.pow_le_pow_right (by decide) (min_le_right ..))
  next no => cases hit

theorem saturated_size (build : Construct) (arch : Archimedean) (n : ℕ) (hn : 2 ≤ n) :
    let b := n.log2+1
    match (collect hn (searchBox n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b)
        (attempt build arch n)) (dyadicTargets (Fixed.beta b)).sort).1 with
    | .divisor .. => True
    | .orders e .. => saturate e b (Fixed.beta b) ≤ 2^(2^(2017*TwoThirdsCost.scale b)) := by
  exact Fixed.splitter_exponent hn (Nat.succ_pos _) (attempt build arch n) (attempt_bound build arch n)

end Cogentic.TryPair

#print axioms Cogentic.TryPair.saturated_size
