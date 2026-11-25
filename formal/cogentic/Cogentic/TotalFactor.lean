import Cogentic.Concrete

namespace Cogentic.Concrete
open TwoThirdsSearch TwoThirdsFactor TwoThirdsFinish

private def asDecision {n : ℕ} (d : {d // ProperDivisor n d}) : Decision n :=
  .split d.val ⟨d.property.1,d.property.2.1⟩ d.property.2.2

private def trial (n : ℕ) (hn : 2 ≤ n) : Decision n :=
  if h : n.minFac < n then
    .split n.minFac ⟨(Nat.minFac_prime (by omega : n ≠ 1)).one_lt,h⟩ (Nat.minFac_dvd n)
  else
    .prime (Nat.prime_def.mp (by
      by_contra bad
      exact h ((Nat.not_prime_iff_minFac_lt hn).mp bad)))

def fixedCollection (n : ℕ) (hn : 2 ≤ n) :=
  let b := n.log2+1
  let gs := (dyadicTargets (Fixed.beta b)).sort
  let probe := searchBox n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b) (candidate n)
  collect hn probe gs

/-- An exponent backend is only called when the fixed search returns orders. -/
def tryDivisorWith (n : ℕ) (hn : 2 ≤ n) (split : ℕ → Option {d // ProperDivisor n d}) :
    Option {d // ProperDivisor n d} :=
  let b := n.log2+1
  match (fixedCollection n hn).1 with
  | .divisor d h => some ⟨d,h⟩
  | .orders e _ _ _ _ => split (saturate e b (Fixed.beta b))

/-- If the fixed search has insufficient certificates, the splitter may still
    succeed. A divisor returned here is checked independently of prime supply. -/
def tryDivisor (n : ℕ) (hn : 2 ≤ n) (bases : List ℕ) : Option {d // ProperDivisor n d} :=
  tryDivisorWith n hn (fun m => splitWithExponent n m bases)

/-- Dense verified targets force the real splitter to return a divisor on a
    surviving composite with at least two distinct prime factors. -/
theorem tryDivisor_succeeds {n : ℕ} (hn : 2 ≤ n) (bases : List ℕ)
    (gen : generatesUnits n bases) (odd : ¬2 ∣ n) (npp : ¬ IsPrimePow n)
    (count : let b := n.log2+1
      2^(Fixed.beta b) ≤ 3*Fixed.beta b*(dyadicTargets (Fixed.beta b)).card)
    (covered : let b := n.log2+1
      ∀ p ∈ dyadicTargets (Fixed.beta b),
        BoxWitness n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b) (candidate n) p) :
    tryDivisor n hn bases ≠ none := by
  let b := n.log2+1
  let beta := Fixed.beta b
  let gs := (dyadicTargets beta).sort
  let probe := searchBox n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b) (candidate n)
  have mem {g : ℕ} (h : g ∈ gs) : g ∈ dyadicTargets beta := by
    have m := List.mem_toFinset.mpr h
    simpa only [gs,Finset.sort_toFinset] using m
  have complete := collect_complete hn probe gs (fun p hp => searchBox_complete (covered p (mem hp)))
  have posb : 0 < b := Nat.succ_pos _
  have posβ : 0 < beta := by
    have pd := Fixed.degree_pos posb
    dsimp [beta,Fixed.beta,Fixed.h,Fixed.z]; positivity
  unfold tryDivisor
  change (match (collect hn probe gs).1 with
    | .divisor d h => some ⟨d,h⟩
    | .orders e _ _ _ _ => splitWithExponent n (saturate e b beta) bases) ≠ none
  cases eq : (collect hn probe gs).1 with
  | divisor d hd => simp
  | orders e big even retained valid =>
    rw [eq] at complete
    change retained = gs at complete
    subst retained
    have size : 2^beta ≤ 3*beta*gs.toFinset.card := by simpa [gs] using count
    have sat (p : ℕ) (hp : p.Prime) (div : p ∣ n) : p-1 ∣ saturate e b beta :=
      collected_orders_saturate gs hn Nat.lt_log2_self posβ big
        (fun _ h => (mem_dyadicTargets.mp (mem h)).1)
        (fun _ h => (mem_dyadicTargets.mp (mem h)).2.2) size valid hp div
    have idxPos : 0 < (Finset.Icc 1 (indexCap b beta)).lcm id := Nat.pos_of_ne_zero
      (Finset.lcm_ne_zero_iff.mpr (fun a ha => Nat.ne_of_gt (Finset.mem_Icc.mp ha).1))
    obtain ⟨p,pm,q,qm,neq⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp npp
    obtain ⟨pp,pn,_⟩ := Nat.mem_primeFactors.mp pm
    obtain ⟨qp,qn,_⟩ := Nat.mem_primeFactors.mp qm
    have : Fact p.Prime := ⟨pp⟩
    have : Fact q.Prime := ⟨qp⟩
    have gt (r : ℕ) (prime : r.Prime) (div : r ∣ n) : 2 < r :=
      lt_of_le_of_ne prime.two_le (fun same => odd (same ▸ div))
    exact saturated_splitter hn (big.trans (Nat.le_mul_of_pos_right _ idxPos)) (gt p pp pn)
      (gt q qp qn) neq pn qn (sat p pp pn) (sat q qp qn) bases gen

/-- On every sufficiently large surviving input, coverage alone forces the
concrete splitter to return a divisor. The dyadic prime-count guard follows
from the critical-line theorem at the selected integer scale. -/
theorem tryDivisor_of_coverage (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (hn : 2 ≤ n) (bases : List ℕ), generatesUnits n bases →
      ¬n.Prime → ¬2 ∣ n → ¬IsPrimePow n →
      presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = none →
      (Fixed.parameters candidate n).Covers n → tryDivisor n hn bases ≠ none := by
  obtain ⟨β,count⟩ := dyadic_count_from_critical_line line
  obtain ⟨n₀,grow⟩ := Fixed.parameters_grow candidate β
  exact ⟨n₀,fun n large hn bases gen composite odd npp absent covers =>
    tryDivisor_succeeds hn bases gen odd npp (count _ (grow n large))
      (covers composite odd npp absent)⟩

/-- Fixed program with explicit trial division on a search miss. Inputs up to
    eight bits skip parameter construction altogether. -/
def totalStepWith (search : (a : ℕ) → 2 ≤ a → List ℕ → Option {d // ProperDivisor a d})
    (k n : ℕ) (hn : 2 ≤ n)
    (gen : generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))) : Decision n := by
  if n.log2+1 ≤ 8 then exact trial n hn
  else
    let b := n.log2+1
    let bases := List.range' 1 (polyCutoff k b)
    if h : primeCheck n bases = true then exact .prime (Nat.prime_def.mp ((primeCheck_correct _ _ gen).mp h))
    else
      if even : 2 ∣ n then
        have ne : n ≠ 2 := fun e => h ((primeCheck_correct _ _ gen).mpr (e ▸ Nat.prime_two))
        exact .split 2 ⟨by decide,by omega⟩ even
      else
        let result := (powerDivisor n b).orElse fun _ =>
          (presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)).orElse fun _ =>
            search n hn bases
        match result with
        | some d => exact asDecision d
        | none => exact trial n hn

def totalStep (k n : ℕ) (hn : 2 ≤ n)
    (gen : generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))) : Decision n :=
  totalStepWith tryDivisor k n hn gen

def run (k : ℕ) (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1))))
    (n : ℕ) (hn : 2 ≤ n) := TwoThirdsFactor.factor (fun a ha => totalStep k a ha (gen a ha)) n hn

/-- All inputs are factored with correct multiplicities, even when the
    smooth-window extractor misses a target. Its fast worst-case running
    time still requires a uniform proof that trial division is avoided. -/
theorem total_factorization (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
      ∀ n (hn : 2 ≤ n),
        let factors := (run k gen n hn).factors
        factors.prod = n ∧ (∀ p ∈ factors, p.Prime) ∧
          ∀ p, p.Prime → ∀ j, p^j ∣ n ↔ j ≤ factors.count p := by
  obtain ⟨k,bases⟩ := polynomial_generators_from_critical_line line
  have gen (n : ℕ) (hn : 2 ≤ n) : generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1))) := by
    have : NeZero n := ⟨by omega⟩
    exact bases n _ Nat.lt_log2_self
  refine ⟨k,gen,fun n hn => ?_⟩
  let tree := run k gen n hn
  exact ⟨tree.correct.1,fun p hp => Nat.prime_def.mpr (tree.correct.2 p hp),
    fun _ hp => tree.multiplicity (Nat.prime_def.mp hp)⟩

end Cogentic.Concrete
