import Cogentic.SearchSaturation

namespace Cogentic.Companion
open TwoThirdsSearch

/-- If the collector returns orders, it retains exactly the successful target
probes, preserving their order. A divisor can terminate the collection early. -/
theorem collect_covers_filter {n : ℕ} (hn : 2≤n) (probe : (g : ℕ) → Probe (Hit n g))
    (gs : List ℕ) :
    (collect hn probe gs).1.covers (gs.filter fun g => (probe g).answer.isSome) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h : (probe g).answer with
    | none => simpa only [collect,h,List.filter_cons,Option.isSome_none,Bool.false_eq_true,if_false] using ih
    | some hit =>
      cases hit with
      | divisor d proper => simp [collect,h,Output.covers]
      | exponent e verified =>
        cases tail : (collect hn probe gs).1 with
        | divisor d proper =>
          simp only [collect,h,tail,List.filter_cons,Option.isSome_some,if_true]
          trivial
        | orders E big even retained valid =>
          rw [tail] at ih
          change retained = _ at ih
          simp only [collect,h,tail,List.filter_cons,Option.isSome_some,if_true]
          change g::retained = g::_
          rw [ih]

/-- A finite set of successful probes supplies the saturation cardinality
even if other scheduled targets exhaust all candidates without a hit. -/
theorem search_saturation_of_hit_subset {n β bits : ℕ} (gs : List ℕ) (probe : (g : ℕ) → Probe (Hit n g))
    (hn : 2≤n) (length : n<2^bits) (beta : 0<β)
    (primes : ∀ g∈gs, g.Prime) (upper : ∀ g∈gs, g≤2^β)
    (S : Finset ℕ) (subset : ∀ g∈S, g∈gs) (hits : ∀ g∈S, (probe g).answer≠none)
    (enough : 2^β≤3*β*S.card) :
    match (collect hn probe gs).1 with
    | .divisor d _ => ProperDivisor n d
    | .orders E .. => ∀ p : ℕ, p.Prime → p∣n → p-1 ∣ saturate E bits β := by
  let kept := gs.filter (fun g => (probe g).answer.isSome)
  have contains : S ⊆ kept.toFinset := by
    intro g hg
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨subset g hg,Option.isSome_iff_ne_none.mpr (hits g hg)⟩)
  have threshold := enough.trans (Nat.mul_le_mul_left (3*β) (Finset.card_le_card contains))
  have output := collect_covers_filter hn probe gs
  cases h : (collect hn probe gs).1 with
  | divisor d valid => exact valid
  | orders E big even retained verified =>
    rw [h] at output
    change retained=kept at output
    subst retained
    exact fun p hp hd => collected_orders_saturate kept hn length beta big
      (fun g hg=>primes g (List.mem_filter.mp hg).1)
      (fun g hg=>upper g (List.mem_filter.mp hg).1) threshold verified hp hd

end Cogentic.Companion

#print axioms Cogentic.Companion.collect_covers_filter
#print axioms Cogentic.Companion.search_saturation_of_hit_subset
