import Cogentic.Saturation
import TwoThirdsSearch

namespace Cogentic

/-- A returned order list may be shorter than the input when a box has no hit.
    Saturation only needs the distinct primes actually retained. -/
theorem collected_orders_saturate {N E β bits : ℕ} (retained : List ℕ)
    (input : 2 ≤ N) (length : N < 2^bits) (beta : 0 < β) (positive : 2 ≤ E)
    (primes : ∀ a ∈ retained, Nat.Prime a) (bound : ∀ a ∈ retained, a ≤ 2^β)
    (accept : 2^β ≤ 3*β*retained.toFinset.card)
    (checked : ∀ a ∈ retained, ModularPower.powMod a E N = 1)
    {p : ℕ} (prime : p.Prime) (divides : p ∣ N) : p-1 ∣ saturate E bits β := by
  apply saturate_all_prime_factors retained.toFinset (by omega) length beta (by omega)
      (by simpa using primes) (by simpa using bound) accept _ prime divides
  intro a ha
  have h := congrArg (fun m : ℕ => (m : ZMod N)) (checked a (List.mem_toFinset.mp ha))
  simpa only [ModularPower.powMod_def, ZMod.natCast_mod, Nat.cast_pow, Nat.cast_one] using h

/-- The output of the actual search is a factor or a saturated common order,
    whenever its retained list passes the integer count guard. -/
theorem search_saturation {N β bits : ℕ} (gs : List ℕ) (search : (g : ℕ) → TwoThirdsSearch.Probe
    (TwoThirdsSearch.Hit N g)) (hn : 2 ≤ N) (length : N < 2^bits) (beta : 0 < β)
    (primes : ∀ a ∈ gs, Nat.Prime a) (bound : ∀ a ∈ gs, a ≤ 2^β)
    (accept : 2^β ≤ 3*β*gs.toFinset.card)
    (hits : ∀ g ∈ gs, (search g).answer ≠ none) :
    match (TwoThirdsSearch.collect hn search gs).1 with
    | .divisor d _ => TwoThirdsSearch.ProperDivisor N d
    | .orders E _ _ _ _ => ∀ p, p.Prime → p ∣ N → p-1 ∣ saturate E bits β := by
  have h := TwoThirdsSearch.collect_complete hn search gs hits
  generalize he : (TwoThirdsSearch.collect hn search gs).1 = out at *
  cases out with
  | divisor d hd => exact hd
  | orders E big even retained checked =>
    change retained = gs at h
    subst retained
    exact fun _ hp hd => collected_orders_saturate gs hn length beta big primes bound accept checked hp hd

end Cogentic
