import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Cogentic.SealedSquareSupport

/-- The explicit gcd splits the modulus if a fiber of squaring contains
representatives from two different global-sign classes (Cogentic, Lemma 5.3). -/
theorem gcd_of_sealed_collision {n a b : ℕ} (order : a<b) (reduced : b<n)
    (equalSquare : a^2 ≡ b^2 [MOD n]) (differentSign : ¬n∣b+a) :
    1<Nat.gcd n (b-a) ∧ Nat.gcd n (b-a)<n ∧ Nat.gcd n (b-a)∣n := by
  have equation := equalSquare.dvd'
  rw [Nat.sq_sub_sq] at equation
  have cop : ¬n.Coprime (b-a) := fun h => differentSign (h.dvd_of_dvd_mul_right equation)
  have positive := Nat.gcd_pos_of_pos_left (b-a) (by omega : 0<n)
  have bound := Nat.le_of_dvd (by omega : 0<b-a) (Nat.gcd_dvd_right n (b-a))
  change Nat.gcd n (b-a) ≠ 1 at cop
  exact ⟨by omega,by omega,Nat.gcd_dvd_left ..⟩

/-- If checking the gcd of all pairs in an enumerable support yields no
proper divisor, each disclosed square fixes the root in that support up to sign. -/
theorem square_fibers_of_failed_gcd_scan {n : ℕ} (S : Finset (Fin n))
    (failed : ∀ a∈S, ∀ b∈S, a<b → ¬(1<Nat.gcd n (b.val-a.val) ∧ Nat.gcd n (b.val-a.val)<n)) :
    ∀ a∈S, ∀ b∈S, a.val^2 ≡ b.val^2 [MOD n] → a=b ∨ n∣b.val+a.val := by
  intro a ha b hb squares
  rcases lt_trichotomy a b with ab|rfl|ba
  · right; by_contra nonsign
    obtain ⟨lo,hi,_⟩ := gcd_of_sealed_collision ab b.isLt squares nonsign
    exact failed a ha b hb ab ⟨lo,hi⟩
  · exact Or.inl rfl
  · right; by_contra nonsign
    rw [Nat.add_comm] at nonsign
    obtain ⟨lo,hi,_⟩ := gcd_of_sealed_collision ba a.isLt squares.symm nonsign
    exact failed b hb a ha ba ⟨lo,hi⟩

/-- Below √n, small representatives have pairwise different disclosed squares. -/
theorem small_square_support_injective {n : ℕ} {a b : Fin n}
    (smallA : a.val^2<n) (smallB : b.val^2<n) (squares : a.val^2 ≡ b.val^2 [MOD n]) : a=b := by
  have eq : a.val^2=b.val^2 := by simpa [Nat.ModEq,Nat.mod_eq_of_lt smallA,Nat.mod_eq_of_lt smallB] using squares
  exact Fin.ext ((Nat.pow_left_inj (by decide : (2:ℕ)≠0)).mp eq)

/-- On a short initial support the blind procedure can return the ordinary square
root of the disclosed residue. Its gcd is then n on every draw, whereas the
upstream lemma for full uniform units gives at least one-half split probability. -/
theorem blind_decoder_on_small_support {n z : ℕ} (small : z^2<n) :
    let w := z^2%n
    Nat.sqrt w=z ∧ Nat.gcd n (z-Nat.sqrt w)=n := by
  simp [Nat.mod_eq_of_lt small]

end Cogentic.SealedSquareSupport

#print axioms Cogentic.SealedSquareSupport.square_fibers_of_failed_gcd_scan
#print axioms Cogentic.SealedSquareSupport.small_square_support_injective

#print axioms Cogentic.SealedSquareSupport.blind_decoder_on_small_support
