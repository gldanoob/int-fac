import Cogentic.CleanWindows
import Cogentic.DyadicTargets

namespace Cogentic.Construction
open Finset

theorem dyadic_target_in_primeBand {b ell : ℕ} (bp : 0<b) (mem : ell∈dyadicTargets (Fixed.beta b)) :
    ell∈primeBand b := by
  obtain ⟨pp,lower,upper⟩ := mem_dyadicTargets.mp mem
  have βp : 0<Fixed.beta b := Nat.mul_pos (by decide) (Nat.mul_pos (Fixed.degree_pos bp) (Nat.succ_pos _))
  have eq : Fixed.B b=2^(Fixed.beta b-1)*2 := by
    rw [←pow_succ,Nat.sub_add_cancel βp]
    rfl
  refine mem_primeBand.mpr ⟨pp,upper,?_⟩
  rw [eq,pow_two]
  exact (Nat.mul_lt_mul_of_pos_right lower (by decide : 0<2)).trans_le (Nat.mul_le_mul_left ell pp.two_le)

/-- There are enough ordinary primes left after the cofactor sieve to add a
dummy prime to any one-row observable, avoiding its row prime and the target. -/
theorem auxiliary_ordinary_prime (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ p : ℕ, ∃ q∈sieveBand n ell 1,q≠p ∧ q≠ell := by
  obtain ⟨cut,count⟩ := dyadic_count_from_critical_line line
  obtain ⟨b₀,grows⟩ := Fixed.degree_grows (max 10004 cut)
  refine ⟨b₀,?_⟩
  intro n ell b big hn comp target absent p
  let z := Fixed.z b;let d := Fixed.d b; let β := Fixed.beta b
  have deg := grows b big
  have dp : 1≤d := (by decide : 1≤10004).trans ((le_max_left ..).trans deg)
  have zp : 1≤z := Nat.succ_pos _
  have dz : d≤d*z := Nat.le_mul_of_pos_right _ zp
  have zz : z≤d*z := Nat.le_mul_of_pos_left _ dp
  have large : cut≤β := ((le_max_right ..).trans deg).trans (by change d≤1000*(d*z);omega)
  have lim := count β large
  let S := sieveBand n ell 1; let J := primeBand b
  have C : 0<conductorCap n := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (primorial_pos _) (Nat.succ_pos _))
    (Nat.pow_pos (by decide))) (Nat.pow_pos (Nat.pow_pos (by decide)))
  have drop := omitted_card (ell:=ell) (forced:=1) (q₀:=1) hn ((le_max_left ..).trans deg) comp target absent
    (by decide) (Nat.pow_pos (Nat.pow_pos (by decide))) (by decide) C
  have nodvd (q : ℕ) (h : q∈S) : ¬q∣1 := (mem_primeBand.mp (mem_filter.mp h).1).1.not_dvd_one
  change (J \ S.filter (fun q=> ¬q∣1)).card≤b^3 at drop
  rw [filter_true_of_mem nodvd] at drop
  have expBig : 3*β*(b^3+3)<2^β := by
    have one : 3*β≤2^(12+d+z) := by
      rw [Nat.pow_add,Nat.pow_add]
      change 3*(1000*(d*z))≤2^12*2^d*2^z
      exact (show 3*(1000*(d*z))≤4096*d*z by rw [Nat.mul_assoc 4096]; omega).trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left 4096 (Nat.lt_two_pow_self.le)) Nat.lt_two_pow_self.le)
    have bnd := Nat.pow_le_pow_left (Nat.lt_log2_self.le : b≤2^z) 3
    rw [←Nat.pow_mul] at bnd
    change b^3≤2^(z*3) at bnd
    have powers : 1≤2^(z*3) := Nat.one_le_two_pow
    have two : b^3+3≤2^(z*3+2) := by rw [Nat.pow_add];omega
    apply (Nat.mul_le_mul one two).trans_lt
    rw [←Nat.pow_add]
    apply Nat.pow_lt_pow_right (by decide)
    change _ < 1000*(d*z)
    omega
  have cardD : (dyadicTargets β).card ≤ J.card := card_le_card
    (fun q h=>dyadic_target_in_primeBand (Nat.succ_pos n.log2) h)
  have sub : S⊆J := filter_subset ..
  have partition := card_sdiff_add_card_eq_card sub
  by_contra! miss
  have cover : S ⊆ {p,ell} := by
    intro q h
    by_cases eq : q=p
    · simp [eq]
    · simp [miss q h eq]
  have small := (card_le_card cover).trans (card_insert_le ..)
  rw [card_singleton] at small
  have inc : (dyadicTargets β).card≤b^3+3 := by omega
  exact expBig.not_ge (lim.trans (Nat.mul_le_mul_left _ inc))

end Cogentic.Construction

#print axioms Cogentic.Construction.auxiliary_ordinary_prime
