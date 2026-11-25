import Cogentic.MarkIntervals
import Cogentic.CleanWindows

namespace Cogentic.Construction
open Finset

private theorem prime_square_lcm {p q : ℕ} (prime : p.Prime) (sq : Squarefree q) :
    p*q ≤ (p^2).lcm q := by
  let g := (p^2).gcd q; let m := (p^2).lcm q
  have gp : g≤p := by
    obtain ⟨k,hk,eq⟩ := (Nat.dvd_prime_pow prime).mp (Nat.gcd_dvd_left (p^2) q)
    change g=p^k at eq
    interval_cases k
    · rw [eq,pow_zero]; exact prime.one_le
    · simp [eq]
    · have bad : p*p∣q := by simpa only [←pow_two,←eq] using Nat.gcd_dvd_right (p^2) q
      exact ((Nat.squarefree_iff_prime_squarefree.mp sq p prime) bad).elim
  apply Nat.le_of_mul_le_mul_left _ prime.pos
  calc p*(p*q) = g*m := by rw [show g*m=p^2*q from Nat.gcd_mul_lcm ..]; ring
       _ ≤ p*m := Nat.mul_le_mul_right _ gp

/-- In a squarefree residue class, imposing a square-prime congruence
costs at least a factor p even when p divides the class modulus. -/
theorem square_prime_cell_count {p q : ℕ} (prime : p.Prime) (sq : Squarefree q) (lo M a r : ℕ) :
    let X := (Ico lo (lo+M)).filter (fun t => t ≡ r [MOD q] ∧ t ≡ a [MOD p^2])
    (X.card:ℝ) ≤ (M:ℝ)/(p*q)+1 := by
  classical
  intro X
  by_cases empty : X.Nonempty
  · obtain ⟨v,hv⟩ := empty
    let m := (p^2).lcm q
    have small := prime_square_lcm prime sq
    have qp := Nat.pos_of_ne_zero sq.ne_zero
    have mp : 0 < m := (Nat.mul_pos prime.pos qp).trans_le small
    have sub : X⊆(Ico lo (lo+M)).filter (fun t => t ≡ v [MOD m]) := by
      intro t ht
      obtain ⟨interval,qt,pt⟩ := mem_filter.mp ht
      obtain ⟨_,qv,pv⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨interval,Nat.mod_lcm (pt.trans pv.symm) (qt.trans qv.symm)⟩
    have le := (abs_le.mp (interval_residue_error (Nat.le_add_right lo M) mp v)).2
    simp only [Nat.cast_add,add_sub_cancel_left] at le
    have card : (X.card:ℝ)≤_ := Nat.cast_le.mpr (card_le_card sub)
    have div := div_le_div_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) M) (by exact_mod_cast Nat.mul_pos prime.pos qp : 0<(p:ℝ)*q)
      (show (p:ℝ)*q ≤ m by exact_mod_cast small)
    linarith
  · rw [not_nonempty_iff_eq_empty.mp empty]; simp; positivity

/-- Uniform relative contribution of each prescribed exceptional prime
square in the cells of the fixed schedule, including the endpoint error. -/
theorem fixed_square_prime_loss {b p q : ℕ} (member : p∈primeBand b)
    (sq : Squarefree q) (cap : q≤(Fixed.B b)^3) (lo a r : ℕ) :
    let M := cellMarkCount b
    let X := (Ico lo (lo+M)).filter (fun t => t ≡ r [MOD q] ∧ t ≡ a [MOD p^2])
    (X.card:ℝ) ≤ (M:ℝ)/q * (2/2^(500*Fixed.h b)) := by
  intro M X
  let L := 2^(500*Fixed.h b)
  have lp : 0<L := Nat.pow_pos (by decide)
  have qp := Nat.pos_of_ne_zero sq.ne_zero
  obtain ⟨pp,_,top⟩ := mem_primeBand.mp member
  have low : L≤p := by
    by_contra! small
    have bb : Fixed.B b=L^2 := by change 2^(1000*Fixed.h b)=(2^(500*Fixed.h b))^2; rw [←pow_mul]; congr 1; ring
    exact top.not_ge (bb ▸ Nat.pow_le_pow_left small.le 2)
  have endpt : q*L≤M := calc
    _ ≤ (Fixed.B b)^3*L := Nat.mul_le_mul_right _ cap
    _ ≤ _ := by
      change (2^(1000*Fixed.h b))^3*2^(500*Fixed.h b)≤2^(9997*Fixed.h b)
      rw [←pow_mul,←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have qr : (0:ℝ)<q := by exact_mod_cast qp
  have lr : (0:ℝ)<L := by exact_mod_cast lp
  have pr : (0:ℝ)<p := by exact_mod_cast pp.pos
  have enough : (q:ℝ)*L ≤ M := by exact_mod_cast endpt
  have one : (1:ℝ)≤(M:ℝ)/q/L := by
    rw [le_div_iff₀ lr,le_div_iff₀ qr]; linarith only [enough]
  have cmp := div_le_div_of_nonneg_left (by positivity : 0≤(M:ℝ)/q) lr (show (L:ℝ)≤p by exact_mod_cast low)
  have cnt := square_prime_cell_count pp sq lo M a r
  change (X.card:ℝ) ≤ (M:ℝ)/(p*q)+1 at cnt
  rw [mul_comm (p:ℝ),←div_div] at cnt
  have res := cnt.trans (add_le_add cmp one)
  change (X.card:ℝ) ≤ (M:ℝ)/q*(2/2^(500*Fixed.h b))
  simpa only [show (2:ℝ)^(500*Fixed.h b)=(L:ℝ) by simp [L]] using res.trans_eq (by ring)

end Cogentic.Construction
