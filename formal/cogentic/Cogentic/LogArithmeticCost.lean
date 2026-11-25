import Cogentic.ArchNumerics
import Cogentic.BackSubstitutionBounds

/-! Bit sizes of the partial sums in the exact rational logarithm series. -/
namespace Cogentic.ArchNumerics
open Finset

private theorem scaled_term (y : ℚ) (k T : ℕ) (kp : 0<k) (kt : k≤T) :
    ∃ z : ℤ, (y^k/k)*((y.den^T*T.factorial:ℕ):ℚ) = z := by
  obtain ⟨m,hm⟩ := Nat.dvd_factorial kp kt
  refine ⟨y.num^k*(y.den:ℤ)^(T-k)*m,?_⟩
  have dd : (y.den:ℚ)≠0 := by exact_mod_cast y.den_ne_zero
  have kz : (k:ℚ)≠0 := by exact_mod_cast kp.ne'
  have powers : (y.den:ℚ)^T = (y.den:ℚ)^k*(y.den:ℚ)^(T-k) := by rw [←pow_add]; congr 1; omega
  have yy : y^k*(y.den:ℚ)^k=(y.num:ℚ)^k := by
    rw [←mul_pow]; congr 1; exact (eq_div_iff dd).mp y.num_div_den.symm
  push_cast
  rw [powers,hm]; push_cast
  calc
    _ = (y^k*(y.den:ℚ)^k)*(y.den:ℚ)^(T-k)*m := by field_simp
    _ = _ := by rw [yy]

/-- Every partial sum, in any summation order, has reduced numerator and
denominator bounded by `(T+1) den(y)^T T!`. Here `y=1-1/x` is the geometric
series argument used by `reducedLog`. -/
theorem log_partial_fraction_height (y : ℚ) (small : |y|≤1) (T : ℕ)
    (s : Finset ℕ) (selected : s ⊆ range T) :
    let q := ∑ i ∈ s, y^(i+1)/((i:ℚ)+1)
    let budget := (T+1)*y.den^T*T.factorial
    q.num.natAbs ≤ budget ∧ q.den ≤ budget := by
  let D := y.den^T*T.factorial
  let q := ∑ i ∈ s, y^(i+1)/((i:ℚ)+1)
  have dp : 0<D := Nat.mul_pos (Nat.pow_pos y.pos) (Nat.factorial_pos _)
  have integral (i : ℕ) (hi : i∈s) : ∃ z : ℤ,
      (y^(i+1)/((i:ℚ)+1))*(D:ℚ)=z := by
    simpa [D] using scaled_term y (i+1) T (Nat.succ_pos _) (mem_range.mp (selected hi))
  choose! Z hz using integral
  let z := ∑ i ∈ s, Z i
  have eq : q*(D:ℚ)=(z:ℚ) := by
    dsimp [q,z]; push_cast; rw [sum_mul]; exact sum_congr rfl hz
  have boundTerm (i : ℕ) : |y^(i+1)/((i:ℚ)+1)| ≤ 1 := by
    rw [abs_div,abs_pow,abs_of_pos (by positivity : (0:ℚ) < (i:ℚ)+1),div_le_one (by positivity)]
    exact (pow_le_one₀ (abs_nonneg _) small).trans (by linarith [Nat.cast_nonneg (α := ℚ) i])
  have smallSum : |q| ≤ T := by
    calc
      _ ≤ ∑ i ∈ s, |y^(i+1)/((i:ℚ)+1)| := abs_sum_le_sum_abs ..
      _ ≤ ∑ _i ∈ s, (1:ℚ) := sum_le_sum (fun i _ => boundTerm i)
      _ ≤ T := by simpa using (show (s.card:ℚ)≤T by exact_mod_cast (card_le_card selected).trans_eq (card_range _))
  have sz : |z| ≤ (T:ℤ)*D := by
    have e := congrArg abs eq
    simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg D : 0≤(D:ℚ))] at e
    have le := (le_of_eq e.symm).trans (mul_le_mul_of_nonneg_right smallSum (Nat.cast_nonneg D))
    exact_mod_cast le
  have bf : Elimination.BoundedFraction (fun _ : Fin 1 => q) (((T:ℤ)+1)*D) := by
    refine ⟨D,by exact_mod_cast dp.ne',?_,fun _ => z,fun _ => ?_,fun _ => ?_⟩
    · rw [abs_of_nonneg (Int.natCast_nonneg D)]; nlinarith [Int.natCast_nonneg T,Int.natCast_nonneg D,mul_nonneg (Int.natCast_nonneg T) (Int.natCast_nonneg D)]
    · exact sz.trans (by nlinarith [Int.natCast_nonneg D])
    · simpa using eq
  have red := bf.reduced 0
  change q.num.natAbs ≤ _ ∧ q.den ≤ _
  dsimp only [D] at red; push_cast at red; rw [Int.abs_eq_natAbs] at red
  exact_mod_cast (by simpa only [mul_assoc] using red : ((q.num.natAbs:ℤ)≤((T:ℤ)+1)*(y.den:ℤ)^T*T.factorial) ∧ ((q.den:ℤ)≤((T:ℤ)+1)*(y.den:ℤ)^T*T.factorial))

end Cogentic.ArchNumerics

#print axioms Cogentic.ArchNumerics.log_partial_fraction_height
