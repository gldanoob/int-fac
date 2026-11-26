import Cogentic.GaussianMeans
import Cogentic.SaddleComparison

namespace Cogentic.Construction

open Real

/-- The logarithmic displacement of every admissible constructed
    evaluation center from the common amplitude is at most one
    two-hundredth of the prime-band logarithm. -/
theorem mark_log_displacement {n ell a : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (cap : a ≤ Fixed.A (n.log2+1))
    (grid : onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a)
    (side : Bool) (Y : ℝ) (shift : |Y-(exactMean n ell a side:ℝ)| ≤ 4*((n.log2+1:ℕ):ℝ)^3*referenceWidth n) :
    |log Y - log (amplitude n)| ≤ log (Fixed.B (n.log2+1))/200 := by
  let b := n.log2+1
  let x : ℝ := dyadicUnit b
  let X : ℝ := amplitude n
  obtain ⟨lower,upper⟩ := centered_envelope hn big target cap grid side Y shift
  change X/(2*x^4) ≤ Y at lower
  change Y ≤ 2*X at upper
  have ⟨xx,_,_,BB,_,_,_⟩ := dyadic_data (b:=b) (Nat.succ_pos _)
  have x2 : (2:ℝ) ≤ x := by dsimp [x]; exact_mod_cast xx
  have xp : 0 < x := by linarith
  have l : log 2 ≤ log x := log_le_log (by norm_num) x2
  have xl : 0 ≤ log x := log_nonneg (by linarith)
  have B : (Fixed.B b:ℝ)=x^1000 := by dsimp [x]; exact_mod_cast BB
  change |log Y-log X| ≤ log (Fixed.B b)/200
  rw [B,log_pow]
  rcases (show 0≤X from Nat.cast_nonneg _).eq_or_lt with hX | hX
  · rw [←hX,zero_div] at lower
    rw [←hX,mul_zero] at upper
    rw [le_antisymm upper lower,←hX,sub_self,abs_zero]
    positivity
  have yp : 0<Y := (div_pos hX (by positivity)).trans_le lower
  have lo := log_le_log (div_pos hX (by positivity)) lower
  have hi := log_le_log yp upper
  rw [log_div hX.ne' (by positivity),log_mul (by norm_num) (by positivity),log_pow] at lo
  rw [log_mul (by norm_num) hX.ne'] at hi
  exact abs_le.mpr ⟨by norm_num at *; linarith,by norm_num at *; linarith⟩

end Cogentic.Construction

namespace Cogentic.Window
open Real

/-- Moving a saddle center by at most `D` band logarithms changes each
prime weight by at most `8*D/u`. -/
theorem prime_weight_of_saddle_gap (J : Finset ℕ) (α β H u D : ℝ)
    (ha : 0 ≤ α) (hb : 0 ≤ β) (hH : 0 < H) (hu : 0 < u)
    (small : 4*D ≤ u)
    (hJ : ∀ p ∈ J, 1 ≤ p) (hband : ∀ p ∈ J, H/2 ≤ log p ∧ log p ≤ H)
    (ma : H*u ≤ saddleMean J α) (mb : H*u ≤ saddleMean J β)
    (near : |saddleMean J α-saddleMean J β| ≤ D*H) (q : ℕ) (hq : q ∈ J) :
    |(q:ℝ)^(-α)/(q:ℝ)^(-β)-1| ≤ 8*D/u := by
  have close (a b : ℝ) (s : 0≤a) (ab : a≤b) (lo : H*u ≤ saddleMean J b)
      (hi : saddleMean J a-saddleMean J b ≤ D*H) : (b-a)*H ≤ 4*D/u := by
    have z := (saddle_displacement J a b H s ab hH.le hJ hband).1
    have y := mul_le_mul_of_nonneg_left lo (mul_nonneg (sub_nonneg.mpr ab) hH.le)
    apply (le_div_iff₀ hu).mpr
    apply (mul_le_mul_iff_right₀ hH).mp
    nlinarith only [z,y,hi]
  have h : |β-α| * H ≤ 4*D/u := by
    rcases le_total α β with ab | ba
    · rw [abs_of_nonneg (sub_nonneg.mpr ab)]
      exact close α β ha ab mb (abs_le.mp near).2
    · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr ba)]
      apply close β α hb ba ma
      linarith [(abs_le.mp near).1]
  have qp : (0:ℝ)<q := by exact_mod_cast (hJ q hq)
  have ql : 0 ≤ log q := by exact log_nonneg (by exact_mod_cast hJ q hq)
  have e : |(β-α)*log q| ≤ 4*D/u := by
    rw [abs_mul,abs_of_nonneg ql]
    exact (mul_le_mul_of_nonneg_left (hband q hq).2 (abs_nonneg _)).trans h
  have f := Real.abs_exp_sub_one_le (e.trans ((div_le_one hu).mpr small))
  have id : (q:ℝ)^(-α)/(q:ℝ)^(-β)=exp ((β-α)*log q) := by
    rw [Real.rpow_def_of_pos qp,Real.rpow_def_of_pos qp,← exp_sub]
    congr 1; ring
  rw [id]
  calc _ ≤ 2*|(β-α)*log q| := f
       _ ≤ 2*(4*D/u) := by gcongr
       _ = _ := by ring

/-- At marks within one two-hundredth of the band logarithm of the
    reference center, every single-prime insertion weight changes by
    at most 1/(25u) in relative value. -/
theorem neighboring_prime_weight (J : Finset ℕ) (α β H u : ℝ)
    (ha : 0 ≤ α) (hb : 0 ≤ β) (hH : 0 < H) (hu : 1 ≤ u)
    (hJ : ∀ p ∈ J, 1 ≤ p) (hband : ∀ p ∈ J, H/2 ≤ log p ∧ log p ≤ H)
    (ma : H*u ≤ saddleMean J α) (mb : H*u ≤ saddleMean J β)
    (near : |saddleMean J α-saddleMean J β| ≤ H/200) (q : ℕ) (hq : q ∈ J) :
    |(q:ℝ)^(-α)/(q:ℝ)^(-β)-1| ≤ 1/(25*u) := by
  have bound := prime_weight_of_saddle_gap J α β H u (1/200)
    ha hb hH (by linarith) (by linarith) hJ hband ma mb (by linarith only [near]) q hq
  convert bound using 1 <;> ring

/-- Prime weights at the actual constructed mark are uniformly close to
    the amplitude-saddle weights, including for displaced conditional means. -/
theorem mark_prime_weight {n ell a : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (cap : a ≤ Fixed.A (n.log2+1))
    (grid : Construction.onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a)
    (side : Bool) (Y : ℝ) (shift : |Y-(Construction.exactMean n ell a side:ℝ)| ≤
        4*((n.log2+1:ℕ):ℝ)^3*Construction.referenceWidth n)
    (J : Finset ℕ) (α β u : ℝ) (q : ℕ) (hq : q∈J) :
    let H := log (Fixed.B (n.log2+1))
    0 ≤ α → 0 ≤ β → 0 < H → 1 ≤ u → (∀ p∈J, 1 ≤ p) →
    (∀ p∈J, H/2 ≤ log p ∧ log p ≤ H) → H*u ≤ log Y →
    H*u ≤ log (Construction.amplitude n) → saddleMean J α = log Y →
    saddleMean J β = log (Construction.amplitude n) →
    |(q:ℝ)^(-α)/(q:ℝ)^(-β)-1| ≤ 1/(25*u) := by
  intro H ha hb hH hu hJ hband ya yb ma mb
  apply neighboring_prime_weight J α β H u ha hb hH hu hJ hband
    (ma ▸ ya) (mb ▸ yb) _ q hq
  rw [ma,mb]
  exact Construction.mark_log_displacement hn big target cap grid side Y shift

end Cogentic.Window
