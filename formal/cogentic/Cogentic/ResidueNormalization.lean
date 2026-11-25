import Cogentic.RelativePrincipalMass
import Cogentic.PrincipalResidue

namespace Cogentic.Window
open Real Set

theorem shallow_fixed_saddle (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ (u α : ℝ),
      let d := (Fixed.d b:ℝ)
      let B := (Fixed.B b:ℝ)
      let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      u ≤ 110*d → 199/200 ≤ α → α ≤ 1 → saddleMean J α = log B*u → 999/1000 ≤ α := by
  obtain ⟨C,cpos,margin⟩ := fixed_saddle_euler_margin line
  obtain ⟨n,overhead⟩ := fixed_prime_overhead C cpos 0
  obtain ⟨n₁,grow⟩ := Fixed.degree_grows 50000
  refine ⟨max n n₁,?_⟩
  intro b huge u α d B J ub lo hi mean
  obtain ⟨bn,bd⟩ := max_le_iff.mp huge
  have hd := grow b bd
  have hb := hd.trans (Fixed.degree_le_bits b)
  have d0 : 50000 ≤ d := by dsimp [d]; exact_mod_cast hd
  have hlow : 1000*d ≤ log B := (fixed_band_log_bounds b (by omega) (by omega)).1
  have hp : 0 < log B := by linarith
  have bp : 0 < B := by dsimp [B,Fixed.B]; positivity
  have bl : 16 ≤ B := by linarith [add_one_le_exp (log B),exp_log bp]
  have small := overhead b bn ∅ (by simp)
  simp only [Finset.card_empty,Nat.cast_zero,zero_mul,add_zero] at small
  have tilt : (1-α)*log B ≤ d := by
    by_cases lt : 2 ≤ (1-α)*log B
    · have est := (margin B α u ∅ bl lo hi (small.trans (by norm_num)) (Finset.empty_subset _) mean lt).2.1
      by_cases arg : 0 < 16*u+4
      · have tay := pow_div_factorial_le_exp (d/2) (by positivity) 2
        norm_num at tay
        have cap : 16*u+4 ≤ exp (d/2) := by
          nlinarith only [tay,ub,d0,mul_nonneg (show 0≤d-20000 by linarith only [d0]) (show 0≤d by linarith only [d0])]
        have lg := log_le_log arg cap
        rw [log_exp] at lg
        linarith
      · have nn : 0 ≤ saddleMean J α := Finset.sum_nonneg (fun p h =>
          mul_nonneg (by unfold primeProbability; positivity) (log_nonneg (by exact_mod_cast (Finset.mem_filter.mp h).2.one_le)))
        rw [mean] at nn
        have un := (mul_nonneg_iff_of_pos_left hp).mp nn
        linarith
    · linarith
  by_contra! contrary
  have h := mul_lt_mul_of_pos_right contrary hp
  linarith

/-- The nonprincipal character error on the fixed schedule is negligible
relative to the full principal saddle model even after two insertions. -/
theorem fixed_character_relative (line : DirichletLZerosOnLine) (k : ℕ) (K : ℝ) (hK : 1 ≤ K) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ (u α Y : ℝ) (D : Finset ℕ),
    let d := (Fixed.d b:ℝ)
    let B := (Fixed.B b:ℝ)
    let H := log B
    let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    90*d ≤ u → u ≤ 110*d → 199/200 ≤ α → α ≤ 1 → saddleMean J α=H*u →
    D.card ≤ b^k → D ⊆ J → 1 ≤ Y → H*(80*d) ≤ log Y → |H*u-log Y| ≤ 2*H →
    let F := Y^(α-1)*eulerMass (J \ D) α
    let M := omittedMass J D (primeProbability α) (fun p => log p) H (H*u-log Y)
    Y^(-3/1000:ℝ) ≤ 2000*F*M*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨n₀,shallow⟩ := shallow_fixed_saddle line
  obtain ⟨n₁,central⟩ := fixed_central_mass_lower k
  obtain ⟨n₂,exponential⟩ := fixed_band_power_savings (K+3) (by linarith)
  obtain ⟨n₃,grow⟩ := Fixed.degree_grows 50000
  refine ⟨max n₀ (max n₁ (max n₂ n₃)),?_⟩
  intro b big u α Y D d B H J ulo uhi lo hi mean card sub hy ly shift F M
  obtain ⟨bs,h⟩ := max_le_iff.mp big
  obtain ⟨bc,h⟩ := max_le_iff.mp h
  obtain ⟨be,bg⟩ := max_le_iff.mp h
  have hd := grow b bg
  have hb := hd.trans (Fixed.degree_le_bits b)
  have dr : 50000 ≤ d := by dsimp [d]; exact_mod_cast hd
  have hlow : 1000*d ≤ H := (fixed_band_log_bounds b (by omega) (by omega)).1
  have hp : 0 < H := by linarith
  have up : 0 < u := by linarith
  have yp := zero_lt_one.trans_le hy
  have bp : 0 < B := by dsimp [B,Fixed.B]; positivity
  let z := (Fixed.z b:ℝ)
  have z1 : 1 ≤ z := by change (1:ℝ) ≤ (↑(b.log2+1):ℝ); exact_mod_cast Nat.le_add_left 1 b.log2
  have base := character_error_at_saddle Y α (J \ D) hy (shallow b bs u α uhi lo hi mean)
  have minM := central b bc u α (H*u-log Y) D ulo uhi lo mean shift card sub
  change 1/(2*H*sqrt u) ≤ M at minM
  have mp : 0 < M := (by positivity : 0 < 1/(2*H*sqrt u)).trans_le minM
  have fp : 0 < F := mul_pos (rpow_pos_of_pos yp _) (eulerMass_pos _ _)
  have pay := (div_le_iff₀ (by positivity : 0 < 2*H*sqrt u)).mp minM
  have overhead := pay.trans (mul_le_mul_of_nonneg_left (fixed_central_scale hd uhi) mp.le)
  have save : Y^(-1/500:ℝ) ≤ exp (-(K+3)*z^2) := by
    refine le_trans ?_ (exponential b be)
    rw [rpow_def_of_pos yp,rpow_def_of_pos bp,exp_le_exp]
    change log Y*(-1/500) ≤ H*(-17/200)
    nlinarith only [ly,hp.le,mul_le_mul_of_nonneg_right dr hp.le]
  have rate : exp (-(K+3)*z^2)*exp (3*z) ≤ exp (-K*z^2) := by
    rw [←exp_add,exp_le_exp]
    nlinarith only [mul_nonneg (sub_nonneg.mpr z1) (show 0≤z by linarith only [z1])]
  have x := mul_le_mul_of_nonneg_left overhead (mul_nonneg fp.le (exp_pos (-(K+3)*z^2)).le)
  have y := mul_le_mul_of_nonneg_right rate (show 0≤2000*F*M by positivity)
  calc Y^(-3/1000:ℝ) ≤ F*exp (-(K+3)*z^2) := base.trans (mul_le_mul_of_nonneg_left save fp.le)
       _ ≤ F*exp (-(K+3)*z^2)*(M*(2000*exp (3*z))) := by simpa only [mul_one] using x
       _ = (exp (-(K+3)*z^2)*exp (3*z))*(2000*F*M) := by ring
       _ ≤ _ := y.trans_eq (by ring)

end Cogentic.Window
