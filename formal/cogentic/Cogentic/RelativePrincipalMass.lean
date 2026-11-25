import Cogentic.SaddleNormalization

namespace Cogentic.Window
open Real Set

theorem fixed_central_scale {b : ℕ} (hd : 50000 ≤ Fixed.d b) {u : ℝ}
    (uhi : u ≤ 110*(Fixed.d b:ℝ)) :
    2*log (Fixed.B b)*sqrt u ≤ 2000*exp (3*(Fixed.z b:ℝ)) := by
  let d := (Fixed.d b:ℝ)
  let z := (Fixed.z b:ℝ)
  let B := (Fixed.B b:ℝ)
  let H := log B
  have dr : 50000 ≤ d := by dsimp [d]; exact_mod_cast hd
  have db : d ≤ b := by dsimp [d]; exact_mod_cast Fixed.degree_le_bits b
  change 2*H*sqrt u ≤ 2000*exp (3*z)
  have dcap : d ≤ exp z := by
    have c : (b:ℝ) ≤ (2:ℝ)^(Fixed.z b) := by exact_mod_cast (Nat.lt_log2_self.le : b ≤ 2^(Fixed.z b))
    have t := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2)
      (by linarith [exp_one_gt_d9] : (2:ℝ) ≤ exp 1) (Fixed.z b)
    rw [←exp_nat_mul, mul_one] at t
    exact db.trans (c.trans t)
  have root : sqrt u ≤ d := (sqrt_le_left (by dsimp [d]; positivity)).mpr (by
    nlinarith only [uhi,mul_nonneg (show 0 ≤ d-110 by linarith only [dr]) (show 0≤d by linarith only [dr])])
  have raw : H = 1000*d*z*log 2 := by
    dsimp [H,B,Fixed.B,Fixed.beta,Fixed.h,d,z]
    push_cast
    rw [log_pow]
    push_cast
    ring
  have lc : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hcap : H ≤ 1000*d*z := raw.le.trans ((mul_le_mul_of_nonneg_left lc (by positivity)).trans_eq (mul_one _))
  have zcap : z ≤ exp z := by linarith [add_one_le_exp z]
  have prod := mul_le_mul (mul_le_mul dcap zcap (by positivity) (exp_pos _).le)
    (root.trans dcap) (sqrt_nonneg _) (by positivity)
  rw [show 3*z=z+z+z by ring,exp_add,exp_add]
  linarith only [mul_le_mul_of_nonneg_right hcap (sqrt_nonneg u),prod]

/-- Relative accuracy for the original Gaussian sum after division by up
to two fixed prime factors, using the saddle at the original mean. -/
theorem fixed_relative_principal_mass (line : DirichletLZerosOnLine) (k : ℕ) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ (u Y S : ℝ) (D : Finset ℕ),
    let d := (Fixed.d b:ℝ)
    let B := (Fixed.B b:ℝ)
    let H := log B
    let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    90*d ≤ u → u ≤ 110*d → H*(80*d) ≤ log Y → |H*u-log Y| ≤ 2*H →
    0 < Y → 0 < S → B^(17/200:ℝ) ≤ Y/S → Y/S ≤ B^(17/100:ℝ) → D.card ≤ b^k → D ⊆ J →
    ∃ α ∈ Icc (199/200:ℝ) 1, saddleMean J α = H*u ∧
      let F := Y^(α-1)*eulerMass (J \ D) α
      let M := omittedMass J D (primeProbability α) (fun p => log p) H (H*u-log Y)
      0 < M ∧ |2*π*gaussianMass (J \ D) Y S/(F*M)-1| ≤ C*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨C,cp,n₀,full⟩ := fixed_full_principal_mass line k (K+3) (by linarith)
  obtain ⟨n₁,central⟩ := fixed_central_mass_lower k
  obtain ⟨n₂,degree⟩ := Fixed.degree_grows 50000
  refine ⟨2000*C,by positivity,max n₀ (max n₁ n₂),?_⟩
  intro b big u Y S D d B H J ulo uhi ylo shift yp sp lo hi card sub
  obtain ⟨bn,h⟩ := max_le_iff.mp big
  obtain ⟨bc,bd⟩ := max_le_iff.mp h
  obtain ⟨α,ha,mean,err⟩ := full b bn u Y S D ulo uhi ylo yp sp lo hi card sub
  let M := omittedMass J D (primeProbability α) (fun p => log p) H (H*u-log Y)
  let F := Y^(α-1)*eulerMass (J \ D) α
  let z := (Fixed.z b:ℝ)
  have hd := degree b bd
  have dr : 50000 ≤ d := by dsimp [d]; exact_mod_cast hd
  have db : d ≤ b := by dsimp [d]; exact_mod_cast Fixed.degree_le_bits b
  have hb : 0 < b := lt_of_lt_of_le (by omega : 0 < Fixed.d b) (Fixed.degree_le_bits b)
  have hs : 1000*d ≤ H := (fixed_band_log_bounds b hb (by omega)).1
  have hp : 0 < H := by linarith
  have up : 0 < u := by linarith
  have low := central b bc u α (H*u-log Y) D ulo uhi ha.1 mean shift card sub
  change 1/(2*H*sqrt u) ≤ M at low
  have mp : 0 < M := (by positivity : 0 < 1/(2*H*sqrt u)).trans_le low
  have fp : 0 < F := mul_pos (rpow_pos_of_pos yp _) (eulerMass_pos _ _)
  have z1 : 1 ≤ z := by change (1:ℝ) ≤ (↑(b.log2+1):ℝ); exact_mod_cast Nat.le_add_left 1 b.log2
  have budget := fixed_central_scale hd uhi
  refine ⟨α,ha,mean,mp,?_⟩
  change |2*π*gaussianMass (J \ D) Y S/(F*M)-1| ≤ 2000*C*exp (-K*z^2)
  rw [←div_self (mul_ne_zero fp.ne' mp.ne') (a:=F*M),←sub_div,abs_div,abs_of_pos (mul_pos fp mp)]
  apply (div_le_iff₀ (mul_pos fp mp)).mpr
  change |2*π*gaussianMass (J \ D) Y S-F*M| ≤ C*F*exp (-(K+3)*z^2) at err
  refine err.trans ?_
  have scale := (div_le_iff₀ (by positivity : 0 < 2*H*sqrt u)).mp low
  have den : 1 ≤ 2000*exp (3*z)*M :=
    scale.trans ((mul_le_mul_of_nonneg_left budget mp.le).trans_eq (mul_comm ..))
  have rate : exp (-(K+3)*z^2)*exp (3*z) ≤ exp (-K*z^2) := by
    rw [←exp_add,exp_le_exp]
    nlinarith only [mul_nonneg (sub_nonneg.mpr z1) (show 0≤z by linarith only [z1])]
  have x := mul_le_mul_of_nonneg_left den (le_of_lt (mul_pos (mul_pos cp fp) (exp_pos (-(K+3)*z^2))))
  have y := mul_le_mul_of_nonneg_right rate (show 0≤2000*C*F*M by positivity)
  calc C*F*exp (-(K+3)*z^2) ≤ C*F*exp (-(K+3)*z^2)*(2000*exp (3*z)*M) := by simpa only [mul_one] using x
       _ = (exp (-(K+3)*z^2)*exp (3*z))*(2000*C*F*M) := by ring
       _ ≤ _ := y.trans_eq (by ring)

end Cogentic.Window
