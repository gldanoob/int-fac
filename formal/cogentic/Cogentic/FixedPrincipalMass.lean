import Cogentic.FixedErrorBudget
import Cogentic.SaddleComparison

namespace Cogentic.Window
open Real Set

set_option maxHeartbeats 800000 in

/-- At the fixed degree and band, the full squarefree window has
exponentially small error relative to its Euler prefactor, uniformly in
polynomially many omissions, shifted centers and all allowed widths. -/
theorem fixed_full_principal_mass (line : DirichletLZerosOnLine) (k : ℕ) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ (u Y S : ℝ) (D : Finset ℕ),
    let d := (Fixed.d b:ℝ)
    let B := (Fixed.B b:ℝ)
    let H := log B
    let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    90*d ≤ u → u ≤ 110*d → H*(80*d) ≤ log Y → 0 < Y → 0 < S →
    B^(17/200:ℝ) ≤ Y/S → Y/S ≤ B^(17/100:ℝ) → D.card ≤ b^k → D ⊆ J →
    ∃ α ∈ Icc (199/200:ℝ) 1, saddleMean J α = H*u ∧
      let E := eulerMass (J \ D) α
      let F := Y^(α-1)*E
      |2*π*gaussianMass (J \ D) Y S -
        F*omittedMass J D (primeProbability α) (fun p => log p) H (H*u-log Y)| ≤
        C*F*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨Cw,Cm,cw,cm,full⟩ := full_principal_mass line
  obtain ⟨Cp,cp,locate⟩ := middle_loss_at_saddle line
  obtain ⟨nw,wings⟩ := eventual_fixed_saddle_wings line Cw cw k
  obtain ⟨np,ovp⟩ := fixed_prime_overhead Cp cp k
  obtain ⟨nm,ovm⟩ := fixed_prime_overhead Cm cm k
  obtain ⟨ns,saving⟩ := fixed_band_power_savings K hK
  obtain ⟨nc,midCut⟩ := fixed_middle_savings K hK
  obtain ⟨nd,degree⟩ := Fixed.degree_grows 50000
  let Dm := (8*exp 1+16)*exp (1/16)
  let C := 1+2*(Dm+5)+48/π
  refine ⟨C,by dsimp [C,Dm]; positivity,max 1 (max nd (max nw (max np (max nm (max ns nc))))),?_⟩
  intro b huge u Y S D d B H J ulo uhi ylo ypos spos rlo rhi dc om
  obtain ⟨hb,h⟩ := max_le_iff.mp huge
  obtain ⟨bd,h⟩ := max_le_iff.mp h
  obtain ⟨bw,h⟩ := max_le_iff.mp h
  obtain ⟨bp',h⟩ := max_le_iff.mp h
  obtain ⟨bm,h⟩ := max_le_iff.mp h
  obtain ⟨bs,bc⟩ := max_le_iff.mp h
  have hd := degree b bd
  have dr : 50000 ≤ d := by dsimp [d]; exact_mod_cast hd
  have lowH : 1000*d ≤ H := (fixed_band_log_bounds b hb (by omega)).1
  have H1 : 1 ≤ H := by linarith
  have hp : 0 < H := by linarith
  have bp : 0 < B := by dsimp [B,Fixed.B]; positivity
  have b16 : 16 ≤ B := by
    have e := add_one_le_exp H
    change H+1 ≤ exp (log B) at e
    rw [exp_log bp] at e; linarith
  have y1 : 1 ≤ Y := by
    apply (log_nonneg_iff ypos).mp
    exact (mul_nonneg hp.le (by linarith : 0 ≤ 80*d)).trans ylo
  have hR : 1 ≤ Y/S := (one_le_rpow (by linarith : 1 ≤ B) (by norm_num : (0:ℝ) ≤ 17/200)).trans rlo
  let v := log Y/H
  have vlo : 80*d ≤ v := (le_div_iff₀ hp).mpr (by linarith)
  have center : log Y = H*v := by dsimp [v]; field_simp
  obtain ⟨α,ha,saddle,lam,bg,ga,wing⟩ := wings b bw u v Y D ulo uhi vlo dc ypos om center
  let E := eulerMass (J \ D) α
  let F := Y^(α-1)*E
  let R := Y/S
  let T := B^(1/5:ℝ)
  let T₁ := B^(1/200:ℝ)
  let β := (199/200:ℝ)
  let γ := α-log d/2/H
  let cap := contourCap Cw B Y D.card
  let W := (T₁-1)*cap γ γ 1+(T-T₁)*cap β β T₁+(α-γ)*cap γ α 1+(γ-β)*cap β γ T₁+(α-β)*cap β α T
  let tilt := (1-α)*H
  let e := Cm*(1+log (3*B))^2*B^(-19/400:ℝ)
  let loss := (D.card:ℝ)*B^(-199/400:ℝ)
  let A := exp ((e+2*loss-exp (tilt-1)/(36*tilt^3))/4)
  let η := exp (-K*(Fixed.z b:ℝ)^2)
  have f0 : 0 ≤ F := mul_nonneg (rpow_nonneg ypos.le _) (eulerMass_pos _ _).le
  have fc := fun {a b : ℝ} (h : a ≤ b) => mul_le_mul_of_nonneg_left h f0
  have u10 : 10 ≤ u := by linarith
  have small := ovp b bp' ∅ (by simp)
  simp only [Finset.card_empty,Nat.cast_zero,zero_mul,add_zero] at small
  have rate := locate B α u b16 ha.1 ha.2 u10 small saddle
  have piece : e+loss ≤ 1/4 := ovm b bm D dc
  have e0 : 0 ≤ e := by dsimp [e]; positivity
  have charge : e+2*loss ≤ 1/2 := by linarith
  let I := u/(1152*(log (8*u+1))^3)
  change I ≤ exp (tilt-1)/(36*tilt^3) at rate
  have mid : exp ((1/4-I)/4) ≤ η := midCut b bc u (by change d ≤ u; linarith)
  have aBound : A ≤ exp (1/16)*η := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left mid (exp_pos _).le)
    rw [← exp_add]
    apply exp_le_exp.mpr
    linarith only [charge,rate]
  have log1 : 1 ≤ log (8*u+1) := (le_log_iff_exp_le (by linarith)).mpr (by linarith [exp_one_lt_d9])
  have ile : I ≤ u := div_le_self (by linarith) (by nlinarith [one_le_pow₀ (n := 3) log1])
  have wBound : W ≤ 5*F*η := by
    change W ≤ 5*F*exp (-u/2) at wing
    exact wing.trans (mul_le_mul_of_nonneg_left ((exp_le_exp.mpr (by linarith : -u/2 ≤ (1/4-I)/4)).trans mid)
      (by positivity))
  have bpow : 100 ≤ B^(1/100:ℝ) := by
    rw [rpow_def_of_pos bp]
    linarith [add_one_le_exp (log B*(1/100)),show 10000≤log B by change 10000≤H; linarith]
  have tail := fixed_gaussian_tail B Y S α (J \ D) (by linarith) ypos spos rhi bpow
  have Bcut := saving b bs
  change B^(-17/200:ℝ) ≤ η at Bcut
  have tailSave : exp (-(B^(1/50:ℝ))) ≤ η := by
    refine le_trans ?_ Bcut
    rw [rpow_def_of_pos bp,rpow_def_of_pos bp,exp_le_exp]
    have extra := pow_div_factorial_le_exp (H/50) (by positivity) 2
    norm_num at extra
    change -(exp (H*(1/50))) ≤ H*(-17/200)
    rw [show H*(1/50)=H/50 by ring]
    nlinarith only [extra,hp,mul_nonneg (show 0≤H-1000 by linarith only [lowH,dr]) hp.le]
  have central := (fixed_gaussian_central_error B R bp H1 rlo).trans
    (mul_le_mul_of_nonneg_left Bcut (by positivity))
  have t1 : 1 ≤ T₁ := one_le_rpow (by linarith : 1 ≤ B) (by norm_num)
  have t12 : T₁ ≤ T := rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have total := full B Y S β γ α T₁ T D b16 y1 spos hR le_rfl bg ga ha.2 t1 t12 le_rfl lam om
  dsimp only at total tail
  rw [mul_assoc (2:ℝ) (D.card:ℝ) (B^(-199/400:ℝ))] at total
  change |2*π*gaussianMass (J \ D) Y S - F*omittedMass J D (primeProbability α) (fun p => log p) H (saddleMean J α-log Y)| ≤
    _ + 2*((8*exp 1+16)*F*A+W) + F*(48/(π*R*H)) at total
  rw [saddle] at total
  refine ⟨α,ha,saddle,total.trans ?_⟩
  have t := tail.trans (fc tailSave)
  have m := mul_le_mul_of_nonneg_left aBound (by positivity : 0 ≤ (8*exp 1+16)*F)
  have c := fc central
  change _ ≤ C*F*η
  dsimp only [C,Dm]
  linarith only [t,m,c,wBound]

/-- The positive full-band mean determines the tilt uniquely. In particular
independent invocations of the contour estimates for different omissions
or evaluation centers use the same tilt at a common reference mean. -/
theorem band_saddle_unique {B α β : ℝ} (hb : 1 < B) (ha : 0 ≤ α) (hc : 0 ≤ β) :
    let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    0 < saddleMean J α → saddleMean J α = saddleMean J β → α=β := by
  intro J m eq
  let H := log B
  have hH : 0 < H := log_pos hb
  have bp := zero_lt_one.trans hb
  have band (p : ℕ) (hp : p ∈ J) : H/2 ≤ log p ∧ log p ≤ H := by
    obtain ⟨mem,pp⟩ := Finset.mem_filter.mp hp
    obtain ⟨lo,hi⟩ := Finset.mem_Ioc.mp mem
    constructor
    · dsimp [H]; rw [← log_sqrt bp.le]
      exact log_le_log (sqrt_pos.mpr bp) (Nat.lt_of_floor_lt lo).le
    · exact log_le_log (by exact_mod_cast pp.pos) ((Nat.cast_le.mpr hi).trans (Nat.floor_le bp.le))
  have one (p : ℕ) (hp : p ∈ J) := (Finset.mem_filter.mp hp).2.one_le
  have strict (a c : ℝ) (a0 : 0 ≤ a) (lt : a < c) (pos : 0 < saddleMean J c) :
      saddleMean J c < saddleMean J a := by
    have lower := (saddle_displacement J a c H a0 lt.le hH.le one band).1
    have : 0 < (c-a)*H*saddleMean J c/4 := by positivity
    linarith
  rcases lt_trichotomy α β with lt | same | gt
  · exact False.elim ((strict α β ha lt (eq ▸ m)).ne eq.symm)
  · exact same
  · exact False.elim ((strict β α hc gt m).ne eq)

end Cogentic.Window
