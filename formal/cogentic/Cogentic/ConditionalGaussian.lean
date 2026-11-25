import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic

open Real Set Filter Asymptotics
open scoped Real FourierTransform BigOperators

namespace Cogentic.Window

noncomputable section

/-- The unnormalized Gaussian weight on a scalar coordinate. -/
def coeffGaussian (x μ σ : ℝ) : ℝ := Real.exp (-π*((x-μ)/σ)^2)

/-- Completing the square after fixing the first evaluation coordinate. -/
theorem conditional_gaussian_weight (u₀ u₁ c₀ c₁ a s₀ s₁ : ℝ)
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) :
    let v := s₀^2+a^2*s₁^2
    let t := s₀*s₁/Real.sqrt v
    let x := u₀+a*u₁
    let μ := c₀+a*c₁
    let m := c₁ + a*s₁^2/v*(x-μ)
    coeffGaussian u₀ c₀ s₀ * coeffGaussian u₁ c₁ s₁ =
      coeffGaussian x μ (Real.sqrt v) * coeffGaussian u₁ m t := by
  dsimp [coeffGaussian]
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  have hv : 0 < s₀^2+a^2*s₁^2 := by positivity
  have hsq := Real.sq_sqrt hv.le
  simp only [div_pow]
  rw [hsq]
  field_simp
  ring

/-- Changing from a coefficient on a congruence class to the second evaluation
    scales the Gaussian width and the lattice step by the same amount. -/
theorem conditional_second_weight {d : ℝ} (hd : d ≠ 0) (x u μ t : ℝ) :
    coeffGaussian (x+d*u) (x+d*μ) (|d| * t) = coeffGaussian u μ t := by
  unfold coeffGaussian
  rw [div_pow,div_pow,mul_pow,sq_abs,show x+d*u-(x+d*μ)=d*(u-μ) by ring,mul_pow]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hd)]

/-- The shifted Gaussian Poisson identity, with its lattice-width factor explicit. -/
theorem shifted_gaussian_poisson (θ τ : ℝ) (hτ : 0 < τ) :
    ((∑' j : ℤ, coeffGaussian j θ τ : ℝ) : ℂ) =
      (τ:ℂ)* ∑' n : ℤ, (Real.exp (-π*τ^2*(n:ℝ)^2) : ℂ) *
        fourier n ((-θ : ℝ) : UnitAddCircle) := by
  let a : ℝ := (τ⁻¹)^2
  let f : ℝ → ℂ := fun x => Complex.exp (-(π:ℂ)*(a:ℂ)*(x:ℂ)^2)
  have ha : 0 < a := by dsimp [a]; positivity
  have h1 : 0 < ((π:ℂ)*a).re := by simpa using mul_pos Real.pi_pos ha
  have h2 : 0 < ((π:ℂ)/a).re := by
    rw [← Complex.ofReal_div,Complex.ofReal_re]
    positivity
  have hscale : 1/(a:ℂ)^(1/2:ℂ) = τ := by
    have hs : a^(1/2:ℝ) = τ⁻¹ := by
      rw [← Real.sqrt_eq_rpow,Real.sqrt_sq (inv_nonneg.mpr hτ.le)]
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,← Complex.ofReal_cpow ha.le,hs]
    simp
  have hF : 𝓕 f = fun x : ℝ => (τ:ℂ)*Complex.exp (-(π:ℂ)/(a:ℂ)*(x:ℂ)^2) := by
    simpa only [f,hscale] using (fourier_gaussian_pi (show 0 < (a:ℂ).re by exact ha))
  have hdec : f =O[cocompact ℝ] (|·|^(-2:ℝ)) := by
    simpa only [f,neg_mul] using (isLittleO_exp_neg_mul_sq_cocompact h1 (-2)).isBigO
  have hdecF : (𝓕 f) =O[cocompact ℝ] (|·|^(-2:ℝ)) := by
    rw [hF]
    simpa only [neg_div] using
      ((isLittleO_exp_neg_mul_sq_cocompact h2 (-2)).isBigO.const_mul_left (τ:ℂ))
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay (f := f)
    (by dsimp [f]; fun_prop) one_lt_two hdec hdecF (-θ)
  rw [Complex.ofReal_tsum,← tsum_mul_left]
  convert hp using 1
  · apply tsum_congr; intro n
    simp only [coeffGaussian,Complex.ofReal_exp,f]
    congr 1
    push_cast
    dsimp [a]
    push_cast
    ring
  · rw [hF]
    apply tsum_congr; intro n
    rw [← mul_assoc]
    congr 2
    rw [Complex.ofReal_exp]
    congr 1
    dsimp [a]
    push_cast
    ring_nf
    simp
    ring

/-- The two nonzero-frequency wings of a bilateral Fourier series. -/
private theorem bilateral_fourier_tail (f : ℤ → ℂ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hz : f 0 = 1)
    (h : ∀ n : ℕ, ‖f ((n : ℤ)+1)‖ ≤ ρ^(n+1) ∧ ‖f (-((n:ℤ)+1))‖ ≤ ρ^(n+1)) :
    ‖(∑' n : ℤ, f n)-1‖ ≤ 2*ρ/(1-ρ) := by
  have geo : HasSum (fun n : ℕ => ρ^(n+1)) (ρ/(1-ρ)) := by
    simpa only [pow_succ',div_eq_mul_inv,one_div] using
      (hasSum_geometric_of_lt_one hρ hρ').mul_left ρ
  have hp : Summable (fun n : ℕ => f ((n : ℤ)+1)) :=
    Summable.of_norm_bounded geo.summable (fun n => (h n).1)
  have hn : Summable (fun n : ℕ => f (-((n : ℤ)+1))) :=
    Summable.of_norm_bounded geo.summable (fun n => (h n).2)
  have hp0 : Summable (fun n : ℕ => f (n:ℤ)) := (summable_nat_add_iff 1).mp hp
  rw [tsum_of_nat_of_neg_add_one hp0 hn,hp0.tsum_eq_zero_add]
  simp only [Nat.cast_zero,hz,Nat.cast_add,Nat.cast_one]
  rw [show 1 + (∑' n : ℕ, f ((n:ℤ)+1)) + (∑' n : ℕ, f (-((n:ℤ)+1))) - 1 =
    (∑' n : ℕ, f ((n:ℤ)+1)) + (∑' n : ℕ, f (-((n:ℤ)+1))) by ring]
  exact (norm_add_le ..).trans ((add_le_add
    (tsum_of_norm_bounded geo (fun n => (h n).1))
    (tsum_of_norm_bounded geo (fun n => (h n).2))).trans_eq (by ring))

/-- The relative error of the scalar Gaussian progression normalizer is
    exponentially small, uniformly in the shift. -/
theorem shifted_gaussian_normalizer (θ τ : ℝ) (hτ : 1 ≤ τ) :
    |(∑' j : ℤ, coeffGaussian j θ τ)/τ-1| ≤ 3*Real.exp (-π*τ^2) := by
  have ht : 0 < τ := by linarith
  let ρ := Real.exp (-π*τ^2)
  have hpos : 0 < ρ := Real.exp_pos _
  have hr : ρ ≤ 1/3 := by
    have hp : 3 ≤ π := by linarith [Real.pi_gt_three]
    have he : 3 ≤ Real.exp (π*τ^2) := by
      nlinarith [Real.add_one_le_exp (π*τ^2),mul_nonneg Real.pi_pos.le
        (show 0 ≤ τ^2-1 by nlinarith)]
    dsimp [ρ]
    rw [neg_mul,Real.exp_neg]
    exact inv_anti₀ (by norm_num : 0 < (3:ℝ)) he |>.trans_eq (by ring)
  let f : ℤ → ℂ := fun n => (Real.exp (-π*τ^2*(n:ℝ)^2) : ℂ) *
    fourier n ((-θ : ℝ) : UnitAddCircle)
  have fnorm (n : ℤ) : ‖f n‖ = Real.exp (-π*τ^2*(n:ℝ)^2) := by
    change ‖(Real.exp (-π*τ^2*(n:ℝ)^2) : ℂ) * fourier n ((-θ:ℝ):UnitAddCircle)‖ = _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      show ‖fourier n ((-θ : ℝ) : UnitAddCircle)‖ = 1 from Circle.norm_coe _,mul_one]
  have coeff (n : ℕ) :
      ‖f ((n:ℤ)+1)‖ ≤ ρ^(n+1) ∧ ‖f (-((n:ℤ)+1))‖ ≤ ρ^(n+1) := by
    rw [fnorm,fnorm]
    dsimp [ρ]
    rw [← Real.exp_nat_mul]
    push_cast
    constructor <;> apply Real.exp_le_exp.mpr <;>
      nlinarith [mul_nonneg (show 0 ≤ π*τ^2 by positivity) (show 0 ≤ (n:ℝ)^2+n by positivity)]
  have tail := bilateral_fourier_tail f ρ hpos.le (by linarith) (by simp [f]) coeff
  have id := shifted_gaussian_poisson θ τ ht
  change _ = (τ:ℂ)*∑' n : ℤ, f n at id
  have id' : (∑' n : ℤ, f n) = ((∑' j : ℤ, coeffGaussian j θ τ : ℝ):ℂ) / τ := by
    rw [eq_div_iff (Complex.ofReal_ne_zero.mpr ht.ne'),id,mul_comm]
  rw [id',← Complex.ofReal_div,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] at tail
  exact tail.trans ((div_le_iff₀ (by linarith : 0 < 1-ρ)).mpr
    (by nlinarith [mul_nonneg hpos.le (show 0 ≤ 1/3-ρ by linarith)]))

theorem coeffGaussian_progression (c M j μ t : ℝ) (hM : 0 < M) :
    coeffGaussian (c+M*j) μ t = coeffGaussian j ((μ-c)/M) (t/M) := by
  unfold coeffGaussian
  congr 3
  field_simp
  ring

/-- Dividing by the true progression normalizer gives a relative, uniform
    error bound for the probability of any event on that progression. -/
theorem conditional_progression_probability (c M μ t : ℝ) (hM : 0 < M) (hτ : 2 ≤ t/M)
    (E : ℤ → Prop) [DecidablePred E] :
    let w := fun j : ℤ => coeffGaussian (c+M*j) μ t
    let z := ∑' j : ℤ, w j
    let n := ∑' j : ℤ, if E j then w j else 0
    0 < z ∧ |n/z - M/t*n| ≤ 6*Real.exp (-π*(t/M)^2)*(M/t*n) := by
  dsimp only
  let Z := ∑' j : ℤ, coeffGaussian (c+M*j) μ t
  let N := ∑' j : ℤ, if E j then coeffGaussian (c+M*j) μ t else 0
  let τ := t/M
  let e := 3*Real.exp (-π*τ^2)
  have ht : 0 < τ := by dsimp [τ]; linarith
  have Zerr : |Z/τ-1| ≤ e := by
    dsimp [Z,τ,e]
    simp_rw [coeffGaussian_progression _ _ _ _ _ hM]
    exact shifted_gaussian_normalizer _ _ (by linarith)
  have he : e ≤ 1/2 := by
    have hq : 2 ≤ τ := hτ
    have hπ : 3 ≤ π := Real.pi_gt_three.le
    have hx : 6 ≤ Real.exp (π*τ^2) := by
      nlinarith [Real.add_one_le_exp (π*τ^2),mul_nonneg Real.pi_pos.le
        (show 0 ≤ τ^2-4 by nlinarith)]
    dsimp [e]
    rw [neg_mul,Real.exp_neg]
    have hi := inv_anti₀ (by norm_num : 0 < (6:ℝ)) hx
    linarith
  have zp : 0 < Z := by
    have := (abs_le.mp Zerr).1
    have h : 0 < Z/τ := by linarith
    exact (div_pos_iff_of_pos_right ht).mp h
  have Zlow : τ ≤ 2*Z := by
    have low : 1/2 ≤ Z/τ := by linarith [(abs_le.mp Zerr).1]
    have := (le_div_iff₀ ht).mp low
    linarith
  have zabs : |Z-τ| ≤ τ*e := by
    have eq : Z/τ-1=(Z-τ)/τ := by field_simp
    rw [eq,abs_div,abs_of_pos ht] at Zerr
    exact ((div_le_iff₀ ht).mp Zerr).trans_eq (by ring)
  have npos : 0 ≤ N := by
    apply tsum_nonneg
    intro j
    split
    · exact (Real.exp_pos _).le
    · rfl
  change 0 < Z ∧ |N/Z - M/t*N| ≤ 6*Real.exp (-π*τ^2)*(M/t*N)
  rw [show 6*Real.exp (-π*τ^2)=2*e by dsimp [e]; ring]
  have tpos : 0 < t := (div_pos_iff_of_pos_right hM).mp ht
  have minv : M/t=1/τ := by dsimp [τ]; field_simp
  rw [minv]
  refine ⟨zp, ?_⟩
  have eq : N/Z-1/τ*N = (N/τ)*((τ-Z)/Z) := by field_simp
  rw [eq,abs_mul,abs_of_nonneg (div_nonneg npos ht.le),abs_div,abs_of_pos zp,abs_sub_comm τ Z]
  have err : |Z-τ| /Z ≤ 2*e := by
    rw [div_le_iff₀ zp]
    have ep : 0 ≤ e := by dsimp [e]; positivity
    exact zabs.trans ((mul_le_mul_of_nonneg_right Zlow ep).trans_eq (by ring))
  exact (mul_le_mul_of_nonneg_left err (div_nonneg npos ht.le)).trans_eq (by ring)

/-- The actual joint coefficient weight on a fixed first coordinate and
    a congruence class for the remaining coefficient. The second integer
    polynomial evaluation may be tested against any predicate. -/
theorem polynomial_conditional_probability (a b x c M F K : ℤ)
    (s₀ s₁ c₀ c₁ : ℝ) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) (hM : 0 < M)
    (hb : b ≠ a) (hK : K ≠ 0) (E : ℤ → Prop) [DecidablePred E] :
    let v := s₀^2+(a:ℝ)^2*s₁^2
    let t := s₀*s₁/Real.sqrt v
    let μ := c₁+(a:ℝ)*s₁^2/v*((x:ℝ)-(c₀+(a:ℝ)*c₁))
    let w := fun j : ℤ => c+M*j
    let joint := fun j : ℤ => coeffGaussian (x-a*w j : ℤ) c₀ s₀ * coeffGaussian (w j) c₁ s₁
    let value := fun j : ℤ => F+K*(x+(b-a)*w j)
    let center := (F:ℝ)+(K:ℝ)*((x:ℝ)+((b:ℝ)-(a:ℝ))*μ)
    let span := |(K:ℝ)*((b:ℝ)-(a:ℝ))|
    let window := ∑' j : ℤ, if E (value j) then coeffGaussian (value j) center (span*t) else 0
    let mass := (∑' j : ℤ, if E (value j) then joint j else 0)/(∑' j : ℤ, joint j)
    2 ≤ t/M → |mass-(M:ℝ)/t*window| ≤
      6*Real.exp (-π*(t/M)^2)*((M:ℝ)/t*window) := by
  dsimp only
  let v := s₀^2+(a:ℝ)^2*s₁^2
  let t := s₀*s₁/Real.sqrt v
  let μ := c₁+(a:ℝ)*s₁^2/v*((x:ℝ)-(c₀+(a:ℝ)*c₁))
  let w := fun j : ℤ => c+M*j
  let n := fun j : ℤ => F+K*(x+(b-a)*w j)
  let center := (F:ℝ)+(K:ℝ)*((x:ℝ)+((b:ℝ)-(a:ℝ))*μ)
  let D := (K:ℝ)*((b:ℝ)-(a:ℝ))
  let C := coeffGaussian x (c₀+(a:ℝ)*c₁) (Real.sqrt v)
  let g := fun j : ℤ => coeffGaussian (w j) μ t
  have hD : D ≠ 0 := mul_ne_zero (by exact_mod_cast hK) (sub_ne_zero.mpr (by exact_mod_cast hb))
  have cg : C ≠ 0 := (Real.exp_pos _).ne'
  have joint (j : ℤ) :
      coeffGaussian (x-a*w j : ℤ) c₀ s₀ * coeffGaussian (w j) c₁ s₁ = C*g j := by
    have eq := conditional_gaussian_weight (↑(x-a*w j : ℤ)) (↑(w j)) c₀ c₁ a s₀ s₁ hs₀ hs₁
    dsimp only at eq
    push_cast at eq ⊢
    simpa only [sub_add_cancel,C,g,v,μ,t] using eq
  have gw (j : ℤ) : coeffGaussian (n j) center (|D| * t) = g j := by
    let l := (F:ℝ)+(K:ℝ)*(x:ℝ)
    have ej : (n j:ℝ)=l+D*(w j:ℝ) := by dsimp [l,n,D]; push_cast; ring
    have ec : center=l+D*μ := by dsimp [center,l,D]; ring
    rw [ej,ec]
    exact conditional_second_weight hD _ _ _ _
  intro ht
  have qm : (0:ℝ) < M := by exact_mod_cast hM
  have cond := (conditional_progression_probability c M μ t qm ht (fun j => E (n j))).2
  have castw (j : ℤ) : ((w j : ℤ):ℝ)=(c:ℝ)+(M:ℝ)*j := by simp [w]
  change |(∑' j : ℤ, if E (n j) then
    coeffGaussian (x-a*w j : ℤ) c₀ s₀ * coeffGaussian (w j) c₁ s₁ else 0) /
    (∑' j : ℤ, coeffGaussian (x-a*w j : ℤ) c₀ s₀ * coeffGaussian (w j) c₁ s₁) -
    (M:ℝ)/t*(∑' j : ℤ, if E (n j) then coeffGaussian (n j) center (|D| * t) else 0)| ≤
    6*Real.exp (-π*(t/(M:ℝ))^2)*((M:ℝ)/t*
      (∑' j : ℤ, if E (n j) then coeffGaussian (n j) center (|D| * t) else 0))
  simp_rw [joint,gw,← mul_ite_zero,tsum_mul_left]
  rw [mul_div_mul_left _ _ cg]
  simpa only [g,castw] using cond

end

end Cogentic.Window
