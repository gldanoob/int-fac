import Cogentic.ConditionalGaussian
import Mathlib.Tactic

open Real
open scoped BigOperators

namespace Cogentic.Window

noncomputable section

private theorem event_weight_summable {A : ℤ → ℝ} (hA : Summable A) (hpos : ∀ i, 0 ≤ A i)
    (E : ℤ → Prop) [DecidablePred E] : Summable (fun i => if E i then A i else 0) :=
  Summable.of_nonneg_of_le (fun i => by split <;> first | exact hpos i | rfl)
    (fun i => by split <;> first | exact hpos i | rfl) hA

/-- Uniform multiplicative perturbations of unnormalized masses preserve
    a relative error estimate after conditioning on the whole sample space. -/
private theorem event_mass_perturbation (A W : ℤ → ℝ) {e : ℝ} (he : 0 ≤ e) (he' : e ≤ 1/2)
    (hA : Summable A) (pos : ∀ i, 0 ≤ A i) (hpos : 0 < ∑' i, A i)
    (err : ∀ i, |W i-A i| ≤ e*A i) (E : ℤ → Prop) [DecidablePred E] :
    let Z := ∑' i, A i
    let N := ∑' i, if E i then A i else 0
    let V := ∑' i, W i
    let K := ∑' i, if E i then W i else 0
    0 < V ∧ |K/V-N/Z| ≤ 4*e*(N/Z) := by
  dsimp only
  have ep : 0 ≤ 1-e := by linarith
  have bounds (i : ℤ) : (1-e)*A i ≤ W i ∧ W i ≤ (1+e)*A i := by
    have h := abs_le.mp (err i)
    constructor <;> nlinarith only [h.1,h.2]
  have wp (i : ℤ) : 0 ≤ W i := (mul_nonneg ep (pos i)).trans (bounds i).1
  have hW := Summable.of_nonneg_of_le wp (fun i => (bounds i).2) (hA.mul_left (1+e))
  let B := fun i => if E i then A i else 0
  let F := fun i => if E i then W i else 0
  have bep := event_weight_summable hA pos E
  have wep := event_weight_summable hW wp E
  have both (i : ℤ) : (1-e)*B i ≤ F i ∧ F i ≤ (1+e)*B i := by
    dsimp [F,B]
    split <;> simp [bounds i]
  let Z := ∑' i, A i
  let N := ∑' i, B i
  let V := ∑' i, W i
  let K := ∑' i, F i
  have lo : (1-e)*Z ≤ V := by
    rw [← tsum_mul_left]; exact (hA.mul_left _).tsum_le_tsum (fun i => (bounds i).1) hW
  have hi : V ≤ (1+e)*Z := by
    rw [← tsum_mul_left]; exact hW.tsum_le_tsum (fun i => (bounds i).2) (hA.mul_left _)
  have kn : (1-e)*N ≤ K := by
    rw [← tsum_mul_left]; exact (bep.mul_left _).tsum_le_tsum (fun i => (both i).1) wep
  have kx : K ≤ (1+e)*N := by
    rw [← tsum_mul_left]; exact wep.tsum_le_tsum (fun i => (both i).2) (bep.mul_left _)
  have np : 0 ≤ N := tsum_nonneg (fun i => by dsimp [B]; split <;> first | exact pos i | rfl)
  have vp : 0 < V := (mul_pos (by linarith : 0 < 1-e) hpos).trans_le lo
  change 0 < V ∧ |K/V-N/Z| ≤ 4*e*(N/Z)
  refine ⟨vp, ?_⟩
  have zp : 0 < Z := hpos
  have hhalf : Z ≤ 2*V := by
    have hh := mul_le_mul_of_nonneg_right he' zp.le
    nlinarith [lo]
  have ub := mul_le_mul_of_nonneg_right kx zp.le
  have lb := mul_le_mul_of_nonneg_right kn zp.le
  have vs := mul_le_mul_of_nonneg_left lo np
  have vl := mul_le_mul_of_nonneg_left hi np
  have cab : |K*Z-N*V| ≤ 2*e*N*Z := by
    rw [abs_le]
    constructor <;> nlinarith only [ub,lb,vs,vl]
  have eq : K/V-N/Z = (K*Z-N*V)/(V*Z) := by field_simp
  rw [eq,abs_div,abs_of_pos (mul_pos vp zp),div_le_iff₀ (mul_pos vp zp)]
  have scale := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2*e*N by positivity)
  exact cab.trans (scale.trans_eq (by field_simp; ring))

/-- Summing over a Gaussian coefficient in a congruence class whose center
    and residue may both depend on the first coordinate changes each first-
    coordinate event by an exponentially small relative amount. -/
theorem gaussian_first_marginal (c Q S M t μ : ℝ) (r m : ℤ → ℝ)
    (hQ : 0 < Q) (hM : 0 < M) (hs : 2 ≤ S/Q) (ht : 2 ≤ t/M)
    (E : ℤ → Prop) [DecidablePred E] :
    let p := fun i : ℤ => coeffGaussian (c+Q*i) μ S
    let w := fun i : ℤ => ∑' j : ℤ, p i * coeffGaussian (r i+M*j) (m i) t
    let conditional := (∑' i : ℤ, if E i then w i else 0)/(∑' i : ℤ, w i)
    let reference := Q/S*(∑' i : ℤ, if E i then p i else 0)
    let e₁ := 6*Real.exp (-π*(S/Q)^2)
    let e₂ := 12*Real.exp (-π*(t/M)^2)
    |conditional-reference| ≤ (e₂+e₁*(1+e₂))*reference := by
  dsimp only
  let p := fun i : ℤ => coeffGaussian (c+Q*i) μ S
  let A := ∑' i : ℤ, p i
  let N := ∑' i : ℤ, if E i then p i else 0
  let τ := t/M
  let e := 3*Real.exp (-π*τ^2)
  let B := Q/S*N
  let e₁ := 6*Real.exp (-π*(S/Q)^2)
  let Z := fun i : ℤ => ∑' j : ℤ, coeffGaussian (r i+M*j) (m i) t
  let w := fun i : ℤ => ∑' j : ℤ, p i*coeffGaussian (r i+M*j) (m i) t
  let P := (∑' i : ℤ, if E i then w i else 0)/(∑' i : ℤ, w i)
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have he : 0 ≤ e := by dsimp [e]; positivity
  have he' : e ≤ 1/2 := by
    have hτ' : 2 ≤ τ := ht
    have big : 6 ≤ Real.exp (π*τ^2) := by
      nlinarith [Real.add_one_le_exp (π*τ^2), Real.pi_gt_three,
        mul_nonneg Real.pi_pos.le (show 0 ≤ τ^2-4 by nlinarith)]
    have ri := inv_anti₀ (by norm_num : 0 < (6:ℝ)) big
    dsimp [e]
    rw [neg_mul,Real.exp_neg]
    linarith
  have scalar := conditional_progression_probability c Q μ S hQ hs E
  change 0 < A ∧ |N/A-B| ≤ e₁*B at scalar
  have pp (i : ℤ) : 0 ≤ p i := (Real.exp_pos _).le
  have summable : Summable p := by
    by_contra h
    exact scalar.1.ne' (tsum_eq_zero_of_not_summable h)
  have ew (i : ℤ) : |w i-τ*p i| ≤ e*(τ*p i) := by
    have zerr : |Z i/τ-1| ≤ e := by
      dsimp [Z,τ,e]
      simp_rw [coeffGaussian_progression _ _ _ _ _ hM]
      exact shifted_gaussian_normalizer _ _ (by linarith)
    rw [show Z i/τ-1 = (Z i-τ)/τ by field_simp,abs_div,abs_of_pos hτ] at zerr
    have main := mul_le_mul_of_nonneg_left ((div_le_iff₀ hτ).mp zerr) (pp i)
    change |(∑' j : ℤ, p i*coeffGaussian (r i+M*j) (m i) t)-τ*p i| ≤ _
    rw [tsum_mul_left,mul_comm τ,← mul_sub,abs_mul,abs_of_nonneg (pp i)]
    exact main.trans_eq (by ring)
  have hA : 0 < ∑' i, τ*p i := by rw [tsum_mul_left]; exact mul_pos hτ scalar.1
  have actual := (event_mass_perturbation (fun i => τ*p i) w he he'
    (summable.mul_left _) (fun i => mul_nonneg hτ.le (pp i)) hA ew E).2
  simp_rw [← mul_ite_zero,tsum_mul_left] at actual
  rw [mul_div_mul_left _ _ hτ.ne'] at actual
  change |P-N/A| ≤ 4*e*(N/A) at actual
  have maxed : N/A ≤ B+e₁*B := by linarith [(abs_le.mp scalar.2).2]
  have total := (abs_sub_le P (N/A) B).trans (add_le_add actual scalar.2)
  have err := mul_le_mul_of_nonneg_left maxed (show 0 ≤ 4*e by positivity)
  change |P-B| ≤ (12*Real.exp (-π*τ^2)+e₁*(1+12*Real.exp (-π*τ^2)))*B
  rw [show 12*Real.exp (-π*τ^2) = 4*e by dsimp [e]; ring]
  calc _ ≤ 4*e*(N/A)+e₁*B := total
       _ ≤ 4*e*(B+e₁*B)+e₁*B := by linarith only [err]
       _ = _ := by ring

/-- On the exact two-dimensional coefficient lattice obtained by CRT,
    the first polynomial evaluation has a single scalar Gaussian law. -/
theorem polynomial_first_probability (a c Q M F K : ℤ) (r : ℤ → ℤ) (s₀ s₁ c₀ c₁ : ℝ)
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) (hQ : 0 < Q) (hM : 0 < M) (hK : K ≠ 0)
    (E : ℤ → Prop) [DecidablePred E] :
    let v := s₀^2+(a:ℝ)^2*s₁^2
    let S := Real.sqrt v
    let t := s₀*s₁/S
    let μ := c₀+(a:ℝ)*c₁
    let x := fun i : ℤ => c+Q*i
    let z := fun i j : ℤ => r i+M*j
    let n := fun i => F+K*x i
    let w := fun i => ∑' j : ℤ, coeffGaussian (x i-a*z i j : ℤ) c₀ s₀ *
      coeffGaussian (z i j) c₁ s₁
    let P := (∑' i : ℤ, if E (n i) then w i else 0)/(∑' i : ℤ, w i)
    let B := (Q:ℝ)/S*(∑' i : ℤ, if E (n i) then
      coeffGaussian (n i) ((F:ℝ)+(K:ℝ)*μ) (|(K:ℝ)| * S) else 0)
    let e₁ := 6*Real.exp (-π*(S/Q)^2)
    let e₂ := 12*Real.exp (-π*(t/M)^2)
    2 ≤ S/Q → 2 ≤ t/M → |P-B| ≤ (e₂+e₁*(1+e₂))*B := by
  dsimp only
  let v := s₀^2+(a:ℝ)^2*s₁^2
  let S := Real.sqrt v
  let t := s₀*s₁/S
  let μ := c₀+(a:ℝ)*c₁
  let x := fun i : ℤ => c+Q*i
  let z := fun i j : ℤ => r i+M*j
  let n := fun i => F+K*x i
  let m := fun i => c₁+(a:ℝ)*s₁^2/v*((x i:ℝ)-μ)
  let p := fun i : ℤ => coeffGaussian (x i) μ S
  let w := fun i => ∑' j : ℤ, coeffGaussian (x i-a*z i j : ℤ) c₀ s₀ * coeffGaussian (z i j) c₁ s₁
  have joint (i j : ℤ) : coeffGaussian (x i-a*z i j : ℤ) c₀ s₀ *
      coeffGaussian (z i j) c₁ s₁ = p i*coeffGaussian (z i j) (m i) t := by
    have law := conditional_gaussian_weight (↑(x i-a*z i j : ℤ)) (↑(z i j)) c₀ c₁ a s₀ s₁ hs₀ hs₁
    dsimp only at law
    push_cast at law ⊢
    simpa only [sub_add_cancel,p,m,μ,t,S,v] using law
  have valued (i : ℤ) : coeffGaussian (n i) ((F:ℝ)+(K:ℝ)*μ) (|(K:ℝ)| * S) = p i := by
    dsimp only [n]
    push_cast
    exact conditional_second_weight (by exact_mod_cast hK) _ _ _ _
  intro hs ht
  have gm := gaussian_first_marginal c Q S M t μ (fun i => (r i:ℝ)) m
    (by exact_mod_cast hQ) (by exact_mod_cast hM) hs ht (fun i => E (n i))
  let e₁ := 6*Real.exp (-π*(S/Q)^2)
  let e₂ := 12*Real.exp (-π*(t/M)^2)
  change |(∑' i : ℤ, if E (n i) then w i else 0)/(∑' i : ℤ, w i) -
    (Q:ℝ)/S*(∑' i : ℤ, if E (n i) then coeffGaussian (n i) ((F:ℝ)+(K:ℝ)*μ) (|(K:ℝ)| * S) else 0)| ≤
    (e₂+e₁*(1+e₂))*((Q:ℝ)/S*(∑' i : ℤ, if E (n i) then
      coeffGaussian (n i) ((F:ℝ)+(K:ℝ)*μ) (|(K:ℝ)| * S) else 0))
  simp_rw [valued,w,joint]
  simpa only [p,x,z,Int.cast_add,Int.cast_mul] using gm

/-- A uniform lattice Gaussian tail by comparison with the same shifted
    Gaussian at twice the width. -/
theorem lattice_gaussian_tail (θ τ T : ℝ) (hτ : 1 ≤ τ) (hT : 0 ≤ T) :
    (∑' n : ℤ, if T*τ ≤ |(n:ℝ)-θ| then coeffGaussian n θ τ else 0) ≤
      8*τ*Real.exp (-π*T^2/2) := by
  have ht : 0 < τ := by linarith
  have h2 : 1 ≤ 2*τ := by linarith
  let F := fun n : ℤ => coeffGaussian n θ (2*τ)
  let G := Real.exp (-π*T^2/2)
  have norm := shifted_gaussian_normalizer θ (2*τ) h2
  have heft : 3*Real.exp (-π*(2*τ)^2) ≤ 1/2 := by
    have eb : 6 ≤ Real.exp (π*(2*τ)^2) := by
      nlinarith [Real.add_one_le_exp (π*(2*τ)^2), Real.pi_gt_three,
        mul_nonneg Real.pi_pos.le (show 0 ≤ (2*τ)^2-4 by nlinarith)]
    rw [neg_mul,Real.exp_neg]
    have := inv_anti₀ (by norm_num : 0 < (6:ℝ)) eb
    linarith
  have mass : ∑' n, F n ≤ 8*τ := by
    have h : (∑' n, F n)/(2*τ) ≤ 4 := by linarith [(abs_le.mp norm).2]
    have := (div_le_iff₀ (by positivity : 0 < 2*τ)).mp h
    linarith
  have sp : Summable F := by
    by_contra h
    have hz := tsum_eq_zero_of_not_summable h
    change |(∑' n : ℤ, F n)/(2*τ)-1| ≤ _ at norm
    rw [hz,zero_div,zero_sub,abs_neg,abs_one] at norm
    linarith
  let U := fun n : ℤ => if T*τ ≤ |(n:ℝ)-θ| then coeffGaussian n θ τ else 0
  have up (n : ℤ) : U n ≤ G*F n := by
    dsimp [U,F,G,coeffGaussian]
    split
    · rename_i hn
      rw [← Real.exp_add,Real.exp_le_exp]
      have s : T ≤ |((n:ℝ)-θ)/τ| := by
        rw [abs_div,abs_of_pos ht,le_div_iff₀ ht]
        exact hn
      have sq := (sq_le_sq₀ hT (abs_nonneg _)).mpr s
      rw [sq_abs] at sq
      rw [show ((n:ℝ)-θ)/(2*τ) = (((n:ℝ)-θ)/τ)/2 by field_simp]
      have a := mul_nonneg Real.pi_pos.le (sub_nonneg.mpr sq)
      nlinarith only [a,mul_nonneg Real.pi_pos.le (sq_nonneg (((n:ℝ)-θ)/τ))]
    · positivity
  have nonneg (n : ℤ) : 0 ≤ U n := by
    dsimp [U]
    split
    · exact (Real.exp_pos _).le
    · rfl
  have sum := (Summable.of_nonneg_of_le nonneg up (sp.mul_left G)).tsum_le_tsum up (sp.mul_left G)
  rw [tsum_mul_left] at sum
  exact sum.trans ((mul_le_mul_of_nonneg_left mass (Real.exp_pos _).le).trans_eq (by ring))

end

end Cogentic.Window
