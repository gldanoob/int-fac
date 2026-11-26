import Cogentic.FixedSchedule
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Cogentic.Construction
open Finset Real
noncomputable section

/-- Centering by the unconditional raw-mesh numerator incurs only the mass
drift of the conditional model. For a fixed prescription, all cells and ordinary
and target hit patterns share the scalar center. -/
theorem mesh_numerator_center_error {C B : Type*} [Fintype C] [Fintype B]
    (M : ℕ) (mp : 0<M) [Nonempty C] (f z : C→B→ℕ→ℝ) (μ : B→ℝ) (η : ℝ)
    (norm : ∀ c j, j<M → |(∑ h,μ h*f c h j)-1|≤η) :
    let count := (Fintype.card C:ℝ)*M
    let θ := (∑ c,∑ h,μ h*(∑ j∈range M,z c h j*f c h j))/count
    |∑ c,∑ h,μ h*(∑ j∈range M,(z c h j-θ)*f c h j)|≤|θ| * count*η := by
  intro count θ
  have cp : 0<count := mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr mp)
  let d := ∑ c : C,∑ h : B,μ h*(∑ j∈range M,f c h j)
  have drift : |d-count|≤count*η := by
    have eq : d-count=∑ c : C,∑ j∈range M,((∑ h : B,μ h*f c h j)-1) := by
      dsimp only [d,count]
      simp only [mul_sum,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,mul_one,card_univ]
      congr 1
      apply sum_congr rfl;intro c _
      exact sum_comm
    rw [eq]
    apply (abs_sum_le_sum_abs ..).trans
    trans ∑ c : C,∑ j∈range M,|(∑ h : B,μ h*f c h j)-1|
    · apply sum_le_sum;intro c _;exact abs_sum_le_sum_abs ..
    have v := sum_le_sum (s:=univ) (fun (c:C) _=>sum_le_sum (s:=range M) (fun j hj=>norm c j (mem_range.mp hj)))
    simpa only [sum_const,card_range,nsmul_eq_mul,card_univ,count,mul_assoc] using v
  have numerator : (∑ c,∑ h,μ h*(∑ j∈range M,z c h j*f c h j))=θ*count := by
    dsimp only [θ];field_simp
  have id : (∑ c : C, ∑ h : B, μ h*(∑ j∈range M,(z c h j-θ)*f c h j))=θ*(count-d) := by
    simp only [sub_mul,sum_sub_distrib,mul_sub,←mul_sum,sum_sub_distrib]
    rw [numerator];dsimp only [d]
    simp only [mul_sum,mul_left_comm]
  rw [id,abs_mul,abs_sub_comm count d]
  exact (mul_le_mul_of_nonneg_left drift (abs_nonneg _)).trans_eq (mul_assoc ..).symm

/-- Centering on the entire raw mesh preserves the sparse CRT weight up to
the uniform insertion bound. The denominator is the number of mesh positions. -/
theorem mesh_numerator_budget {C B : Type*} [Fintype C] [Fintype B] [Nonempty C]
    {M : ℕ} (mp : 0<M) (μ ν : B→ℝ) (F Z : C→B→ℕ→ℝ) (D : C→B→ℝ)
    (H η : ℝ) (hv : ∀ h, |μ h|≤ν h) (vsum : 1≤∑ h,ν h ∧ ∑ h,ν h≤27)
    (hn : 0≤H) (en : 0≤η)
    (fd : ∀ c h j, j<M → |F c h j|≤H)
    (zd : ∀ c h j, j<M → |Z c h j|≤D c h)
    (norm : ∀ c j, j<M → |(∑ h,μ h*F c h j)-1|≤η) :
    let nc := (Fintype.card C:ℝ); let N := ∑ c,∑ h,ν h*D c h
    let θ := (∑ c,∑ h,μ h*(∑ j∈range M,Z c h j*F c h j))/(nc*M)
    let Nc := ∑ c : C,∑ h,ν h*(D c h+|θ|)
    |θ| *nc≤N*H ∧ Nc≤N*(1+27*H) ∧
    |∑ c,∑ h,μ h*(∑ j∈range M,(Z c h j-θ)*F c h j)|≤Nc*M*η := by
  intro nc N θ Nc
  let U := ∑ c,∑ h,μ h*(∑ j∈range M,Z c h j*F c h j)
  have cp : 0<nc := Nat.cast_pos.mpr Fintype.card_pos
  have mpos : (0:ℝ)<M := Nat.cast_pos.mpr mp
  have dn c h : 0≤D c h := (abs_nonneg _).trans (zd c h 0 mp)
  have vn h : 0≤ν h := (abs_nonneg _).trans (hv h)
  have np : 0≤N := sum_nonneg (fun c _=>sum_nonneg (fun h _=>mul_nonneg (vn h) (dn c h)))
  have ubd : |U| ≤ N*H*M := by
    dsimp only [U]
    apply (abs_sum_le_sum_abs ..).trans
    calc _ ≤ ∑ c,∑ h,|μ h*(∑ j∈range M,Z c h j*F c h j)| :=
          sum_le_sum (fun c _=>abs_sum_le_sum_abs ..)
         _ ≤ ∑ c,∑ h,ν h*((M:ℝ)*(D c h*H)) := by
          apply sum_le_sum; intro c _;apply sum_le_sum;intro h _
          rw [abs_mul]
          apply mul_le_mul (hv h) _ (abs_nonneg _) (vn h)
          apply (abs_sum_le_sum_abs ..).trans
          have v := sum_le_sum (s:=range M) (fun j hj=>mul_le_mul (zd c h j (mem_range.mp hj))
            (fd c h j (mem_range.mp hj)) (abs_nonneg _) (dn _ _))
          simpa only [abs_mul,sum_const,card_range,nsmul_eq_mul] using v
         _ = _ := by
          dsimp only [N];simp only [sum_mul]
          apply sum_congr rfl; intro c _; apply sum_congr rfl; intro h _;ring
  have tbd : |θ| *nc≤N*H := by
    change |U/(nc*M)| *nc≤_
    rw [abs_div,abs_of_pos (mul_pos cp mpos)]
    apply (le_of_mul_le_mul_right ?_ mpos)
    rwa [mul_assoc,div_mul_cancel₀ _ (mul_pos cp mpos).ne']
  have eq : Nc=N+(|θ| *nc)*(∑ h,ν h) := by
    simp only [Nc,N,mul_add,sum_add_distrib,←sum_mul,sum_const,card_univ,nsmul_eq_mul,nc];ring
  have lo : |θ| *nc≤Nc := by
    rw [eq]; exact (le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) cp.le) vsum.1).trans (le_add_of_nonneg_left np)
  refine ⟨tbd,?_,?_⟩
  · rw [eq]; have u := mul_le_mul tbd vsum.2 (zero_le_one.trans vsum.1) (mul_nonneg np hn)
    linarith only [u]
  · have v := mesh_numerator_center_error M mp F Z μ η norm
    have last := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right lo mpos.le) en
    exact v.trans (by simpa only [←mul_assoc] using last)

/-- Increasing the requested accuracy exponent by 54 absorbs the full polynomial
branch-profile loss in the physical second moment. -/
theorem branch_mesh_accuracy (b : ℕ) (bp : 0<b) (K : ℝ) :
    let d := (Fixed.d b:ℝ); let z := (Fixed.z b:ℝ)
    let A := 3*(1760*d+4)^4; let V := 40*d^2*(1760*d+4)^4*(24+32*sqrt (110*d))
    let P := 3*A^2+2*A*V
    ((1+27*A^2)*P)^2*exp (-(K+54)*z^2) ≤ (2048:ℝ)^54*exp (-K*z^2) := by
  intro d z A V P
  let t := 2048*d
  have d1 : 1≤d := by dsimp only [d];exact_mod_cast (Fixed.degree_pos bp : 1≤Fixed.d b)
  have dn := zero_le_one.trans d1
  have t2 : 2≤t := by dsimp only [t];linarith
  have t1 : 1≤t := by linarith
  have tn := zero_le_one.trans t1
  have dt : d≤t := by dsimp only [t];linarith
  have base : 1760*d+4≤t := by dsimp only [t];linarith
  have small (i j : ℕ) (ij : i≤j) : t^i≤t^j := pow_le_pow_right₀ t1 ij
  have root : sqrt (110*d)≤11*d := (sqrt_le_iff).mpr ⟨by positivity,
    by nlinarith only [mul_nonneg dn (sub_nonneg.mpr d1),dn]⟩
  have root' : 24+32*sqrt (110*d)≤t := by dsimp only [t];linarith
  have a : A≤t^5 := calc
    _ ≤ t*t^4 := by dsimp only [A];gcongr <;> first | exact base | dsimp only [t];linarith
    _ = _ := by ring
  have v : V≤t^8 := calc
    _ ≤ t*t^2*t^4*t := by dsimp only [V];gcongr <;> first | exact dt | exact base | exact root' | dsimp only [t];linarith
    _ = _ := by ring
  have an : 0≤A := by dsimp only [A];positivity
  have vn : 0≤V := by dsimp only [V];positivity
  have p : P≤t^15 := calc
    _ ≤ t*(t^5)^2+t*t^5*t^8 := by dsimp only [P];gcongr <;> first | exact a | exact v | dsimp only [t];linarith
    _ = t^11+t^14 := by ring
    _ ≤ 2*t^14 := by linarith only [small 11 14 (by decide)]
    _ ≤ t*t^14 := mul_le_mul_of_nonneg_right t2 (pow_nonneg tn _)
    _ = _ := by ring
  have u : 1+27*A^2≤t^12 := calc
    _ ≤ t^11+t*(t^5)^2 := by gcongr <;> first | exact a | exact one_le_pow₀ t1 | dsimp only [t];linarith
    _ = 2*t^11 := by ring
    _ ≤ t*t^11 := mul_le_mul_of_nonneg_right t2 (pow_nonneg tn _)
    _ = _ := by ring
  have pn : 0≤P := by dsimp only [P];positivity
  have ub : (1+27*A^2)*P≤t^27 := (mul_le_mul u p pn (pow_nonneg tn _)).trans_eq (by ring)
  have sqb : ((1+27*A^2)*P)^2≤t^54 := (pow_le_pow_left₀ (mul_nonneg (by positivity) pn) ub 2).trans_eq (by ring)
  have dexp : d≤exp z := by
    have bcap : (b:ℝ)≤(2:ℝ)^(Fixed.z b) := by exact_mod_cast (Nat.lt_log2_self.le : b ≤ 2^(Fixed.z b))
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (by linarith [exp_one_gt_d9] : (2:ℝ)≤exp 1) (Fixed.z b)
    rw [←exp_nat_mul,mul_one] at h
    exact (by dsimp only [d];exact_mod_cast Fixed.degree_le_bits b : d≤(b:ℝ)).trans (bcap.trans h)
  have z1 : 1≤z := by dsimp only [z,Fixed.z];exact_mod_cast Nat.succ_le_succ (Nat.zero_le b.log2)
  have h := pow_le_pow_left₀ dn dexp 54
  rw [←exp_nat_mul] at h
  have e := mul_le_mul_of_nonneg_right h (exp_pos (-(K+54)*z^2)).le
  rw [←exp_add] at e
  have s := e.trans (exp_le_exp.mpr (show ((54:ℕ):ℝ)*z+ -(K+54)*z^2≤ -K*z^2 by
    norm_num;nlinarith only [mul_nonneg (zero_le_one.trans z1) (sub_nonneg.mpr z1)]))
  apply (mul_le_mul_of_nonneg_right sqb (exp_pos _).le).trans
  simpa only [t,mul_pow,mul_assoc] using mul_le_mul_of_nonneg_left s (by positivity : (0:ℝ)≤2048^54)

end
end Cogentic.Construction
#print axioms Cogentic.Construction.mesh_numerator_budget
#print axioms Cogentic.Construction.branch_mesh_accuracy
