import Cogentic.PrincipalContour
import Cogentic.SaddleLocation

namespace Cogentic.Window
open Set MeasureTheory Complex

noncomputable def gaussianMass (J : Finset ℕ) (Y S : ℝ) : ℝ :=
  ∑ n ∈ squarefreeSupport J, gaussian Y S n

/-- Cutting the *actual sum* off at height T on the saddle line costs at
    most an exponentially small Gaussian tail times the real Euler product. -/
theorem principal_truncation (J : Finset ℕ) (prime : ∀ p ∈ J, p.Prime)
    (Y S α T : ℝ) (hY : 0 < Y) (hS : 0 < S) (hR : 1 ≤ Y/S)
    (hl : 1/2 ≤ α) (hu : α ≤ 1) (hT : 0 ≤ T) :
    |2*Real.pi*gaussianMass J Y S - (vertical (principalIntegrand J Y S) α (-T) T).re| ≤
      eulerMass J α*((Y^α/S*4*Real.exp (Real.pi/4+1))*(2*(4*(Y/S)))*Real.exp (-T/(4*(Y/S)))) := by
  let W := fun x : ℝ => (gaussian Y S x:ℂ)
  let line := fun t : ℝ => (α:ℂ)+(t:ℂ)*Complex.I
  let f := fun t : ℝ => principalIntegrand J Y S (line t)
  let M := fun t : ℝ => ‖mellin W (line t)‖
  have pc (t : ℝ) : (line t).re = α := by simp [line]
  have jpos (p : ℕ) (hp : p∈J) := (prime p hp).pos
  have env (t : ℝ) : ‖f t‖ ≤ eulerMass J α*M t := by
    rw [show ‖f t‖ = ‖principalEuler J (line t)‖*M t by exact norm_mul ..]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have h := principalEuler_critical_norm J jpos α (-t)
    simpa [line] using h
  have mi : Integrable M := (gaussian_vertical_integrable Y S α hY hS hR hl hu).norm
  have c : Continuous f := continuous_iff_continuousAt.mpr fun t =>
    (principalIntegrand_differentiableAt J jpos Y S hS (line t) (by rw [pc]; linarith)).continuousAt.comp
      (by dsimp [line]; fun_prop)
  have fi : Integrable f := (mi.const_mul (eulerMass J α)).mono' c.aestronglyMeasurable
    (Filter.Eventually.of_forall env)
  have one (n : ℕ) : (1:DirichletCharacter ℂ 1) (n:ZMod 1) = 1 := by
    rw [Subsingleton.elim (n:ZMod 1) 1,map_one]
  have inv := squarefree_mellin J prime (1:DirichletCharacter ℂ 1) α W
    (gaussian_mellin_convergent Y S α hY hS hR hl hu)
    (gaussian_vertical_integrable Y S α hY hS hR hl hu) (by dsimp [W,gaussian]; fun_prop)
  simp only [twist,one,one_mul,mul_one] at inv
  have eq : ((2*Real.pi*gaussianMass J Y S:ℝ):ℂ) = ∫ t : ℝ, f t := by
    rw [Complex.ofReal_mul,show ((gaussianMass J Y S:ℝ):ℂ) = ∑ n ∈ squarefreeSupport J, W n by
      simp [gaussianMass,W],inv,← mul_assoc,← Complex.ofReal_mul]
    rw [show (2*Real.pi)*(1/(2*Real.pi)) = 1 by field_simp,Complex.ofReal_one,one_mul]
    rfl
  have order : -T ≤ T := by linarith
  have split := integral_add_compl (s := Icc (-T) T) measurableSet_Icc fi
  have compl : (Icc (-T) T)ᶜ = {t : ℝ | T < |t|} := by
    ext t
    simp only [mem_compl_iff,mem_Icc,mem_ofPred_eq,not_and_or,not_le,lt_abs,lt_neg]
    tauto
  rw [compl,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le order] at split
  have tail := (gaussian_mellin_integral_bounds Y S α T hY hS hR hl hu hT).2
  have cut := (integral_mono (μ := volume.restrict {t : ℝ | T < |t|}) fi.norm.integrableOn
    (mi.const_mul (eulerMass J α)).integrableOn env)
  rw [integral_const_mul] at cut
  have delta : ((2*Real.pi*gaussianMass J Y S:ℝ):ℂ) - vertical (principalIntegrand J Y S) α (-T) T =
      ∫ t in {t : ℝ | T < |t|}, f t := by
    rw [eq,← split]
    change ((∫ x in -T..T, f x) + _ - (∫ x in -T..T, f x)) = _
    abel
  have rr := congrArg Complex.re delta
  rw [Complex.sub_re,Complex.ofReal_re] at rr
  rw [rr]
  exact (Complex.abs_re_le_norm _).trans ((norm_integral_le_integral_norm _).trans
    (cut.trans (mul_le_mul_of_nonneg_left tail (eulerMass_pos ..).le)))

private theorem euler_norm (J : Finset ℕ) (hp : ∀ p ∈ J, 0 < p) (α t : ℝ) :
    ‖principalEuler J ((α:ℂ)+(t:ℂ)*Complex.I)‖ =
      eulerMass J α*‖saddleCharacteristic J (primeProbability α) (fun p => Real.log p) (-t)‖ := by
  have eq := congrArg norm (saddle_characteristic_euler J hp α (-t))
  have castE : (eulerMass J α:ℂ) = ∏ p ∈ J, (1+(((p:ℝ)^(-α):ℝ):ℂ)) := by simp [eulerMass]
  rw [norm_div,norm_mul,← castE,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (eulerMass_pos ..)] at eq
  simp only [Complex.ofReal_neg,neg_mul,sub_neg_eq_add,Complex.norm_exp,Complex.neg_re,
    Complex.neg_im,Complex.mul_re,Complex.I_re, Complex.I_im,Complex.ofReal_im,Complex.ofReal_re,
    mul_zero,zero_mul,sub_zero,neg_zero,Real.exp_zero,one_mul,Complex.mul_im,add_zero] at eq
  rw [eq_div_iff (eulerMass_pos J α).ne'] at eq
  linarith

/-- The middle-frequency segment between 1/log(B) and 1 for either sign.
    The bound applies also at centers displaced from the common saddle. -/
theorem principal_middle_bound (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B Y S α sign : ℝ) (D : Finset ℕ), 16 ≤ B → 0 < Y → 0 < S →
      1 ≤ Y/S → 199/200 ≤ α → α ≤ 1 → 2 ≤ (1-α)*Real.log B → |sign| = 1 →
      let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      D ⊆ J →
      ‖vertical (principalIntegrand (J \ D) Y S) α (sign*(1/Real.log B)) sign‖ ≤
        ((8*Real.exp 1+16)*Y^(α-1)*eulerMass (J \ D) α)*
          Real.exp ((C*(1+Real.log (3*B))^2*B^(-19/400:ℝ)+2*D.card*B^(-199/400:ℝ)-
            Real.exp ((1-α)*Real.log B-1)/(36*((1-α)*Real.log B)^3))/4) := by
  obtain ⟨C,hC,off⟩ := principal_product_off_center line
  refine ⟨C,hC,fun B Y S α sign D hB hY hS hR lo hi hLam sgn => ?_⟩
  let H := Real.log B
  let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
  dsimp only
  intro om
  have hH : 1 ≤ H := by
    apply (Real.le_log_iff_exp_le (by linarith : 0 < B)).mpr
    linarith [Real.exp_one_lt_d9]
  have hp : 0 < H := by linarith
  have short : 1/H ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
  have boundpos : 1 ≤ B^(1/5:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  let rate := Real.exp ((C*(1+Real.log (3*B))^2*B^(-19/400:ℝ)+2*D.card*B^(-199/400:ℝ)-
    Real.exp ((1-α)*H-1)/(36*((1-α)*H)^3))/4)
  let m := (8*Real.exp 1+16)*Y^(α-1)*eulerMass (J \ D) α*rate
  have jpos (p : ℕ) (mem : p ∈ J \ D) : 0 < p := (Finset.mem_filter.mp (Finset.mem_sdiff.mp mem).1).2.pos
  have point (t : ℝ) (mem : t ∈ uIoc (sign*(1/H)) sign) :
      ‖principalIntegrand (J \ D) Y S ((α:ℂ)+(t:ℂ)*Complex.I)‖ ≤ m := by
    have bnd := signed_band sgn (one_div_pos.mpr hp).le short
      (show t ∈ uIcc (sign*(1/H)) (sign*1) by simpa using uIoc_subset_uIcc mem)
    have fr : 1 ≤ |(-t)*H| := by rw [abs_mul,abs_neg,abs_of_pos hp]; exact (div_le_iff₀ hp).mp bnd.1
    have low := off B α (-t) D hB lo hi (by rw [abs_neg]; exact bnd.2.trans boundpos) hLam fr om
    have me := gaussian_mellin_uniform Y S (α+t*Complex.I) hY hS hR (by simp; linarith) (by simpa)
    simp only [Complex.add_re, Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im,neg_zero,add_zero] at me
    change ‖saddleCharacteristic (J \ D) (primeProbability α) (fun p => Real.log p) (-t)‖ ≤ rate at low
    rw [principalIntegrand,norm_mul,euler_norm _ jpos]
    refine (mul_le_mul (mul_le_mul_of_nonneg_left low (eulerMass_pos ..).le) me (norm_nonneg _) (mul_nonneg (eulerMass_pos _ _).le (Real.exp_pos _).le)).trans_eq ?_
    dsimp only [m]; ring
  have norm := intervalIntegral.norm_integral_le_of_norm_le_const point
  have length : |sign-sign*(1/H)| ≤ 1 := by
    rw [show sign-sign*(1/H) = sign*(1-1/H) by ring,abs_mul,sgn,one_mul,abs_of_nonneg (by linarith)]
    linarith [one_div_pos.mpr hp]
  have positive : 0 ≤ m := by dsimp [m,rate]; positivity [eulerMass_pos (J \ D) α]
  exact norm.trans ((mul_le_mul_of_nonneg_left length positive).trans_eq (mul_one m))

/-- A finite saddle-point approximation to the original squarefree Gaussian
    sum, with all parts of both frequency wings, the lost primes, and the
    Gaussian tails charged explicitly. The same tilt is allowed at shifted Y. -/
theorem full_principal_mass (line : DirichletLZerosOnLine) :
    ∃ Cw Cm : ℝ, 0 ≤ Cw ∧ 0 ≤ Cm ∧ ∀ (B Y S β γ α T₁ T : ℝ) (D : Finset ℕ),
      16 ≤ B → 1 ≤ Y → 0 < S → 1 ≤ Y/S → 199/200 ≤ β → β ≤ γ → γ ≤ α → α ≤ 1 →
      1 ≤ T₁ → T₁ ≤ T → T ≤ B^(1/5:ℝ) → 2 ≤ (1-α)*Real.log B →
      let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      D ⊆ J →
      let H := Real.log B
      let E := eulerMass (J \ D) α
      let F := Y^(α-1)*E
      let cap := contourCap Cw B Y D.card
      let wing := (T₁-1)*cap γ γ 1 + (T-T₁)*cap β β T₁ + (α-γ)*cap γ α 1 +
        (γ-β)*cap β γ T₁ + (α-β)*cap β α T
      let middle := (8*Real.exp 1+16)*F*Real.exp ((Cm*(1+Real.log (3*B))^2*B^(-19/400:ℝ)+
        2*D.card*B^(-199/400:ℝ) - Real.exp ((1-α)*H-1)/(36*((1-α)*H)^3))/4)
      let tail := E*((Y^α/S*4*Real.exp (Real.pi/4+1))*(2*(4*(Y/S)))*Real.exp (-T/(4*(Y/S))))
      |2*Real.pi*gaussianMass (J \ D) Y S -
        F*omittedMass J D (primeProbability α) (fun p => Real.log p) H (saddleMean J α-Real.log Y)| ≤
        tail + 2*(middle+wing) + F*(48/(Real.pi*(Y/S)*H)) := by
  obtain ⟨Cw,hCw,w⟩ := principal_wing_bound line
  obtain ⟨Cm,hCm,m⟩ := principal_middle_bound line
  refine ⟨Cw,Cm,hCw,hCm,fun B Y S β γ α T₁ T D hB hY hS hR lo bg ga al t1 t12 tB hLam => ?_⟩
  dsimp only
  intro omitted
  let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
  let H := Real.log B
  let K := principalIntegrand (J \ D) Y S
  let G (x : ℝ) := K ((α:ℂ)+(x:ℂ)*Complex.I)
  let L := 1/H
  let cap := contourCap Cw B Y D.card
  let wing := (T₁-1)*cap γ γ 1 + (T-T₁)*cap β β T₁ + (α-γ)*cap γ α 1 +
        (γ-β)*cap β γ T₁ + (α-β)*cap β α T
  let F := Y^(α-1)*eulerMass (J \ D) α
  let middle := (8*Real.exp 1+16)*F*Real.exp ((Cm*(1+Real.log (3*B))^2*B^(-19/400:ℝ)+
        2*D.card*B^(-199/400:ℝ)-Real.exp ((1-α)*H-1)/(36*((1-α)*H)^3))/4)
  have hH : 1 ≤ H := (Real.le_log_iff_exp_le (by linarith : 0 < B)).mpr (by linarith [Real.exp_one_lt_d9])
  have half : 1/2 ≤ α := by linarith
  have ypos : 0 < Y := zero_lt_one.trans_le hY
  have jprime (p : ℕ) (hp : p ∈ J) := (Finset.mem_filter.mp hp).2
  have jp (p : ℕ) (hp : p ∈ J \ D) := (jprime p (Finset.mem_sdiff.mp hp).1).pos
  have gc : Continuous G := continuous_iff_continuousAt.mpr (fun x =>
    (principalIntegrand_differentiableAt _ jp Y S hS _ (by simp; linarith)).continuousAt.comp (by fun_prop))
  have add (a b c : ℝ) : vertical K α a b + vertical K α b c = vertical K α a c :=
    intervalIntegral.integral_add_adjacent_intervals (gc.intervalIntegrable a b) (gc.intervalIntegrable b c)
  have sides (s : ℝ) (hs : |s| = 1) : ‖vertical K α (s*L) (s*T)‖ ≤ middle+wing := by
    have ww := w B Y S β γ α 1 T₁ T s D hB hY hS hR lo bg ga al zero_lt_one t1 t12 tB hs omitted
    simp only [mul_one] at ww
    have mm := m B Y S α s D hB ypos hS hR (lo.trans (bg.trans ga)) al hLam hs omitted
    have mid : ‖vertical K α (s*L) s‖ ≤ middle := by
      convert mm using 1; dsimp [middle,F,H]; ring
    rw [← add (s*L) s (s*T)]
    exact (norm_add_le ..).trans (add_le_add mid ww)
  have plus : ‖vertical K α L T‖ ≤ middle+wing := by simpa using sides 1 (by norm_num)
  have minus : ‖vertical K α (-T) (-L)‖ ≤ middle+wing := by
    have h : ‖vertical K α (-L) (-T)‖ ≤ middle+wing := by simpa using sides (-1) (by norm_num)
    rwa [vertical,intervalIntegral.integral_symm,norm_neg] at h
  have rims : |(vertical K α (-T) T).re - (vertical K α (-L) L).re| ≤ 2*(middle+wing) := by
    rw [← add (-T) L T,← add (-T) (-L) L,Complex.add_re,Complex.add_re]
    have down := (Complex.abs_re_le_norm _).trans minus
    have up := (Complex.abs_re_le_norm _).trans plus
    rw [abs_le]; constructor <;> linarith [(abs_le.mp down).1,(abs_le.mp down).2,(abs_le.mp up).1,(abs_le.mp up).2]
  have central := principal_central_mellin J D (fun p hp => (jprime p hp).pos)
    α H Y S half al hH ypos hS hR
  have id : (∫ x in -L..L, (principalEuler (J \ D) (α-x*Complex.I)*
      mellin (fun t : ℝ => (gaussian Y S t:ℂ)) (α-x*Complex.I)).re) = (vertical K α (-L) L).re := by
    have flip := intervalIntegral.integral_comp_neg (a := -L) (b := L) (fun x : ℝ => (G x).re)
    simp only [neg_neg] at flip
    have ri : (∫ x in -L..L, (G x).re) = (vertical K α (-L) L).re :=
      intervalIntegral.intervalIntegral_re (gc.intervalIntegrable _ _)
    refine Eq.trans ?_ (flip.trans ri)
    apply intervalIntegral.integral_congr
    intro x _
    simp [G,K,principalIntegrand,sub_eq_add_neg]
  dsimp only at central
  dsimp only [L] at id
  rw [id] at central
  have tail := principal_truncation (J \ D) (fun p hp => jprime p (Finset.mem_sdiff.mp hp).1)
    Y S α T ypos hS hR half al (by linarith)
  have all := (abs_sub_le (2*Real.pi*gaussianMass (J \ D) Y S) (vertical K α (-T) T).re
    (F*omittedMass J D (primeProbability α) (fun p => Real.log p) H (saddleMean J α-Real.log Y))).trans
    (add_le_add tail ((abs_sub_le _ (vertical K α (-L) L).re _).trans (add_le_add rims central)))
  dsimp only [F,J,H,middle,wing,cap] at all
  linarith

end Cogentic.Window
