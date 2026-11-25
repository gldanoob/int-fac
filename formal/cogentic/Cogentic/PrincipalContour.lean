import Cogentic.PrincipalDecay
import Cogentic.WindowCentral

namespace Cogentic.Window
open Set MeasureTheory Complex

noncomputable def principalIntegrand (J : Finset ℕ) (Y S : ℝ) (s : ℂ) : ℂ :=
  principalEuler J s * mellin (fun x : ℝ => (gaussian Y S x:ℂ)) s

theorem principalIntegrand_differentiableAt (J : Finset ℕ) (band : ∀ p ∈ J, 0 < p)
    (Y S : ℝ) (hs : 0 < S) (s : ℂ) (pos : 0 < s.re) :
    DifferentiableAt ℂ (principalIntegrand J Y S) s := by
  apply DifferentiableAt.mul _ (gaussian_mellin_differentiable Y S s hs pos)
  unfold principalEuler
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  have nz : (p:ℂ) ≠ 0 := by exact_mod_cast (band p hp).ne'
  simp_rw [Complex.cpow_def_of_ne_zero nz]
  fun_prop

noncomputable def horizontal (F : ℂ → ℂ) (l r t : ℝ) :=
  ∫ x in l..r, F ((x:ℂ)+(t:ℂ)*Complex.I)
noncomputable def vertical (F : ℂ → ℂ) (s a b : ℝ) :=
  ∫ t in a..b, F ((s:ℂ)+(t:ℂ)*Complex.I)

private theorem rect (F : ℂ → ℂ) (l r a b : ℝ) (hl : 0 < l) (lr : l ≤ r)
    (diff : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ F s) :
    horizontal F l r a - horizontal F l r b + Complex.I*vertical F r a b -
      Complex.I*vertical F l a b = 0 := by
  let z : ℂ := (l:ℂ)+(a:ℂ)*Complex.I
  let w : ℂ := (r:ℂ)+(b:ℂ)*Complex.I
  have zl : z.re = l := by simp [z]
  have wr : w.re = r := by simp [w]
  have za : z.im = a := by simp [z]
  have wb : w.im = b := by simp [w]
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w (by
    intro s hs
    have hmem := hs.1
    rw [zl,wr, uIcc_of_le lr] at hmem
    exact (diff _ (hl.trans_le hmem.1)).differentiableWithinAt)
  simpa only [horizontal,vertical,zl,wr,za,wb,smul_eq_mul] using h

/-- Exact two-rectangle deformation of a frequency wing. The three heights
    may also be negative and decreasing. -/
theorem principal_two_rectangles (J : Finset ℕ) (band : ∀ p ∈ J, 0 < p)
    (Y S β γ α a b c : ℝ) (hS : 0 < S) (hb : 0 < β) (bg : β ≤ γ) (ga : γ ≤ α) :
    let F := principalIntegrand J Y S
    Complex.I*vertical F α a c =
      Complex.I*vertical F γ a b + Complex.I*vertical F β b c -
        horizontal F γ α a - horizontal F β γ b + horizontal F β α c := by
  let F := principalIntegrand J Y S
  have dif := principalIntegrand_differentiableAt J band Y S hS
  have r1 := rect F γ α a b (hb.trans_le bg) ga dif
  have r2 := rect F β α b c hb (bg.trans ga) dif
  have cv (u v : ℝ) : IntervalIntegrable (fun t : ℝ => F ((α:ℂ)+(t:ℂ)*Complex.I)) volume u v :=
    Continuous.intervalIntegrable (continuous_iff_continuousAt.mpr fun t =>
      (dif _ (by simp; linarith)).continuousAt.comp (by fun_prop)) u v
  have ch (u v : ℝ) (hp : 0 < u) (hv : u ≤ v) :
      IntervalIntegrable (fun x : ℝ => F ((x:ℂ)+(b:ℂ)*Complex.I)) volume u v := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hv] at hx
    exact ((dif _ (by simpa using hp.trans_le hx.1)).continuousAt.comp
      (by fun_prop : ContinuousAt (fun y : ℝ => (y:ℂ)+(b:ℂ)*Complex.I) x)).continuousWithinAt
  have vadd : vertical F α a b + vertical F α b c = vertical F α a c :=
    intervalIntegral.integral_add_adjacent_intervals (cv a b) (cv b c)
  have hadd : horizontal F β γ b + horizontal F γ α b = horizontal F β α b :=
    intervalIntegral.integral_add_adjacent_intervals (ch β γ hb bg) (ch γ α (hb.trans_le bg) ga)
  change Complex.I*vertical F α a c = _
  rw [← vadd,mul_add]
  rw [← hadd] at r2
  linear_combination r1+r2

/-- Actual pointwise majorant on a pole-free wing. It is uniform on the
    horizontal segment l ≤ Re(s) ≤ r and all |Im(s)| ≥ t₀ up to B^(1/5). -/
theorem principal_contour_majorant (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B Y S l r t₀ : ℝ) (D : Finset ℕ), 16 ≤ B → 1 ≤ Y →
      0 < S → 1 ≤ Y/S → 199/200 ≤ l → r ≤ 1 → 0 < t₀ →
      let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      D ⊆ J → ∀ s : ℂ, l ≤ s.re → s.re ≤ r → t₀ ≤ |s.im| → |s.im| ≤ B^(1/5:ℝ) →
      ‖principalIntegrand (J \ D) Y S s‖ ≤ (8*Real.exp 1+16)*Y^(r-1)*
        Real.exp (6*B^(1-l)/(t₀*Real.log B) + C*(1+Real.log (3*B))^2*B^(-19/400:ℝ) +
          D.card*B^(-199/400:ℝ) + (∑' n : ℕ, (n:ℝ)^(-3/2:ℝ))/2) := by
  obtain ⟨C,hC,main⟩ := principal_euler_frequency_bound line
  refine ⟨C,hC,fun B Y S l r t₀ D hB hY hS hR hl hr ht => ?_⟩
  dsimp only
  intro omitted s sl sr tl tu
  have lo := hl.trans sl
  have hi := sr.trans hr
  have eb := main B D s hB lo hi (ht.trans_le tl) tu omitted
  have mb := gaussian_mellin_uniform Y S s (zero_lt_one.trans_le hY) hS hR (by linarith) (by linarith)
  have logpos := Real.log_pos (by linarith : 1 < B)
  have quot : 6*B^(1-s.re)/(|s.im| * Real.log B) ≤ 6*B^(1-l)/(t₀*Real.log B) :=
    div_le_div₀ (by positivity) (by gcongr; linarith) (mul_pos ht logpos)
      (mul_le_mul_of_nonneg_right tl logpos.le)
  rw [principalIntegrand,norm_mul,mul_comm]
  apply mul_le_mul (mb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hY (by linarith)) (by positivity)))
    (eb.trans (Real.exp_le_exp.mpr (by linarith))) (norm_nonneg _) (by positivity)

noncomputable def contourCap (C B Y D l r t : ℝ) : ℝ :=
  (8*Real.exp 1+16)*Y^(r-1)*Real.exp (6*B^(1-l)/(t*Real.log B) +
    C*(1+Real.log (3*B))^2*B^(-19/400:ℝ) + D*B^(-199/400:ℝ) +
    (∑' n : ℕ, (n:ℝ)^(-3/2:ℝ))/2)

theorem signed_band {sign x y t : ℝ} (sgn : |sign| = 1)
    (hx : 0 ≤ x) (xy : x ≤ y) (mem : t ∈ uIcc (sign*x) (sign*y)) : x ≤ |t| ∧ |t| ≤ y := by
  rcases abs_choice sign with he | he
  · have s : sign = 1 := he.symm.trans sgn
    rw [s,one_mul,one_mul,uIcc_of_le xy] at mem
    rwa [abs_of_nonneg (hx.trans mem.1)]
  · have s : sign = -1 := by linarith
    rw [s,neg_one_mul,neg_one_mul,uIcc_of_ge (by linarith)] at mem
    rw [abs_of_nonpos (by linarith [mem.2])]
    exact ⟨by linarith [mem.2],by linarith [mem.1]⟩

/-- The sum of the two shifted vertical segments and the three horizontal
    segments controls either full wing of the original principal integral. -/
theorem principal_wing_bound (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B Y S β γ α a b c sign : ℝ) (D : Finset ℕ), 16 ≤ B → 1 ≤ Y →
      0 < S → 1 ≤ Y/S → 199/200 ≤ β → β ≤ γ → γ ≤ α → α ≤ 1 →
      0 < a → a ≤ b → b ≤ c → c ≤ B^(1/5:ℝ) → |sign| = 1 →
      let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      D ⊆ J →
      let F := principalIntegrand (J \ D) Y S
      let cap := contourCap C B Y D.card
      ‖vertical F α (sign*a) (sign*c)‖ ≤
        (b-a)*cap γ γ a + (c-b)*cap β β b + (α-γ)*cap γ α a +
        (γ-β)*cap β γ b + (α-β)*cap β α c := by
  obtain ⟨C,hC,major⟩ := principal_contour_majorant line
  refine ⟨C,hC,fun B Y S β γ α a b c sign D hB hY hS hR lo bg ga al ap ab bc ct sgn => ?_⟩
  let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
  let F := principalIntegrand (J \ D) Y S
  let cap := contourCap C B Y D.card
  dsimp only
  intro omitted
  have jpos (p : ℕ) (hp : p ∈ J \ D) : 0 < p := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.pos
  have w := principal_two_rectangles (J \ D) jpos Y S β γ α (sign*a) (sign*b) (sign*c) hS (by linarith) bg ga
  change Complex.I*vertical F α _ _ = _ at w
  have vbd (l x y : ℝ) (ll : β ≤ l) (lr : l ≤ α) (xp : 0 < x) (xy : x ≤ y) (yc : y ≤ c) :
      ‖vertical F l (sign*x) (sign*y)‖ ≤ (y-x)*cap l l x := by
    have z := intervalIntegral.norm_integral_le_of_norm_le_const (C := cap l l x)
      (a := sign*x) (b := sign*y) (f := fun v : ℝ => F ((l:ℂ)+(v:ℂ)*Complex.I)) (by
        intro v mem
        have mt := signed_band sgn xp.le xy (uIoc_subset_uIcc mem)
        apply major B Y S l l x D hB hY hS hR (lo.trans ll) (lr.trans al) xp omitted _
        all_goals simp only [Complex.add_re, Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im,
          neg_zero,add_zero,Complex.add_im,Complex.mul_I_im,zero_add]
        exacts [le_rfl,le_rfl,mt.1,mt.2.trans (yc.trans ct)])
    rw [← mul_sub,abs_mul,sgn,one_mul,abs_of_nonneg (sub_nonneg.mpr xy)] at z
    exact z.trans_eq (mul_comm ..)
  have hbd (l r t : ℝ) (ll : β ≤ l) (lr : l ≤ r) (ra : r ≤ α) (tp : 0 < t) (tc : t ≤ c) :
      ‖horizontal F l r (sign*t)‖ ≤ (r-l)*cap l r t := by
    have z := intervalIntegral.norm_integral_le_of_norm_le_const (C := cap l r t)
      (a := l) (b := r) (f := fun v : ℝ => F ((v:ℂ)+((sign*t:ℝ):ℂ)*Complex.I)) (by
        intro v mem
        have hs := uIoc_subset_uIcc mem
        rw [uIcc_of_le lr] at hs
        apply major B Y S l r t D hB hY hS hR (lo.trans ll) (ra.trans al) tp omitted _
        all_goals simp only [Complex.add_re, Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im,
          neg_zero,add_zero,Complex.add_im,Complex.mul_I_im,zero_add,abs_mul,sgn,abs_of_pos tp,one_mul]
        exacts [hs.1,hs.2,le_rfl,tc.trans ct])
    rw [abs_of_nonneg (sub_nonneg.mpr lr)] at z
    exact z.trans_eq (mul_comm ..)
  change ‖vertical F α (sign*a) (sign*c)‖ ≤ _
  rw [← one_mul ‖vertical F α (sign*a) (sign*c)‖,← Complex.norm_I,← norm_mul,w]
  refine (norm_add_le ..).trans (add_le_add ?_ (hbd β α c le_rfl (bg.trans ga) le_rfl (ap.trans_le (ab.trans bc)) le_rfl))
  refine (norm_sub_le ..).trans (add_le_add ?_ (hbd β γ b le_rfl bg ga (ap.trans_le ab) bc))
  refine (norm_sub_le ..).trans (add_le_add ?_ (hbd γ α a bg ga le_rfl ap (ab.trans bc)))
  refine (norm_add_le ..).trans ?_
  rw [norm_mul,norm_mul,Complex.norm_I,one_mul,one_mul]
  exact add_le_add (vbd γ a b bg ga ap ab bc)
    (vbd β b c le_rfl (bg.trans ga) (ap.trans_le ab) bc le_rfl)

end Cogentic.Window
