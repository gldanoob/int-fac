import Cogentic.CharacterEstimate
import Cogentic.Window
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Cogentic.Window
open Finset Real Set

/-- Uniform low-frequency Euler bound on the original band, with arbitrary
    omissions. The constant is independent of the modulus, conductor and window. -/
theorem nonprincipal_band_euler (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (B : ℝ) (D : Finset ℕ) (s : ℂ), 4 ≤ B → 199/200 ≤ s.re → s.re ≤ 1 →
      |s.im| ≤ B^(1/5:ℝ) → D ⊆ (Finset.Ioc ⌊√B⌋₊ ⌊B⌋₊).filter Nat.Prime →
      let J := (Finset.Ioc ⌊√B⌋₊ ⌊B⌋₊).filter Nat.Prime
      ‖∏ p ∈ J \ D, (1+(p:ℂ)^(-s)*χ p)‖ ≤ Real.exp
        (8*(K*(1+Real.log (3*q*B))^2)*B^(-19/400:ℝ) + D.card*B^(-199/400:ℝ) +
        (∑' n : ℕ, (n:ℝ)^(-3/2:ℝ))/2) := by
  obtain ⟨K,hK,counts⟩ := nonprincipal_prime_count_from_critical_line line
  refine ⟨K,hK,fun q _ χ hχ B D s hB lo hi tim omitted => ?_⟩
  apply fixed_frequency_euler_product_omitting χ B _ s D (by linarith) (by positivity)
    lo hi tim _ omitted
  intro x hx
  exact counts q χ hχ B x ((Real.le_sqrt_of_sq_le (by nlinarith : (2:ℝ)^2 ≤ B)).trans hx.1) hx.2

/-- At all frequencies the unsigned Euler product costs at most exp(B^(1/200)(1+log B)).
    Bounding each summand by B^(1/200)/p keeps the cutoff above the Gaussian tail scale. -/
theorem unsigned_band_euler {B σ : ℝ} (J : Finset ℕ) (hB : 1 ≤ B)
    (lo : 199/200 ≤ σ) (hi : σ ≤ 1)
    (band : J ⊆ Finset.Icc 1 ⌊B⌋₊) :
    ∏ p ∈ J, (1+(p:ℝ)^(-σ)) ≤ Real.exp (B^(1/200:ℝ)*(1+Real.log B)) := by
  have term (p : ℕ) (hp : p ∈ J) : (p:ℝ)^(-σ) ≤ B^(1/200:ℝ)*(p:ℝ)⁻¹ := by
    have mem := Finset.mem_Icc.mp (band hp)
    have p1 : (1:ℝ) ≤ p := by exact_mod_cast mem.1
    have pos : (0:ℝ) < p := by linarith
    have pb : (p:ℝ) ≤ B := (Nat.cast_le.mpr mem.2).trans (Nat.floor_le (by linarith))
    calc
      _ = (p:ℝ)^(1-σ)*(p:ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add pos]
        congr 1
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (Real.rpow_le_rpow pos.le pb (by linarith)).trans
          (Real.rpow_le_rpow_of_exponent_le hB (by linarith))
  have H := harmonic_floor_le_one_add_log B hB
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at H
  have major := (Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => (p:ℝ)⁻¹)
    band (fun _ _ _ => by positivity)).trans H
  calc
    _ ≤ ∏ p ∈ J, Real.exp ((p:ℝ)^(-σ)) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro p _
      simpa only [add_comm] using Real.add_one_le_exp ((p:ℝ)^(-σ))
    _ = Real.exp (∑ p ∈ J, (p:ℝ)^(-σ)) := (Real.exp_sum _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      refine (Finset.sum_le_sum term).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left major (by positivity)

/-- Absolute discrepancy for every reduced residue with the original Gaussian.
    The first exponential comes from the prime character sum. The second is the
    full unsigned Euler bound times the high-frequency Gaussian tail. -/
theorem gaussian_progression_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (B Y S σ : ℝ) (D : Finset ℕ),
      4 ≤ B → 0 < S → S ≤ Y → 199/200 ≤ σ → σ ≤ 1 →
      D ⊆ (Finset.Ioc ⌊√B⌋₊ ⌊B⌋₊).filter Nat.Prime → ∀ r : (ZMod q)ˣ,
      let J := ((Finset.Ioc ⌊√B⌋₊ ⌊B⌋₊).filter Nat.Prime) \ D
      let w := fun n : ℕ => (gaussian Y S n : ℂ)
      let R := Y/S
      let T := B^(1/5:ℝ)
      let low := 8*(K*(1+Real.log (3*q*B))^2)*B^(-19/400:ℝ) + D.card*B^(-199/400:ℝ)
        + (∑' n : ℕ, (n:ℝ)^(-3/2:ℝ))/2
      let high := B^(1/200:ℝ)*(1+Real.log B)
      let M := (Y^σ/S*4*Real.exp (Real.pi/4+1))*(2*(4*R))
      ‖(q:ℂ)*classMass (squarefreeSupport J) w r -
        ((q:ℂ)/q.totient)*twist (squarefreeSupport J) w (1 : DirichletCharacter ℂ q)‖ ≤
        q*((1/(2*Real.pi))*M*(Real.exp low + Real.exp (high-T/(4*R)))) := by
  obtain ⟨K,hK,bandBound⟩ := nonprincipal_band_euler line
  refine ⟨K,hK,fun q _ B Y S σ D hB hS hSY hlo hhi hD r => ?_⟩
  dsimp only
  let J := ((Finset.Ioc ⌊√B⌋₊ ⌊B⌋₊).filter Nat.Prime) \ D
  let T := B^(1/5:ℝ)
  let f := fun x : ℝ => (gaussian Y S x : ℂ)
  have hY := hS.trans_le hSY
  have hR : 1 ≤ Y/S := (one_le_div hS).mpr hSY
  have hs : 1/2 ≤ σ := by linarith
  have tpos : 0 ≤ T := Real.rpow_nonneg (by linarith) _
  have hJ (p : ℕ) (hp : p ∈ J) : p.Prime := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
  have Jsub : J ⊆ Finset.Icc 1 ⌊B⌋₊ := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(hJ p hp).pos,
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1).2⟩
  have umaj := unsigned_band_euler J (by linarith) hlo hhi Jsub
  have ⟨mfull,mtail⟩ := gaussian_mellin_integral_bounds Y S σ T hY hS hR hs hhi tpos
  apply uniform_progression_bound _ _ _ (by positivity) _ r
  intro χ nc
  let low := 8*(K*(1+Real.log (3*q*B))^2)*B^(-19/400:ℝ) + D.card*B^(-199/400:ℝ)
    + (∑' n : ℕ, (n:ℝ)^(-3/2:ℝ))/2
  have eb (t : ℝ) (ht : |t| ≤ T) :
      ‖∏ p ∈ J, (1+(p:ℂ)^(-((σ:ℂ)+t*Complex.I))*χ p)‖ ≤ Real.exp low := by
    apply bandBound q χ nc B D _ hB <;> simp_all [T]
  have osc := squarefree_window_bound J hJ χ σ T (Real.exp low) (Real.exp_pos _).le f
    (gaussian_mellin_convergent Y S _ hY hS hR (by simpa using hs) (by simpa using hhi))
    (gaussian_vertical_integrable Y S σ hY hS hR hs hhi) (by dsimp [f,gaussian]; fun_prop) eb
  dsimp only at osc
  apply osc.trans
  have epos : 0 ≤ ∫ t in {t : ℝ | T < |t|}, ‖mellin f (σ+t*Complex.I)‖ :=
    MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have full := mul_le_mul_of_nonneg_left mfull (Real.exp_pos low).le
  have tail := mul_le_mul umaj mtail epos (Real.exp_pos _).le
  apply (mul_le_mul_of_nonneg_left (add_le_add full tail) (by positivity : 0 ≤ 1/(2*Real.pi))).trans_eq
  have expand (a b d : ℝ) : Real.exp (a-b/d) = Real.exp a * Real.exp (-b/d) := by
    rw [sub_eq_add_neg, Real.exp_add, neg_div]
  rw [expand (B^(1/200:ℝ)*(1+Real.log B)) (B^(1/5:ℝ)) (4*(Y/S))]
  dsimp [low,T]
  ring

/-- A clean fixed-schedule window has a power saving in its center Y after
    normalization by q. The other bounds are finite inequalities on the window inputs. -/
theorem clean_progression_error (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (B Y S : ℝ) (D : Finset ℕ),
      4 ≤ B → 0 < S → S ≤ Y → 1 ≤ Y → 404 ≤ B^(3/200:ℝ) →
      (1+Real.log (3*q*B)) ≤ B^(1/100:ℝ) → (D.card:ℝ) ≤ B^(1/100:ℝ) →
      Y/S ≤ B^(17/100:ℝ) → (q:ℝ) ≤ Y^(1/1000:ℝ) → Y/S ≤ Y^(1/2000:ℝ) →
      D ⊆ (Finset.Ioc ⌊√B⌋₊ ⌊B⌋₊).filter Nat.Prime → ∀ r : (ZMod q)ˣ,
      let J := ((Finset.Ioc ⌊√B⌋₊ ⌊B⌋₊).filter Nat.Prime) \ D
      let w := fun n : ℕ => (gaussian Y S n : ℂ)
      ‖(q:ℂ)*classMass (squarefreeSupport J) w r -
         ((q:ℂ)/q.totient)*twist (squarefreeSupport J) w (1 : DirichletCharacter ℂ q)‖ ≤
         C*Y^(-3/1000:ℝ) := by
  obtain ⟨K,hK,bounds⟩ := gaussian_progression_from_critical_line line
  let zetaTerm := (∑' n : ℕ, (n:ℝ)^(-3/2:ℝ))/2
  let coeff := 32*Real.exp (Real.pi/4+1)/(2*Real.pi)
  let maxEuler := Real.exp (8*K+1+zetaTerm) + 1
  have cpos : 0 < coeff := by dsimp [coeff]; positivity
  have epos : 0 < maxEuler := by dsimp [maxEuler]; positivity
  refine ⟨coeff*maxEuler,mul_pos cpos epos,fun q _ B Y S D hB hS hSY hy size logs omissions rb qy ry hD r => ?_⟩
  have bp : 0 < B := by linarith
  have b1 : 1 ≤ B := by linarith
  have yp : 0 < Y := by linarith
  have q1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have lp : 0 ≤ 1+Real.log (3*q*B) := by
    linarith [Real.log_nonneg (show 1 ≤ 3*q*B by nlinarith)]
  have grow (a b : ℝ) (h : a ≤ b) : B^a ≤ B^b := Real.rpow_le_rpow_of_exponent_le b1 h
  have low1 : (1+Real.log (3*q*B))^2*B^(-19/400:ℝ) ≤ 1 := by
    calc
      _ ≤ (B^(1/100:ℝ))^2*B^(-19/400:ℝ) := by gcongr
      _ = B^(-11/400:ℝ) := by rw [sq, ← Real.rpow_add bp, ← Real.rpow_add bp]; norm_num
      _ ≤ B^(0:ℝ) := grow _ _ (by norm_num)
      _ = 1 := Real.rpow_zero B
  have low2 : D.card*B^(-199/400:ℝ) ≤ 1 := by
    calc
      _ ≤ B^(1/100:ℝ)*B^(-199/400:ℝ) := by gcongr
      _ = B^(-39/80:ℝ) := by rw [← Real.rpow_add bp]; norm_num
      _ ≤ B^(0:ℝ) := grow _ _ (by norm_num)
      _ = 1 := Real.rpow_zero B
  have lo := mul_le_mul_of_nonneg_left low1 (show 0 ≤ 8*K by positivity)
  have eLow : Real.exp (8*(K*(1+Real.log (3*q*B))^2)*B^(-19/400:ℝ) + D.card*B^(-199/400:ℝ) + zetaTerm) ≤
      Real.exp (8*K+1+zetaTerm) := Real.exp_le_exp.mpr (by linarith)
  have bl : 1+Real.log B ≤ 101*B^(1/100:ℝ) := by
    have h := Real.log_le_rpow_div bp.le (by norm_num : (0:ℝ) < 1/100)
    have g := Real.one_le_rpow b1 (by norm_num : (0:ℝ) ≤ 1/100)
    linarith
  have eHigh : B^(1/200:ℝ)*(1+Real.log B) ≤ B^(1/5:ℝ)/(4*(Y/S)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (B^(1/200:ℝ)*(101*B^(1/100:ℝ)))*(4*B^(17/100:ℝ)) := by gcongr
      _ = 404*B^(37/200:ℝ) := by
        rw [show ∀ a b c : ℝ, a*(101*b)*(4*c) = 404*(a*b*c) by intro a b c; ring,
          ← Real.rpow_add bp, ← Real.rpow_add bp]
        norm_num
      _ ≤ B^(3/200:ℝ)*B^(37/200:ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add bp]; norm_num
  have eh := Real.exp_le_one_iff.mpr (sub_nonpos.mpr eHigh)
  have h := bounds q B Y S (199/200) D hB hS hSY le_rfl (by norm_num) hD r
  dsimp only at h ⊢
  refine h.trans ?_
  have norm (a : ℝ) : (q:ℝ)*((1/(2*Real.pi))*((Y^(199/200:ℝ)/S*4*Real.exp (Real.pi/4+1))*
      (2*(4*(Y/S))))*a) = coeff*((q:ℝ)*(Y/S)^2*Y^(-1/200:ℝ))*a := by
    rw [show Y^(199/200:ℝ) = Y*Y^(-1/200:ℝ) by
      calc
        _ = Y^((1:ℝ) + (-1/200:ℝ)) := by norm_num
        _ = _ := by rw [Real.rpow_add yp, Real.rpow_one]]
    dsimp [coeff]
    ring
  rw [norm]
  have power : (q:ℝ)*(Y/S)^2*Y^(-1/200:ℝ) ≤ Y^(-3/1000:ℝ) := by
    calc
      _ ≤ Y^(1/1000:ℝ)*(Y^(1/2000:ℝ))^2*Y^(-1/200:ℝ) := by gcongr
      _ = _ := by rw [sq, ← Real.rpow_add yp, ← Real.rpow_add yp, ← Real.rpow_add yp]; norm_num
  calc
    _ ≤ (coeff*(Y^(-3/1000:ℝ)))*maxEuler := mul_le_mul (mul_le_mul_of_nonneg_left power cpos.le)
      (add_le_add eLow eh) (by positivity) (by positivity)
    _ = _ := by ring

end Cogentic.Window
