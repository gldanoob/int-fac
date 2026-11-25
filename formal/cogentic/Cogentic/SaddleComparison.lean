import Cogentic.WindowSaddle

namespace Cogentic.Window

open Real Set

noncomputable section

theorem saddleMean_antitone (J : Finset ℕ) (hJ : ∀ p ∈ J, 0 < p) : Antitone (saddleMean J) := by
  apply antitone_of_deriv_nonpos (fun α => (saddleMean_derivative J hJ α).differentiableAt)
  intro α
  rw [(saddleMean_derivative J hJ α).deriv,neg_nonpos]
  apply Finset.sum_nonneg
  intro p hp
  unfold primeProbability
  have hz : 0 < 1+(p:ℝ)^(-α) := by positivity
  have hle : (p:ℝ)^(-α)/(1+(p:ℝ)^(-α)) ≤ 1 := (div_le_iff₀ hz).mpr (by linarith)
  exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hle)) (sq_nonneg _)

/-- Endpoint saddle means quantify how far the real saddle moves when the
    logarithmic center changes. -/
theorem saddle_displacement (J : Finset ℕ) (α β H : ℝ)
    (ha : 0 ≤ α) (hab : α ≤ β) (hH : 0 ≤ H)
    (hJ : ∀ p ∈ J, 1 ≤ p) (hband : ∀ p ∈ J, H/2 ≤ Real.log p ∧ Real.log p ≤ H) :
    (β-α)*H*saddleMean J β/4 ≤ saddleMean J α - saddleMean J β ∧
      saddleMean J α - saddleMean J β ≤ (β-α)*H*saddleMean J α := by
  rcases hab.eq_or_lt with rfl | lt
  · simp
  have pos : ∀ p ∈ J, 0 < p := hJ
  let var := fun x => saddleVariance J (primeProbability x) (fun p => Real.log p)
  have diff (x : ℝ) : HasDerivAt (saddleMean J) (-(var x)) x := saddleMean_derivative J pos x
  obtain ⟨c,hc,hd⟩ := exists_hasDerivAt_eq_slope (saddleMean J) (fun x => -(var x)) lt
    (fun x _ => (diff x).continuousAt.continuousWithinAt) (fun x _ => diff x)
  have hvar := prime_saddle_variance_bounds J c H (ha.trans hc.1.le) hH hJ hband
  have hl := saddleMean_antitone J pos hc.1.le
  have hr := saddleMean_antitone J pos hc.2.le
  have eq : saddleMean J α-saddleMean J β = (β-α)*var c := by
    rw [eq_div_iff (sub_ne_zero.mpr lt.ne')] at hd
    linarith only [hd, mul_comm (β-α) (var c)]
  change H*saddleMean J c/4 ≤ var c ∧ var c ≤ H*saddleMean J c at hvar
  rw [eq]
  constructor
  · calc (β-α)*H*saddleMean J β/4 = (β-α)*(H*saddleMean J β/4) := by ring
         _ ≤ (β-α)*var c := by gcongr; exact (by gcongr : H*saddleMean J β/4 ≤ H*saddleMean J c/4).trans hvar.1
  · calc (β-α)*var c ≤ (β-α)*(H*saddleMean J α) := by gcongr; exact hvar.2.trans (by gcongr)
         _ = _ := by ring

/-- Logarithm of the unnormalized principal Rankin mass at a real tilt. -/
def rankinAction (J : Finset ℕ) (X α : ℝ) : ℝ :=
  (α-1)*X + ∑ p ∈ J, Real.log (1+(p:ℝ)^(-α))

theorem rankinAction_derivative (J : Finset ℕ) (hJ : ∀ p ∈ J, 0 < p) (X α : ℝ) :
    HasDerivAt (rankinAction J X) (X-saddleMean J α) α := by
  have he (p : ℕ) (hp : p ∈ J) :
      HasDerivAt (fun z : ℝ => Real.log (1+(p:ℝ)^(-z)))
        (-(primeProbability α p * Real.log p)) α := by
    have ppos : (0:ℝ) < p := by exact_mod_cast hJ p hp
    have d := (((hasDerivAt_neg α).const_rpow ppos).const_add 1).log
      (show 1+(p:ℝ)^(-α) ≠ 0 by positivity)
    convert d using 1
    unfold primeProbability
    ring
  have d := (((hasDerivAt_id α).sub_const 1).mul_const X).add
    (HasDerivAt.fun_sum (u := J) (fun p hp => he p hp))
  convert! d using 1
  simp [saddleMean,Finset.sum_neg_distrib,sub_eq_add_neg]

/-- Moving from the exact saddle to a neighboring tilt costs at most the
    tilt distance times the discrepancy of the endpoint means. -/
theorem rankinAction_loss (J : Finset ℕ) (hJ : ∀ p ∈ J, 0 < p) (α β : ℝ) (hab : α ≤ β) :
    0 ≤ rankinAction J (saddleMean J α) β-rankinAction J (saddleMean J α) α ∧
    rankinAction J (saddleMean J α) β-rankinAction J (saddleMean J α) α ≤
        (β-α)*(saddleMean J α-saddleMean J β) := by
  rcases hab.eq_or_lt with rfl | lt
  · simp
  let X := saddleMean J α
  have d := rankinAction_derivative J hJ X
  obtain ⟨c,hc,hd⟩ := exists_hasDerivAt_eq_slope (rankinAction J X)
    (fun x => X-saddleMean J x) lt (fun x _ => (d x).continuousAt.continuousWithinAt) (fun x _ => d x)
  have hβ : 0 ≤ β-α := sub_nonneg.mpr lt.le
  have hx : 0 ≤ X - saddleMean J c := sub_nonneg.mpr (saddleMean_antitone J hJ hc.1.le)
  have hy := saddleMean_antitone J hJ hc.2.le
  change 0 ≤ rankinAction J X β-rankinAction J X α ∧ _ ≤ (β-α)*(X-saddleMean J β)
  rw [eq_div_iff (sub_ne_zero.mpr lt.ne')] at hd
  rw [← hd,mul_comm]
  exact ⟨mul_nonneg hβ hx, by gcongr⟩


/-- Both exact saddles have bounded Rankin loss at the opposite tilt.
    The same estimate holds at either evaluation center. -/
theorem neighboring_rankin_saddles (J : Finset ℕ) (α β H : ℝ)
    (ha : 0 ≤ α) (hab : α ≤ β) (hH : 0 < H)
    (hJ : ∀ p ∈ J, 1 ≤ p) (hband : ∀ p ∈ J, H/2 ≤ Real.log p ∧ Real.log p ≤ H)
    (hμ : 0 < saddleMean J β) :
    let X := saddleMean J α
    let Y := saddleMean J β
    let B := 4*(X-Y)^2/(H*Y)
    0 ≤ rankinAction J X β-rankinAction J X α ∧ rankinAction J X β-rankinAction J X α ≤ B ∧
    0 ≤ rankinAction J Y α-rankinAction J Y β ∧ rankinAction J Y α-rankinAction J Y β ≤ B := by
  let X := saddleMean J α
  let Y := saddleMean J β
  have scale := (saddle_displacement J α β H ha hab hH.le hJ hband).1
  have loss := rankinAction_loss J hJ α β hab
  have gap : 0 ≤ X-Y := sub_nonneg.mpr (saddleMean_antitone J hJ hab)
  have eq : rankinAction J Y α-rankinAction J Y β =
      (β-α)*(X-Y)-(rankinAction J X β-rankinAction J X α) := by
    dsimp [rankinAction]
    ring
  have bound : (β-α)*(X-Y) ≤ 4*(X-Y)^2/(H*Y) := by
    rw [le_div_iff₀ (mul_pos hH hμ)]
    change (β-α)*H*Y/4 ≤ X-Y at scale
    have h := mul_le_mul_of_nonneg_right scale gap
    nlinarith only [h]
  change 0 ≤ rankinAction J X β-rankinAction J X α ∧ _ ≤ _ ∧
    0 ≤ rankinAction J Y α-rankinAction J Y β ∧ rankinAction J Y α-rankinAction J Y β ≤ _
  rw [eq]
  exact ⟨loss.1,loss.2.trans bound,sub_nonneg.mpr loss.2,(sub_le_self _ loss.1).trans bound⟩

end

end Cogentic.Window
