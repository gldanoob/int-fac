import Cogentic.RandomizedBalancedEnvelopeInfimum
import Cogentic.RandomizedPrivateGridUpper
import Mathlib.Data.Rat.Cast.Order

namespace Cogentic.Randomized

open scoped BigOperators

/-- A uniform grid with `k + 1` intervals, exactly representable over the rationals. -/
def balancedUniformKnot (k i : ℕ) : ℚ := (i : ℚ) / ((k : ℚ) + 1)

private theorem cast_balancedUniformKnot (k i : ℕ) :
    (balancedUniformKnot k i : ℝ) = (i : ℝ) / ((k : ℝ) + 1) := by
  simp [balancedUniformKnot]

/-- The unperturbed private scale, row cost, degree scale, and a common positive
perturbation for the balanced schedule. -/
structure BalancedPerturbation where
  u : ℝ
  b : ℝ
  δ : ℝ
  q : ℝ

namespace BalancedPerturbation

noncomputable def M (p : BalancedPerturbation) : ℝ := 2 / (9 * p.u ^ 2)
noncomputable def κ (p : BalancedPerturbation) : ℝ := 2 / (3 * p.u ^ 2 * p.δ)
noncomputable def h (p : BalancedPerturbation) : ℝ := p.u + p.q
noncomputable def α (p : BalancedPerturbation) : ℝ := 1 / 2 + p.q
noncomputable def χ (p : BalancedPerturbation) : ℝ := 1 + p.q
noncomputable def ζ (p : BalancedPerturbation) : ℝ := p.q / 4
noncomputable def y₀ (p : BalancedPerturbation) : ℝ := 3 * p.u ^ 2 * p.δ / 4
noncomputable def v₀ (p : BalancedPerturbation) : ℝ := p.α * p.y₀
noncomputable def y₁ (p : BalancedPerturbation) : ℝ := p.v₀ / 1.43
noncomputable def v₁ (p : BalancedPerturbation) : ℝ := p.α * p.y₁
noncomputable def y₂ (p : BalancedPerturbation) : ℝ := p.v₁ / 1.636
noncomputable def β (p : BalancedPerturbation) : ℝ := p.b / p.δ
noncomputable def R (p : BalancedPerturbation) : ℝ := 1 / p.δ ^ 3
noncomputable def A₀ (p : BalancedPerturbation) : ℝ := p.R * (1 + p.χ * p.v₀)
noncomputable def Aplus (p : BalancedPerturbation) : ℝ := p.A₀ + p.q

noncomputable def lowRatio (p : BalancedPerturbation) : ℝ :=
  (p.β + 2 * p.Aplus + p.R / (3 * p.β) + 4 * p.q) / (2 * p.β - 1 / 3)

noncomputable def lowBox (p : BalancedPerturbation) : ℝ :=
  p.lowRatio - (p.Aplus + p.q) / p.β

noncomputable def lowRaw (p : BalancedPerturbation) : ℝ :=
  p.b + p.δ * p.lowRatio / 3 + 1 / (3 * p.δ * p.b) + 2 * p.q

theorem y₀_eq_inv {p : BalancedPerturbation} (hu : 0 < p.u) (hd : 0 < p.δ) :
    p.y₀ = 1 / (2 * p.κ) := by
  unfold y₀ κ
  field_simp
  norm_num

theorem M_eq {p : BalancedPerturbation} (hd : 0 < p.δ) :
    p.M = p.κ * p.δ / 3 := by
  unfold M κ
  by_cases hu : p.u = 0
  · simp [hu]
  · field_simp
    norm_num

theorem curve_allowance {p : BalancedPerturbation} (hu : 0 < p.u) (hd : 0 < p.δ)
    (hq : 0 < p.q) : 2 * (2 * p.y₀ / (3 * p.δ)) < p.h ^ 2 := by
  have he : 2 * (2 * p.y₀ / (3 * p.δ)) = p.u ^ 2 := by
    unfold y₀
    field_simp
    norm_num
  rw [he]
  exact pow_lt_pow_left₀ (by unfold h; linarith) hu.le (by decide)

theorem positive_width_gaps {p : BalancedPerturbation} (hq : 0 < p.q) :
    1 < p.χ ∧ 1 / 2 < p.α ∧ 0 < p.ζ ∧ 2 * p.ζ < p.χ - 1 := by
  unfold χ α ζ
  constructor
  · linarith
  · exact ⟨by linarith, by positivity, by linarith⟩

private theorem lowRaw_eq {p : BalancedPerturbation}
    (hb : 0 < p.b) (hd : 0 < p.δ) (hden : 0 < 6 * p.b - p.δ) :
    p.lowRaw - 2 * p.q =
      (6 * p.b ^ 2 + (3 * p.χ * p.α / 2) * p.u ^ 2 + 4 / p.δ + 6 * p.δ ^ 2 * p.q) /
        (6 * p.b - p.δ) := by
  unfold lowRaw lowRatio Aplus A₀ R β v₀ y₀
  have he : 2 * (p.b / p.δ) - 1 / 3 = (6 * p.b - p.δ) / (3 * p.δ) := by field_simp; ring
  rw [he]
  generalize hD : 6 * p.b - p.δ = D at hden ⊢
  field_simp [hden.ne']
  rw [← hD]
  ring

/-- The two formerly active low descent geometry tests have exact positive
margins `q` and `2q`. -/
theorem low_margins {p : BalancedPerturbation}
    (hb : 0 < p.b) (hd : 0 < p.δ) (hden : 0 < 6 * p.b - p.δ) :
    (p.lowRatio - p.lowBox) * p.β - p.Aplus = p.q ∧
      (2 * p.lowBox - 1) * p.β - p.lowRatio / 3 - p.R / (3 * p.β) = 2 * p.q := by
  have hβ : 0 < p.β := div_pos hb hd
  have hs : 0 < 2 * p.β - 1 / 3 := by
    unfold β
    apply sub_pos.mpr
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hd).2
    linarith only [hden]
  have hdiv : (p.Aplus + p.q) / p.β * p.β = p.Aplus + p.q :=
    div_mul_cancel₀ _ hβ.ne'
  have hratio := div_mul_cancel₀ (p.β + 2 * p.Aplus + p.R / (3 * p.β) + 4 * p.q) hs.ne'
  change p.lowRatio * (2 * p.β - 1 / 3) = _ at hratio
  unfold lowBox
  constructor <;> nlinarith only [hdiv, hratio]

end BalancedPerturbation

namespace BalancedPerturbation

/-- The fixed top ratio checks every positive squared knot, including the
smallest knot of arbitrarily fine meshes. -/
theorem top_geometry {p : BalancedPerturbation}
    (hu : 0 < p.u) (hu' : p.u < 0.58514029)
    (hd : 0 < p.δ) (hd' : p.δ < 1.4199110)
    (hq : 0 < p.q) (hq' : p.q ≤ 1 / 10 ^ 6)
    {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1) :
    let parent := a * p.y₀
    let box := a * p.v₀
    let child := box / (1 + (1.43 - 1) * a)
    0 < child ∧ child < box ∧ box < parent ∧ parent < 1 ∧ parent < 2 * box ∧
    child ≤ p.y₁ ∧ 1.01 * child - 0.49 * (1 + box - parent) < -1 / 4 ∧
    1.01 * p.y₁ - 0.49 < -1 / 4 ∧ p.y₁ < p.χ * p.v₀ ∧ 2 * p.v₁ < p.χ * p.v₀ ∧
    2 * p.v₀ < 1 ∧ p.χ * p.v₀ < 1 := by
  let parent := a * p.y₀
  let box := a * p.v₀
  let ratio := 1 + (1.43 - 1) * a
  let child := box / ratio
  have hαl : 1 / 2 < p.α := (positive_width_gaps hq).2.1
  have hαu : p.α ≤ 0.51 := by unfold α; linarith only [hq']
  have hχl := (positive_width_gaps hq).1
  have hχu : p.χ ≤ 1.01 := by unfold χ; linarith only [hq']
  have hy : 0 < p.y₀ := by unfold y₀; positivity
  have hyu : p.y₀ < 3 / 8 := by
    unfold y₀
    calc
      _ ≤ 3 * (0.58514029 : ℝ) ^ 2 * 1.4199110 / 4 := by gcongr
      _ < _ := by norm_num
  have hvₗ : p.y₀ / 2 < p.v₀ := by
    unfold v₀
    linarith only [mul_lt_mul_of_pos_right hαl hy]
  have hv : 0 < p.v₀ := (by positivity : 0 < p.y₀ / 2).trans hvₗ
  have hvy : p.v₀ < p.y₀ := by
    unfold v₀
    exact mul_lt_of_lt_one_left hy (hαu.trans_lt (by norm_num))
  have hvᵤ : p.v₀ ≤ 0.19125 := by
    unfold v₀
    calc
      _ ≤ (0.51 : ℝ) * (3 / 8) := by gcongr
      _ = _ := by norm_num
  have hratio : 1 < ratio := by
    dsimp [ratio]
    linarith only [ha]
  have hbox : 0 < box := mul_pos ha hv
  have hchild : 0 < child := div_pos hbox (zero_lt_one.trans hratio)
  have hboxPar : box < parent := mul_lt_mul_of_pos_left hvy ha
  have hparent : parent < 1 := by
    calc
      parent ≤ 1 * p.y₀ := mul_le_mul_of_nonneg_right ha' hy.le
      _ < 1 := by linarith only [hyu]
  have harea : parent < 2 * box := by
    dsimp only [parent,box]
    nlinarith only [mul_lt_mul_of_pos_left hvₗ ha]
  have hy₁ : 0 < p.y₁ := div_pos hv (by norm_num)
  have hy₁u : p.y₁ ≤ 0.134 := by
    unfold y₁
    exact (div_le_iff₀ (by norm_num)).2 (hvᵤ.trans (by norm_num))
  have hprod : p.y₁ * 1.43 = p.v₀ := by unfold y₁; ring
  have hc₁ : child ≤ p.y₁ := by
    apply (div_le_iff₀ (zero_lt_one.trans hratio)).2
    dsimp only [box,ratio]
    nlinarith only [mul_nonneg hy₁.le (sub_nonneg.mpr ha'), congrArg (fun x => a * x) hprod]
  have hscale : 13 / 16 < 1 + box - parent := by
    dsimp only [box,parent]
    nlinarith only [hyu,hvₗ,mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr hvy.le)]
  have hroot : p.y₁ < p.χ * p.v₀ := by
    have hsmall : p.y₁ < p.v₀ := div_lt_self hv (by norm_num)
    exact hsmall.trans (by simpa using mul_lt_mul_of_pos_right hχl hv)
  have hpair : 2 * p.v₁ < p.χ * p.v₀ := by
    have hsmall : 2 * p.v₁ < p.v₀ := by
      unfold v₁
      nlinarith only [hprod, mul_lt_mul_of_pos_right (show p.α < 1.43 / 2 by linarith) hy₁]
    exact hsmall.trans (by simpa using mul_lt_mul_of_pos_right hχl hv)
  have hprog : 1.01 * child - 0.49 * (1 + box - parent) < -1 / 4 := by
    linarith only [hscale,hc₁,hy₁u]
  exact ⟨hchild,div_lt_self hbox hratio,hboxPar,hparent,harea,hc₁,
    hprog, by linarith only [hy₁u], hroot,hpair,
    by linarith only [hvᵤ], by nlinarith only [mul_le_mul_of_nonneg_right hχu hv.le,hvᵤ]⟩

end BalancedPerturbation

private theorem balanced_endpoint_parameters :
    ∃ u b δ : ℝ, 0.58514027 < u ∧ u < 0.58514029 ∧
      0.9448547 < b ∧ b < 0.944855 ∧ 1.4199108 < δ ∧ δ < 1.4199110 ∧
      b + 2 / (9 * u ^ 2) + 2 * u / 3 = balancedEnvelopeInfimum ∧
      (3 / 4) * u ^ 2 + 4 / δ + balancedEnvelopeInfimum * δ =
        6 * b * (balancedEnvelopeInfimum - b) := by
  obtain ⟨u, hul, huu, hroot, hCl, hCu, hfeas⟩ := balanced_envelope_exact_infimum
  let C := balancedStationaryCost u
  let M := 2 / (9 * u ^ 2)
  let b := C - scaledPrivateCost (1 / 2) u
  let δ := 2 / Real.sqrt C
  have hCeq : C = balancedEnvelopeInfimum := by
    have hset : {D | BalancedEnvelopeCeiling D} = Set.Ioi C := Set.ext hfeas
    rw [balancedEnvelopeInfimum, hset, csInf_Ioi]
  have huₗ : 0.58514027 < u := by linarith only [hul]
  have huᵤ : u < 0.58514029 := by linarith only [huu]
  have hu : 0 < u := by linarith only [huₗ]
  have hsₗ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.58514027) huₗ.le 2
  have hsᵤ := pow_le_pow_left₀ hu.le huᵤ.le 2
  have hMₗ : 0.64903404 < M := by
    apply (lt_div_iff₀ (by positivity)).2
    nlinarith only [hsᵤ]
  have hMᵤ : M < 0.64903411 := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith only [hsₗ]
  have hp : scaledPrivateCost (1 / 2) u = M + 2 * u / 3 := by
    unfold scaledPrivateCost M
    norm_num
  have hb : b + M + 2 * u / 3 = C := by dsimp only [b]; rw [hp]; ring
  have hbₗ : 0.9448547 < b := by linarith only [hb, hCl, hMᵤ, huᵤ]
  have hbᵤ : b < 0.944855 := by linarith only [hb, hCu, hMₗ, huₗ]
  have hC : 0 < C := by linarith only [hCl]
  have hsqₗ : (1.40853910 : ℝ) < Real.sqrt C := (Real.lt_sqrt (by norm_num)).2 (by
    linarith only [hCl])
  have hsqᵤ : Real.sqrt C < (1.40853911 : ℝ) :=
    (Real.sqrt_lt hC.le (by norm_num)).2 (by linarith only [hCu])
  have hsq : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  have hdₗ : 1.4199108 < δ := by
    apply (lt_div_iff₀ hsq).2
    linarith only [hsqᵤ]
  have hdᵤ : δ < 1.4199110 := by
    apply (div_lt_iff₀ hsq).2
    linarith only [hsqₗ]
  have hr : 6 * b * (C - b) = (3 / 4) * u ^ 2 + 4 * balancedStationarySqrt u := by
    unfold balancedStationarySqrt b C
    ring
  have hS : 0 < balancedStationarySqrt u := by
    have hmul : (0.94 : ℝ) * 1 < b * (C - b) := by
      apply mul_lt_mul (show (0.94 : ℝ) < b by linarith only [hbₗ]) _
        (by norm_num) (by linarith only [hbₗ])
      linarith only [hCl,hbᵤ]
    nlinarith only [hr, hmul, hsᵤ]
  have hsqeq : Real.sqrt C = balancedStationarySqrt u := by
    change balancedStationarySqrt u ^ 2 = C at hroot
    rw [← hroot, Real.sqrt_sq hS.le]
  have hδeq : 4 / δ + C * δ = 4 * Real.sqrt C := by
    dsimp only [δ]
    calc
      _ = 4 / (2 / Real.sqrt C) + Real.sqrt C ^ 2 * (2 / Real.sqrt C) := by
        rw [Real.sq_sqrt hC.le]
      _ = _ := by field_simp; ring
  refine ⟨u,b,δ,huₗ,huᵤ,hbₗ,hbᵤ,hdₗ,hdᵤ,hb.trans hCeq,?_⟩
  rw [← hCeq]
  linarith only [hr, hsqeq, hδeq]

/-- The two active charged budgets at the endpoint extend to every larger
ceiling at strictly positive width, angle, area, and padding gaps. For all
sufficiently fine rational uniform meshes the same fixed scalar parameters
give positive equalized weights and meet the exact private moment. -/
theorem balanced_finite_private_low_budget {ε : ℝ} (hε : 0 < ε) :
    ∃ p : BalancedPerturbation, ∃ K : ℕ,
      0.58514027 < p.u ∧ p.u < 0.58514029 ∧
      0.9448547 < p.b ∧ p.b < 0.944855 ∧
      1.4199108 < p.δ ∧ p.δ < 1.4199110 ∧
      0 < p.q ∧ p.q < 1 / 10 ^ 6 ∧
      p.h / 3 < p.M ∧ p.b + p.M + 2 * p.h / 3 + p.q < balancedEnvelopeInfimum + ε ∧
      p.lowRaw < balancedEnvelopeInfimum + ε ∧
      ∀ k ≥ K, ∃ w : ℕ → ℝ,
        let z : ℕ → ℝ := fun j => balancedUniformKnot k j
        z 0 = 0 ∧ z (k + 1) = 1 ∧ (∀ j < k + 1, z j < z (j + 1)) ∧
        (∀ i < k + 1, 0 < w i) ∧
        (∑ i ∈ Finset.range (k + 1), z (i + 1) ^ 2 * w i) = p.M ∧
        (∀ i < k + 1, p.b + p.h * z (i + 1) +
          (∑ j ∈ Finset.Ico i (k + 1), w j) + p.q < balancedEnvelopeInfimum + ε) ∧
        p.b + (∑ j ∈ Finset.range (k + 1), w j) + p.q < balancedEnvelopeInfimum + ε := by
  obtain ⟨u,b,δ,huₗ,huᵤ,hbₗ,hbᵤ,hdₗ,hdᵤ,hprivate,hterminal⟩ :=
    balanced_endpoint_parameters
  let C := balancedEnvelopeInfimum
  let τ := min (ε / 4) (1 / 10 ^ 6)
  have hτ : 0 < τ := lt_min (by positivity) (by norm_num)
  have hτε : τ ≤ ε / 4 := min_le_left ..
  have hτsmall : τ ≤ 1 / 10 ^ 6 := min_le_right ..
  have hu : 0 < u := by linarith only [huₗ]
  have hb : 0 < b := by linarith only [hbₗ]
  have hd : 0 < δ := by linarith only [hdₗ]
  have hden : 0 < 6 * b - δ := by linarith only [hbₗ,hdᵤ]
  let coeff := 3 * u ^ 2 + 6 * δ ^ 2
  have hcoeff : 0 < coeff := by dsimp [coeff]; positivity
  let q := min (τ / 10) ((6 * b - δ) * τ / (2 * coeff))
  let p : BalancedPerturbation := ⟨u,b,δ,q⟩
  have hq : 0 < q := lt_min (by positivity) (by positivity)
  have hqτ : q ≤ τ / 10 := min_le_left ..
  have hqsmall : q < 1 / 10 ^ 6 := by linarith only [hqτ,hτsmall]
  have hcharge : q * (2 * coeff) ≤ (6 * b - δ) * τ :=
    (le_div_iff₀ (by positivity)).1 (min_le_right ..)
  have hw : 3 * p.χ * p.α / 2 - 3 / 4 ≤ 3 * q := by
    unfold BalancedPerturbation.χ BalancedPerturbation.α
    change 3 * (1 + q) * (1 / 2 + q) / 2 - 3 / 4 ≤ 3 * q
    nlinarith only [mul_nonneg hq.le (show 0 ≤ 1/2 - q by linarith only [hqsmall])]
  have hw' := mul_le_mul_of_nonneg_right hw (sq_nonneg u)
  have hsurplus : (3 * p.χ * p.α / 2) * u ^ 2 + 6 * δ ^ 2 * q -
      (3 / 4) * u ^ 2 < (6 * b - δ) * τ := by
    dsimp only [coeff] at hcharge
    nlinarith only [hw', hcharge, mul_pos hden hτ]
  have hlraw : p.lowRaw - 2 * q < C + τ := by
    rw [BalancedPerturbation.lowRaw_eq (p := p) hb hd hden]
    apply (div_lt_iff₀ hden).2
    change (3 / 4) * u ^ 2 + 4 / δ + C * δ = 6 * b * (C - b) at hterminal
    dsimp only [p]
    nlinarith only [hterminal, hsurplus]
  have hraw : p.lowRaw < C + ε := by linarith only [hlraw,hqτ,hτε,hε]
  have hh : 0 < p.h := by change 0 < u + q; positivity
  have hM : p.h / 3 < p.M := by
    change (u + q) / 3 < 2 / (9 * u ^ 2)
    have hu₂ := pow_le_pow_left₀ hu.le huᵤ.le 2
    have hMₗ : (0.64 : ℝ) < 2 / (9 * u ^ 2) := by
      apply (lt_div_iff₀ (by positivity)).2
      nlinarith only [hu₂]
    linarith only [hMₗ,huᵤ,hqsmall]
  have hscreen : p.b + p.M + 2 * p.h / 3 + p.q < C + ε := by
    change b + p.M + 2 * (u + q) / 3 + q < C + ε
    change b + p.M + 2 * u / 3 = C at hprivate
    linarith only [hprivate,hqτ,hτε,hε]
  obtain ⟨K, hK⟩ := exists_nat_gt (p.h / τ)
  refine ⟨p,K,huₗ,huᵤ,hbₗ,hbᵤ,hdₗ,hdᵤ,hq,hqsmall,hM,hscreen,hraw,?_⟩
  intro k hk
  let n : ℝ := (k : ℝ) + 1
  have hn : 0 < n := by dsimp [n]; positivity
  have hmesh : p.h / n < τ := by
    have hkn : (K : ℝ) ≤ k := by exact_mod_cast hk
    have hcap := (div_lt_iff₀ hτ).1 (hK.trans_le hkn)
    apply (div_lt_iff₀ hn).2
    dsimp [n]
    linarith only [hcap,hτ]
  obtain ⟨w, _, hwpos, hmoment, hgate, _, herror⟩ :=
    uniform_private_grid_upper k hh hM
  let z : ℕ → ℝ := fun j => (j : ℝ) / n
  have hstep (j : ℕ) : z j < z (j + 1) :=
    (div_lt_div_iff_of_pos_right hn).2 (by exact_mod_cast Nat.lt_succ_self j)
  have hz1 : z (k + 1) = 1 := by simpa [z, n] using div_self hn.ne'
  have hgate' (i : ℕ) (hi : i < k + 1) :
      p.b + p.h * z (i + 1) + (∑ j ∈ Finset.Ico i (k + 1), w j) + p.q < C + ε := by
    have hg := hgate i hi
    change p.h * z (i + 1) + (∑ j ∈ Finset.Ico i (k + 1), w j) =
      p.M + 2 * p.h / 3 + (p.h / (2 * n) - p.h / (6 * n ^ 2)) at hg
    change p.h / (2 * n) - p.h / (6 * n ^ 2) ≤ p.h / n at herror
    change b + p.M + 2 * u / 3 = C at hprivate
    have heq : p.h = u + q := rfl
    change b + p.h * z (i + 1) + (∑ j ∈ Finset.Ico i (k + 1), w j) + q < C + ε
    linarith only [hg,herror,hmesh,hprivate,heq,hqτ,hτε,hε]
  refine ⟨w, ?_⟩
  simp only [cast_balancedUniformKnot]
  refine ⟨by simp, hz1, fun j _ => hstep j, hwpos, hmoment, hgate', ?_⟩
  have he := hgate' 0 (Nat.zero_lt_succ k)
  rw [Nat.Ico_zero_eq_range] at he
  have hz : 0 ≤ z 1 := by dsimp [z]; positivity
  have hz' : 0 ≤ p.h * z 1 := mul_nonneg hh.le hz
  linarith only [he,hz']

#print axioms BalancedPerturbation.low_margins
#print axioms BalancedPerturbation.top_geometry
#print axioms balanced_finite_private_low_budget

end Cogentic.Randomized
