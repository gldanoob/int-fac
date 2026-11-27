import Cogentic.RandomizedNarrowEndpoint

namespace Cogentic.Randomized

open Set Real

/-- Feasible ceilings in the balanced half-width continuum model, at fixed widths
strictly greater than one. -/
def BalancedEnvelopeCeiling (C : ℝ) : Prop :=
  0 < C ∧ ∃ χ u b : ℝ, 1 < χ ∧ 0 < u ∧ 0 < b ∧
    b + scaledPrivateCost (1 / 2) u ≤ C ∧
    (3 * χ / 4) * u ^ 2 + 4 * sqrt C ≤ 6 * b * (C - b)

/-- Solve the stationary balance for the ceiling at the private scale `u`. -/
noncomputable def balancedStationaryCost (u : ℝ) : ℝ :=
  2 * scaledPrivateCost (1 / 2) u + u / (4 * scaledPrivateSlope (1 / 2) u)

/-- The square root given by the unsquared terminal equality. -/
noncomputable def balancedStationarySqrt (u : ℝ) : ℝ :=
  let p := scaledPrivateCost (1 / 2) u
  (6 * (balancedStationaryCost u - p) * p - 3 / 4 * u ^ 2) / 4

private theorem balancedSlope_lt_neg_one {u : ℝ} (hu : 0 < u) (hu' : u ≤ 59 / 100) :
    scaledPrivateSlope (1 / 2) u < -1 := by
  have hp := pow_le_pow_left₀ hu.le hu' 3
  have hinv : (5 / 3 : ℝ) < 4 / (9 * u ^ 3) := by
    apply (lt_div_iff₀ (by positivity)).2
    nlinarith only [hp]
  unfold scaledPrivateSlope
  linarith only [hinv]

private theorem balancedStationary_exact :
    ∃ u : ℝ, 0.58514027906279830 < u ∧ u < 0.58514027906279832 ∧
      balancedStationarySqrt u ^ 2 = balancedStationaryCost u := by
  let a : ℝ := 0.58514027906279830
  let b : ℝ := 0.58514027906279832
  let I := Icc a b
  have hab : a ≤ b := by norm_num [a,b]
  have hpos {x : ℝ} (hx : x ∈ I) : 0 < x := (by norm_num [a] : 0 < a).trans_le hx.1
  have hden {x : ℝ} (hx : x ∈ I) : scaledPrivateSlope (1 / 2) x ≠ 0 :=
    ((balancedSlope_lt_neg_one (hpos hx) (hx.2.trans (by norm_num [b]))).trans (by norm_num)).ne
  have hx : ContinuousOn (fun x : ℝ => x) I := continuous_id.continuousOn
  have hp : ContinuousOn (scaledPrivateCost (1 / 2)) I := by
    unfold scaledPrivateCost
    exact (continuousOn_const.div (continuousOn_const.mul (hx.pow 2))
      (fun x h => mul_ne_zero (by norm_num) (pow_ne_zero _ (hpos h).ne'))).add
        ((continuousOn_const.mul hx).div_const _)
  have hd : ContinuousOn (scaledPrivateSlope (1 / 2)) I := by
    unfold scaledPrivateSlope
    exact continuousOn_const.sub (continuousOn_const.div (continuousOn_const.mul (hx.pow 3))
      (fun x h => mul_ne_zero (by norm_num) (pow_ne_zero _ (hpos h).ne')))
  have hc : ContinuousOn balancedStationaryCost I := by
    unfold balancedStationaryCost
    exact (continuousOn_const.mul hp).add (hx.div (continuousOn_const.mul hd)
      (fun x h => mul_ne_zero (by norm_num) (hden h)))
  have hs : ContinuousOn balancedStationarySqrt I := by
    unfold balancedStationarySqrt
    exact (((continuousOn_const.mul (hc.sub hp)).mul hp).sub
      (continuousOn_const.mul (hx.pow 2))).div_const _
  let f := fun x => balancedStationaryCost x - balancedStationarySqrt x ^ 2
  have ha : f a < 0 := by
    norm_num [f,a,balancedStationaryCost,balancedStationarySqrt,scaledPrivateCost,scaledPrivateSlope]
  have hb : 0 < f b := by
    norm_num [f,b,balancedStationaryCost,balancedStationarySqrt,scaledPrivateCost,scaledPrivateSlope]
  obtain ⟨x, hx', he⟩ := intermediate_value_Icc hab (hc.sub (hs.pow 2))
    (show 0 ∈ Icc (f a) (f b) from ⟨ha.le,hb.le⟩)
  have he' : f x = 0 := he
  exact ⟨x, lt_of_le_of_ne hx'.1 (by rintro rfl; exact ha.ne he'),
    lt_of_le_of_ne hx'.2 (by rintro rfl; exact hb.ne' he'), by dsimp [f] at he'; linarith⟩

private theorem balanced_terminal_strict_monotone {C D b z : ℝ} (hC : 0 < C) (hD : C < D)
    (hb : 0 < b) (hz : 0 ≤ z) (hterm : z + 4 * sqrt C ≤ 6 * b * (C - b)) :
    z + 4 * sqrt D < 6 * b * (D - b) := by
  have hs : 0 < sqrt C := sqrt_pos.2 hC
  have hd : 0 < sqrt D - sqrt C := sub_pos.2 (sqrt_lt_sqrt hC.le hD)
  have hcs := sq_sqrt hC.le
  have hds := sq_sqrt (hC.le.trans hD.le)
  have hbase : 4 * sqrt C ≤ 6 * b * C := by nlinarith only [hterm,hz,sq_nonneg b]
  have hcoef : 4 ≤ 6 * b * sqrt C := by
    apply le_of_mul_le_mul_right _ hs
    nlinarith only [hbase, congrArg (fun x : ℝ => 6 * b * x) hcs]
  have hcoeff : 4 < 6 * b * (sqrt D + sqrt C) := by
    nlinarith only [hcoef, mul_pos hb (sqrt_pos.2 (hC.trans hD))]
  have hmove : 4 * (sqrt D - sqrt C) < 6 * b * (D - C) := by
    calc
      _ < (6 * b * (sqrt D + sqrt C)) * (sqrt D - sqrt C) :=
        mul_lt_mul_of_pos_right hcoeff hd
      _ = 6 * b * (sqrt D ^ 2 - sqrt C ^ 2) := by ring
      _ = _ := by rw [hds,hcs]
  linarith only [hterm,hmove]

/-- The exact stationary coefficient is the infimum over widths strictly above
one. At width one the two inequalities become equalities. -/
theorem balanced_envelope_exact_infimum :
    ∃ u : ℝ, 0.58514027906279830 < u ∧ u < 0.58514027906279832 ∧
      balancedStationarySqrt u ^ 2 = balancedStationaryCost u ∧
      1.9839824118071388228 < balancedStationaryCost u ∧
      balancedStationaryCost u < 1.9839824118071388230 ∧
      ∀ D : ℝ, BalancedEnvelopeCeiling D ↔ balancedStationaryCost u < D := by
  obtain ⟨u, hul, huu, hroot⟩ := balancedStationary_exact
  let p := scaledPrivateCost (1 / 2) u
  let d := scaledPrivateSlope (1 / 2) u
  let C := balancedStationaryCost u
  let b := C - p
  let s := balancedStationarySqrt u
  have hu : 0 < u := by linarith only [hul]
  have hu₂ : u ≤ 59 / 100 := by linarith only [huu]
  have hd : d < -1 := balancedSlope_lt_neg_one hu hu₂
  have hpow := pow_le_pow_left₀ hu.le hu₂ 2
  have hp : 9 / 10 < p := by
    have hfrac : (3 / 5 : ℝ) < 2 / (9 * u ^ 2) := by
      apply (lt_div_iff₀ (by positivity)).2
      nlinarith only [hpow]
    dsimp [p,scaledPrivateCost]
    linarith only [hfrac,hul]
  have hneg : u / (4 * d) < 0 := div_neg_of_pos_of_neg hu (by linarith)
  have hlo : -(3 / 20 : ℝ) < u / (4 * d) := by
    apply (lt_div_iff_of_neg (show 4 * d < 0 by linarith)).2
    nlinarith only [hd,hu₂]
  have hCeq : C = 2 * p + u / (4 * d) := rfl
  have hb : 3 / 4 < b := by dsimp only [b]; linarith only [hCeq,hp,hlo]
  have hC : 0 < C := by linarith only [hCeq,hp,hlo]
  have hrel : 6 * b * (C - b) = 3 / 4 * u ^ 2 + 4 * s := by
    dsimp only [b,s,balancedStationarySqrt,C,p]
    ring
  have hprod : (3 / 4) * (9 / 10) < b * p := by
    exact mul_lt_mul hb hp.le (by norm_num) (by linarith only [hb])
  have hs : 0 < s := by
    have he : C - b = p := by dsimp only [b]; ring
    rw [he] at hrel
    nlinarith only [hrel,hprod,hpow]
  have hsqrt : sqrt C = s := by
    change s ^ 2 = C at hroot
    rw [← hroot, sqrt_sq hs.le]
  rw [← hsqrt] at hrel
  have hbC : b + p = C := by dsimp only [b]; ring
  have hgap : 0 ≤ C - 2 * b := by linarith only [hCeq,hbC,hneg]
  have hderiv : -(6 * (C - 2 * b)) * d - 2 * (3 / 4) * u = 0 := by
    rw [show C - 2 * b = -(u / (4 * d)) by linarith only [hCeq,hbC]]
    field_simp [show d ≠ 0 by linarith]
    ring
  have hexact : ∀ D : ℝ, BalancedEnvelopeCeiling D ↔ C < D := by
    intro D
    constructor
    · rintro ⟨hD, χ, x, y, hχ, hx, hy, hpriv, hterm⟩
      by_contra! hle
      have hstrict : 3 / 4 * x ^ 2 + 4 * sqrt D < 6 * y * (D - y) := by
        nlinarith only [hterm, mul_pos (sub_pos.2 hχ) (sq_pos_of_pos hx)]
      have hterm' : 3 / 4 * x ^ 2 + 4 * sqrt C < 6 * y * (C - y) := by
        rcases hle.eq_or_lt with rfl | hlt
        · exact hstrict
        · exact balanced_terminal_strict_monotone hD hlt hy (by positivity) hstrict.le
      have ht := narrow_envelope_tangent (θ := 1 / 2) (U := 3 / 4)
        (by norm_num) (by norm_num) hu hx (le_refl (sqrt C)) hgap (hpriv.trans hle)
      change 6 * y * (C - y) - 3 / 4 * x ^ 2 - 4 * sqrt C ≤
        6 * b * (C - b) - 3 / 4 * u ^ 2 - 4 * sqrt C +
          (-(6 * (C - 2 * b)) * d - 2 * (3 / 4) * u) ^ 2 / (4 * (3 / 4)) at ht
      rw [hderiv] at ht
      nlinarith only [ht,hrel,hterm']
    · intro hD
      have ht : 3 / 4 * u ^ 2 + 4 * sqrt D < 6 * b * (D - b) :=
        balanced_terminal_strict_monotone hC hD (by linarith only [hb]) (by positivity) hrel.ge
      let surplus := 6 * b * (D - b) - (3 / 4 * u ^ 2 + 4 * sqrt D)
      have hsurplus : 0 < surplus := sub_pos.2 ht
      let χ := 1 + surplus / (2 * (3 / 4) * u ^ 2)
      have hχ : 1 < χ := by
        dsimp only [χ]
        linarith only [div_pos hsurplus (show 0 < 2 * (3 / 4) * u ^ 2 by positivity)]
      have he : (3 * χ / 4) * u ^ 2 = 3 / 4 * u ^ 2 + surplus / 2 := by
        dsimp only [χ]
        field_simp
      refine ⟨hC.trans hD, χ, u, b, hχ, hu, by linarith only [hb], ?_, ?_⟩
      · exact hbC.le.trans hD.le
      · rw [he]
        dsimp only [surplus] at hsurplus ⊢
        linarith only [hsurplus]
  have hlo := balanced_envelope_endpoint_lower (χ := 1) (by norm_num) hu
    (by linarith only [hb]) hC hbC.le (by linarith only [hrel])
  obtain ⟨χ, x, y, hχ, hx, hy, hp', ht⟩ := balanced_envelope_endpoint_upper
  have hhi := (hexact _).mp ⟨by norm_num, χ, x, y, hχ, hx, hy, hp', ht⟩
  exact ⟨u,hul,huu,hroot,hlo,hhi,hexact⟩

/-- The coefficient of the balanced continuum envelope. -/
noncomputable def balancedEnvelopeInfimum : ℝ := sInf {D | BalancedEnvelopeCeiling D}

theorem balancedEnvelopeInfimum_spec :
    1.9839824118071388228 < balancedEnvelopeInfimum ∧
    balancedEnvelopeInfimum < 1.9839824118071388230 ∧
    ∀ D : ℝ, BalancedEnvelopeCeiling D ↔ balancedEnvelopeInfimum < D := by
  obtain ⟨u, _, _, _, hlo, hhi, hfeas⟩ := balanced_envelope_exact_infimum
  have heq : {D | BalancedEnvelopeCeiling D} = Ioi (balancedStationaryCost u) := Set.ext hfeas
  rw [balancedEnvelopeInfimum, heq, csInf_Ioi]
  exact ⟨hlo,hhi,hfeas⟩

#print axioms balanced_envelope_exact_infimum
#print axioms balancedEnvelopeInfimum_spec

end Cogentic.Randomized
