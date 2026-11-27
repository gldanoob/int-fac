import Cogentic.RandomizedBalancedFiniteSchedule
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Data.Rat.BigOperators

namespace Cogentic.Randomized

open Filter
open scoped BigOperators Topology

/-- Equalized private weights, with the final weight set by the exact moment. -/
def balancedUniformWeight (k : ℕ) (curve moment : ℚ) (i : ℕ) : ℚ :=
  let step := curve / ((k : ℚ) + 1)
  if i < k then step else
    moment - ∑ j ∈ Finset.range k, balancedUniformKnot k (j + 1) ^ 2 * step

/-- Choose the two rational recognition constants after fixing the strict
curve allowance. Their sum still fits the same curve cap. -/
theorem BalancedPerturbation.rational_elliptic_allowances {p : BalancedPerturbation}
    (hu : 0 < p.u) (hd : 0 < p.δ) (hq : 0 < p.q) :
    ∃ s₁ s₂ : ℚ, 1 / Real.sqrt 2 < (s₁ : ℝ) ∧ 1 / Real.sqrt 2 < (s₂ : ℝ) ∧
      ((s₁ : ℝ) + (s₂ : ℝ)) ^ 2 * (2 * p.y₀ / (3 * p.δ)) < p.h ^ 2 := by
  let x := 2 * p.y₀ / (3 * p.δ)
  have hx : 0 < x := by dsimp [x, BalancedPerturbation.y₀]; positivity
  have hh : 0 < p.h := by unfold BalancedPerturbation.h; positivity
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hL : 0 < 1 / Real.sqrt 2 := by positivity
  have hsq : ((1 / Real.sqrt 2) * (2 * Real.sqrt x)) ^ 2 = 2 * x := by
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hx.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hgap : 1 / Real.sqrt 2 < p.h / (2 * Real.sqrt x) := by
    apply (lt_div_iff₀ (by positivity)).2
    apply (sq_lt_sq₀ (by positivity) hh.le).1
    rw [hsq]
    exact BalancedPerturbation.curve_allowance hu hd hq
  obtain ⟨s, hsₗ, hsᵤ⟩ := exists_rat_btwn hgap
  have hmul : (s : ℝ) * (2 * Real.sqrt x) < p.h := (lt_div_iff₀ (by positivity)).1 hsᵤ
  have hmul₀ : 0 ≤ (s : ℝ) * (2 * Real.sqrt x) := by
    exact mul_nonneg (hL.trans hsₗ).le (by positivity)
  refine ⟨s, s, hsₗ, hsₗ, ?_⟩
  change ((s : ℝ) + (s : ℝ)) ^ 2 * x < p.h ^ 2
  calc
    _ = ((s : ℝ) + (s : ℝ)) ^ 2 * (Real.sqrt x) ^ 2 := by rw [Real.sq_sqrt hx.le]
    _ = ((s : ℝ) * (2 * Real.sqrt x)) ^ 2 := by ring
    _ < _ := (sq_lt_sq₀ hmul₀ hh.le).2 hmul

/-- Any further positive cap from the prime-bin estimate can be imposed on
the angular cutoff without changing the other parameters. -/
theorem BalancedPerturbation.rational_angular_cutoff {p : BalancedPerturbation}
    (hq : 0 < p.q) {cap : ℝ} (hcap : 0 < cap) :
    ∃ ζ : ℚ, 0 < (ζ : ℝ) ∧ 2 * (ζ : ℝ) < p.χ - 1 ∧ (ζ : ℝ) < cap := by
  have hwidth : 0 < (p.χ - 1) / 2 := by unfold BalancedPerturbation.χ; linarith
  obtain ⟨ζ, hζ, hbound⟩ := exists_rat_btwn (lt_min hwidth hcap)
  have hw := hbound.trans_le (min_le_left ((p.χ - 1) / 2) cap)
  exact ⟨ζ, hζ, by linarith only [hw], hbound.trans_le (min_le_right ..)⟩

private theorem rational_balanced_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ u b δ q : ℚ,
      let p : BalancedPerturbation := ⟨u,b,δ,q⟩
      0.58514027 < p.u ∧ p.u < 0.58514029 ∧
      0.9448547 < p.b ∧ p.b < 0.944855 ∧
      1.4199108 < p.δ ∧ p.δ < 1.4199110 ∧
      0 < p.q ∧ p.q < 1 / 10 ^ 6 ∧
      p.h / 3 < p.M ∧ p.b + p.M + 2 * p.h / 3 + p.q < balancedEnvelopeInfimum + ε ∧
      p.lowRaw < balancedEnvelopeInfimum + ε := by
  obtain ⟨p, _, huₗ, huᵤ, hbₗ, hbᵤ, hdₗ, hdᵤ, hq, hq', hM, hgate, hraw, _⟩ :=
    balanced_finite_private_low_budget hε
  let point : ℝ × ℝ × ℝ × ℝ := (p.u,p.b,p.δ,p.q)
  let toParams (x : ℝ × ℝ × ℝ × ℝ) : BalancedPerturbation := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  have he : toParams point = p := by cases p; rfl
  have Hu : Continuous (fun x : ℝ × ℝ × ℝ × ℝ => (toParams x).u) := continuous_fst
  have Hb : Continuous (fun x : ℝ × ℝ × ℝ × ℝ => (toParams x).b) :=
    continuous_fst.comp continuous_snd
  have Hδ : Continuous (fun x : ℝ × ℝ × ℝ × ℝ => (toParams x).δ) :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have Hq : Continuous (fun x : ℝ × ℝ × ℝ × ℝ => (toParams x).q) :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hN (f : BalancedPerturbation → ℝ)
      (hf : ContinuousAt (fun x => f (toParams x)) point) :
      Tendsto (fun x => f (toParams x)) (𝓝 point) (𝓝 (f p)) := by
    change Tendsto (fun x => f (toParams x)) (𝓝 point) (𝓝 (f (toParams point))) at hf
    simpa only [he] using hf
  have hu : 0 < p.u := by linarith only [huₗ]
  have hb : 0 < p.b := by linarith only [hbₗ]
  have hd : 0 < p.δ := by linarith only [hdₗ]
  have hpβ : 0 < p.b / p.δ := div_pos hb hd
  have hpβ' : 0 < 2 * (p.b / p.δ) - 1 / 3 := by
    apply sub_pos.mpr
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hd).2
    linarith only [hbₗ,hdᵤ]
  have HM : ContinuousAt (fun x => (toParams x).M) point := by
    unfold BalancedPerturbation.M
    exact continuousAt_const.div (continuousAt_const.mul (Hu.continuousAt.pow 2))
      (by change 9 * (toParams point).u ^ 2 ≠ 0; rw [he]; positivity)
  have Hh : Continuous (fun x => (toParams x).h) := Hu.add Hq
  have Hβ : ContinuousAt (fun x => (toParams x).β) point :=
    Hb.continuousAt.div Hδ.continuousAt (by rw [he]; exact hd.ne')
  have Hwy : Continuous (fun x => (toParams x).y₀) :=
    ((continuous_const.mul (Hu.pow 2)).mul Hδ).div_const _
  have Hwv : Continuous (fun x => (toParams x).v₀) :=
    (continuous_const.add Hq).mul Hwy
  have HRadix : ContinuousAt (fun x => (toParams x).R) point :=
    continuousAt_const.div (Hδ.continuousAt.pow 3) (by rw [he]; positivity)
  have Hheight : ContinuousAt (fun x => (toParams x).Aplus) point := by
    unfold BalancedPerturbation.Aplus BalancedPerturbation.A₀ BalancedPerturbation.χ
    exact (HRadix.mul (continuousAt_const.add
      ((continuousAt_const.add Hq.continuousAt).mul Hwv.continuousAt))).add Hq.continuousAt
  have HRcut : ContinuousAt (fun x => (toParams x).R / (3 * (toParams x).β)) point :=
    HRadix.div (continuousAt_const.mul Hβ) (by rw [he]; change 3 * (p.b / p.δ) ≠ 0; positivity)
  have Hlow : ContinuousAt (fun x => (toParams x).lowRatio) point := by
    unfold BalancedPerturbation.lowRatio
    exact ((((Hβ.add (continuousAt_const.mul Hheight)).add HRcut).add
      (continuousAt_const.mul Hq.continuousAt)).div
      ((continuousAt_const.mul Hβ).sub continuousAt_const)
      (by rw [he]; exact hpβ'.ne'))
  have HR : ContinuousAt (fun x => (toParams x).lowRaw) point := by
    unfold BalancedPerturbation.lowRaw
    have Hz : ContinuousAt (fun x => 1 / (3 * (toParams x).δ * (toParams x).b)) point :=
      continuousAt_const.div ((continuousAt_const.mul Hδ.continuousAt).mul Hb.continuousAt)
        (by rw [he]; positivity)
    exact (((Hb.continuousAt.add ((Hδ.continuousAt.mul Hlow).div_const _)).add Hz).add
      (continuousAt_const.mul Hq.continuousAt))
  let S : Set (ℝ × ℝ × ℝ × ℝ) := {x |
    let p := toParams x
    0.58514027 < p.u ∧ p.u < 0.58514029 ∧
    0.9448547 < p.b ∧ p.b < 0.944855 ∧
    1.4199108 < p.δ ∧ p.δ < 1.4199110 ∧
    0 < p.q ∧ p.q < 1 / 10 ^ 6 ∧
    p.h / 3 < p.M ∧ p.b + p.M + 2 * p.h / 3 + p.q < balancedEnvelopeInfimum + ε ∧
    p.lowRaw < balancedEnvelopeInfimum + ε}
  have hS : S ∈ 𝓝 point := by
    filter_upwards [(hN BalancedPerturbation.u Hu.continuousAt).eventually_const_lt huₗ,
      (hN BalancedPerturbation.u Hu.continuousAt).eventually_lt_const huᵤ,
      (hN BalancedPerturbation.b Hb.continuousAt).eventually_const_lt hbₗ,
      (hN BalancedPerturbation.b Hb.continuousAt).eventually_lt_const hbᵤ,
      (hN BalancedPerturbation.δ Hδ.continuousAt).eventually_const_lt hdₗ,
      (hN BalancedPerturbation.δ Hδ.continuousAt).eventually_lt_const hdᵤ,
      (hN BalancedPerturbation.q Hq.continuousAt).eventually_const_lt hq,
      (hN BalancedPerturbation.q Hq.continuousAt).eventually_lt_const hq',
      (hN (fun p => p.h / 3) (Hh.continuousAt.div_const 3)).eventually_lt
        (hN BalancedPerturbation.M HM) hM,
      (hN (fun p => p.b + p.M + 2 * p.h / 3 + p.q) (((Hb.continuousAt.add HM).add
        ((continuousAt_const.mul Hh.continuousAt).div_const 3)).add Hq.continuousAt)).eventually_lt_const hgate,
      (hN BalancedPerturbation.lowRaw HR).eventually_lt_const hraw]
      with x hu₁ hu₂ hb₁ hb₂ hd₁ hd₂ hq₁ hq₂ hM' hgate' hraw'
    exact ⟨hu₁,hu₂,hb₁,hb₂,hd₁,hd₂,hq₁,hq₂,hM',hgate',hraw'⟩
  have hdense : DenseRange (fun x : ℚ => (x:ℝ)) := Rat.denseRange_cast
  obtain ⟨⟨u,b,δ,q⟩, hmem⟩ :=
    (hdense.prodMap (hdense.prodMap (hdense.prodMap hdense))).mem_nhds hS
  exact ⟨u,b,δ,q,hmem⟩

/-- Every larger ceiling admits rational scalar parameters and rational
equalized weights. The same scalar parameters work at every sufficiently
fine fixed uniform mesh. -/
theorem rational_balanced_finite_budget {ε : ℝ} (hε : 0 < ε) :
    ∃ u b δ q : ℚ, ∃ K : ℕ,
      let p : BalancedPerturbation := ⟨u,b,δ,q⟩
      0.58514027 < p.u ∧ p.u < 0.58514029 ∧
      0.9448547 < p.b ∧ p.b < 0.944855 ∧
      1.4199108 < p.δ ∧ p.δ < 1.4199110 ∧
      0 < p.q ∧ p.q < 1 / 10 ^ 6 ∧ p.lowRaw < balancedEnvelopeInfimum + ε ∧
      ∀ k ≥ K,
        let z : ℕ → ℝ := fun i => balancedUniformKnot k i
        let w : ℕ → ℝ := fun i => balancedUniformWeight k (u + q) (2 / (9 * u ^ 2)) i
        z 0 = 0 ∧ z (k + 1) = 1 ∧ (∀ i < k + 1, z i < z (i + 1)) ∧
        (∀ i < k + 1, 0 < w i) ∧
        (∑ i ∈ Finset.range (k + 1), z (i + 1) ^ 2 * w i) = p.M ∧
        (∀ i < k + 1, p.b + p.h * z (i + 1) +
          (∑ j ∈ Finset.Ico i (k + 1), w j) + p.q < balancedEnvelopeInfimum + ε) ∧
        p.b + (∑ j ∈ Finset.range (k + 1), w j) + p.q < balancedEnvelopeInfimum + ε ∧
        ((∑ j ∈ Finset.range (k + 1), w j) / p.M) < 1.602 := by
  obtain ⟨u,b,δ,q,huₗ,huᵤ,hbₗ,hbᵤ,hdₗ,hdᵤ,hq,hq',hM,hgate,hraw⟩ :=
    rational_balanced_parameters hε
  let p : BalancedPerturbation := ⟨u,b,δ,q⟩
  let D := balancedEnvelopeInfimum + ε
  let slack := D - (p.b + p.M + 2 * p.h / 3 + p.q)
  have hslack : 0 < slack := sub_pos.mpr hgate
  have hu : 0 < p.u := by linarith only [huₗ]
  have hh : 0 < p.h := by unfold BalancedPerturbation.h; positivity
  have hh' : p.h ≤ 0.58514129 := by unfold BalancedPerturbation.h; linarith only [huᵤ,hq']
  have hMₗ : 0.64903404 < p.M := by
    unfold BalancedPerturbation.M
    apply (lt_div_iff₀ (by positivity)).2
    nlinarith only [pow_le_pow_left₀ hu.le huᵤ.le 2]
  obtain ⟨K,hK⟩ := exists_nat_gt (p.h / slack)
  refine ⟨u,b,δ,q,K,huₗ,huᵤ,hbₗ,hbᵤ,hdₗ,hdᵤ,hq,hq',hraw,?_⟩
  intro k hk
  let n : ℝ := (k : ℝ) + 1
  let z : ℕ → ℝ := fun i => (i : ℝ) / n
  let hqnt : ℚ := u + q
  let mqnt : ℚ := 2 / (9 * u ^ 2)
  let wq : ℕ → ℝ := fun i => balancedUniformWeight k hqnt mqnt i
  have hn : 0 < n := by dsimp [n]; positivity
  have hz (i : ℕ) : (balancedUniformKnot k i : ℝ) = z i := by
    simp [balancedUniformKnot,z,n]
  have heh : (hqnt : ℝ) = p.h := by simp [hqnt,p,BalancedPerturbation.h]
  have heM : (mqnt : ℝ) = p.M := by simp [mqnt,p,BalancedPerturbation.M]
  have hz' : z (k + 1) = 1 := by simpa [z,n] using div_self hn.ne'
  have hstep (i : ℕ) : z i < z (i + 1) :=
    (div_lt_div_iff_of_pos_right hn).2 (by exact_mod_cast Nat.lt_succ_self i)
  have hmesh : p.h / n < slack := by
    have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
    have hcap := (div_lt_iff₀ hslack).1 (hK.trans_le hk')
    apply (div_lt_iff₀ hn).2
    dsimp [n]
    linarith only [hcap,hslack]
  obtain ⟨w,hwInterior,hwPos,hwMoment,hwGate,_,hwError⟩ :=
    uniform_private_grid_upper k hh hM
  have hwInterior' (i : ℕ) (hi : i < k) : w i = p.h / n := by
    have he := hwInterior i hi
    change w i = p.h * (z (i + 2) - z (i + 1)) at he
    rw [he]
    simp only [z, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  have hweq (i : ℕ) (hi : i < k + 1) : wq i = w i := by
    by_cases hik : i < k
    · rw [hwInterior' i hik]
      simp [wq,balancedUniformWeight,hik,heh,n]
    · have he : i = k := by omega
      subst i
      change (∑ j ∈ Finset.range (k + 1), z (j + 1) ^ 2 * w j) = p.M at hwMoment
      rw [Finset.sum_range_succ, hz', one_pow, one_mul] at hwMoment
      have hsum : (∑ j ∈ Finset.range k, z (j + 1) ^ 2 * w j) =
          ∑ j ∈ Finset.range k, z (j + 1) ^ 2 * (p.h / n) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hwInterior' j (Finset.mem_range.mp hj)]
      rw [hsum] at hwMoment
      have he' : wq k = p.M - ∑ j ∈ Finset.range k, z (j + 1) ^ 2 * (p.h / n) := by
        simp [wq,balancedUniformWeight,Rat.cast_sum,heh,heM,hz,n]
      linarith only [hwMoment,he']
  have hwMoment' :
      (∑ j ∈ Finset.range (k + 1), z (j + 1) ^ 2 * wq j) = p.M := by
    calc
      _ = ∑ j ∈ Finset.range (k + 1), z (j + 1) ^ 2 * w j :=
        Finset.sum_congr rfl fun j hj => by rw [hweq j (Finset.mem_range.mp hj)]
      _ = _ := hwMoment
  have htail (i : ℕ) : (∑ j ∈ Finset.Ico i (k + 1), wq j) =
      ∑ j ∈ Finset.Ico i (k + 1), w j :=
    Finset.sum_congr rfl fun j hj => hweq j (Finset.mem_Ico.mp hj).2
  have hgate' (i : ℕ) (hi : i < k + 1) :
      p.b + p.h * z (i + 1) + (∑ j ∈ Finset.Ico i (k + 1), wq j) + p.q < D := by
    have he := hwGate i hi
    change p.h * z (i + 1) + (∑ j ∈ Finset.Ico i (k + 1), w j) =
      p.M + 2 * p.h / 3 + (p.h / (2 * n) - p.h / (6 * n ^ 2)) at he
    change p.h / (2 * n) - p.h / (6 * n ^ 2) ≤ p.h / n at hwError
    dsimp only [slack] at hmesh
    rw [htail]
    linarith only [hmesh,hwError,he]
  have htotal : p.b + (∑ j ∈ Finset.range (k + 1), wq j) + p.q < D := by
    have he := hgate' 0 (Nat.zero_lt_succ k)
    rw [Nat.Ico_zero_eq_range] at he
    have hnz : 0 ≤ z 1 := by dsimp [z]; positivity
    linarith only [he,mul_nonneg hh.le hnz]
  have hratio : (∑ j ∈ Finset.range (k + 1), wq j) / p.M < 1.602 := by
    have he := hwGate 0 (Nat.zero_lt_succ k)
    change p.h * z 1 + (∑ j ∈ Finset.Ico 0 (k + 1), w j) =
      p.M + 2 * p.h / 3 + (p.h / (2 * n) - p.h / (6 * n ^ 2)) at he
    change p.h / (2 * n) - p.h / (6 * n ^ 2) ≤ p.h / n at hwError
    rw [← htail, Nat.Ico_zero_eq_range] at he
    have hz₁ : p.h * z 1 = p.h / n := by
      simp [z,div_eq_mul_inv]
    apply (div_lt_iff₀ (show 0 < p.M by linarith only [hMₗ])).2
    linarith only [he,hwError,hz₁,hh',hMₗ]
  dsimp only
  simp only [hz]
  exact ⟨by simp [z],hz',fun i _ => hstep i,fun i hi => by
    change 0 < wq i
    rw [hweq i hi]
    exact hwPos i hi,
    hwMoment',hgate',htotal,hratio⟩

#print axioms rational_balanced_finite_budget
#print axioms BalancedPerturbation.rational_elliptic_allowances
#print axioms BalancedPerturbation.rational_angular_cutoff

end Cogentic.Randomized
