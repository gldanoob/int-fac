import Cogentic.RandomizedPrivateGridUpper
import Cogentic.RandomizedTerminalAttainment
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Cogentic.Randomized

open scoped BigOperators

/-- The finite cost constraints in the private-grid lower bound, with positive
weights at every stage. -/
structure FinitePrivateSchedule (C : ℝ) where
  n : ℕ
  z : ℕ → ℝ
  w : ℕ → ℝ
  b : ℝ
  δ : ℝ
  curve : ℝ
  h : ℝ
  ratio : ℝ
  v : ℝ
  height : ℝ
  Z : ℝ
  hb : 0 < b
  hd : 0 < δ
  hc : 0 < curve
  hZ : 0 < Z
  hh : curve ≤ h
  hz0 : z 0 = 0
  hzn : z n = Z
  hstep : ∀ i < n, z i ≤ z (i + 1)
  hpositive : ∀ i < n, 0 < w i
  htail : ∀ i < n, (∑ j ∈ Finset.Ico i n, w j) ≤ C - b - h * z (i + 1)
  hmoment : 4 / (9 * curve ^ 2) ≤ ∑ i ∈ Finset.range n, z (i + 1) ^ 2 * w i
  hratio : 0 ≤ ratio
  hheight : (1 + δ * Z ^ 2 / (2 * (2 / (3 * curve ^ 2)))) / δ ^ 3 ≤ height
  hbox : height + v ≤ ratio * (b / δ)
  hmean : ratio / 3 + 1 / (3 * δ ^ 2 * b) ≤ 2 * v - b / δ
  hraw : b + δ * ratio / 3 + 1 / (3 * δ * b) ≤ C

/-- Each positive slack above the algebraic budget is enough for a finite,
uniform grid with positive weights, unit endpoint and h equal to the curve. -/
theorem finite_private_schedule_with_slack {u ε : ℝ}
    (hl : rootLower < u) (hr : u < rootUpper) (hp : rootPolynomial u = 0)
    (hε : 0 < ε) :
    ∃ s : FinitePrivateSchedule (algebraicCost u + ε), s.Z = 1 ∧ s.h = s.curve := by
  let C := algebraicCost u
  let b := C - algebraicPrivate u
  let δ := 2 / algebraicSqrtCost u
  let W := 4 / (9 * u ^ 2)
  obtain ⟨ratio, v, height, hb, hd, hu, hratio, _, _, hprivate, hheight, hbox, hmean, hraw⟩ :=
    isolated_root_terminal_attainment hl hr hp
  change 0 < b at hb
  change 0 < δ at hd
  change b + W + 2 * u / 3 = C at hprivate
  change (1 + δ / (2 * (2 / (3 * u ^ 2)))) / δ ^ 3 = height at hheight
  change height + v = ratio * (b / δ) at hbox
  change ratio / 3 + 1 / (3 * δ ^ 2 * b) = 2 * v - b / δ at hmean
  change b + δ * ratio / 3 + 1 / (3 * δ * b) = C at hraw
  have hu₁ : u ≤ 1 := hr.le.trans (by norm_num [rootUpper])
  have hW : u / 3 < W := by
    have huCube := pow_le_pow_left₀ hu.le hu₁ 3
    dsimp [W]
    apply (lt_div_iff₀ (by positivity)).2
    nlinarith only [huCube]
  obtain ⟨k, hk⟩ := exists_nat_gt (u / ε)
  let n : ℝ := (k : ℝ) + 1
  let z : ℕ → ℝ := fun i => (i : ℝ) / n
  have hn : 0 < n := by dsimp [n]; positivity
  have hmesh : u / n ≤ ε := by
    have h := (div_lt_iff₀ hε).1 hk
    apply (div_le_iff₀ hn).2
    dsimp [n]
    nlinarith only [h, hε]
  obtain ⟨w, _, hpositive, hmoment, hgate, _, herror⟩ :=
    uniform_private_grid_upper k hu hW
  change (∑ i ∈ Finset.range (k + 1), z (i + 1) ^ 2 * w i) = W at hmoment
  have htail (i : ℕ) (hi : i < k + 1) :
      (∑ j ∈ Finset.Ico i (k + 1), w j) ≤ C + ε - b - u * z (i + 1) := by
    have hg := hgate i hi
    change u * z (i + 1) + (∑ j ∈ Finset.Ico i (k + 1), w j) =
      W + 2 * u / 3 + (u / (2 * n) - u / (6 * n ^ 2)) at hg
    change u / (2 * n) - u / (6 * n ^ 2) ≤ u / n at herror
    linarith only [hg, herror, hmesh, hprivate]
  refine ⟨{
    n := k + 1
    z := z
    w := w
    b := b
    δ := δ
    curve := u
    h := u
    ratio := ratio
    v := v
    height := height
    Z := 1
    hb := hb
    hd := hd
    hc := hu
    hZ := by norm_num
    hh := le_rfl
    hz0 := by simp [z]
    hzn := by simpa [z, n] using div_self hn.ne'
    hstep := fun i _ => div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ i) hn.le
    hpositive := hpositive
    htail := htail
    hmoment := hmoment.ge
    hratio := hratio.le
    hheight := by simpa only [one_pow, mul_one] using hheight.le
    hbox := hbox.le
    hmean := hmean.le
    hraw := hraw.le.trans (le_add_of_nonneg_right hε.le)
  }, rfl, rfl⟩

/-- The algebraic budget is the greatest lower bound of the finite private
cost schedules. This is a statement about feasibility of the inequalities. -/
theorem sharp_finite_private_schedule_infimum {u : ℝ}
    (hl : rootLower < u) (hr : u < rootUpper) (hp : rootPolynomial u = 0) :
    IsGLB {C : ℝ | Nonempty (FinitePrivateSchedule C)} (algebraicCost u) := by
  constructor
  · rintro C ⟨s⟩
    by_contra! h
    exact exact_finite_grid_floor s.z s.w hl hr hp h s.hb s.hd s.hc s.hZ s.hh
      s.hz0 s.hzn s.hstep s.htail s.hmoment s.hratio s.hheight s.hbox s.hmean s.hraw
  · intro C hC
    by_contra! h
    let ε := (C - algebraicCost u) / 2
    have hε : 0 < ε := half_pos (sub_pos.mpr h)
    obtain ⟨s, _, _⟩ := finite_private_schedule_with_slack hl hr hp hε
    have bound := hC (show algebraicCost u + ε ∈ {C : ℝ | Nonempty (FinitePrivateSchedule C)}
      from ⟨s⟩)
    change C ≤ algebraicCost u + ε at bound
    dsimp [ε] at bound
    linarith only [bound, h]

end Cogentic.Randomized
