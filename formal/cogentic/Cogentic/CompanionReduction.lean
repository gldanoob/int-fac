import Cogentic.RankCoverage
import Cogentic.CompanionSplitCost

namespace Cogentic.Companion
open TwoThirdsSearch Concrete Real

/-- A splitter returns a verified divisor and its bit-operation count. -/
abbrev Splitter := (n m : ℕ) → Option {d // ProperDivisor n d} × ℕ

/-- The input/output and cost specification of the deterministic paper's Theorem 1.2(a). -/
def SplitterSpec (split : Splitter) (C₁ A : ℝ) : Prop :=
  ∀ n m : ℕ, 4 ≤ n → ¬n.Prime → (∀ x j : ℕ, 2 ≤ x → 2 ≤ j → x^j ≠ n) →
    2 ≤ m → Even m → (∀ p : ℕ, p.Prime → p ∣ n → p-1 ∣ m) →
    (split n m).1 ≠ none ∧ ((split n m).2 : ℝ) ≤
      C₁ * exp (A * sqrt (log n) * log (log ((n : ℝ)+16))) * log m * (log n)^2

/-- Charge the companion call only on the orders branch of our actual fixed search. -/
def splitterWork (split : Splitter) (n : ℕ) (hn : 2 ≤ n) : ℕ :=
  match (fixedCollection n hn).1 with
  | .divisor .. => 0
  | .orders e .. => (split n (saturate e (n.log2+1) (Fixed.beta (n.log2+1)))).2

/-- A full-rank tuple for each target in our fixed box makes the companion splitter
produce a proper divisor within the two-thirds budget, including the direct-divisor branch. -/
theorem split_of_box_rank (line : DirichletLZerosOnLine)
    (split : Splitter) {C₁ A : ℝ} (hc : 0 ≤ C₁) (ha : 0 ≤ A) (spec : SplitterSpec split C₁ A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ hn : 2 ≤ n, ¬n.Prime →
      powerDivisor n (n.log2+1) = none →
      presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = none →
      (∀ ell ∈ dyadicTargets (Fixed.beta (n.log2+1)), BoxHasRank n ell) →
      tryDivisorWith n hn (fun m => (split n m).1) ≠ none ∧
        (splitterWork split n hn : ℝ) ≤ exp ((C₁+12*A+131117)*CompanionSplitCost.scale n) := by
  obtain ⟨β,count⟩ := dyadic_count_from_critical_line line
  obtain ⟨n₁,growβ⟩ := Fixed.parameters_grow candidate β
  obtain ⟨b₀,growd⟩ := Fixed.degree_grows 130000
  refine ⟨max (max n₁ (2^b₀)) 64,?_⟩
  intro n large hn composite powerMiss sieveMiss ranks
  have n64 : 64 ≤ n := (le_max_right ..).trans large
  have lb : max n₁ (2^b₀) ≤ n := (le_max_left ..).trans large
  let b := n.log2+1
  let gs := (dyadicTargets (Fixed.beta b)).sort
  let probe := searchBox n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b) (candidate n)
  have member {p : ℕ} (hp : p ∈ gs) : p ∈ dyadicTargets (Fixed.beta b) := by
    simpa [gs] using hp
  have counted : 2^(Fixed.beta b) ≤ 3*Fixed.beta b*gs.toFinset.card := by
    rw [show gs.toFinset = dyadicTargets (Fixed.beta b) by simp [gs]]
    exact count _ (growβ n ((le_max_left ..).trans lb))
  have many := (Nat.le_log2 (show n ≠ 0 by omega)).mpr ((le_max_right ..).trans lb)
  have deg : 130000 ≤ Fixed.d b := growd _ (by dsimp [b]; omega)
  have betaPos : 0 < Fixed.beta b := by
    have pd := Fixed.degree_pos (Nat.succ_pos n.log2)
    dsimp [Fixed.beta,Fixed.h,Fixed.z,b]; positivity
  have sat := search_saturation gs probe hn Nat.lt_log2_self betaPos
    (fun _ hp => (mem_dyadicTargets.mp (member hp)).1)
    (fun _ hp => (mem_dyadicTargets.mp (member hp)).2.2) counted
    (fun p hp => searchBox_complete
      (witness_of_box_rank hn deg composite (member hp) sieveMiss (ranks p (member hp))))
  have width := TryPair.saturated_size Construction.construct Concrete.arch n hn
  change (match (fixedCollection n hn).1 with
    | .divisor d _ => ProperDivisor n d
    | .orders e .. => ∀ p : ℕ, p.Prime → p ∣ n → p-1 ∣ saturate e b (Fixed.beta b)) at sat
  change (match (fixedCollection n hn).1 with
    | .divisor .. => True
    | .orders e .. => saturate e b (Fixed.beta b) ≤ 2^(2^(2017*TwoThirdsCost.scale b))) at width
  unfold tryDivisorWith splitterWork
  cases h : (fixedCollection n hn).1 with
  | divisor d hd => exact ⟨by simp, by simpa only [Nat.cast_zero] using (exp_pos _).le⟩
  | orders e big even retained valid =>
    rw [h] at sat width
    let m := saturate e b (Fixed.beta b)
    have pos := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr
      (fun i hi => Nat.ne_of_gt (Finset.mem_Icc.mp hi).1 :
        ∀ i ∈ Finset.Icc 1 (indexCap b (Fixed.beta b)), id i ≠ 0))
    have hm : 2 ≤ m := big.trans (Nat.le_mul_of_pos_right e pos)
    have em : Even m := even_iff_two_dvd.mpr (dvd_mul_of_dvd_left even _)
    have nonpower (x j : ℕ) (hx : 2 ≤ x) (hj : 2 ≤ j) (eq : x^j=n) : False :=
      powerDivisor_of_power Nat.lt_log2_self hx hj eq powerMiss
    obtain ⟨success,cost⟩ := spec n m (by omega) composite nonpower hm em sat
    exact ⟨success, cost.trans (CompanionSplitCost.splitter_cost_of_saturated_bound n64
      (show 0 < m by omega) width hc ha)⟩

end Cogentic.Companion
