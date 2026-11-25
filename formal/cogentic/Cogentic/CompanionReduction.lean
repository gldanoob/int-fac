import Cogentic.RankCoverage
import Cogentic.PartialTargetCoverage
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

/-- The finite search has a candidate whose proposal passes the driver's verifier. -/
abbrev BoxHit (n ell : ℕ) : Prop :=
  let b := n.log2+1
  BoxWitness n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b) (candidate n) ell

/-- A density certificate for one input. Distinctness is enforced by the
finite set, and each member has a verified witness in its own search box. -/
def DenseBoxHits (n : ℕ) : Prop :=
  let β := Fixed.beta (n.log2+1)
  ∃ S : Finset ℕ, S ⊆ dyadicTargets β ∧ (∀ g∈S, BoxHit n g) ∧ 2^β≤3*β*S.card

/-- The fixed search still scans its entire dyadic target list. Enough verified
hits imply success of the companion splitter at the original cost bound. -/
theorem split_of_dense_box_hits (split : Splitter) {C₁ A : ℝ} (hc : 0≤C₁) (ha : 0≤A)
    (spec : SplitterSpec split C₁ A) {n : ℕ} (n64 : 64≤n) (hn : 2≤n)
    (composite : ¬n.Prime) (powerMiss : powerDivisor n (n.log2+1)=none)
    (dense : DenseBoxHits n) :
    tryDivisorWith n hn (fun m => (split n m).1) ≠ none ∧
      (splitterWork split n hn : ℝ) ≤ exp ((C₁+12*A+131117)*CompanionSplitCost.scale n) := by
  let b := n.log2+1
  let β := Fixed.beta b
  let gs := (dyadicTargets β).sort
  let probe := searchBox n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b) (candidate n)
  have mem {p : ℕ} : p∈gs ↔ p∈dyadicTargets β := by simp [gs]
  obtain ⟨S,sub,hits,enough⟩ := dense
  have bp : 0<β := by
    have d := Fixed.degree_pos (Nat.succ_pos n.log2)
    dsimp [β,Fixed.beta,Fixed.h,Fixed.z,b]; positivity
  have sat := search_saturation_of_hit_subset gs probe hn Nat.lt_log2_self bp
    (fun _ hp=>(mem_dyadicTargets.mp (mem.mp hp)).1)
    (fun _ hp=>(mem_dyadicTargets.mp (mem.mp hp)).2.2)
    S (fun g hg=>mem.mpr (sub hg)) (fun g hg=>searchBox_complete (hits g hg)) enough
  have width := TryPair.saturated_size Construction.construct Concrete.arch n hn
  change (match (fixedCollection n hn).1 with
    | .divisor d _ => ProperDivisor n d
    | .orders e .. => ∀ p : ℕ, p.Prime → p∣n → p-1 ∣ saturate e b β) at sat
  change (match (fixedCollection n hn).1 with
    | .divisor .. => True
    | .orders e .. => saturate e b β ≤ 2^(2^(2017*TwoThirdsCost.scale b))) at width
  unfold tryDivisorWith splitterWork
  cases h : (fixedCollection n hn).1 with
  | divisor d hd => exact ⟨by simp,by simpa only [Nat.cast_zero] using (exp_pos _).le⟩
  | orders e big even retained valid =>
    rw [h] at sat width
    let m := saturate e b β
    have positive := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr
      (fun i hi => Nat.ne_of_gt (Finset.mem_Icc.mp hi).1 :
        ∀ i ∈ Finset.Icc 1 (indexCap b β), id i ≠ 0))
    have hm : 2 ≤ m := big.trans (Nat.le_mul_of_pos_right e positive)
    have em : Even m := even_iff_two_dvd.mpr (dvd_mul_of_dvd_left even _)
    have nonpower (x j : ℕ) (hx : 2≤x) (hj : 2≤j) (eq : x^j=n) : False :=
      powerDivisor_of_power Nat.lt_log2_self hx hj eq powerMiss
    obtain ⟨success,cost⟩ := spec n m (by omega) composite nonpower hm em sat
    exact ⟨success,cost.trans (CompanionSplitCost.splitter_cost_of_saturated_bound n64
      (show 0 < m by omega) width hc ha)⟩

/-- On sufficiently large inputs all dyadic hits meet the cardinality threshold. -/
theorem dense_of_all_hits (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, (∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), BoxHit n ell) → DenseBoxHits n := by
  obtain ⟨β,count⟩ := dyadic_count_from_critical_line line
  obtain ⟨n₀,grow⟩ := Fixed.parameters_grow candidate β
  exact ⟨n₀,fun n large hits=>⟨_,Finset.Subset.rfl,hits,count _ (grow n large)⟩⟩

/-- Successful local certificates supply every argument of the companion splitter. -/
theorem split_of_box_hits (line : DirichletLZerosOnLine)
    (split : Splitter) {C₁ A : ℝ} (hc : 0 ≤ C₁) (ha : 0 ≤ A) (spec : SplitterSpec split C₁ A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ hn : 2 ≤ n, ¬n.Prime →
      powerDivisor n (n.log2+1) = none →
      presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = none →
      (∀ ell ∈ dyadicTargets (Fixed.beta (n.log2+1)), BoxHit n ell) →
      tryDivisorWith n hn (fun m => (split n m).1) ≠ none ∧
        (splitterWork split n hn : ℝ) ≤ exp ((C₁+12*A+131117)*CompanionSplitCost.scale n) := by
  obtain ⟨n₁,dense⟩ := dense_of_all_hits line
  refine ⟨max n₁ 64,?_⟩
  intro n large hn composite powerMiss _ hits
  obtain ⟨ready,n64⟩ := max_le_iff.mp large
  exact split_of_dense_box_hits split hc ha spec n64 hn composite powerMiss (dense n ready hits)

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
  obtain ⟨n₁,splitter⟩ := split_of_box_hits line split hc ha spec
  obtain ⟨b₀,grow⟩ := Fixed.degree_grows 130000
  refine ⟨max n₁ (2^b₀),?_⟩
  intro n large hn composite power sieve ranks
  obtain ⟨base,bits⟩ := max_le_iff.mp large
  have many := (Nat.le_log2 (show n≠0 by omega)).mpr bits
  exact splitter n base hn composite power sieve (fun ell ht=>
    witness_of_box_rank hn (grow _ (by omega)) composite ht sieve (ranks ell ht))

end Cogentic.Companion
