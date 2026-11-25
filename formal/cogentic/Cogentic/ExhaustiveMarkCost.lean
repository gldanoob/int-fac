import Cogentic.CandidateMarkConstruction
import Cogentic.BinaryMaskCost
import Cogentic.CofactorProductCost
import Cogentic.PerturbationCost
import Cogentic.FactorBaseCost
import Cogentic.ResidueEnumerationCost
import Cogentic.CompanionSplitCost
import Cogentic.MinorVerificationWork
import Cogentic.CollectorCost
import Cogentic.TargetEnumerationCost
import Cogentic.BinaryRootColumnsCost
import Cogentic.ProjectionGates
import Cogentic.ConstructorBaseCost

namespace Cogentic.Concrete
open Finset TwoThirdsSearch

/-- Binary construction of the factor-base list and eligible marks, followed
by row classification and the retained-mark tests. -/
def markTrialWork (n g u v w z : ℕ) : ℕ :=
  let pair := Construction.construct n g u v w z
  (BinaryPerturbation.run (primorial (Fixed.d (n.log2+1))).bits g.bits (Fixed.rootBase n).bits
    u.bits v.bits w.bits z.bits ((BinaryPerturbation.correctedBase n g false).map BinaryPivot.encode)
    ((BinaryPerturbation.correctedBase n g true).map BinaryPivot.encode)).2 +
  (BinaryMaskCost.run (Fixed.d (n.log2+1)).bits).2 +
  (BinaryCofactor.run n.bits (Fixed.rootBase n).bits (pair.first.map BinaryPivot.encode)
    (pair.second.map BinaryPivot.encode)).2 +
  (BinaryFactorBase.run (Fixed.B (n.log2+1)).bits (Construction.markModulus n g).bits).2 +
  (BinaryResidues.enumerate ((TryPair.fixedInput n g (Construction.construct n g u v w z)).base.map Nat.bits)).2 +
  (CandidateMarks.checkedStage n g u v w z).2

/-- Sum a per-trial charge over the four actual search ranges and the dyadic targets. -/
def boxWork (n : ℕ) (trial : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  let b := n.log2+1
  let fast := 2*b^2*Fixed.U b
  let slow := fast*Fixed.A b
  ∑ g ∈ dyadicTargets (Fixed.beta b), ∑ u ∈ Icc 1 slow, ∑ v ∈ Icc 1 fast,
    ∑ w ∈ Icc 1 slow, ∑ z ∈ Icc 1 fast,
      trial g u v w z

theorem boxWork_le (n k : ℕ) (trial : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) :
    let b := n.log2+1
    let fast := 2*b^2*Fixed.U b
    let slow := fast*Fixed.A b
    let gs := dyadicTargets (Fixed.beta b)
    let s := TwoThirdsCost.scale b
    let C := 2^(k*s)
    (∀ g∈gs, ∀ u∈Icc 1 slow, ∀ v∈Icc 1 fast, ∀ w∈Icc 1 slow, ∀ z∈Icc 1 fast,
      trial g u v w z≤C) → boxWork n trial≤2^((421012+k)*s) := by
  intro b fast slow gs s C pay
  have hb : 0<b := Nat.succ_pos _
  have full : boxWork n trial ≤ gs.card*(slow*(fast*(slow*(fast*C)))) := by
    unfold boxWork
    refine (sum_le_sum (fun g hg=>sum_le_sum (fun u hu=>sum_le_sum (fun v hv=>
      sum_le_sum (fun w hw=>sum_le_sum (fun z hz=>pay g hg u hu v hv w hw z hz)))))).trans_eq ?_
    simp [Nat.card_Icc,gs,fast,slow,b,C]
  have deg := Fixed.degree_pos hb
  have vs := (Fixed.scale_bounds hb).1
  have hs : Fixed.h b ≤ s := (Nat.le_mul_of_pos_left _ deg).trans vs
  have zs : Fixed.z b ≤ s := (Nat.le_mul_of_pos_left _ deg).trans hs
  have sp : 0<s := (Nat.succ_pos b.log2).trans_le zs
  have bmax : b ≤ 2^Fixed.z b := Nat.lt_log2_self.le
  have nt : gs.card ≤ Fixed.B b := Fixed.target_card b
  have count : gs.card*(slow*(fast*(slow*fast))) ≤ 2^(421012*s) := by
    calc
      _ ≤ Fixed.B b*((2*(2^Fixed.z b)^2*Fixed.U b*Fixed.A b)*((2*(2^Fixed.z b)^2*Fixed.U b)*
        ((2*(2^Fixed.z b)^2*Fixed.U b*Fixed.A b)*(2*(2^Fixed.z b)^2*Fixed.U b)))) := by
          dsimp [fast,slow]; gcongr
      _ = 2^(400000*Fixed.v b+21000*Fixed.h b+8*Fixed.z b+4) := by
        unfold Fixed.B Fixed.beta Fixed.A Fixed.U
        have twice (e : ℕ) : 2*2^e=2^(1+e) := by rw [pow_add,pow_one]
        simp only [←Nat.pow_mul,twice,←Nat.pow_add]
        congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  calc
    _ ≤ (gs.card*(slow*(fast*(slow*fast))))*C := full.trans_eq (by ring)
    _ ≤ 2^(421012*s)*C := Nat.mul_le_mul_right C count
    _ = _ := by dsimp [C]; rw [←pow_add]; congr 1; ring

def exhaustiveMarkWork (n : ℕ) := boxWork n (markTrialWork n)

/-- Uniform bit budget for the row and mark circuits across all targets and
all candidates on a surviving input, plus target enumeration and collector overhead. -/
theorem exhaustive_mark_gates {n : ℕ} (hn : 2≤n) (large : 130000 ≤ Fixed.d (n.log2+1))
    (composite : ¬n.Prime)
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none) :
    let b := n.log2+1
    exhaustiveMarkWork n+(BinaryTargets.run (Fixed.beta b).bits).2+(BinaryCollector.fixed n).overhead ≤
      2^(511043*TwoThirdsCost.scale b) := by
  let b := n.log2+1
  let fast := 2*b^2*Fixed.U b
  let slow := fast*Fixed.A b
  let gs := dyadicTargets (Fixed.beta b)
  let s := TwoThirdsCost.scale b
  let C := 2^(90029*s)
  have hb : 0<b := Nat.succ_pos _
  have pay (g) (hg : g∈gs) u (hu : u∈Icc 1 slow) v (hv : v∈Icc 1 fast)
      w (hw : w∈Icc 1 slow) z (hz : z∈Icc 1 fast) :
      markTrialWork n g u v w z≤C := by
    have big : 10004≤Fixed.d (n.log2+1) := by omega
    have base := (BinaryFactorBase.fixed_factorBase hn big composite hg sieved u v w z).2.2
    have inBox : u ≤ slow ∧ v ≤ fast ∧ w ≤ slow ∧ z ≤ fast :=
      ⟨(mem_Icc.mp hu).2,(mem_Icc.mp hv).2,(mem_Icc.mp hw).2,(mem_Icc.mp hz).2⟩
    have marks := (CandidateMarks.fixed_checked_stage hn large composite hg sieved inBox).2
    have cofactor := (BinaryCofactor.fixed_markModulus hn large composite hg sieved inBox).2.2
    have changed := (BinaryPerturbation.fixed_pair hn large hg inBox).2.2
    have mask := (BinaryMaskCost.fixed_mask hb).2.2
    have sp : 0<s := (Nat.succ_pos _ : 0<Fixed.z b).trans_le
      ((Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans
        ((Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans (Fixed.scale_bounds hb).1))
    have residues := (BinaryResidues.fixed_residue_enumeration n g (Construction.construct n g u v w z)).2.2
    have resCap : 2^(3010*s) ≤ 2^(5100*s) := Nat.pow_le_pow_right (by decide) (by omega)
    have firstCap : 2^(30*s) ≤ 2^(5100*s) := Nat.pow_le_pow_right (by decide) (by omega)
    have chCap : 2^(47*s) ≤ 2^(5100*s) := Nat.pow_le_pow_right (by decide) (by omega)
    have combo := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add (changed.trans chCap) (mask.trans firstCap)) (cofactor.trans firstCap)) base) (residues.trans resCap)
    have e : 2^(5100*s)+2^(5100*s)+2^(5100*s)+2^(5100*s)+2^(5100*s) ≤ 2^(90028*s) := calc
      _ ≤ 2^(3+5100*s) := by rw [pow_add]; norm_num; omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
    change markTrialWork n g u v w z≤2^(90029*s)
    exact (Nat.add_le_add (combo.trans e) marks).trans (calc
      _ = 2^(1+90028*s) := by rw [pow_add,pow_one,two_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega))
  have running : exhaustiveMarkWork n ≤ 2^(511041*s) := boxWork_le n 90029 (markTrialWork n) pay
  have hs : Fixed.h b ≤ s := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans (Fixed.scale_bounds hb).1
  have sp : 0<s := (Nat.mul_pos (Fixed.degree_pos hb) (Nat.succ_pos _)).trans_le hs
  have extra := (BinaryTargets.fixed_targets hb).2
  have collect := (BinaryCollector.fixed_collector hn).2.2
  have lim : 2^(8000*s) ≤ 2^(511041*s) := Nat.pow_le_pow_right (by decide) (by omega)
  have aux : 2^(6000*Fixed.h b) ≤ 2^(511041*s) := Nat.pow_le_pow_right (by decide) (by omega)
  have bound := Nat.add_le_add (Nat.add_le_add running (extra.trans aux)) (collect.trans lim)
  change _ ≤ 2^(511043*s)
  exact bound.trans (calc
    _ ≤ 4*2^(511041*s) := by omega
    _ = 2^(2+511041*s) := by rw [pow_add]; rfl
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega))

private theorem natural_cost {n c work : ℕ} (hn : 64≤n)
    (bound : work ≤ 2^(c*TwoThirdsCost.scale (n.log2+1))) :
    (work:ℝ) ≤ Real.exp ((c:ℝ)*65*CompanionSplitCost.scale n) := by
  let k := c*TwoThirdsCost.scale (n.log2+1)
  have sc := CompanionSplitCost.binary_scale_le hn
  have kb : (k:ℝ) ≤ (c:ℝ)*65*CompanionSplitCost.scale n := by
    dsimp [k]; push_cast; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left sc (by positivity)
  have lt2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ (2:ℝ)^k := by exact_mod_cast bound
    _ = Real.exp ((k:ℝ)*Real.log 2) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    _ ≤ _ := Real.exp_le_exp.mpr (((mul_le_mul_of_nonneg_left lt2 (Nat.cast_nonneg k)).trans_eq (mul_one _)).trans kb)

/-- A natural-logarithm L bound for all row and mark circuits, target
enumeration, and collection across the exhaustive search. -/
theorem exhaustive_mark_L_two_thirds {n : ℕ} (hn : 64≤n) (large : 130000 ≤ Fixed.d (n.log2+1))
    (composite : ¬n.Prime)
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none) :
    let b := n.log2+1
    ((exhaustiveMarkWork n+(BinaryTargets.run (Fixed.beta b).bits).2+(BinaryCollector.fixed n).overhead : ℕ) : ℝ) ≤
      Real.exp (33217795 * CompanionSplitCost.scale n) := by
  simpa only [Nat.cast_ofNat,show (511043:ℝ)*65=33217795 by norm_num] using
    natural_cost hn (exhaustive_mark_gates (by omega : 2≤n) large composite sieved)

/-- Verification charges follow the guard that enables the rounded archimedean solve. -/
def verificationTrialWork (n ell u v w z : ℕ) : ℕ :=
  let s := TryPair.fixedInput n ell (Construction.construct n ell u v w z)
  match Marking.stageOne s with
  | none => 0
  | some rel => match Elimination.stageTwo rel with
    | none => 0
    | some lat =>
      if lat.free<rel.marks.length ∧ 2*s.degree-2≤lat.free then
        match markColumns s rel with
        | none => 0
        | some cols => minorVerificationWork s rel lat cols
      else 0

/-- Reconstruction and modular verification at every rounded minor, including
failed checks, summed across all tuples of every target. -/
theorem exhaustive_verification_gates {n : ℕ} (hn : 2≤n) (large : 10004≤Fixed.d (n.log2+1)) :
    boxWork n (verificationTrialWork n) ≤ 2^(100441012*TwoThirdsCost.scale (n.log2+1)) := by
  apply boxWork_le n 100020000
  intro ell target u hu v hv w hw z hz
  dsimp only [verificationTrialWork]
  split
  next => exact Nat.zero_le _
  next rel stage =>
    split
    next => exact Nat.zero_le _
    next lat solved =>
      split
      next guard =>
        split
        next => exact Nat.zero_le _
        next cols marked =>
          exact all_minor_verification_gates hn large target
            ⟨(mem_Icc.mp hu).2,(mem_Icc.mp hv).2,(mem_Icc.mp hw).2,(mem_Icc.mp hz).2⟩ stage solved marked guard.1
      next => exact Nat.zero_le _

/-- Charge the binary roots, the guarded mark logarithms, and each Helmert
coefficient, projection and rounding on every enabled candidate. -/
def archNumericsTrialWork (n g u v w z : ℕ) : ℕ :=
  let s := TryPair.fixedInput n g (Construction.construct n g u v w z)
  match Marking.stageOne s with
  | none => 0
  | some rel => match Elimination.stageTwo rel with
    | none => 0
    | some lat => if lat.free<rel.marks.length ∧ 2*s.degree-2≤lat.free then
        BinaryHelmert.columnsWork s rel + BinaryProjection.columnsWork s rel + BinaryRootColumns.work s rel else 0

theorem exhaustive_arch_numerics_gates {n : ℕ} (large : 2≤Fixed.d (n.log2+1)) :
    boxWork n (archNumericsTrialWork n)≤2^(441013*TwoThirdsCost.scale (n.log2+1)) := by
  apply boxWork_le n 20001
  intro g _ u _ v _ w _ z _
  dsimp only [archNumericsTrialWork]
  split
  next => exact Nat.zero_le _
  next rel stage =>
    split
    next => exact Nat.zero_le _
    next =>
      split
      next =>
        let S := TwoThirdsCost.scale (n.log2+1)
        have zs : Fixed.z (n.log2+1)≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos (Nat.succ_pos _))).trans
          ((Nat.le_mul_of_pos_left _ (Fixed.degree_pos (Nat.succ_pos _))).trans (Fixed.scale_bounds (Nat.succ_pos _)).1)
        have sp : 0<S := (Nat.succ_pos _).trans_le zs
        have h := (BinaryHelmert.fixed_columns_gates stage large).trans
          (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : 14000*S≤17000*S))
        have left := (Nat.add_le_add h (BinaryProjection.fixed_columns_gates stage large)).trans (calc
          _ = 2^(1+17000*S) := by rw [pow_add,pow_one,two_mul]
          _ ≤ 2^(20000*S) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
        exact (Nat.add_le_add left (BinaryRootColumns.fixed_work stage)).trans (calc
          _ = 2^(1+20000*S) := by rw [pow_add,pow_one,two_mul]
          _ ≤ 2^(20001*S) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
      next => exact Nat.zero_le _

/-- Pay for the two full local and target polynomials, both CRTs, nearest
rounding and both digit corrections, even when recomputed on every tuple. -/
def correctionTrialWork (n g _u _v _w _z : ℕ) : ℕ :=
  let b := n.log2+1
  (BinaryConstructorBase.run n.bits (Fixed.d b).bits (Fixed.A b).bits (Fixed.rootBase n).bits
    (primorial (Fixed.d b)).bits g.bits (Construction.leadingCoefficient n).bits
    (Construction.binaryMask (Fixed.d b)).bits).2

theorem exhaustive_correction_gates {n : ℕ} (hn : 2≤n) (big : 3≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none) :
    boxWork n (correctionTrialWork n)≤2^(1035056*TwoThirdsCost.scale (n.log2+1)) := by
  apply boxWork_le n 614044
  intro g target _ _ _ _ _ _ _ _
  exact (BinaryConstructorBase.fixed_base hn big comp target sieved).2

/-- Sum of the measured search stages used in the recursive factorization charge. -/
def measuredSearchWork (n : ℕ) : ℕ :=
  exhaustiveMarkWork n + (BinaryTargets.run (Fixed.beta (n.log2+1)).bits).2 +
    (BinaryCollector.fixed n).overhead + boxWork n (archNumericsTrialWork n) + boxWork n (correctionTrialWork n) +
      boxWork n (verificationTrialWork n)

theorem measured_search_L_two_thirds {n : ℕ} (hn : 64≤n) (large : 130000≤Fixed.d (n.log2+1))
    (composite : ¬n.Prime)
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none) :
    (measuredSearchWork n:ℝ) ≤ Real.exp (6528665845*CompanionSplitCost.scale n) := by
  let b := n.log2+1
  let s := TwoThirdsCost.scale b
  have hb : 0<b := Nat.succ_pos _
  have sp : 0<s := (Nat.mul_pos (Fixed.degree_pos hb) (Nat.mul_pos (Fixed.degree_pos hb) (Nat.succ_pos _))).trans_le
    (Fixed.scale_bounds hb).1
  have two : 2≤n := by omega
  have mark := exhaustive_mark_gates two large composite sieved
  have arch := (exhaustive_arch_numerics_gates (by omega : 2≤Fixed.d (n.log2+1))).trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : 441013*s≤511043*s))
  have setup := (Nat.add_le_add mark arch).trans (calc
    _ = 2^(1+511043*s) := by rw [pow_add,pow_one,two_mul]
    _ ≤ 2^(1035056*s) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have front := (Nat.add_le_add setup (exhaustive_correction_gates two (by omega) composite sieved)).trans (calc
    _ = 2^(1+1035056*s) := by rw [pow_add,pow_one,two_mul]
    _ ≤ 2^(100441012*s) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have both := Nat.add_le_add front (exhaustive_verification_gates two (by omega : 10004≤Fixed.d (n.log2+1)))
  have total : measuredSearchWork n≤2^(100441013*s) := both.trans (calc
    _ = 2^(1+100441012*s) := by rw [pow_add,pow_one,two_mul]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  simpa only [Nat.cast_ofNat,show (100441013:ℝ)*65=6528665845 by norm_num] using natural_cost hn total

end Cogentic.Concrete

#print axioms Cogentic.Concrete.exhaustive_mark_gates
