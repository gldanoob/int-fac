import Cogentic.SolverBoxCost
import Cogentic.PrecisionWordCost
import Cogentic.RelationAssemblyCost

namespace Cogentic.Concrete
open TwoThirdsSearch Finset

/-- Form the precision words and materialize the input to the relation solver. -/
def relationSetupWork (n g u v w z : ℕ) : ℕ :=
  let b := n.log2+1
  let s := TryPair.fixedInput n g (Construction.construct n g u v w z)
  match Marking.stageOne s with
  | none => 0
  | some rel => (BinaryPrecision.run b.bits (Fixed.d b).bits rel.rows).2 + (BinaryRelations.assemble rel).2

def additionalSearchWork (n : ℕ) : ℕ :=
  boxWork n (SolverStage.trialWork n) + boxWork n (fun g u v w z => relationSetupWork n g u v w z+8)

theorem additional_search_bound {n : ℕ} (hn : 2≤n) (d : 10004≤Fixed.d (n.log2+1)) :
    additionalSearchWork n ≤ 2^(10441015*TwoThirdsCost.scale (n.log2+1)) := by
  let b := n.log2+1
  let S := TwoThirdsCost.scale b
  have dp := Fixed.degree_pos (Nat.succ_pos n.log2)
  have sp : 0<S := (Nat.mul_pos dp (Nat.mul_pos dp (Nat.succ_pos _))).trans_le (Fixed.scale_bounds (Nat.succ_pos _)).1
  have localCost (g u v w z) : relationSetupWork n g u v w z≤2^(200001*S) := by
    dsimp only [relationSetupWork]; split
    next => exact Nat.zero_le _
    next rel h =>
      have prec := (BinaryPrecision.fixed_words h).2.trans
        (Nat.pow_le_pow_right Nat.zero_lt_two (by change 2040*S≤200000*S; omega))
      exact (Nat.add_le_add prec (BinaryRelations.assembled_rows h).2).trans (calc
        _ = 2^(1+200000*S) := by rw [pow_add,pow_one,two_mul]
        _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have control := boxWork_le n 200002 (fun g u v w z => relationSetupWork n g u v w z+8)
  have cap : 8≤2^(200001*S) := (show 8=2^3 by decide).le.trans (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have aux := control (fun g _ u _ v _ w _ z _ => (Nat.add_le_add (localCost g u v w z) cap).trans (calc
    _ = 2^(1+200001*S) := by rw [pow_add,pow_one,two_mul]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by change 1+200001*S≤200002*S; omega)))
  have costs := Nat.add_le_add (SolverStage.exhaustive_solver_gates hn d)
    (aux.trans (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_right S (by decide : 421012+200002≤10441014))))
  exact costs.trans (calc
    _ = 2^(1+10441014*S) := by rw [pow_add,pow_one,two_mul]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by change 1+10441014*S ≤ 10441015*S; omega))

private def trial (n : ℕ) := markTrialWork n + archNumericsTrialWork n + correctionTrialWork n +
  observationTrialWork n + verificationTrialWork n + SolverStage.trialWork n + relationSetupWork n

/-- The counter stops on the same candidate and target as the fixed collector. -/
def searchTrace (n : ℕ) (hn : 2≤n) :=
  let b := n.log2+1
  let fast := 2*b^2*Fixed.U b
  collect hn (meteredBox n (fast*Fixed.A b) fast (candidate n) (trial n)) (dyadicTargets (Fixed.beta b)).sort

def traceSearchWork (n : ℕ) (hn : 2≤n) :=
  (searchTrace n hn).2+(BinaryTargets.run (Fixed.beta (n.log2+1)).bits).2+(BinaryCollector.fixed n).overhead

private theorem box_add (n : ℕ) (f g : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) :
    boxWork n (f+g)=boxWork n f+boxWork n g := by
  simp only [boxWork,Pi.add_apply,sum_add_distrib]

theorem search_trace_spec (n : ℕ) (hn : 2≤n) :
    (searchTrace n hn).1=(fixedCollection n hn).1 ∧
      traceSearchWork n hn ≤ measuredSearchWork n+additionalSearchWork n := by
  have result := fixed_metered_boxWork n hn (trial n)
  refine ⟨result.1,?_⟩
  let ticks : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ := fun _ _ _ _ _ => 8
  have visit : (searchTrace n hn).2 ≤ boxWork n (trial n+ticks) := result.2
  have plus : (fun g u v w z => relationSetupWork n g u v w z+8) = relationSetupWork n+ticks := rfl
  simp only [trial,box_add] at visit
  unfold traceSearchWork measuredSearchWork exhaustiveMarkWork additionalSearchWork
  rw [plus,box_add]
  omega

end Cogentic.Concrete

#print axioms Cogentic.Concrete.search_trace_spec
