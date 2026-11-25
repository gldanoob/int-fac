import Cogentic.CandidateRuntime
import Cogentic.CandidateSieveCost
import Cogentic.ConstructionCofactors
import Cogentic.ConstructionHeight

namespace Cogentic.BinaryFactorBase
open BinaryDivision BinaryPivot BinarySaturation BinaryPresieve CandidateRuntime

/-- The two non-primality conditions in the constructor's factor-base filter. -/
def admissible (B k q : List Bool) : Bool × ℕ :=
  let sq := multiply q q
  let small := leq sq.1 B
  let divides := residueEq k q []
  (!small.1 && !divides.1,sq.2+small.2+divides.2+3)

private theorem admissible_spec (B k q : List Bool) {w : ℕ} (qp : 0<value q)
    (bw : B.length≤w) (kw : k.length≤w) (qw : q.length≤w) :
    ((admissible B k q).1=true ↔ value B<(value q)^2 ∧ ¬value q∣value k) ∧
      (admissible B k q).2≤36*w^2+50*w+8 := by
  let sq := multiply q q
  let small := leq sq.1 B
  let divides := residueEq k q []
  have ⟨sv,sl,sc⟩ := multiply_spec q q
  change value sq.1=_ at sv; change sq.1.length≤_ at sl; change sq.2≤_ at sc
  obtain ⟨bv,bc⟩ := leq_spec sq.1 B
  obtain ⟨dv,dc⟩ := residue_spec k q [] qp w kw qw (by simp)
  change (small.1=true ↔ _) at bv; change small.2=_ at bc
  change (divides.1=true ↔ value k%value q=0) at dv; change divides.2≤_ at dc
  rw [sv,←pow_two] at bv
  have smallFalse : small.1=false ↔ value B<(value q)^2 := by
    cases h : small.1 <;> simp [h] at bv ⊢ <;> omega
  have no : divides.1=false ↔ ¬value q∣value k := by
    rw [Nat.dvd_iff_mod_eq_zero]
    cases h : divides.1 <;> simp [h] at dv ⊢ <;> exact dv
  change ((!small.1 && !divides.1)=true ↔ _) ∧ sq.2+small.2+divides.2+3≤_
  refine ⟨by simp only [Bool.and_eq_true,Bool.not_eq_true',smallFalse,no],?_⟩
  have sqCost : sq.2≤16*w^2 := sc.trans (calc
    _ ≤ w*(w+5*(w+2*w)) := by gcongr
    _ = _ := by ring)
  have length : max sq.1.length B.length≤3*w := max_le (by omega) (by omega)
  nlinarith only [sqCost,bc,dc,length]

/-- A binary cursor visits each integer from two through B in increasing order.
The same trial fuel supplies all primality checks in the range. -/
def visit (B k : List Bool) (trial : List Unit) : List Unit → List Bool → List (List Bool) × ℕ
  | [], _ => ([],0)
  | _::ts,prev =>
    let q := addDigits prev.length prev [] true
    let prime := trialPrime q.1 trial
    let keep := admissible B k q.1
    let tail := visit B k trial ts q.1
    let out := canonical q.1
    (if prime.1 && keep.1 then out.1::tail.1 else tail.1,q.2+prime.2+keep.2+out.2+tail.2+3)

private theorem visit_spec (B k : List Bool) (trial ts : List Unit) (prev : List Bool) (w : ℕ)
    (start : 0<value prev) (enough : value prev+ts.length≤trial.length+1)
    (trialWidth : 2+trial.length≤w) (width : prev.length+ts.length≤w)
    (bw : B.length≤w) (kw : k.length≤w) :
    (visit B k trial ts prev).1=((List.range' (value prev+1) ts.length).filter
      (fun q => decide (q.Prime ∧ value B<q^2 ∧ ¬q∣value k))).map Nat.bits ∧
    (visit B k trial ts prev).2≤ts.length*(trial.length*visitBudget w+36*w^2+58*w+12) := by
  induction ts generalizing prev with
  | nil => simp [visit]
  | cons tok ts ih =>
    let q := addDigits prev.length prev [] true
    obtain ⟨ql,qc,qv⟩ := addDigits_spec prev.length prev [] true le_rfl (by simp)
    change q.1.length=_ at ql; change q.2=_ at qc; change value q.1=value prev+0+1 at qv
    rw [Nat.add_zero] at qv
    simp only [List.length_cons] at enough width
    obtain ⟨prime,cost⟩ := trialPrime_spec q.1 trial (by omega) (by omega) w (by omega) trialWidth
    obtain ⟨keep,paid⟩ := admissible_spec B k q.1 (by omega) bw kw (by omega)
    obtain ⟨tail,work⟩ := ih q.1 (by omega) (by omega) (by omega)
    have ok : ((trialPrime q.1 trial).1 && (admissible B k q.1).1)=
        decide ((value prev+1).Prime ∧ value B<(value prev+1)^2 ∧ ¬(value prev+1)∣value k) := by
      apply Bool.eq_iff_iff.mpr
      rw [Bool.and_eq_true,prime,decide_eq_true_eq,keep,qv,decide_eq_true_eq]
    have ⟨out,normalized⟩ := canonical_spec q.1
    change (if _ then (canonical q.1).1::(visit B k trial ts q.1).1 else (visit B k trial ts q.1).1)=_ ∧
      q.2+(trialPrime q.1 trial).2+(admissible B k q.1).2+(canonical q.1).2+(visit B k trial ts q.1).2+3≤_
    constructor
    · rw [ok,List.length_cons,List.range'_succ,List.filter_cons]
      rw [qv] at tail
      by_cases h : (value prev+1).Prime ∧ value B<(value prev+1)^2 ∧ ¬(value prev+1)∣value k
      · simp only [decide_eq_true h,↓reduceIte,List.map_cons,out,qv,tail]
      · simp only [decide_eq_false h,Bool.false_eq_true,↓reduceIte,tail]
    · rw [List.length_cons,Nat.succ_mul]; omega

/-- Binary bounds and cofactor product are supplied directly. Tokenizing B
also supplies the outer loop length B-1, including the B=0 and B=1 cases. -/
def run (B k : List Bool) : List (List Bool) × ℕ :=
  let tokensB := tokens B
  let base := visit B k tokensB.1 tokensB.1.tail [true]
  (base.1,tokensB.2+base.2+2)

theorem run_spec (B k : List Bool) :
    let w := value B+B.length+k.length+3
    (run B k).1=((List.range' 2 (value B-1)).filter
      (fun q => decide (q.Prime ∧ value B<q^2 ∧ ¬q∣value k))).map Nat.bits ∧
    (run B k).2≤100000*w^5 := by
  intro w
  let t := tokens B
  obtain ⟨len,paid⟩ := token_spec B
  change t.1.length=_ at len; change t.2≤_ at paid
  have tail : t.1.tail.length=value B-1 := by simp [len]
  have b1 : value [true]=1 := by decide
  obtain ⟨base,cost⟩ := visit_spec B k t.1 t.1.tail [true] w (by decide) (by rw [b1,len,tail]; omega)
    (by dsimp [w]; omega) (by simp only [List.length_cons,List.length_nil]; dsimp [w]; omega)
    (by dsimp [w]; omega) (by dsimp [w]; omega)
  rw [b1,tail] at base
  rw [tail,len] at cost
  refine ⟨base,?_⟩
  change t.2+(visit B k t.1 t.1.tail [true]).2+2≤_
  have be : value B≤w := by dsimp [w]; omega
  have bw : B.length≤w := by dsimp [w]; omega
  have wp : 1≤w := by dsimp [w]; omega
  calc _ ≤ 3*w+w*(w*visitBudget w+36*w^2+58*w+12)+2 := by
             have l := Nat.mul_le_mul (show value B-1≤w by omega)
               (show value B*visitBudget w+36*w^2+58*w+12≤w*visitBudget w+36*w^2+58*w+12 by gcongr)
             omega
       _ ≤ _ := by
         unfold visitBudget probeBudget BinaryModularPower.gcdBudget
         let W := w^5
         have h1 : w≤W := Nat.le_self_pow (by decide) w
         have h2 : w^2≤W := Nat.pow_le_pow_right wp (by decide)
         have h3 : w^3≤W := Nat.pow_le_pow_right wp (by decide)
         have h4 : w^4≤W := Nat.pow_le_pow_right wp (by decide)
         dsimp [W] at *
         ring_nf; omega


/-- The constructor uses the same cofactor product for every perturbation.
The emitted list agrees in order and with every exclusion. -/
theorem constructed_base (n ell u₀ u₁ v₀ v₁ : ℕ) :
    let B := Fixed.B (n.log2+1)
    let k := Construction.markModulus n ell
    (run B.bits k.bits).1=(Construction.construct n ell u₀ u₁ v₀ v₁).factorBase.map Nat.bits ∧
    (run B.bits k.bits).2≤100000*(B+B.size+k.size+3)^5 := by
  intro B k
  have ⟨eq,cost⟩ := run_spec B.bits k.bits
  simp only [value_bits,Nat.size_eq_bits_len] at eq cost
  refine ⟨eq.trans ?_,cost⟩
  simp only [Construction.construct,k,Construction.markModulus,Construction.perturb_at_base,B]

/-- On a surviving candidate the two exact cofactors bound the bit length
of their product. This places the entire factor-base enumeration and filter
on the fixed two-thirds schedule, given the binary B and cofactor product. -/
theorem fixed_factorBase {n ell : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (survived : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1))
      (Fixed.rootBase n)=Option.none) (u₀ u₁ v₀ v₁ : ℕ) :
    let b := n.log2+1
    let B := Fixed.B b
    let k := Construction.markModulus n ell
    (run B.bits k.bits).1=(Construction.construct n ell u₀ u₁ v₀ v₁).factorBase.map Nat.bits ∧
    k.size≤2+222240*Fixed.v b ∧ (run B.bits k.bits).2≤2^(5100*TwoThirdsCost.scale b) := by
  intro b B k
  have hb : 0<b := Nat.succ_pos _
  let s := TwoThirdsCost.scale b
  have vs : Fixed.v b≤ s := (Fixed.scale_bounds hb).1
  have dp := Fixed.degree_pos hb
  have hs : Fixed.h b≤ s := (Nat.le_mul_of_pos_left _ dp).trans vs
  have sp : 0< s := (Nat.mul_pos dp (Nat.succ_pos _)).trans_le hs
  have ks := (Construction.markModulus_spec hn big composite target survived).2.1
  have kW : k.size≤2+222240*Fixed.v b := by
    apply Nat.size_le.mpr
    refine ks.trans_le ((Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 (Construction.leading_size hn)) 2).trans_eq ?_)
    change (2*2^(111120*Fixed.v b))^2=2^(2+222240*Fixed.v b)
    calc _=(2^(1+111120*Fixed.v b))^2 := by rw [pow_add,pow_one]
         _=_ := by rw [←pow_mul]; congr 1; ring
  obtain ⟨eq,work⟩ := constructed_base n ell u₀ u₁ v₀ v₁
  refine ⟨eq,kW,work.trans ?_⟩
  let X := 2^(1000*s)
  have BW : B≤X := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 1000 hs)
  have Bs : B.size≤X := (Nat.size_le.mpr Nat.lt_two_pow_self).trans BW
  have kw : k.size≤X := calc
    _ ≤ 2^18*s := by norm_num; omega
    _ ≤ 2^18*2^s := Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
    _ = 2^(18+s) := (pow_add 2 18 s).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have xp : 1≤X := Nat.one_le_two_pow
  have ww : B+B.size+k.size+3≤8*X := by omega
  calc 100000*(B+B.size+k.size+3)^5 ≤ 2^17*(8*X)^5 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left ww 5)
       _ = 2^(17+(3+1000*s)*5) := by
         change 2^17*(2^3*2^(1000*s))^5=_
         rw [←pow_add,←pow_mul,←pow_add]
       _ ≤ _ := Nat.pow_le_pow_right (by decide) (show 17+(3+1000*s)*5≤5100*s by omega)

end Cogentic.BinaryFactorBase

#print axioms Cogentic.BinaryFactorBase.run_spec
#print axioms Cogentic.BinaryFactorBase.fixed_factorBase
