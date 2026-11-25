import Cogentic.CandidateRuntime

namespace Cogentic.BinaryResidues
open BinaryDivision BinaryPivot BinarySaturation CandidateRuntime

structure WordRow where
  second : Bool
  q : List Bool
  r : List Bool

def pack (row : Marking.Row) : WordRow := ⟨row.second,row.q.bits,row.r.bits⟩

def WordRow.decode (r : WordRow) : Marking.Row := ⟨r.second,value r.q,value r.r⟩

@[simp] private theorem decode_pack (r : Marking.Row) : (pack r).decode=r := by
  cases r; simp [pack,WordRow.decode]

private def pair (q r : ℕ) := [Marking.Row.mk false q r,Marking.Row.mk true q r]

/-- Emit the two signed-field rows at each residue. The output tail is shared
across primes, so concatenation needs no second traversal of the residue list. -/
def rangeInto (q : List Bool) (acc : List WordRow) :
    List Unit → List Bool → List WordRow × ℕ
  | [], _ => (acc,1)
  | _::rest,a =>
    let inc := addDigits a.length a [] true
    let next := canonical inc.1
    let tail := rangeInto q acc rest next.1
    (⟨false,q,a⟩::⟨true,q,a⟩::tail.1,inc.2+next.2+tail.2+2*(q.length+a.length)+4)

private theorem range_spec (q : ℕ) (acc : List WordRow) (ts : List Unit) (a B : ℕ)
    (qB : q≤B) (space : a+ts.length≤B) :
    (rangeInto q.bits acc ts a.bits).1=((List.range' a ts.length).flatMap (pair q)).map pack ++ acc ∧
    (rangeInto q.bits acc ts a.bits).2 ≤ 1+ts.length*(12*B+7) := by
  induction ts generalizing a with
  | nil => simp [rangeInto]
  | cons t ts ih =>
    let inc := addDigits a.bits.length a.bits [] true
    let next := canonical inc.1
    obtain ⟨il,ic,iv⟩ := addDigits_spec a.bits.length a.bits [] true le_rfl (by simp)
    change inc.1.length=_ at il
    change inc.2=_ at ic
    change value inc.1=_ at iv
    simp only [value_bits,value,Bool.toNat_true,Nat.add_zero] at iv
    obtain ⟨nv,nc⟩ := canonical_spec inc.1
    change next.1=_ at nv
    change next.2=_ at nc
    rw [iv] at nv
    rw [il] at nc
    simp only [Nat.size_eq_bits_len] at ic nc
    simp only [List.length_cons] at space ⊢
    obtain ⟨v,c⟩ := ih (a+1) (by omega)
    have qb := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=q))).trans qB
    have ab := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=a))).trans (by omega : a≤B)
    change _::_::(rangeInto q.bits acc ts next.1).1 = _ ∧
      inc.2+next.2+(rangeInto q.bits acc ts next.1).2+2*(q.bits.length+a.bits.length)+4≤_
    rw [nv,v,List.range'_succ]
    refine ⟨by simp [pair,pack],?_⟩
    simp only [Nat.size_eq_bits_len,Nat.succ_mul ts.length]; omega

/-- The only numeric inputs are the canonical words of the factor base.
The scan creates its unary fuel and the canonical residue words on demand. -/
def enumerate : List (List Bool) → List WordRow × ℕ
  | [] => ([],1)
  | q::qs =>
    let tail := enumerate qs
    let fuel := tokens q
    let out := rangeInto q tail.1 fuel.1 []
    (out.1,tail.2+fuel.2+out.2+1)

def allRows (qs : List ℕ) := qs.flatMap fun q => (List.range q).flatMap (pair q)

def enumerationBudget (B k : ℕ) := 1+k*(3*B+B*(12*B+7)+2)

/-- The cost includes both row records, copying the canonical coordinates, and
the counter and loop-fuel operations, even on a prime with no polynomial roots. -/
theorem enumerate_spec (qs : List ℕ) (B : ℕ) (small : ∀ q∈qs,q≤B) :
    (enumerate (qs.map Nat.bits)).1=(allRows qs).map pack ∧
    (enumerate (qs.map Nat.bits)).2≤enumerationBudget B qs.length := by
  induction qs with
  | nil => simp [enumerate,allRows,enumerationBudget]
  | cons q qs ih =>
    obtain ⟨tv,tc⟩ := ih (fun p hp=>small p (by simp [hp]))
    have qb := small q (by simp)
    let tail := enumerate (qs.map Nat.bits)
    let fuel := tokens q.bits
    have ⟨len,c⟩ := token_spec q.bits
    change fuel.1.length=_ at len
    change fuel.2≤_ at c
    rw [value_bits] at len c
    rw [Nat.size_eq_bits_len] at c
    have size := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=q))).trans qb
    have ⟨v,w⟩ := range_spec q tail.1 fuel.1 0 B qb (by omega)
    rw [len] at v w
    change tail.1=_ at tv
    change tail.2≤_ at tc
    change (rangeInto q.bits tail.1 fuel.1 []).1=_ ∧ tail.2+fuel.2+(rangeInto q.bits tail.1 fuel.1 []).2+1≤_
    refine ⟨?_,?_⟩
    · rw [show ([] : List Bool)=(0:ℕ).bits from rfl,v,tv]
      simp only [allRows,List.flatMap_cons,List.map_append,List.range_eq_range']
    · change (rangeInto q.bits tail.1 fuel.1 []).2≤_ at w
      have bound := Nat.mul_le_mul_right (12*B+7) qb
      unfold enumerationBudget at tc ⊢
      rw [List.length_cons,Nat.succ_mul qs.length]; omega

/-- Feed the ordered binary rows to the classifier used by stage one. -/
def classifyRows (s : Marking.Input) (encoded : List WordRow) : ClassifiedRows :=
  let first := s.first.map encode
  let second := s.second.map encode
  partitionRows (fun r => if r.second then classify second first r else classify first second r)
    (encoded.map WordRow.decode)

theorem fixed_residue_enumeration (n g : ℕ) (pairData : TryPair.PairData) :
    let b := n.log2+1
    let s := TryPair.fixedInput n g pairData
    let out := enumerate (s.base.map Nat.bits)
    out.1 = (allRows s.base).map pack ∧ classifyRows s out.1 = prepareRows s ∧
    out.2≤2^(3010*TwoThirdsCost.scale b) := by
  intro b s out
  have ⟨v,c⟩ := enumerate_spec s.base s.B (fun p hp=>(Marking.mem_base.mp hp).2.2.1)
  change out.1=_ at v
  change out.2≤_ at c
  refine ⟨v,?_,c.trans ?_⟩
  · rw [v]
    simp only [classifyRows,List.map_map,Function.comp_def,decode_pack]
    rw [show (fun x : Marking.Row=>x)=id from rfl,List.map_id]
    rfl
  · have sub : s.base.toFinset ⊆ Finset.range (s.B+1) := by
      intro q h; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Marking.mem_base.mp (List.mem_toFinset.mp h)).2.2.1)
    have nd : s.base.Nodup := List.nodup_dedup _
    have len := Finset.card_le_card sub
    rw [List.toFinset_card_of_nodup nd,Finset.card_range] at len
    let t := TwoThirdsCost.scale b
    let X := 2^(1000*t)
    have d := Fixed.degree_pos (Nat.succ_pos n.log2)
    have ht : Fixed.h b≤t := (Nat.le_mul_of_pos_left _ d).trans (Fixed.scale_bounds (Nat.succ_pos n.log2)).1
    have pos : 0<t := (Nat.mul_pos d (Nat.succ_pos _)).trans_le ht
    have xb : s.B≤X := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 1000 ht)
    have xp : 0<X := Nat.two_pow_pos _
    calc enumerationBudget s.B s.base.length ≤ enumerationBudget X (X+1) := by
           unfold enumerationBudget
           gcongr; omega
         _ ≤ 256*X^3 := by
           unfold enumerationBudget
           have x0 := Nat.one_le_pow 3 X xp
           have x1 := Nat.le_self_pow (by decide : 3≠0) X
           have x2 := Nat.pow_le_pow_right xp (by decide : 2≤3)
           nlinarith only [x0,x1,x2]
         _ ≤ 2^(3010*t) := by
           change 2^8*(2^(1000*t))^3≤_
           rw [←pow_mul,←pow_add]
           exact Nat.pow_le_pow_right (by decide) (by omega)

end Cogentic.BinaryResidues

#print axioms Cogentic.BinaryResidues.enumerate_spec
#print axioms Cogentic.BinaryResidues.fixed_residue_enumeration
