import Cogentic.BinaryIrreducible
import Cogentic.SaturationCost

namespace Cogentic.BinaryMaskCost
open BinaryDivision Construction

private theorem tail_value (x : List Bool) : value x/2=value x.tail := by
  rw [value_head x]; cases x.headD false <;> simp; omega

private theorem head_digit (x : List Bool) : x.headD false=(value x).testBit 0 := by
  rw [Nat.testBit_zero,value_head x]
  cases x.headD false <;> simp

/-- Read a coefficient from a little-endian word, charging the traversal. -/
def digit (x : List Bool) : ℕ → Bool × ℕ
  | 0 => (x.headD false,1)
  | i+1 => let p := digit x.tail i; (p.1,p.2+1)

theorem digit_spec (x : List Bool) (i : ℕ) :
    (digit x i).1=(value x).testBit i ∧ (digit x i).2=i+1 := by
  induction i generalizing x with
  | zero => exact ⟨head_digit _,rfl⟩
  | succ i ih => simpa [digit,Nat.testBit_succ,tail_value] using ih x.tail

def coefficient (a b i : ℕ) :=
  (Finset.range (i+1)).sum (fun j => bitCoeff a j*bitCoeff b (i-j))

/-- Ascend the first operand while descending the second. Each cross term
is an AND and the running parity is an XOR. -/
def parity (a b : List Bool) : ℕ → Bool × ℕ
  | 0 => (a.headD false && b.headD false,3)
  | i+1 =>
    let y := digit b (i+1)
    let rest := parity a.tail b i
    (xor (a.headD false && y.1) rest.1,y.2+rest.2+4)

private theorem parity_step (a b c : Bool) :
    (xor (a && b) c).toNat=(a.toNat*b.toNat+c.toNat)%2 := by
  cases a <;> cases b <;> cases c <;> decide

theorem parity_spec (a b : List Bool) (i : ℕ) :
    (parity a b i).1.toNat=coefficient (value a) (value b) i%2 ∧
    (parity a b i).2 ≤ 5*(i+1)^2 := by
  induction i generalizing a with
  | zero =>
    simp only [parity,coefficient,Nat.zero_add,Finset.range_one,Finset.sum_singleton,Nat.sub_zero,
      bitCoeff,←head_digit]
    cases a.headD false <;> cases b.headD false <;> decide
  | succ i ih =>
    have ⟨p,work⟩ := ih a.tail
    have ⟨d,c⟩ := digit_spec b (i+1)
    have eq : coefficient (value a) (value b) (i+1)=
        (a.headD false).toNat*bitCoeff (value b) (i+1)+coefficient (value a.tail) (value b) i := by
      unfold coefficient
      rw [Finset.sum_range_succ']
      simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero,bitCoeff,Nat.testBit_succ,tail_value,←head_digit]
      exact Nat.add_comm ..
    refine ⟨?_,?_⟩
    · rw [parity,parity_step,d,p,eq,Nat.add_mod_mod]
      rfl
    · change (digit b (i+1)).2+(parity a.tail b i).2+4 ≤ _
      nlinarith only [c,work]

def bitMatches (m a b i : ℕ) := coefficient a b i%2 == bitCoeff m i

/-- Compare all low coefficients of the product with the proposed mask. -/
def product (m a b : List Bool) : ℕ → Bool × ℕ
  | 0 => (true,0)
  | i+1 =>
    let rest := product m a b i
    let p := parity a b i
    let target := digit m i
    (rest.1 && (p.1 == target.1),rest.2+p.2+target.2+3)

theorem product_spec (m a b : List Bool) (d : ℕ) :
    (product m a b d).1=(List.range d).all (bitMatches (value m) (value a) (value b)) ∧
      (product m a b d).2 ≤ 10*(d+1)^3 := by
  induction d with
  | zero => exact ⟨rfl,by simp [product]⟩
  | succ d ih =>
    obtain ⟨prev,work⟩ := ih
    have ⟨p,pc⟩ := parity_spec a b d
    have ⟨target,tc⟩ := digit_spec m d
    have eq : ((parity a b d).1 == (digit m d).1)=bitMatches (value m) (value a) (value b) d := by
      unfold bitMatches bitCoeff
      rw [←target,←p]
      cases (parity a b d).1 <;> cases (digit m d).1 <;> decide
    refine ⟨?_,?_⟩
    · simp [product,List.range_succ,prev,eq]
    · change (product m a b d).2+(parity a b d).2+(digit m d).2+3 ≤ _
      nlinarith only [work,pc,tc,Nat.zero_le (d^2)]

private theorem append_one_value (xs : List Bool) (b : Bool) :
    value (xs++[b])=2^xs.length*b.toNat+value xs := by
  induction xs with
  | nil => simp [value]
  | cons v xs ih => simp [value,ih,pow_succ]; ring

/-- Enumerate all fixed-width words in increasing numerical order. Appending
a high digit visits every cell of the old word and is included in the meter. -/
def words : ℕ → List (List Bool) × ℕ
  | 0 => ([[]],1)
  | d+1 =>
    let prev := words d
    ((prev.1.map (·++[false]))++(prev.1.map (·++[true])),prev.2+prev.1.length*(2*d+6)+1)

private theorem words_spec (d : ℕ) :
    (words d).1.map value=List.range (2^d) ∧
    (∀ x∈(words d).1, x.length=d) ∧ (words d).2 ≤ 2^d*(8*(d+1)^2) := by
  induction d with
  | zero => exact ⟨rfl,by simp [words],by decide⟩
  | succ d ih =>
    obtain ⟨values,width,paid⟩ := ih
    have n : (words d).1.length=2^d := by simpa using congrArg List.length values
    have low : ((words d).1.map (·++[false])).map value=(words d).1.map value := by
      rw [List.map_map]
      apply List.map_congr_left
      intro x _; simp [Function.comp_apply,append_one_value]
    have high : ((words d).1.map (·++[true])).map value=((words d).1.map value).map (2^d+·) := by
      rw [List.map_map,List.map_map]
      apply List.map_congr_left
      intro x hx; simp [Function.comp_apply,append_one_value,width x hx]
    refine ⟨?_,?_,?_⟩
    · simp only [words,List.map_append,low,high,values,←List.range_add,pow_succ,Nat.mul_two]
    · intro x hx
      simp only [words,List.mem_append,List.mem_map] at hx
      rcases hx with ⟨y,hy,rfl⟩ | ⟨y,hy,rfl⟩ <;> simp [width y hy]
    · change (words d).2+(words d).1.length*(2*d+6)+1 ≤ _
      rw [n,pow_succ]
      have ep := Nat.one_le_two_pow (n:=d)
      nlinarith only [paid,ep,Nat.zero_le (2^d*d^2),Nat.zero_le (2^d*d)]

private def first (f : List Bool → Bool × ℕ) : List (List Bool) → Option (List Bool) × ℕ
  | [] => (none,0)
  | x::xs => let t := f x
             if t.1 then (some x,t.2+1) else
               let rest := first f xs
               (rest.1,t.2+1+rest.2)

def search (d : ℕ) (test : List Bool → Bool × ℕ) : Option (List Bool) × ℕ :=
  let ws := words d
  let found := first test ws.1
  (found.1,ws.2+found.2)

def searchBudget (d T : ℕ) := 2^d*(8*(d+1)^2+T+2)

private theorem search_spec (d T : ℕ) (f : List Bool → Bool × ℕ) (pred : ℕ → Bool)
    (test : ∀ x, x.length=d → (f x).1=pred (value x) ∧ (f x).2 ≤ T) :
    (search d f).1.map value=(List.range (2^d)).find? pred ∧ (search d f).2 ≤ searchBudget d T := by
  have ⟨values,width,paid⟩ := words_spec d
  have aux (xs : List (List Bool)) (all : ∀ x∈xs, x.length=d) :
      (first f xs).1.map value=(xs.map value).find? pred ∧ (first f xs).2 ≤ xs.length*(T+1) := by
    induction xs with
    | nil => exact ⟨rfl,by simp [first]⟩
    | cons x xs ih =>
      have ⟨eq,cost⟩ := test x (all x (by simp))
      have ⟨res,tail⟩ := ih (fun y hy => all y (by simp [hy]))
      cases h : (f x).1 with
      | false =>
        simp only [first,h,Bool.false_eq_true,↓reduceIte,List.map_cons,List.find?_cons,←eq,res]
        refine ⟨trivial,?_⟩; rw [List.length_cons,Nat.succ_mul]; omega
      | true =>
        simp only [first,h,↓reduceIte,List.map_cons,List.find?_cons,←eq,Option.map_some]
        refine ⟨trivial,?_⟩; rw [List.length_cons,Nat.succ_mul]; omega
  obtain ⟨eq,cost⟩ := aux _ width
  rw [values] at eq
  have L : (words d).1.length=2^d := by simpa using congrArg List.length values
  rw [L] at cost
  refine ⟨eq,?_⟩
  change (words d).2+(first f (words d).1).2 ≤ _
  unfold searchBudget
  nlinarith only [paid,cost]

private def anyWord (d : ℕ) (test : List Bool → Bool × ℕ) : Bool × ℕ :=
  let s := search d test
  (s.1.isSome,s.2+1)

private theorem anyWord_spec (d T : ℕ) (f : List Bool → Bool × ℕ) (pred : ℕ → Bool)
    (test : ∀ x, x.length=d → (f x).1=pred (value x) ∧ (f x).2 ≤ T) :
    (anyWord d f).1=(List.range (2^d)).any pred ∧ (anyWord d f).2 ≤ searchBudget d T+1 := by
  have ⟨eq,cost⟩ := search_spec d T f pred test
  have b := congrArg Option.isSome eq
  simp only [Option.isSome_map,List.isSome_find?] at b
  exact ⟨b,Nat.add_le_add_right cost 1⟩

private theorem search_mono {d D p P : ℕ} (degree : d ≤ D) (work : p ≤ P) :
    searchBudget d p ≤ searchBudget D P := by unfold searchBudget; gcongr; decide

private def monicPair (d : ℕ) (m a b : List Bool) : Bool × ℕ :=
  let out := product m (a++[true]) (b++[true]) d
  (out.1,out.2+a.length+b.length+2)

def factorTest (d k m a b : ℕ) :=
  (List.range d).all (bitMatches m (2^k+a) (2^(d-k)+b))

def degreeTest (d k m : ℕ) :=
  (List.range (2^k)).any (fun a => (List.range (2^(d-k))).any (factorTest d k m a))

def pairWork (d : ℕ) := searchBudget d (searchBudget d (12*(d+1)^3)+1)+1

/-- Both monic factors are represented by appending the leading one to
their independently enumerated lower-coefficient words. -/
def byDegree (d k : ℕ) (m : List Bool) : Bool × ℕ :=
  let otherDegree := d-k
  anyWord k (fun a => anyWord otherDegree (monicPair d m a))

theorem byDegree_spec (d k : ℕ) (m : List Bool) (within : k ≤ d) :
    (byDegree d k m).1=degreeTest d k (value m) ∧ (byDegree d k m).2 ≤ pairWork d := by
  have step (a : List Bool) (aw : a.length=k) (b : List Bool) (bw : b.length=d-k) :
      (monicPair d m a b).1=factorTest d k (value m) (value a) (value b) ∧
      (monicPair d m a b).2 ≤ 12*(d+1)^3 := by
    obtain ⟨eq,cost⟩ := product_spec m (a++[true]) (b++[true]) d
    refine ⟨by simpa only [monicPair,factorTest,append_one_value,aw,bw,Bool.toNat_true,Nat.mul_one] using eq,?_⟩
    change (product m (a++[true]) (b++[true]) d).2+a.length+b.length+2 ≤ _
    have widths : a.length+b.length=d := by omega
    nlinarith only [cost,widths,Nat.zero_le (d^2),Nat.zero_le (d^3)]
  have inner (a : List Bool) (aw : a.length=k) :
      (anyWord (d-k) (monicPair d m a)).1=(List.range (2^(d-k))).any (factorTest d k (value m) (value a)) ∧
      (anyWord (d-k) (monicPair d m a)).2 ≤ searchBudget d (12*(d+1)^3)+1 := by
    have ⟨eq,cost⟩ := anyWord_spec (d-k) (12*(d+1)^3) _ _ (step a aw)
    exact ⟨eq,cost.trans (Nat.add_le_add_right (search_mono (Nat.sub_le ..) le_rfl) 1)⟩
  have ⟨eq,cost⟩ := anyWord_spec k (searchBudget d (12*(d+1)^3)+1)
    (fun a => anyWord (d-k) (monicPair d m a))
    (fun a => (List.range (2^(d-k))).any (factorTest d k (value m) a)) inner
  exact ⟨eq,cost.trans (Nat.add_le_add_right (search_mono within le_rfl) 1)⟩

private def splits (d : ℕ) (m : List Bool) : ℕ → ℕ → Bool × ℕ
  | _,0 => (false,0)
  | k,t+1 =>
    let h := byDegree d k m
    if h.1 then (true,h.2+d+2) else
      let rest := splits d m (k+1) t
      (rest.1,h.2+d+2+rest.2)

private theorem splits_spec (d k t : ℕ) (m : List Bool) (fit : k+t ≤ d+1) :
    (splits d m k t).1=(List.range' k t).any (fun j => degreeTest d j (value m)) ∧
      (splits d m k t).2 ≤ t*(pairWork d+d+2) := by
  induction t generalizing k with
  | zero => exact ⟨rfl,by simp [splits]⟩
  | succ t ih =>
    have ⟨eq,cost⟩ := byDegree_spec d k m (by omega)
    have ⟨ans,tail⟩ := ih (k+1) (by omega)
    cases gate : (byDegree d k m).1 with
    | false =>
      rw [gate] at eq
      simp only [splits,gate,Bool.false_eq_true,↓reduceIte,List.range'_succ,List.any_cons,←eq,Bool.false_or,ans]
      refine ⟨trivial,?_⟩; rw [Nat.succ_mul]; omega
    | true =>
      rw [gate] at eq
      simp only [splits,gate,↓reduceIte,List.range'_succ,List.any_cons,←eq,Bool.true_or]
      refine ⟨trivial,?_⟩; rw [Nat.succ_mul]; omega

def hasFactor (d : ℕ) (mask : List Bool) := splits d mask 1 (d-1)

theorem hasFactor_spec (d : ℕ) (mask : List Bool) :
    (hasFactor d mask).1=hasBinaryFactor d (value mask) ∧
    (hasFactor d mask).2 ≤ d*(pairWork d+d+2) := by
  have ⟨eq,paid⟩ := splits_spec d 1 (d-1) mask (by omega)
  exact ⟨eq,paid.trans (Nat.mul_le_mul_right _ (Nat.sub_le ..))⟩

private theorem first_member (f : List Bool → Bool × ℕ) (xs : List (List Bool)) (x : List Bool)
    (eq : (first f xs).1=some x) : x∈xs := by
  induction xs with
  | nil => simp [first] at eq
  | cons y ys ih =>
    cases gate : (f y).1 <;> simp only [first,gate,Bool.false_eq_true,↓reduceIte] at eq
    · exact List.mem_cons_of_mem _ (ih eq)
    · cases eq; simp

def maskWork (d : ℕ) := searchBudget d (d*(pairWork d+d+2)+1)+3*d+2

/-- Find the first successful mask in numerical order and normalize its word.
The getD fallback matches the constructor even at degree zero. -/
def mask (d : ℕ) : List Bool × ℕ :=
  let scan := search d (fun x => let t := hasFactor d x; (!t.1,t.2+1))
  let out := BinarySaturation.canonical (scan.1.getD [])
  (out.1,scan.2+out.2+2)

theorem mask_spec (d : ℕ) : (mask d).1=(binaryMask d).bits ∧ (mask d).2 ≤ maskWork d := by
  let f := fun x => let t := hasFactor d x; (!t.1,t.2+1)
  let s := search d f
  obtain ⟨eq,paid⟩ := search_spec d (d*(pairWork d+d+2)+1) f (fun x => !(hasBinaryFactor d x))
    (fun x _ => ⟨congrArg (!·) (hasFactor_spec d x).1,Nat.add_le_add_right (hasFactor_spec d x).2 1⟩)
  change s.1.map value=_ at eq
  change s.2 ≤ _ at paid
  have ⟨can,cost⟩ := BinarySaturation.canonical_spec (s.1.getD [])
  change _ ∧ s.2+(BinarySaturation.canonical (s.1.getD [])).2+2 ≤ _
  have raw : value (s.1.getD [])=binaryMask d := by
    unfold binaryMask
    rw [←eq]; cases s.1 <;> rfl
  have width : (s.1.getD []).length ≤ d := by
    cases h : s.1 with
    | none => simp
    | some x => exact ((words_spec d).2.1 x (first_member f (words d).1 x h)).le
  exact ⟨can.trans (congrArg Nat.bits raw),by unfold maskWork; omega⟩

def run (degree : List Bool) :=
  let fuel := BinarySaturation.tokens degree
  let out := mask fuel.1.length
  (out.1,fuel.2+fuel.1.length+out.2)

theorem run_spec (degree : List Bool) :
    (run degree).1=(binaryMask (value degree)).bits ∧
      (run degree).2 ≤ maskWork (value degree)+2*value degree+2*degree.length := by
  have ⟨len,fuel⟩ := BinarySaturation.token_spec degree
  have ⟨eq,work⟩ := mask_spec (BinarySaturation.tokens degree).1.length
  simp only [len] at eq work
  change (mask (BinarySaturation.tokens degree).1.length).1=_ ∧ (BinarySaturation.tokens degree).2+(BinarySaturation.tokens degree).1.length+
    (mask (BinarySaturation.tokens degree).1.length).2 ≤ _
  rw [len]
  exact ⟨eq,by omega⟩

/-- The actual canonical mask at the fixed degree is irreducible. The meter
includes all lower-word construction, factor-pair and coefficient scans,
and the search over candidate masks. -/
theorem fixed_mask {b : ℕ} (hb : 0<b) :
    let d := Fixed.d b
    (run d.bits).1=(binaryMask d).bits ∧ Irreducible (binaryPoly d (value (run d.bits).1)) ∧
      (run d.bits).2 ≤ 2^(30*TwoThirdsCost.scale b) := by
  intro d
  obtain ⟨eq,work⟩ := run_spec d.bits
  simp only [value_bits,Nat.size_eq_bits_len] at eq work
  have dp := Fixed.degree_pos hb
  refine ⟨eq,by rw [eq,value_bits]; exact (binaryMask_irreducible dp).2,work.trans ?_⟩
  let s := TwoThirdsCost.scale b
  let X := 2^s
  have hle : Fixed.h b ≤ s := (Nat.le_mul_of_pos_left _ dp).trans (Fixed.scale_bounds hb).1
  have ds : d ≤ s := (Nat.le_mul_of_pos_right _ (Nat.succ_pos b.log2)).trans hle
  have sp : 0<s := dp.trans_le ds
  have dx : d ≤ X := ds.trans Nat.lt_two_pow_self.le
  have ex : 2^d ≤ X := Nat.pow_le_pow_right (by decide) ds
  have dsiz : d.size ≤ X := (Nat.size_le.mpr Nat.lt_two_pow_self).trans dx
  have xp : 1 ≤ X := Nat.one_le_two_pow
  change maskWork d+2*d+2*d.size ≤ 2^(30*s)
  calc _  ≤ X*(8*(X+1)^2+(X*(X*(8*(X+1)^2+(X*(8*(X+1)^2+12*(X+1)^3+2)+1)+2)+1+X+2)+1)+2)+
             3*X+2+2*X+2*X := by unfold maskWork pairWork searchBudget; gcongr
       _  ≤ 2^16*X^7 := by
            have h1 : X ≤ X^7 := Nat.le_self_pow (by decide) X
            have h2 : X^2 ≤ X^7 := Nat.pow_le_pow_right xp (by decide)
            have h3 : X^3 ≤ X^7 := Nat.pow_le_pow_right xp (by decide)
            have h4 : X^4 ≤ X^7 := Nat.pow_le_pow_right xp (by decide)
            have h5 : X^5 ≤ X^7 := Nat.pow_le_pow_right xp (by decide)
            have h6 : X^6 ≤ X^7 := Nat.pow_le_pow_right xp (by decide)
            ring_nf; omega
       _ = 2^(16+s*7) := by rw [show X=2^s from rfl,←pow_mul,pow_add]
       _  ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- The constructor selects X⁵+X²+1 at degree five. -/
example : (run (5:ℕ).bits).1=[true,false,true] := by decide

end Cogentic.BinaryMaskCost

#print axioms Cogentic.BinaryMaskCost.product_spec
#print axioms Cogentic.BinaryMaskCost.hasFactor_spec
#print axioms Cogentic.BinaryMaskCost.fixed_mask
