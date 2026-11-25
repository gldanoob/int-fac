import Cogentic.ModularPowerCost
import Cogentic.Concrete

namespace Cogentic.BinarySplitter

open BinaryDivision BinaryModularPower TwoThirdsFinish

/-- The borrow wire of the full-width subtractor compares zero-extended inputs. -/
private theorem borrow_lt (w : ℕ) (x y : List Bool) (hx : x.length ≤ w) (hy : y.length ≤ w) :
    (subtract w x y false).borrow = true ↔ value x < value y := by
  obtain ⟨len, _, eq⟩ := subtract_spec w x y false hx hy
  have small := value_lt (subtract w x y false).digits
  rw [len] at small
  cases h : (subtract w x y false).borrow <;> simp [h] at eq ⊢ <;> omega

/-- Truncated decrement, including the all-zero input. -/
def predBits (x : List Bool) : List Bool × ℕ :=
  let sub := subtract x.length x [] true
  let sel := selectDigits x.length sub.borrow (!sub.borrow) [] sub.digits
  (sel.1, sub.gates + sel.2 + 1)

private theorem pred_spec (x : List Bool) :
    value (predBits x).1 = value x - 1 ∧ (predBits x).1.length = x.length ∧
    (predBits x).2 = 10*x.length+1 := by
  let sub := subtract x.length x [] true
  obtain ⟨len,work,eq⟩ := subtract_spec x.length x [] true (by rfl) (by simp)
  change value sub.digits + 0 + 1 = _ + _*sub.borrow.toNat at eq
  obtain ⟨width,cost,res⟩ := select_spec x.length sub.borrow [] sub.digits (by simp) len.le
  change value (selectDigits ..).1 = _ ∧ _ = _ ∧ _ = _
  refine ⟨?_, width, ?_⟩
  · rw [res]
    have small := value_lt sub.digits
    rw [show sub.digits.length = x.length from len] at small
    cases h : sub.borrow <;> simp [h, value] at eq ⊢ <;> omega
  · change sub.gates + (selectDigits x.length sub.borrow (!sub.borrow) [] sub.digits).2 + 1 = _
    change sub.gates = _ at work
    omega

/-- Check both strict inequalities using subtractor borrow wires. -/
def proper (n g : List Bool) : Bool × ℕ :=
  let high := subtract n.length [true] g false
  let low := subtract n.length g n false
  (high.borrow && low.borrow, high.gates+low.gates+1)

theorem proper_spec (n g : List Bool) (pos : 0 < value n) (hg : g.length ≤ n.length) :
    ((proper n g).1 = true ↔ 1 < value g ∧ value g < value n) ∧
      (proper n g).2 = 14*n.length+1 := by
  have hn : [true].length ≤ n.length := by cases n <;> simp [value] at *
  have high := borrow_lt n.length [true] g hn hg
  have low := borrow_lt n.length g n hg le_rfl
  have hi := (subtract_spec n.length [true] g false hn hg).2.1
  have lo := (subtract_spec n.length g n false hg le_rfl).2.1
  refine ⟨by simpa [proper,value] using and_congr high low, ?_⟩
  simp [proper,hi,lo]
  omega

/-- The next iteration receives the computed square. Each inspected residue incurs
at most one modular squaring, including when two consecutive residues coincide. -/
def scanBits (n : List Bool) (x : List Bool) : List Unit → Option (List Bool) × ℕ
  | [] => (none,0)
  | _::k =>
    let sub := predBits x
    let gd := gcdBits n sub.1
    let ok := proper n gd.1
    let cost := sub.2+gd.2+ok.2+1
    if ok.1 then (some gd.1,cost)
    else
      let sq := mulMod n x x
      let next := scanBits n sq.1 k
      (next.1,cost+sq.2+next.2)

def scanStepBudget (W : ℕ) := gcdBudget W + 136*W^2+27*W+3

theorem scanBits_spec (n x : List Bool) (k : List Unit) (pos : 0 < value n) (hx : x.length≤n.length) :
    (scanBits n x k).1.map value = OrderCertificate.scan (value n) (value x) k.length ∧
    (scanBits n x k).2 ≤ k.length * scanStepBudget n.length := by
  induction k generalizing x with
  | nil => simp [scanBits,OrderCertificate.scan]
  | cons u k ih =>
    let sub := predBits x
    let gd := gcdBits n sub.1
    let ok := proper n gd.1
    obtain ⟨pv,pl,pc⟩ := pred_spec x
    change value sub.1 = _ at pv
    change sub.1.length = _ at pl
    change sub.2 = _ at pc
    have ⟨gv,gl,gc⟩ := gcdBits_spec n sub.1 n.length le_rfl (pl.le.trans hx)
    change value gd.1 = _ at gv
    change gd.1.length ≤ _ at gl
    change gd.2 ≤ _ at gc
    rw [pv] at gv
    have cnt := Elimination.gcdWithCount_le (value n) (value sub.1)
    have ws : (value n).size ≤ n.length := Nat.size_le.mpr (value_lt n)
    have gc' : gd.2 ≤ gcdBudget n.length := gc.trans (by unfold gcdBudget; gcongr; omega)
    obtain ⟨ov,oc⟩ := proper_spec n gd.1 pos gl
    change (ok.1=true ↔ _) at ov
    change ok.2=_ at oc
    rw [gv] at ov
    let sq := mulMod n x x
    have ⟨sv,sl,sc⟩ := mulMod_spec n x x pos hx hx
    change value sq.1 = _ at sv
    have ⟨tv,tc⟩ := ih sq.1 sl
    rw [sv] at tv
    rw [scanBits, List.length_cons, OrderCertificate.scan, Nat.succ_mul]
    change (if ok.1 then (some gd.1,sub.2+gd.2+ok.2+1) else
      ((scanBits n sq.1 k).1,sub.2+gd.2+ok.2+1+sq.2+(scanBits n sq.1 k).2)).1.map value = _ ∧ _
    change sq.2 ≤ _ at sc
    cases h : ok.1 with
    | true =>
      simp only [↓reduceIte, Option.map_some, ov.mp h]
      refine ⟨congrArg some gv, ?_⟩
      change sub.2+gd.2+ok.2+1 ≤ _
      unfold scanStepBudget; omega
    | false =>
      have no := mt ov.mpr (by simp [h])
      simp only [Bool.false_eq_true,↓reduceIte,no]
      refine ⟨tv,?_⟩
      change sub.2+gd.2+ok.2+1+sq.2+(scanBits n sq.1 k).2 ≤ _
      unfold scanStepBudget at tc ⊢
      omega



structure Stripped where
  zeros : List Unit
  odd : List Bool
  probes : ℕ

/-- Stripping low zero bits uses a single pass over the exponent representation.
The resulting list supplies one scan step per zero without a binary loop counter. -/
def strip : List Bool → Stripped
  | [] => ⟨[],[],0⟩
  | true::hi => ⟨[],true::hi,1⟩
  | false::hi =>
    let rest := strip hi
    ⟨()::rest.zeros,rest.odd,rest.probes+1⟩

theorem strip_spec (xs : List Bool) (positive : 0 < value xs) :
    ((strip xs).zeros.length, value (strip xs).odd) = stripTwos (value xs) ∧
    (strip xs).zeros.length ≤ xs.length ∧ (strip xs).odd.length ≤ xs.length ∧
    (strip xs).probes ≤ xs.length := by
  induction xs with
  | nil => simp [value] at positive
  | cons bit xs ih =>
    cases bit with
    | true =>
      rw [stripTwos]
      simp [strip,value]
    | false =>
      have p : 0 < value xs := by simpa [value] using positive
      obtain ⟨res,len,width,cost⟩ := ih p
      rw [stripTwos]
      simp only [strip,value,Bool.toNat_false,zero_add,List.length_cons] at positive ⊢
      have half : 2 * value xs / 2 = value xs := by omega
      simp [positive,half,←res]
      omega

/-- A base needs one modular power for the odd part and one scan over trailing zeroes. -/
def base (n g : ℕ) (t : Stripped) : Option (List Bool) × ℕ :=
  let init := power g (value t.odd) n
  let out := scanBits n.bits init.1 t.zeros
  (out.1,init.2+out.2)

def baseBudget (A E W : ℕ) := powerBudget A E W + E*scanStepBudget W

private theorem base_spec (n g m A : ℕ) (hn : 0 < n) (hm : 0 < m) (hg : g.size ≤ A) :
    let out := base n g (strip m.bits)
    out.1.map value = (splitBase n m g).map Subtype.val ∧
    out.2 ≤ baseBudget A m.size n.size := by
  let t := strip m.bits
  have ⟨eq,twos,odd,_⟩ := strip_spec m.bits (by simpa using hm)
  simp only [value_bits] at eq
  rw [Nat.size_eq_bits_len] at twos odd
  change (t.zeros.length, value t.odd) = _ at eq
  change t.zeros.length ≤ _ at twos
  change t.odd.length ≤ _ at odd
  let init := power g (value t.odd) n
  obtain ⟨width,powCost⟩ := power_gates g (value t.odd) n hn
  change init.1.length ≤ _ at width
  change init.2 ≤ _ at powCost
  obtain ⟨scanVal,scanCost⟩ := scanBits_spec n.bits init.1 t.zeros
    (by simpa using hn) (by simpa only [← Nat.size_eq_bits_len] using width)
  simp only [value_bits] at scanVal
  rw [Nat.size_eq_bits_len] at scanCost
  change (scanBits n.bits init.1 t.zeros).1.map value = _ ∧
    init.2+(scanBits n.bits init.1 t.zeros).2 ≤ _
  constructor
  · rw [scanVal]
    rw [show value init.1 = _ from power_value g (value t.odd) n,
      show value t.odd = (stripTwos m).2 from congrArg Prod.snd eq,
      show t.zeros.length = (stripTwos m).1 from congrArg Prod.fst eq]
    unfold splitBase
    dsimp only
    split <;> rename_i h <;> simp [h]
  · have exponent : (value t.odd).size ≤ m.size := (Nat.size_le.mpr (value_lt t.odd)).trans odd
    have powBound : powerBudget g.size (value t.odd).size n.size ≤ powerBudget A m.size n.size := by
      unfold powerBudget; gcongr
    exact Nat.add_le_add (powCost.trans powBound) (scanCost.trans (Nat.mul_le_mul_right _ twos))

def bases (n : ℕ) (t : Stripped) : List ℕ → Option (List Bool) × ℕ
  | [] => (none,0)
  | g::gs =>
    let out := base n g t
    match out.1 with
    | some d => (some d,out.2+1)
    | none =>
      let rest := bases n t gs
      (rest.1,out.2+1+rest.2)

private theorem bases_spec (n m A : ℕ) (gs : List ℕ) (hn : 0 < n) (hm : 0 < m)
    (bound : ∀ g ∈ gs, g.size ≤ A) :
    (bases n (strip m.bits) gs).1.map value = (splitWithExponent n m gs).map Subtype.val ∧
    (bases n (strip m.bits) gs).2 ≤ gs.length*(baseBudget A m.size n.size+1) := by
  induction gs with
  | nil => simp [bases,splitWithExponent]
  | cons g gs ih =>
    obtain ⟨bv,bc⟩ := base_spec n g m A hn hm (bound g (by simp))
    obtain ⟨rv,rc⟩ := ih (fun b hb => bound b (by simp [hb]))
    simp only [splitWithExponent] at rv ⊢
    rw [bases, List.findSome?_cons, List.length_cons, Nat.succ_mul]
    cases h : (base n g (strip m.bits)).1 <;>
      cases f : splitBase n m g <;>
      simp_all only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] <;>
      exact ⟨trivial,by omega⟩

/-- Bit predicates, modular arithmetic and data-dependent branch decisions are
charged. Input encoding, wiring, allocation and traversal of the list spine are
outside the Boolean-operation model inherited from the arithmetic circuits. -/
def splitter (n m : ℕ) (gs : List ℕ) : Option (List Bool) × ℕ :=
  let t := strip m.bits
  let out := bases n t gs
  (out.1,t.probes+out.2)

theorem splitter_spec (n m A : ℕ) (gs : List ℕ) (hn : 0 < n) (hm : 0 < m)
    (bound : ∀ g ∈ gs, g.size ≤ A) :
    (splitter n m gs).1.map value = (splitWithExponent n m gs).map Subtype.val ∧
    (splitter n m gs).2 ≤ m.size+gs.length*(baseBudget A m.size n.size+1) := by
  obtain ⟨output,cost⟩ := bases_spec n m A gs hn hm bound
  have probes := (strip_spec m.bits (by simpa using hm)).2.2.2
  rw [Nat.size_eq_bits_len] at probes
  exact ⟨output,Nat.add_le_add probes cost⟩



structure Header where
  two : Bool
  candidate : Bool
  gates : ℕ

/-- Equality to two, strict lower bound and parity use only input bits. -/
def header (x : List Bool) : Header :=
  let w := x.length+2
  let low := subtract w x [false,true] false
  let high := subtract w [false,true] x false
  ⟨!(low.borrow || high.borrow), high.borrow && x.headD false, low.gates+high.gates+3⟩

private theorem header_spec (x : List Bool) :
    (header x).two = decide (value x=2) ∧
    (header x).candidate = (decide (2<value x) && decide (value x % 2 = 1)) ∧
    (header x).gates = 14*x.length+31 := by
  let w := x.length+2
  have hx : x.length≤w := by dsimp [w]; omega
  have ht : [false,true].length ≤ w := by simp [w]
  let low := subtract w x [false,true] false
  let high := subtract w [false,true] x false
  have lv : low.borrow=true ↔ value x<2 := borrow_lt w x [false,true] hx ht
  have hv : high.borrow=true ↔ 2<value x := borrow_lt w [false,true] x ht hx
  have lc : low.gates = 7*w := (subtract_spec w x [false,true] false hx ht).2.1
  have hc : high.gates = 7*w := (subtract_spec w [false,true] x false ht hx).2.1
  have odd : x.headD false=true ↔ value x%2=1 := by
    rw [value_head x]
    cases x.headD false <;> simp
  change (!(low.borrow || high.borrow)) = _ ∧ (high.borrow && x.headD false) = _ ∧ _ = _
  refine ⟨Bool.eq_iff_iff.mpr ?_, Bool.eq_iff_iff.mpr ?_,?_⟩
  · simp only [Bool.not_eq_true',Bool.eq_false_iff,ne_eq,Bool.or_eq_true,lv,hv,decide_eq_true_eq]
    omega
  · simp only [Bool.and_eq_true,decide_eq_true_eq,hv,odd]
  · change low.gates+high.gates+3=_
    rw [lc,hc]; dsimp [w]; omega

/-- Reuse one counted decrement to supply both the Fermat exponents and the
splitter exponent. The small/even cases return immediately. -/
def primality (n : ℕ) (gs : List ℕ) : Bool × ℕ :=
  let start := header n.bits
  if start.candidate then
    let sub := predBits n.bits
    let m := value sub.1
    let guards := fermatGuardsAt n m gs
    let split := splitter n m gs
    (guards.1 && split.1.isNone,start.gates+sub.2+guards.2+split.2+3)
  else (start.two,start.gates+1)

def primalityBudget (W count : ℕ) :=
  25*W+35+count*(gcdBudget W+powerBudget W W W+2*W+7+(baseBudget W W W+1))

theorem primality_spec (n W : ℕ) (gs : List ℕ) (hn : n.size≤W)
    (bound : ∀ g ∈ gs, g.size≤W) :
    (primality n gs).1 = primeCheck n gs ∧
    (primality n gs).2 ≤ primalityBudget W gs.length := by
  obtain ⟨two,can,headerCost⟩ := header_spec n.bits
  simp only [value_bits,Nat.size_eq_bits_len] at two can headerCost
  unfold primality
  dsimp only
  split
  next h =>
    have h' := can.symm.trans h
    simp only [Bool.and_eq_true,decide_eq_true_eq] at h'
    have pos : 0 < n := by omega
    have mp : 0 < n-1 := by omega
    have diff := pred_spec n.bits
    simp only [value_bits,Nat.size_eq_bits_len] at diff
    rw [diff.1]
    obtain ⟨guardVal,guardCost⟩ := fermatGuards_spec n W gs pos hn bound
    change (fermatGuardsAt n (n-1) gs).1 = _ at guardVal
    change (fermatGuardsAt n (n-1) gs).2 ≤ _ at guardCost
    obtain ⟨sv,sc⟩ := splitter_spec n (n-1) W gs pos mp bound
    have same := congrArg Option.isNone sv
    simp only [Option.isNone_map] at same
    constructor
    · simp [primeCheck,guardVal,same,h'.1,h'.2,show n≠2 by omega]
    · have e : (n-1).size≤W := (Nat.size_le_size (Nat.sub_le n 1)).trans hn
      have step : scanStepBudget n.size ≤ scanStepBudget W := by
        unfold scanStepBudget gcdBudget; gcongr
      have b : baseBudget W (n-1).size n.size ≤ baseBudget W W W := by
        unfold baseBudget powerBudget; gcongr
      have sc' := sc.trans (show _ ≤ W+gs.length*(baseBudget W W W+1) by gcongr)
      have total := Nat.add_le_add guardCost sc'
      unfold primalityBudget
      rw [Nat.mul_add]
      rw [headerCost,diff.2.2]
      omega
  next h =>
    have no : (decide (2<n) && decide (n%2=1)) = false := by
      cases hc : (header n.bits).candidate <;> simp_all
    constructor
    · have odd : (n%2 == 1) = decide (n%2=1) := Bool.eq_iff_iff.mpr (by simp)
      have eq : (n == 2) = decide (n=2) := Bool.eq_iff_iff.mpr (by simp)
      simpa only [primeCheck,odd,eq,no,Bool.false_and,Bool.or_false] using two
    · rw [headerCost]; unfold primalityBudget; omega


private theorem range_base_width (cap : ℕ) {g : ℕ} (hg : g ∈ List.range' 1 cap) :
    g.size ≤ cap.size := by
  have hi := (List.mem_range'_1.mp hg).2
  exact Nat.size_le_size (by omega)

/-- The actual primality path in totalStep uses this polynomial cutoff. The
maximum width here also covers the bases when the cutoff exceeds the modulus. -/
theorem driver_primality (n k : ℕ) :
    let b := n.log2+1
    let cap := polyCutoff k b
    let gs := List.range' 1 cap
    (primality n gs).1 = primeCheck n gs ∧
      (primality n gs).2 ≤ primalityBudget (max b cap.size) cap := by
  dsimp only
  have w : n.size ≤ n.log2+1 := Nat.size_le.mpr Nat.lt_log2_self
  simpa only [List.length_range'] using primality_spec n _ _
    (w.trans (le_max_left _ _))
    (fun g hg => (range_base_width (polyCutoff k (n.log2+1)) hg).trans (le_max_right _ _))

/-- The concrete searcher's exponent guard controls the square-chain bit budget
on its actual orders branch, independently of analytic coverage. Costs incurred
before the saturated exponent is available are accounted for in other stages. -/
theorem driver_splitter (n k : ℕ) (hn : 2 ≤ n) :
    let b := n.log2+1
    let cap := polyCutoff k b
    let gs := List.range' 1 cap
    let E := 2^(2017*TwoThirdsCost.scale b)+1
    match (TwoThirdsSearch.collect hn
      (TwoThirdsSearch.searchBox n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b)
        (Concrete.candidate n)) (dyadicTargets (Fixed.beta b)).sort).1 with
    | .divisor .. => True
    | .orders e .. =>
      let m := saturate e b (Fixed.beta b)
      (splitter n m gs).1.map value = (splitWithExponent n m gs).map Subtype.val ∧
      (splitter n m gs).2 ≤ E+cap*(baseBudget cap.size E b+1) := by
  let b := n.log2+1
  let cap := polyCutoff k b
  let gs := List.range' 1 cap
  let E := 2^(2017*TwoThirdsCost.scale b)+1
  let res := (TwoThirdsSearch.collect hn
    (TwoThirdsSearch.searchBox n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b)
      (Concrete.candidate n)) (dyadicTargets (Fixed.beta b)).sort).1
  change match res with
    | .divisor .. => True
    | .orders e .. =>
      let m := saturate e b (Fixed.beta b)
      (splitter n m gs).1.map value = (splitWithExponent n m gs).map Subtype.val ∧
      (splitter n m gs).2 ≤ E+cap*(baseBudget cap.size E b+1)
  have upper := TryPair.saturated_size Construction.construct Concrete.arch n hn
  change (match res with
    | .divisor .. => True
    | .orders e .. => saturate e b (Fixed.beta b) ≤ 2^(2^(2017*TwoThirdsCost.scale b))) at upper
  cases h : res with
  | divisor => trivial
  | orders e big even retained valid =>
    rw [h] at upper
    let m := saturate e b (Fixed.beta b)
    have size : m.size ≤ E := (Nat.size_le_size upper).trans_eq Nat.size_pow
    have ew : n.size ≤ b := Nat.size_le.mpr Nat.lt_log2_self
    have mp : 0 < m := Nat.mul_pos (by omega : 0 < e)
      (Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun i hi =>
        Nat.ne_of_gt <| (Finset.mem_Icc.mp hi).1)))
    obtain ⟨val,cost⟩ := splitter_spec n m cap.size gs (by omega) mp
      (fun g hg => range_base_width cap hg)
    have step : scanStepBudget n.size ≤ scanStepBudget b := by
      unfold scanStepBudget gcdBudget; gcongr
    have budget : baseBudget cap.size m.size n.size ≤ baseBudget cap.size E b := by
      unfold baseBudget powerBudget; gcongr
    have len : gs.length = cap := by simp [gs]
    rw [len] at cost
    exact ⟨val,cost.trans (by gcongr)⟩


/-- Once the input bit length exceeds the fixed generator constant, both
driver budgets fit a single exponential in the paper's two-thirds scale. -/
theorem driver_budgets_scale (b k : ℕ) (hb : 0 < b) (hk : k ≤ b) :
    let cap := polyCutoff k b
    let E := 2^(2017*TwoThirdsCost.scale b)+1
    let bound := 2^(10102*TwoThirdsCost.scale b)
    primalityBudget (max b cap.size) cap ≤ bound ∧
      E+cap*(baseBudget cap.size E b+1) ≤ bound := by
  let s := TwoThirdsCost.scale b
  let X := 2^(2018*s)
  let cap := polyCutoff k b
  let E := 2^(2017*s)+1
  have dpos := Fixed.degree_pos hb
  have zs : Fixed.z b ≤ s := (Nat.le_mul_of_pos_left _ dpos).trans
    ((Nat.le_mul_of_pos_left _ dpos).trans (Fixed.scale_bounds hb).1)
  have sp : 0 < s := (show 0 < Fixed.z b from Nat.succ_pos _).trans_le zs
  have small : b ≤ 2^s := (Nat.lt_log2_self (n:=b)).le.trans (Nat.pow_le_pow_right (by decide) zs)
  have bw : b ≤ X := small.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have base : 1000*(k+b+1) ≤ 2^(12+s) := by
    rw [Nat.pow_add]
    norm_num
    have := Nat.two_pow_pos s
    omega
  have capBound : cap ≤ X := by
    unfold cap polyCutoff X
    calc
      _ ≤ (2^(12+s))^6 := Nat.pow_le_pow_left base 6
      _ = 2^((12+s)*6) := (Nat.pow_mul ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have width : cap.size ≤ X := (Nat.size_le.mpr Nat.lt_two_pow_self).trans capBound
  have maxW := max_le bw width
  have expo : E ≤ X := by
    have grow : 2017*s+1 ≤ 2018*s := by omega
    have pos := Nat.two_pow_pos (2017*s)
    calc E ≤ 2^(2017*s+1) := by dsimp [E]; rw [Nat.pow_succ]; omega
         _ ≤ X := Nat.pow_le_pow_right (by decide) grow
  have large : primalityBudget X X ≤ 4096*X^5 := by
    have xp : 0 < X := Nat.two_pow_pos _
    obtain ⟨u,eq⟩ := Nat.exists_eq_succ_of_ne_zero xp.ne'
    rw [eq,Nat.succ_eq_add_one]
    unfold primalityBudget baseBudget scanStepBudget powerBudget gcdBudget
    ring_nf
    omega
  have bound : primalityBudget X X ≤ 2^(10102*s) := large.trans (by
    change 2^12*(2^(2018*s))^5 ≤ _
    rw [←Nat.pow_mul,←Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega))
  change primalityBudget (max b cap.size) cap ≤ 2^(10102*s) ∧
    E+cap*(baseBudget cap.size E b+1) ≤ 2^(10102*s)
  constructor
  · apply LE.le.trans _ bound
    unfold primalityBudget baseBudget scanStepBudget powerBudget gcdBudget
    gcongr
  · apply LE.le.trans _ bound
    have le : E+cap*(baseBudget cap.size E b+1) ≤ X+X*(baseBudget X X X+1) := by
      unfold baseBudget scanStepBudget powerBudget gcdBudget; gcongr
    apply le.trans
    unfold primalityBudget
    conv_rhs => rw [Nat.mul_add]
    omega

end Cogentic.BinarySplitter

#print axioms Cogentic.BinarySplitter.splitter_spec
#print axioms Cogentic.BinarySplitter.primality_spec

#print axioms Cogentic.BinarySplitter.driver_primality
#print axioms Cogentic.BinarySplitter.driver_splitter

#print axioms Cogentic.BinarySplitter.driver_budgets_scale
