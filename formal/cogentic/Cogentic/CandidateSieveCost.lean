import Cogentic.SplitterCost
import Cogentic.SaturationCost

namespace Cogentic.BinaryPresieve
open BinaryDivision BinaryPivot BinaryModularPower TwoThirdsSearch

private theorem value_padding (xs : List Bool) (k : ℕ) :
    value (xs ++ List.replicate k false) = value xs := by
  induction xs with
  | nil => induction k with | zero => rfl | succ k ih => simp [List.replicate_succ,value] at ih ⊢; omega
  | cons b xs ih => simp [value,ih]

/-- The gcd result may have leading zeroes. Pad the modulus for the strict
comparison and charge both the padding and the outcome dispatch. -/
def probe (n z : List Bool) : Option (List Bool) × ℕ :=
  let wide := n ++ List.replicate z.length false
  let gd := gcdBits n z
  let ok := BinarySplitter.proper wide gd.1
  (if ok.1 then some gd.1 else none,gd.2+ok.2+n.length+z.length+1)

private def factor (n z : ℕ) : Option ℕ :=
  let g := n.gcd z
  if 1<g ∧ g<n then some g else none

def probeBudget (w : ℕ) := gcdBudget w+15*w+2

private theorem probe_spec (n z : List Bool) (w : ℕ) (pos : 0<value n)
    (size : n.length+z.length ≤ w) :
    (probe n z).1.map value = factor (value n) (value z) ∧ (probe n z).2≤probeBudget w := by
  let len := n.length+z.length
  let wide := n ++ List.replicate z.length false
  let gd := gcdBits n z
  have nl : n.length≤len := Nat.le_add_right ..
  have zl : z.length≤len := Nat.le_add_left ..
  obtain ⟨gv,gl,gc⟩ := gcdBits_spec n z len nl zl
  have wl : wide.length=len := by simp [wide,len]
  have wv : value wide=value n := value_padding ..
  have pc := BinarySplitter.proper_spec wide gd.1 (wv ▸ pos) (wl ▸ gl)
  change value gd.1=_ at gv
  rw [wv,gv,wl] at pc
  have gh := (Elimination.gcdWithCount_le (value n) (value z)).trans
    (Nat.mul_le_mul_left 2 ((Nat.size_le.mpr (value_lt n)).trans (nl.trans size)))
  have gw : gd.2≤gcdBudget w := gc.trans (by unfold gcdBudget; gcongr)
  refine ⟨?_,?_⟩
  · change (if (BinarySplitter.proper wide gd.1).1 then some gd.1 else none).map value=_
    by_cases yes : 1<(value n).gcd (value z) ∧ (value n).gcd (value z)<value n
    · simp [pc.1.mpr yes,factor,yes,gv]
    · simp [Bool.eq_false_iff.mpr (fun q=>yes (pc.1.mp q)),factor,yes]
  · change gd.2+(BinarySplitter.proper wide gd.1).2+n.length+z.length+1≤_
    rw [pc.2]; unfold probeBudget; dsimp only [len] at *; omega

/-- Absolute base difference, including when the mark exceeds the base. -/
def gap (m a : List Bool) : List Bool × ℕ :=
  let w := max m.length a.length
  let down := subtract w m a false
  let up := subtract w a m false
  let out := selectDigits w down.borrow (!down.borrow) up.digits down.digits
  (out.1,down.gates+up.gates+out.2+1)

theorem gap_spec (m a : List Bool) :
    value (gap m a).1=((value a:ℤ)-value m).natAbs ∧
    (gap m a).1.length=max m.length a.length ∧ (gap m a).2=17*(max m.length a.length)+1 := by
  let w := max m.length a.length
  let down := subtract w m a false
  let up := subtract w a m false
  have ⟨dl,dc,dv⟩ := subtract_spec w m a false (le_max_left ..) (le_max_right ..)
  have ⟨ul,uc,uv⟩ := subtract_spec w a m false (le_max_right ..) (le_max_left ..)
  have ⟨ol,oc,ov⟩ := select_spec w down.borrow up.digits down.digits ul.le dl.le
  change (value down.digits)+value a+0=value m+2^w*down.borrow.toNat at dv
  change (value up.digits)+value m+0=value a+2^w*up.borrow.toNat at uv
  have ds := value_lt down.digits
  have us := value_lt up.digits
  change down.digits.length=w at dl
  change up.digits.length=w at ul
  rw [dl] at ds; rw [ul] at us
  change value (selectDigits ..).1=_ ∧ (selectDigits ..).1.length=w ∧ _=17*w+1
  refine ⟨?_,ol,?_⟩
  · rw [ov]
    cases hd : down.borrow <;> cases hu : up.borrow <;> simp [hd,hu] at dv uv ⊢ <;> omega
  · change down.gates+up.gates+(selectDigits w down.borrow (!down.borrow) up.digits down.digits).2+1=_
    rw [oc]; change down.gates=7*w at dc; change up.gates=7*w at uc; omega

/-- Iteration over binary loop fuel in exactly the ascending order of
List.range'. A failed probe increments the binary cursor. -/
def scan (n : List Bool) (arg : List Bool → List Bool × ℕ) :
    List Unit → List Bool → Option (List Bool) × ℕ
  | [], _ => (none,0)
  | _::rest, a =>
    let z := arg a
    let test := probe n z.1
    match test.1 with
    | some d => (some d,1+z.2+test.2)
    | none =>
      let next := addDigits a.length a [] true
      let tail := scan n arg rest next.1
      (tail.1,1+z.2+test.2+next.2+tail.2)

def visitBudget (w : ℕ) := 2+22*w+probeBudget (2*w)

private theorem scan_spec (n : List Bool) (pos : 0<value n) (w : ℕ) (nw : n.length≤w)
    (arg : List Bool → List Bool × ℕ) (f : ℕ→ℕ)
    (argSpec : ∀ a : List Bool,a.length≤w →
      value (arg a).1=f (value a) ∧ (arg a).1.length≤w ∧ (arg a).2≤17*w+1)
    (ts : List Unit) (a : List Bool) (aw : a.length+ts.length≤w) :
    (scan n arg ts a).1.map value=(List.range' (value a) ts.length).findSome? (fun j=>factor (value n) (f j)) ∧
    (scan n arg ts a).2≤ts.length*visitBudget w := by
  induction ts generalizing a with
  | nil => simp [scan]
  | cons tok ts ih =>
    have aw' : a.length≤w := by simp only [List.length_cons] at aw; omega
    obtain ⟨av,al,ac⟩ := argSpec a aw'
    obtain ⟨val,cost⟩ := probe_spec n (arg a).1 (2*w) pos (by omega)
    rw [av] at val
    obtain ⟨len,addWork,num⟩ := addDigits_spec a.length a [] true le_rfl (by simp)
    change value (addDigits a.length a [] true).1=value a+0+1 at num
    simp only [Nat.add_zero] at num
    simp only [List.length_cons] at aw ⊢
    have tail := ih (addDigits a.length a [] true).1 (by rw [len]; omega)
    rw [num] at tail
    rw [List.range'_succ,List.findSome?_cons,←val]
    cases h : (probe n (arg a).1).1 with
    | none =>
      simp only [scan,h,Option.map_none] at *
      refine ⟨tail.1,?_⟩
      have step : 1+(arg a).2+(probe n (arg a).1).2+(addDigits a.length a [] true).2≤visitBudget w := by
        unfold visitBudget; omega
      exact (Nat.add_le_add step tail.2).trans_eq (Nat.succ_mul .. |>.trans (Nat.add_comm ..) |>.symm)
    | some d =>
      simp only [scan,h,Option.map_some,true_and]
      rw [Nat.succ_mul]; unfold visitBudget; omega

/-- Both ascending scans use binary fuel lengths. The second scan is only
started when the small trial divisors have all failed. -/
def run (n cap A m : List Bool) : Option (List Bool) × ℕ :=
  let t := BinarySaturation.tokens cap
  let early := scan n (fun a=>(a,0)) t.1.tail [false,true]
  match early.1 with
  | some d => (some d,t.2+early.2+2)
  | none =>
    let a := BinarySaturation.tokens A
    let late := scan n (gap m) a.1 [true]
    (late.1,t.2+early.2+2+a.2+late.2)

def width (n cap A m : ℕ) := 2+n.size+m.size+cap+A

def budget (n cap A m : ℕ) :=
  cap+2*cap.size+A+2*A.size+2+(cap+A)*visitBudget (width n cap A m)

private theorem map_orElse {α β : Type} (f : α→β) (x y : Option α) :
    (x.orElse (fun _=>y)).map f=(x.map f).orElse (fun _=>y.map f) := by cases x <;> rfl

private theorem presieve_values (n bits β A m : ℕ) :
    (presieve n bits β A m).map Subtype.val =
      ((List.range' 2 (indexCap bits β-1)).findSome? (factor n)).orElse
        (fun _=>(List.range' 1 A).findSome? (fun (a : ℕ)=>factor n ((a:ℤ)-m).natAbs)) := by
  let candidate (x : ℕ) : Option {d // ProperDivisor n d} :=
    if h : 1<n.gcd x ∧ n.gcd x<n then some ⟨n.gcd x,h.1,h.2,Nat.gcd_dvd_left ..⟩ else none
  have read (i : ℕ) : (candidate i).map Subtype.val=factor n i := by
    dsimp only [candidate,factor]; split <;> simp_all
  change (((List.range' 2 _).findSome? candidate).orElse (fun _=>(List.range' 1 A).findSome?
    (fun a=>candidate ((a:ℤ)-m).natAbs))).map Subtype.val = _
  simp only [map_orElse,List.map_findSome?,bind_pure_comp,List.map_eq_map,List.findSome?_map,Function.comp_def,read]

theorem run_spec (n bits β A m : ℕ) (hn : 0<n) :
    let k := indexCap bits β
    let out := run n.bits k.bits A.bits m.bits
    out.1.map value=(presieve n bits β A m).map Subtype.val ∧ out.2≤budget n k A m := by
  intro k out
  let w := width n k A m
  let t := BinarySaturation.tokens k.bits
  let u := BinarySaturation.tokens A.bits
  have ⟨tl,tc⟩ := BinarySaturation.token_spec k.bits
  have ⟨ul,uc⟩ := BinarySaturation.token_spec A.bits
  change t.1.length=_ at tl; change t.2≤_ at tc
  change u.1.length=_ at ul; change u.2≤_ at uc
  simp only [value_bits,Nat.size_eq_bits_len] at tl tc ul uc
  have nl : n.bits.length≤w := by rw [Nat.size_eq_bits_len]; unfold w width; omega
  have ml : m.bits.length≤w := by rw [Nat.size_eq_bits_len]; unfold w width; omega
  have pos : 0<value n.bits := by simpa only [value_bits] using hn
  let early := scan n.bits (fun a=>(a,0)) t.1.tail [false,true]
  obtain ⟨ev,ec⟩ := scan_spec n.bits pos w nl (fun a=>(a,0)) id
    (fun a ha=>⟨rfl,ha,Nat.zero_le _⟩) t.1.tail [false,true] (by
      rw [List.length_tail,tl]; change 2+(k-1)≤_; unfold w width; omega)
  change early.1.map value=_ at ev
  change early.2≤_ at ec
  simp only [List.length_tail,tl,value_bits,id_eq] at ev ec
  change early.1.map value=(List.range' 2 (k-1)).findSome? (factor n) at ev
  let late := scan n.bits (gap m.bits) u.1 [true]
  obtain ⟨lv,lc⟩ := scan_spec n.bits pos w nl (gap m.bits) (fun a=>((a:ℤ)-m).natAbs)
    (fun x hx=>by
      have ⟨v,l,c⟩ := gap_spec m.bits x
      rw [value_bits] at v; rw [l,c]
      refine ⟨v,max_le ml hx,?_⟩; gcongr; exact max_le ml hx)
    u.1 [true] (by rw [ul]; change 1+A≤_; unfold w width; omega)
  change late.1.map value=_ at lv
  change late.2≤_ at lc
  simp only [ul,value_bits] at lv lc
  change late.1.map value=(List.range' 1 A).findSome? (fun (a : ℕ)=>factor n ((a:ℤ)-m).natAbs) at lv
  rw [presieve_values,←ev,←lv]
  have before : early.2≤k*visitBudget w := ec.trans (Nat.mul_le_mul_right _ (Nat.sub_le ..))
  unfold budget
  change _ ∧ out.2 ≤ k+2*k.size+A+2*A.size+2+(k+A)*visitBudget w
  rw [Nat.add_mul]
  change (match early.1 with | some d => (some d,t.2+early.2+2) | none => (late.1,t.2+early.2+2+u.2+late.2)).1.map value=_ ∧
    (match early.1 with | some d => (some d,t.2+early.2+2) | none => (late.1,t.2+early.2+2+u.2+late.2)).2≤_
  cases h : early.1 <;> simp <;> omega

/-- Complete cost of the presieve scans on the fixed schedule given the
binary modulus, index cap, mark limit and base. -/
theorem fixed_presieve {n : ℕ} (hn : 2≤n) :
    let b := n.log2+1; let k := indexCap b (Fixed.beta b)
    let out := run n.bits k.bits (Fixed.A b).bits (Fixed.rootBase n).bits
    out.1.map value=(presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)).map Subtype.val ∧
      out.2≤2^(40020*TwoThirdsCost.scale b) := by
  intro b k out
  obtain ⟨val,cost⟩ := run_spec n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n) (by omega)
  refine ⟨val,cost.trans ?_⟩
  let s := TwoThirdsCost.scale b; let X := 2^(10000*s)
  have hb : 0<b := Nat.succ_pos _
  have d := Fixed.degree_pos hb
  have vs := (Fixed.scale_bounds hb).1
  have hs : Fixed.h b≤ s := (Nat.le_mul_of_pos_left _ d).trans vs
  have zs : Fixed.z b≤ s := (Nat.le_mul_of_pos_left _ d).trans hs
  have hp : 0< s := (Nat.succ_pos b.log2).trans_le zs
  have xp : 1≤X := Nat.one_le_two_pow
  have xp' : 0<X := xp
  have kn : k≤X := (Fixed.index_bound hb).trans (Nat.pow_le_pow_right (by decide) (by
    unfold Fixed.beta; change Fixed.v b≤ s at vs; omega))
  have an : Fixed.A b≤X := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 10000 hs)
  have bX : b≤X := (Nat.lt_log2_self (n:=b)).le.trans (Nat.pow_le_pow_right (by decide) (by
    change b.log2+1≤ s at zs; omega))
  have ns : n.size≤b := Nat.size_le.mpr Nat.lt_log2_self
  have ms : (Fixed.rootBase n).size≤b+1 := Nat.size_le.mpr ((Fixed.rootBase_spec hn).2.2.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self b)))
  have kl : k.size≤X := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=k))).trans kn
  have al : (Fixed.A b).size≤X := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=Fixed.A b))).trans an
  have wX : width n k (Fixed.A b) (Fixed.rootBase n)≤7*X := by unfold width; omega
  have overhead : visitBudget (width n k (Fixed.A b) (Fixed.rootBase n))≤visitBudget (7*X) := by
    unfold visitBudget probeBudget gcdBudget; gcongr
  have low := Nat.le_self_pow (n:=4) (by decide) X
  have sq := Nat.pow_le_pow_right xp' (by decide : 2≤4)
  have cube := Nat.pow_le_pow_right xp' (by decide : 3≤4)
  calc budget n k (Fixed.A b) (Fixed.rootBase n)
      ≤ X+2*X+X+2*X+2+(X+X)*visitBudget (7*X) := by
        unfold budget; gcongr
    _ ≤ 1048576*X^4 := by
      unfold visitBudget probeBudget gcdBudget
      have one : 1≤X^4 := Nat.one_le_pow _ _ xp'
      nlinarith only [low,sq,cube,one]
    _ ≤ 2^(40020*s) := by
      change 2^20*(2^(10000*s))^4≤_
      rw [←pow_mul,←pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Reuse the divisor scan as a primality test on the small integers in the factor base. -/
def trialPrime (n : List Bool) (fuel : List Unit) : Bool × ℕ :=
  let r := scan n (fun a=>(a,0)) fuel [false,true]
  (r.1.isNone,r.2+1)

theorem trialPrime_spec (n : List Bool) (fuel : List Unit) (two : 2 ≤ value n)
    (enough : value n ≤ fuel.length+1) (w : ℕ) (nw : n.length ≤ w) (fw : 2+fuel.length ≤ w) :
    (trialPrime n fuel).1 = decide (value n).Prime ∧ (trialPrime n fuel).2 ≤ fuel.length*visitBudget w+1 := by
  obtain ⟨out,work⟩ := scan_spec n (by omega) w nw (fun a=>(a,0)) id
    (fun a ha=>⟨rfl,ha,Nat.zero_le _⟩) fuel [false,true] fw
  change _ = (List.range' 2 fuel.length).findSome? (fun j=>factor (value n) j) at out
  refine ⟨?_,Nat.add_le_add_right work 1⟩
  change (scan n (fun a=>(a,0)) fuel [false,true]).1.isNone = _
  rw [← Option.isNone_map (f:=value), out]
  by_cases hp : (value n).Prime
  · have no (j : ℕ) : factor (value n) j = none := by
      rcases (Nat.dvd_prime hp).mp (Nat.gcd_dvd_left (value n) j) with h|h <;> simp [factor,h]
    simp [no,hp]
  · have hit : (List.range' 2 fuel.length).findSome? (fun j=>factor (value n) j) ≠ none := by
      let q := (value n).minFac
      have q2 : 1<q := (Nat.minFac_prime (by omega : value n ≠ 1)).one_lt
      have qn : q<value n := (Nat.not_prime_iff_minFac_lt two).mp hp
      have dvd : q∣value n := Nat.minFac_dvd _
      intro miss
      have atQ := List.findSome?_eq_none_iff.mp miss q (List.mem_range'_1.mpr ⟨q2,by omega⟩)
      simp [factor,Nat.gcd_eq_right dvd,q2,qn] at atQ
    obtain ⟨a,found⟩ := Option.ne_none_iff_exists'.mp hit
    rw [found]
    simp [hp]

/-- Trial division on a bounded-size input, or on a failed search. The first
proper gcd in ascending order equals the least prime factor. -/
def trialFactor (n : List Bool) : Option (List Bool) × ℕ :=
  let clock := BinarySaturation.tokens n
  let trial := scan n (fun a => (a,0)) clock.1 [false,true]
  match trial.1 with
  | none => (none,clock.2+trial.2+1)
  | some d =>
    let out := BinarySaturation.canonical d
    (some out.1,clock.2+trial.2+out.2+1)

private theorem first_trial {n : ℕ} (hn : 2≤n) (comp : n.minFac<n)
    (len a : ℕ) (start : 2≤a) (before : a≤n.minFac) (enough : n.minFac<a+len) :
    (List.range' a len).findSome? (factor n) = some n.minFac := by
  induction len generalizing a with
  | zero => omega
  | succ k ih =>
    rw [List.range'_succ,List.findSome?_cons]
    by_cases eq : a=n.minFac
    · subst a
      have nontrivial := (Nat.minFac_prime (by omega : n≠1)).one_lt
      simp [factor,Nat.gcd_eq_right (Nat.minFac_dvd n),nontrivial,comp]
    · have miss : factor n a = none := by
        unfold factor
        apply if_neg
        intro h
        have lower := Nat.minFac_le_of_dvd h.1 (Nat.gcd_dvd_left n a)
        have upper := Nat.le_of_dvd (by omega : 0<a) (Nat.gcd_dvd_right n a)
        omega
      simpa only [miss,Option.orElse_none] using ih (a+1) (by omega) (by omega) (by omega)

theorem trialFactor_spec {n : ℕ} (hn : 2≤n) :
    (trialFactor n.bits).1 = if n.minFac<n then some n.minFac.bits else none := by
  let fuel := (BinarySaturation.tokens n.bits).1
  let scanWord := scan n.bits (fun a => (a,0)) fuel [false,true]
  have length : fuel.length = n := (BinarySaturation.token_spec _).1.trans (value_bits n)
  obtain ⟨out,_⟩ := scan_spec n.bits (by simpa using (show 0<n by omega)) (n.size+n+2)
    (by rw [Nat.size_eq_bits_len]; omega) (fun a => (a,0)) id (fun a ha=>⟨rfl,ha,Nat.zero_le _⟩)
    fuel [false,true] (by change 2+fuel.length≤_; omega)
  change scanWord.1.map value = (List.range' 2 fuel.length).findSome? (fun j => factor (value n.bits) j) at out
  rw [value_bits,length] at out
  by_cases comp : n.minFac<n
  · have low := (Nat.minFac_prime (by omega : n≠1)).two_le
    rw [first_trial hn comp n 2 le_rfl low (by omega)] at out
    cases eq : scanWord.1 with
    | none => simp [eq] at out
    | some d =>
      have val : value d=n.minFac := by simpa [eq] using out
      have can := (BinarySaturation.canonical_spec d).1
      dsimp only [scanWord,fuel] at eq
      simp only [trialFactor,eq,can,val,if_pos comp]
  · have prime : n.Prime := by contrapose! comp; exact (Nat.not_prime_iff_minFac_lt hn).mp comp
    have no (j : ℕ) : factor n j=none := by
      rcases (Nat.dvd_prime prime).mp (Nat.gcd_dvd_left n j) with h|h <;> simp [factor,h]
    have miss : scanWord.1=none := by
      simpa only [List.findSome?_eq_none_iff.mpr (fun j (_ : j∈List.range' 2 n) => no j),
        Option.map_eq_none_iff] using out
    dsimp only [scanWord,fuel] at miss
    simp only [trialFactor,miss,if_neg comp]

end Cogentic.BinaryPresieve

#print axioms Cogentic.BinaryPresieve.run_spec

#print axioms Cogentic.BinaryPresieve.fixed_presieve

#print axioms Cogentic.BinaryPresieve.trialFactor_spec
