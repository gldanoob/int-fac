import Cogentic.ConstructorGridCost
import Cogentic.ConstructionHeight

namespace Cogentic.BinaryLocalCoeffs
open BinaryDivision BinaryPivot BinarySaturation BinaryPerturbation BinaryPreliminary
open BinaryConstructorGrid BinaryRootProduct BinaryCorrectedBase CandidateRuntime Construction

private def binaryRange (n : List Bool) : List (List Bool) × ℕ :=
  let t := tokens n
  let out := progression [true] t.1 []
  (out.1,t.2+out.2+1)

private theorem range_spec (n W : ℕ) (wp : 0<W) (nw : n.size≤W) :
    (binaryRange n.bits).1=(List.range n).map Nat.bits ∧ (binaryRange n.bits).2≤ 3+(n+1)*(11*W+8) := by
  obtain ⟨tl,tc⟩ := token_spec n.bits
  simp only [value_bits,Nat.size_eq_bits_len] at tl tc
  obtain ⟨v,c⟩ := progression_spec 1 0 (tokens n.bits).1 W wp (by simpa [tl] using nw)
  rw [tl,←List.range_eq_range'] at v
  rw [tl] at c
  refine ⟨v,?_⟩
  change (tokens n.bits).2+(progression (1:ℕ).bits (tokens n.bits).1 (0:ℕ).bits).2+1≤_
  nlinarith only [tc,c,nw,Nat.zero_le (n*W),Nat.zero_le n,Nat.zero_le W]

private def traverse (f : α→β×ℕ) : List α → List β × ℕ
  | [] => ([],1)
  | x::xs => let a := f x; let t := traverse f xs; (a.1::t.1,a.2+t.2+1)

private theorem traverse_spec (f : α→β×ℕ) (xs : List γ) (e : γ→α) (g : γ→β) (K : ℕ)
    (step : ∀ x∈xs,(f (e x)).1=g x ∧ (f (e x)).2≤K) :
    (traverse f (xs.map e)).1=xs.map g ∧ (traverse f (xs.map e)).2≤1+xs.length*(K+1) := by
  induction xs with
  | nil => exact ⟨rfl,by simp [traverse]⟩
  | cons x xs ih =>
    obtain ⟨a,b⟩ := step x (by simp)
    obtain ⟨t,u⟩ := ih (fun y hy=>step y (by simp [hy]))
    simp only [List.map_cons,traverse,a,t,List.length_cons,Nat.succ_mul xs.length]
    exact ⟨trivial,by omega⟩

private theorem filter_spec (f : α→Bool×ℕ) (xs : List γ) (e : γ→α) (p : γ→Bool) (K : ℕ)
    (step : ∀ x∈xs,(f (e x)).1=p x ∧ (f (e x)).2≤K) :
    (screenWith f (xs.map e)).1=(xs.filter p).map e ∧ (screenWith f (xs.map e)).2≤1+xs.length*(K+1) := by
  induction xs with
  | nil => exact ⟨rfl,by simp [screenWith]⟩
  | cons x xs ih =>
    obtain ⟨a,b⟩ := step x (by simp)
    obtain ⟨t,u⟩ := ih (fun y hy=>step y (by simp [hy]))
    simp only [List.map_cons,screenWith,a,t,List.filter_cons,List.length_cons,Nat.succ_mul xs.length]
    split <;> simp <;> omega

private def first (f : α→Bool×ℕ) : List α → Option α × ℕ
  | [] => (none,1)
  | x::xs => let a := f x; let t := first f xs; (if a.1 then some x else t.1,a.2+t.2+1)

private theorem first_spec (f : α→Bool×ℕ) (xs : List γ) (e : γ→α) (p : γ→Bool) (K : ℕ)
    (step : ∀ x∈xs,(f (e x)).1=p x ∧ (f (e x)).2≤K) :
    (first f (xs.map e)).1=(xs.find? p).map e ∧ (first f (xs.map e)).2≤1+xs.length*(K+1) := by
  induction xs with
  | nil => exact ⟨rfl,by simp [first]⟩
  | cons x xs ih =>
    obtain ⟨a,b⟩ := step x (by simp)
    obtain ⟨t,u⟩ := ih (fun y hy=>step y (by simp [hy]))
    simp only [List.map_cons,first,a,t,List.find?_cons,List.length_cons,Nat.succ_mul xs.length]
    cases p x <;> exact ⟨rfl,by omega⟩

private def clip : List Unit → List α → List α
  | _::ts,a::as => a::clip ts as
  | _,_ => []

private theorem clip_eq (ts : List Unit) (xs : List α) : clip ts xs=xs.take ts.length := by
  induction ts generalizing xs with
  | nil => simp [clip]
  | cons u us ih => cases xs <;> simp [clip,ih]

private def except (rem : List Bool) (x : List Bool) : Bool×ℕ :=
  let e := equalWords x rem
  (!e.1,e.2+1)

private def wantedWords (d ell m : List Bool) (xs : List (List Bool)) : List (List Bool) × ℕ :=
  let r := signedResidue ⟨false,m⟩ ell
  let sel := screenWith (except r.1) xs
  let t := tokens d
  (clip t.1 sel.1,r.2+sel.2+t.2+t.1.length+3)

private theorem wantedWords_spec (d ell m W : ℕ) (ep : 0<ell) (dw : d.size≤W) (ew : ell.size≤W) (mw : m.size≤W) :
    let xs := (List.range ell).map Nat.bits
    (wantedWords d.bits ell.bits m.bits xs).1=(wanted d ell m).map Nat.bits ∧
    (wantedWords d.bits ell.bits m.bits xs).2≤256*(ell+d+1)*(W+1)^2 := by
  intro xs
  have en (a : ℕ) : encode (a:ℤ)=⟨false,a.bits⟩ := by simp [encode]
  obtain ⟨r,rc⟩ := signedResidue_spec (m:ℤ) ep (by simpa using mw) ew
  have em : modulusResidue (m:ℤ) ell = m%ell := by simp only [modulusResidue,←Int.natCast_mod,Int.toNat_natCast]
  rw [en,em] at r
  rw [en] at rc
  have sw := (Nat.size_le_size (Nat.mod_lt m ep).le).trans ew
  obtain ⟨sv,sc⟩ := filter_spec (except (m%ell).bits) (List.range ell) Nat.bits (fun x=>x != m%ell) (14*W+4) (by
    intro a ha
    have aw := (Nat.size_le_size (List.mem_range.mp ha).le).trans ew
    obtain ⟨v,c⟩ := equalWords_spec a.bits (m%ell).bits
    simp only [value_bits,Nat.size_eq_bits_len] at v c
    have h : (equalWords a.bits (m%ell).bits).1=decide (a=m%ell) := by apply Bool.eq_iff_iff.mpr;simpa only [decide_eq_true_eq] using v
    exact ⟨by simp only [except,h,bne];congr 1,by dsimp [except];rw [c];omega⟩)
  obtain ⟨tl,tc⟩ := token_spec d.bits
  simp only [value_bits,Nat.size_eq_bits_len] at tl tc
  simp only [List.length_range] at sc
  simp only [wantedWords,xs,r,sv,clip_eq,tl,List.map_take,wanted]
  refine ⟨trivial,?_⟩
  nlinarith only [rc,sc,tc,dw,Nat.zero_le (ell*W^2),Nat.zero_le (d*W^2),Nat.zero_le (d*W),
    Nat.zero_le (ell*W),Nat.zero_le d,Nat.zero_le ell,Nat.zero_le W,Nat.zero_le (W^2)]

private def modPowerWord (a d ell : List Bool) : List Bool×ℕ :=
  let b := BinaryModularPower.reduce ell a
  let one := BinaryModularPower.reduce ell [true]
  let p := BinaryModularPower.powerBits ell b.1 one.1 d
  (p.1,b.2+one.2+p.2)

private def shift (d ell a : List Bool) : List Bool×ℕ :=
  let p := modPowerWord a d ell
  let dif := adjust ⟨false,p.1⟩ a false
  let v := signedResidue dif.1 ell
  (v.1,p.2+dif.2+v.2+2)

private def imageNat (d ell a : ℕ) := modulusResidue ((ModularPower.powMod a d ell:ℤ)-a) ell

private theorem shift_spec (d ell a W : ℕ) (ep : 0<ell) (dw : d.size≤W) (ew : ell.size≤W) (aw : a.size≤W) :
    (shift d.bits ell.bits a.bits).1=(imageNat d ell a).bits ∧
    (shift d.bits ell.bits a.bits).2≤2048*(W+1)^3 := by
  let p := modPowerWord a.bits d.bits ell.bits
  have eq : BinaryModularPower.power a d ell = p := by simp [BinaryModularPower.power,ep.ne',p,modPowerWord]
  have pv := BinaryModularPower.power_value a d ell
  obtain ⟨pw,pc⟩ := BinaryModularPower.power_gates a d ell ep
  rw [eq] at pv pw pc
  obtain ⟨v,l,c⟩ := adjust_spec ⟨false,p.1⟩ a.bits false
  simp only [SignedWord.decode,signed,Bool.false_eq_true,if_false,value_bits,pv,Nat.size_eq_bits_len] at v l c
  rw [v] at l
  change ((ModularPower.powMod a d ell:ℤ)-a).natAbs.bits.length≤_ at l
  rw [Nat.size_eq_bits_len] at l
  have bound : ((ModularPower.powMod a d ell:ℤ)-a).natAbs.size≤W+1 := by omega
  obtain ⟨z,g⟩ := signedResidue_spec ((ModularPower.powMod a d ell:ℤ)-a) ep bound (by omega : ell.size≤W+1)
  change (signedResidue (adjust ⟨false,p.1⟩ a.bits false).1 ell.bits).1=_ ∧ p.2+(adjust ⟨false,p.1⟩ a.bits false).2+
    (signedResidue (adjust ⟨false,p.1⟩ a.bits false).1 ell.bits).2+2≤_
  rw [v,c]
  refine ⟨z,?_⟩
  have budget : BinaryModularPower.powerBudget a.size d.size ell.size≤BinaryModularPower.powerBudget W W W := by unfold BinaryModularPower.powerBudget;gcongr
  have bp := pc.trans budget
  unfold BinaryModularPower.powerBudget at bp
  have ma : max p.1.length a.size≤W := max_le (pw.trans ew) aw
  nlinarith only [bp,g,ma,Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]

private def outside (xs : List (List Bool)) (s : List Bool) : Bool × ℕ :=
  let out := first (equalWords s) xs
  (out.1.isNone,out.2+1)

private theorem outside_spec (xs : List ℕ) (s W : ℕ) (sw : s.size≤W) (bound : ∀ a∈xs,a.size≤W) :
    (outside (xs.map Nat.bits) s.bits).1= !xs.contains s ∧
    (outside (xs.map Nat.bits) s.bits).2 ≤ 2+xs.length*(14*W+4) := by
  obtain ⟨v,c⟩ := first_spec (equalWords s.bits) xs Nat.bits (fun a=>decide (a=s)) (14*W+3) (by
    intro a ha
    obtain ⟨h,b⟩ := equalWords_spec s.bits a.bits
    simp only [value_bits,Nat.size_eq_bits_len] at h b
    refine ⟨by apply Bool.eq_iff_iff.mpr;simpa only [decide_eq_true_eq] using h.trans eq_comm,?_⟩
    rw [b];have := bound a ha;omega)
  have hmem : ((xs.find? (fun a=>decide (a=s))).map Nat.bits).isNone= !xs.contains s := by
    apply Bool.eq_iff_iff.mpr
    simp [List.find?_eq_none];aesop
  exact ⟨by simpa only [outside,v] using hmem,by dsimp [outside];change _ ≤ 2+xs.length*(14*W+3+1);omega⟩

private def missing (d ell : List Bool) (xs : List (List Bool)) : List Bool × ℕ :=
  let im := traverse (shift d ell) xs
  let sel := first (outside im.1) xs
  (sel.1.getD [],im.2+sel.2+1)

private theorem missing_spec (d ell W : ℕ) (ep : 0<ell) (dw : d.size≤W) (ew : ell.size≤W) :
    let xs := (List.range ell).map Nat.bits
    (missing d.bits ell.bits xs).1=(missingShift d ell).bits ∧
    (missing d.bits ell.bits xs).2≤4096*(ell+1)^2*(W+1)^3 := by
  intro xs
  let im := (List.range ell).map (imageNat d ell)
  have nonneg a : 0≤((ModularPower.powMod a d ell:ℤ)-a)%(ell:ℤ) := Int.emod_nonneg _ (by exact_mod_cast ep.ne')
  have small a : imageNat d ell a<ell := by
    have := Int.emod_lt_of_pos ((ModularPower.powMod a d ell:ℤ)-a) (show 0<(ell:ℤ) by exact_mod_cast ep)
    unfold imageNat modulusResidue;have := nonneg a;omega
  have same : im.map (fun j : ℕ=>(j:ℤ))=(List.range ell).map (fun a=>((ModularPower.powMod a d ell:ℤ)-a)%(ell:ℤ)) := by
    simp [im,List.map_map,Function.comp_def,imageNat,modulusResidue,Int.toNat_of_nonneg (nonneg _)]
  obtain ⟨v,c⟩ := traverse_spec (shift d.bits ell.bits) (List.range ell) Nat.bits (fun a=>(imageNat d ell a).bits) (2048*(W+1)^3)
    (fun a ha=>shift_spec d ell a W ep dw ew ((Nat.size_le_size (List.mem_range.mp ha).le).trans ew))
  have vv : (traverse (shift d.bits ell.bits) xs).1=im.map Nat.bits := by simpa only [im,List.map_map,Function.comp_def] using v
  have len : im.length=ell := by simp [im]
  obtain ⟨sv,sc⟩ := first_spec (outside (im.map Nat.bits)) (List.range ell) Nat.bits (fun s=> !im.contains s) (2+ell*(14*W+4)) (by
    intro s hs
    apply (outside_spec im s W ((Nat.size_le_size (List.mem_range.mp hs).le).trans ew) ?_).imp_right
    · rw [len];exact id
    · intro x hx; obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx;exact (Nat.size_le_size (small a).le).trans ew)
  change (first (outside (im.map Nat.bits)) xs).1=_ at sv
  change (first (outside (im.map Nat.bits)) xs).2≤_ at sc
  have matchPred (s : ℕ) : (im.map (fun j : ℕ=>(j:ℤ))).contains (s:ℤ)=im.contains s := by apply Bool.eq_iff_iff.mpr;simp
  simp only [missing,vv,sv,missingShift,←same,matchPred]
  refine ⟨?_,?_⟩
  · cases (List.range ell).find? (fun s=> !im.contains s) <;> rfl
  · simp only [List.length_range] at c sc
    nlinarith only [c,sc,Nat.zero_le (ell^2*W^3),Nat.zero_le (ell^2*W^2),Nat.zero_le (ell^2*W),Nat.zero_le (ell^2),
      Nat.zero_le (ell*W^3),Nat.zero_le (ell*W^2),Nat.zero_le (ell*W),Nat.zero_le ell,Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]



private theorem cast_linear (a prev : ℤ) (xs : List ℤ) :
    (linear a prev xs).map (fun z : ℤ=>(z:ℚ))=linear (a:ℚ) (prev:ℚ) (xs.map (fun z : ℤ=>(z:ℚ))) := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [linear,ih]

private theorem cast_roots (rs : List ℕ) :
    (fromRoots (rs.map Int.ofNat)).map (fun z : ℤ=>(z:ℚ))=fromRoots (rs.map (fun a : ℕ=>(a:ℚ))) := by
  have fold (as : List ℕ) (cs : List ℤ) :
      ((as.map Int.ofNat).foldl (fun p r=>linear r 0 p) cs).map (fun z : ℤ=>(z:ℚ)) =
      (as.map (fun a : ℕ=>(a:ℚ))).foldl (fun p r=>linear r 0 p) (cs.map (fun z : ℤ=>(z:ℚ))) := by
    induction as generalizing cs with
    | nil => rfl
    | cons r rs ih => simp only [List.map_cons,List.foldl_cons,ih,cast_linear,Int.cast_zero];rfl
  simpa only [fromRoots,List.map_singleton,Int.cast_one] using fold rs [1]

private def scaled (leading : List Bool) (v : SignedWord) := affine leading v (encode 0)

private def firstField (d ell m leading : List Bool) (xs : List (List Bool)) : List SignedWord×ℕ :=
  let rs := wantedWords d ell m xs
  let prod := build [true] rs.1 [encode 1] [true]
  let out := traverse (scaled leading) prod.coeffs
  (out.1,rs.2+prod.gates+out.2+2)

private theorem firstField_spec (d ell m leading W : ℕ) (large : d<ell) (eb : ell≤W)
    (mw : m.size≤W) (lw : leading.size≤W) :
    let xs := (List.range ell).map Nat.bits; let H := 16^d*W
    (firstField d.bits ell.bits m.bits leading.bits xs).1=(localCoeffs d ell m leading false).map encode ∧
    (∀ z∈localCoeffs d ell m leading false,z.natAbs.size≤6*(H+1)) ∧
    (firstField d.bits ell.bits m.bits leading.bits xs).2≤2^18*(H+1)^5 := by
  intro xs H
  have ep : 0<ell := by omega
  have ew : ell.size≤W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans eb
  have dw : d.size≤W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have wp : 0<W := ep.trans_le eb
  have WH : W≤H := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
  let rs := wanted d ell m
  let cs := fromRoots (rs.map Int.ofNat)
  obtain ⟨len,_,small⟩ := wanted_spec large m
  obtain ⟨rv,rc⟩ := wantedWords_spec d ell m W ep dw ew mw
  change (wantedWords d.bits ell.bits m.bits xs).1=rs.map Nat.bits at rv
  obtain ⟨out,y,cv,yd,yp,rep,width,_,cost⟩ := root_product 1 rs wp (by decide) wp
    (fun a ha=>(Nat.size_le_size (small a ha).1.le).trans ew)
  have eq : y=1 := by
    have e := (build_one_den (rs.map Nat.bits) [encode 1]).symm.trans yd
    simpa only [value_bits] using (congrArg value e.symm : value y.bits=value (1:ℕ).bits)
  subst y
  have repr : out.map (fun z : ℤ=>(z:ℚ))=cs.map (fun z : ℤ=>(z:ℚ)) := by
    rw [show cs.map (fun z : ℤ=>(z:ℚ)) = _ from cast_roots rs]
    simpa [fractions] using rep
  obtain rfl : out=cs := List.map_injective_iff.mpr (Int.cast_injective (α:=ℚ)) repr
  change rs.length=d at len
  rw [len] at cost width
  have clen : cs.length=d+1 := by simp only [cs,(fromRoots_shape _).1,List.length_map,len]
  have step z (hz : z∈cs) := affine_spec leading.bits z 0 (W:=H) ((Nat.size_eq_bits_len _).le.trans (lw.trans WH)) (width z hz) (by simp)
  have sv z (hz : z∈cs) : (scaled leading.bits (encode z)).1=encode ((leading:ℤ)*z) ∧
      (scaled leading.bits (encode z)).2≤2000*(H+1)^2 := by
    obtain ⟨v,_,c⟩ := step z hz
    exact ⟨by simpa only [scaled,value_bits,zero_add] using v,c⟩
  obtain ⟨outv,outc⟩ := traverse_spec (scaled leading.bits) cs encode (fun z=>encode ((leading:ℤ)*z)) _ sv
  change (traverse (scaled leading.bits) (build [true] (wantedWords d.bits ell.bits m.bits xs).1 [encode 1] [true]).coeffs).1=_ ∧ _ ∧
    (wantedWords d.bits ell.bits m.bits xs).2+(build [true] (wantedWords d.bits ell.bits m.bits xs).1 [encode 1] [true]).gates+
    (traverse (scaled leading.bits) (build [true] (wantedWords d.bits ell.bits m.bits xs).1 [encode 1] [true]).coeffs).2+2≤_
  change (build [true] (rs.map Nat.bits) [encode 1] [true]).coeffs = cs.map encode at cv
  rw [rv,cv,outv]
  refine ⟨by simp [localCoeffs,cs,rs,List.map_map,Function.comp_def],?_,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (show z∈cs.map ((leading:ℤ)*·) from hz)
    obtain ⟨v,l,_⟩ := step x hx
    rw [v,value_bits,zero_add] at l
    exact (Nat.size_eq_bits_len _).ge.trans l
  · rw [clen] at outc
    change (wantedWords d.bits ell.bits m.bits xs).2≤_ at rc
    let X := H+1
    have xp : 0<X := Nat.succ_pos _
    have rmax : 256*(ell+d+1)*(W+1)^2≤512*X^3 := by
      exact (Nat.mul_le_mul (Nat.mul_le_mul_left 256 (show ell+d+1≤2*X by dsimp [X];omega)) (Nat.pow_le_pow_left (show W+1≤X by dsimp [X];omega) 2)).trans_eq (by ring)
    have pmax : 1+d*(d+3)*(6000*(H+1)^2)≤1+18000*X^4 := by
      have prod := Nat.mul_le_mul (show d≤X by dsimp [X];omega) (show d+3≤3*X by dsimp [X];omega)
      exact Nat.add_le_add_left ((Nat.mul_le_mul_right (6000*X^2) prod).trans_eq (by ring)) 1
    have smax : 1+(d+1)*(2000*(H+1)^2+1)≤1+2001*X^3 := by
      refine Nat.add_le_add_left ((Nat.mul_le_mul (show d+1≤X by dsimp [X];omega) (show 2000*X^2+1≤2001*X^2 by have := Nat.pow_pos xp (n:=2);omega)).trans_eq (by ring)) 1
    have h1 := Nat.one_le_pow 5 X xp
    have h3 := Nat.pow_le_pow_right xp (show 3≤5 by decide)
    have h4 := Nat.pow_le_pow_right xp (show 4≤5 by decide)
    change _ ≤ 2^18*X^5
    change (build [true] (rs.map Nat.bits) [encode 1] [true]).gates≤1+d*(d+3)*(6000*(H+1)^2) at cost
    have := rc.trans rmax;have := cost.trans pmax;have := outc.trans smax
    omega

private def lowWord (constant negative : SignedWord) (j : List Bool) : SignedWord×ℕ :=
  let z := equalWords j []
  let o := equalWords j [true]
  (if z.1 then constant else if o.1 then negative else encode 0,z.2+o.2+2)

private def secondField (d ell leading : List Bool) (xs : List (List Bool)) : List SignedWord×ℕ :=
  let s := missing d ell xs
  let negative := adjust (encode 0) leading false
  let c := affine s.1 negative.1 (encode 0)
  let js := binaryRange d
  let coeffs := traverse (lowWord c.1 negative.1) js.1
  (coeffs.1++[⟨false,leading⟩],s.2+negative.2+c.2+js.2+coeffs.2+js.1.length+5)

private theorem secondField_spec (d ell leading W : ℕ) (dp : 0<d) (prime : ell.Prime) (large : d<ell)
    (ew : ell≤W) (lw : leading.size≤W) :
    let xs := (List.range ell).map Nat.bits
    (secondField d.bits ell.bits leading.bits xs).1=(localCoeffs d ell 0 leading true).map encode ∧
    (∀ z∈localCoeffs d ell 0 leading true,z.natAbs.size≤6*(W+1)) ∧
    (secondField d.bits ell.bits leading.bits xs).2≤2^16*(W+1)^5 := by
  intro xs
  let sh := missingShift d ell
  let neg := -(leading:ℤ)
  let co := neg*sh
  have ds := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=d))).trans (show d≤W by omega)
  have es := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=ell))).trans ew
  have wp : 0<W := by omega
  obtain ⟨mv,mc⟩ := missing_spec d ell W prime.pos ds es
  change (missing d.bits ell.bits xs).1=sh.bits at mv
  obtain ⟨nv,nl,nc⟩ := adjust_spec (encode 0) leading.bits false
  simp only [decode_encode,signed,Bool.false_eq_true,if_false,value_bits,zero_sub] at nv
  change (adjust (encode 0) leading.bits false).1=encode neg at nv
  change (adjust (encode 0) leading.bits false).2=28*max 0 leading.bits.length+14 at nc
  rw [Nat.max_comm 0,Nat.max_zero,Nat.size_eq_bits_len] at nc
  have shw : sh.size≤W := (Nat.size_le_size (missingShift_avoids prime dp).1.le).trans es
  have negw : neg.natAbs.size≤W := by simpa [neg] using lw
  obtain ⟨cv,cl,cc⟩ := affine_spec sh.bits neg 0 ((Nat.size_eq_bits_len _).le.trans shw) negw (by simp)
  rw [value_bits,zero_add,mul_comm] at cv
  change (affine sh.bits (encode neg) (encode 0)).1=encode co at cv
  rw [cv] at cl
  change co.natAbs.bits.length≤6*(W+1) at cl
  rw [Nat.size_eq_bits_len] at cl
  let f (j : ℕ) : ℤ := if j=0 then co else if j=1 then neg else 0
  have coeff : localCoeffs d ell 0 leading true = (List.range d).map f++[(leading:ℤ)] := by
    simp only [localCoeffs,if_true,List.range_succ,List.map_append,List.map_singleton]
    congr 1
    apply List.map_inj_left.mpr;intro j hj
    simp only [if_neg (List.mem_range.mp hj).ne,f,co,neg,sh]
  obtain ⟨jv,jc⟩ := range_spec d W wp ds
  obtain ⟨outv,outc⟩ := traverse_spec (lowWord (encode co) (encode neg)) (List.range d) Nat.bits (fun j=>encode (f j)) (28*W+8) (by
    intro j hj
    have jw := (Nat.size_le_size (List.mem_range.mp hj).le).trans ds
    obtain ⟨z,zc⟩ := equalWords_spec j.bits []
    obtain ⟨o,oc⟩ := equalWords_spec j.bits [true]
    change (equalWords j.bits []).1=true ↔ value j.bits=0 at z
    change (equalWords j.bits [true]).1=true ↔ value j.bits=1 at o
    simp only [value_bits] at z o
    change (equalWords j.bits []).2=14*max j.bits.length 0+3 at zc
    change (equalWords j.bits [true]).2=14*max j.bits.length 1+3 at oc
    rw [Nat.size_eq_bits_len] at oc zc
    exact ⟨by simp only [lowWord,z,o,f];split <;> first | rfl | split <;> rfl,by dsimp only [lowWord];rw [oc,zc];omega⟩)
  simp only [secondField,mv,nv,cv,jv,outv,coeff,List.map_append,List.map_singleton,List.map_map,Function.comp_def,List.length_map,List.length_range]
  refine ⟨by simp [encode],?_,?_⟩
  · intro z hz
    rcases List.mem_append.mp hz with h|h
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
      dsimp only [f];split;exact cl;split;omega;simp
    · obtain rfl := List.mem_singleton.mp h
      simpa using (lw.trans (show W≤6*(W+1) by omega))
  · simp only [List.length_range] at outc
    change (missing d.bits ell.bits xs).2≤_ at mc
    let X := W+1
    have xp : 0<X := Nat.succ_pos _
    have mmax := mc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left (show ell+1≤X by dsimp [X];omega) 2)))
    have jc' := jc.trans (Nat.add_le_add_left (Nat.mul_le_mul (show d+1≤X by dsimp [X];omega) (show 11*W+8≤11*X by dsimp [X];omega)) 3)
    have oc' := outc.trans (Nat.add_le_add_left (Nat.mul_le_mul (show d≤X by dsimp [X];omega) (show 28*W+8+1≤29*X by dsimp [X];omega)) 1)
    change _≤2^16*X^5
    have h1 := Nat.one_le_pow 5 X xp
    have h2 := Nat.pow_le_pow_right xp (show 2≤5 by decide)
    have hx := Nat.le_self_pow (show 5≠0 by decide) X
    have wl : W≤X := Nat.le_succ _
    have dX : d≤X := by omega
    change _≤2000*X^2 at cc
    change _≤4096*X^2*X^3 at mmax
    ring_nf at mmax jc' oc'
    omega

/-- Construct all local polynomial coefficients from the four binary inputs.
Both fields scan the exact target residue interval. -/
def localWord (d ell m leading : List Bool) (side : Bool) : List SignedWord×ℕ :=
  let xs := binaryRange ell
  let field := if side then secondField d ell leading xs.1 else firstField d ell m leading xs.1
  (field.1,xs.2+field.2+1)



theorem localWord_spec (d ell m leading W : ℕ) (side : Bool)
    (dp : 0<d) (prime : ell.Prime) (large : d<ell) (ew : ell≤W) (mw : m.size≤W) (lw : leading.size≤W) :
    let H := 16^d*W; let out := localWord d.bits ell.bits m.bits leading.bits side
    out.1=(localCoeffs d ell m leading side).map encode ∧
    (∀ z∈localCoeffs d ell m leading side,z.natAbs.size≤6*(H+1)) ∧
    out.2≤2^19*(H+1)^5 := by
  intro H out
  have wp := prime.pos.trans_le ew
  have wh : W≤H := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
  obtain ⟨xv,xc⟩ := range_spec ell W wp ((Nat.size_le.mpr Nat.lt_two_pow_self).trans ew)
  let X := H+1
  have xp : 0<X := Nat.succ_pos _
  have h1 := Nat.one_le_pow 5 X xp
  have h2 := Nat.pow_le_pow_right xp (show 2≤5 by decide)
  have xpay := xc.trans (Nat.add_le_add_left (Nat.mul_le_mul (show ell+1≤X by dsimp [X];omega)
    (show 11*W+8≤11*X by dsimp [X];omega)) 3)
  ring_nf at xpay
  cases side with
  | false =>
    obtain ⟨v,w,c⟩ := firstField_spec d ell m leading W large ew mw lw
    simp only [out,localWord,Bool.false_eq_true,if_false,xv]
    exact ⟨v,w,by change _≤2^19*X^5;change _≤2^18*X^5 at c;omega⟩
  | true =>
    obtain ⟨v,w,c⟩ := secondField_spec d ell leading W dp prime large ew lw
    simp only [out,localWord,if_true,xv]
    have up := c.trans (Nat.mul_le_mul_left (2^16) (Nat.pow_le_pow_left (show W+1≤X by dsimp [X];omega) 5))
    exact ⟨v,fun z hz=>(w z hz).trans (by omega),by change _≤2^19*X^5;omega⟩

/-- At every scheduled target the complete local assembly and every signed
output coefficient fit the integer two-thirds bounds. -/
theorem fixed_localCoeffs {n ell : ℕ} (hn : 2≤n) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (side : Bool) :
    let b := n.log2+1; let s := TwoThirdsCost.scale b; let d := Fixed.d b
    let m := Fixed.rootBase n; let leading := leadingCoefficient n
    let out := localWord d.bits ell.bits m.bits leading.bits side
    out.1=(localCoeffs d ell m leading side).map encode ∧
    (∀ z∈localCoeffs d ell m leading side,z.natAbs.size≤2^(1010*s)) ∧
    out.2≤2^(5200*s) := by
  intro b s d m leading out
  let W := 2^(1001*s)
  have dp := Fixed.degree_pos (Nat.succ_pos n.log2)
  have vs := (Fixed.scale_bounds (Nat.succ_pos n.log2)).1
  change Fixed.v b≤ s at vs
  have hs : Fixed.h b≤ s := (Nat.le_mul_of_pos_left _ dp).trans vs
  have dh : d≤Fixed.h b := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have ds := dh.trans hs
  have sp : 0<s := dp.trans_le ds
  have zs : b.log2+1≤ s := (Nat.le_mul_of_pos_left _ dp).trans hs
  have es : ell≤W := (mem_dyadicTargets.mp target).2.2.trans (Nat.pow_le_pow_right (by decide) (by
    change 1000*Fixed.h b≤1001*s;omega))
  have m0 : m.size≤b+1 := Nat.size_le.mpr ((Fixed.rootBase_spec hn).2.2.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self b)))
  have ms : m.size≤W := m0.trans ((Nat.lt_log2_self (n:=b)).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  have ll := Nat.size_le_size (leading_size hn)
  rw [Nat.size_pow] at ll
  change leading.size≤111120*Fixed.v b+1 at ll
  have ls : leading.size≤W := calc
    _ ≤ 2^18*s := by norm_num;omega
    _ ≤ 2^18*2^s := Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
    _ = 2^(18+s) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨v,w,c⟩ := localWord_spec d ell m leading W side dp (mem_dyadicTargets.mp target).1 (target_gt_degree target) es ms ls
  let H := 16^d*W
  have He : H=2^(4*d+1001*s) := by
    change (2^4)^d*2^(1001*s)=_
    rw [←pow_mul,←pow_add]
  have Hs : H+1≤2^(1006*s) := calc
    _ ≤ 2^(4*d+1001*s+1) := by rw [He,pow_succ];have := Nat.one_le_two_pow (n:=4*d+1001*s);omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨v,fun z hz=>(w z hz).trans ?_,c.trans ?_⟩
  · calc 6*(H+1) ≤ 2^3*2^(1006*s) := Nat.mul_le_mul (by decide) Hs
         _ = 2^(3+1006*s) := (pow_add ..).symm
         _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  · calc 2^19*(H+1)^5 ≤ 2^19*(2^(1006*s))^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left Hs 5)
         _ = 2^(19+1006*s*5) := by rw [←pow_mul,←pow_add]
         _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

end Cogentic.BinaryLocalCoeffs

#print axioms Cogentic.BinaryLocalCoeffs.fixed_localCoeffs
