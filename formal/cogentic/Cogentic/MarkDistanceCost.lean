import Cogentic.HelmertCost
import Cogentic.LogRoundingGates
import Cogentic.ReconstructionCost

namespace Cogentic.BinaryMarkDistance
open BinaryDivision BinaryPivot BinarySaturation BinaryReconstruction BinaryModularPower BinaryLogSeries

/-- Canonical reduced binary numerator and denominator. These are the inputs
to approxLog, whose truncation length depends on both individual bit lengths. -/
def reduced (p q : List Bool) : (List Bool × List Bool) × ℕ :=
  let g := gcdBits p q
  let x := divide g.1 p
  let y := divide g.1 q
  let u := canonical x.quotient
  let v := canonical y.quotient
  ((u.1,v.1),g.2+x.gates+y.gates+u.2+v.2)

private theorem quotient_value (d x : List Bool) (dp : 0<value d) :
    value (divide d x).quotient=value x/value d := by
  obtain ⟨_,_,eq,small,_⟩ := divide_spec d x dp
  conv_rhs => rw [eq,Nat.mul_comm (value (divide d x).quotient),Nat.mul_add_div dp,Nat.div_eq_of_lt small,Nat.add_zero]

theorem reduced_spec (p q : List Bool) (qp : 0<value q) (W : ℕ) (pw : p.length≤W) (qw : q.length≤W) :
    let f := (value p:ℚ)/value q
    let r := reduced p q
    r.1=(f.num.natAbs.bits,f.den.bits) ∧ r.2≤100*(W+1)^3 := by
  let g := gcdBits p q
  let x := divide g.1 p
  let y := divide g.1 q
  obtain ⟨gv,gl,gc⟩ := gcdBits_spec p q W pw qw
  change value g.1=_ at gv; change g.1.length≤_ at gl; change g.2≤_ at gc
  have count := (Elimination.gcdWithCount_le (value p) (value q)).trans
    (Nat.mul_le_mul_left 2 ((Nat.size_le.mpr (value_lt p)).trans pw))
  have gCost : g.2≤gcdBudget W := gc.trans (by unfold gcdBudget; gcongr)
  have gp : 0<value g.1 := gv ▸ Nat.gcd_pos_of_pos_right _ qp
  have xv := quotient_value g.1 p gp
  have yv := quotient_value g.1 q gp
  change value x.quotient=_ at xv; change value y.quotient=_ at yv
  have xc := (divide_spec g.1 p gp).2.2.2.2
  have yc := (divide_spec g.1 q gp).2.2.2.2
  have xl : x.quotient.length=p.length := BinaryIndexCap.quotient_length ..
  have yl : y.quotient.length=q.length := BinaryIndexCap.quotient_length ..
  have fx : (value p:ℚ)/value q=mkRat (value p) (value q) := by rw [Rat.mkRat_eq_div]; simp
  have xbits := (canonical_spec x.quotient).1
  have ybits := (canonical_spec y.quotient).1
  simp only [xv,yv,gv] at xbits ybits
  refine ⟨?_,?_⟩
  · change ((canonical x.quotient).1,(canonical y.quotient).1)=_
    rw [xbits,ybits,fx,Rat.num_mkRat,Rat.den_mkRat,if_neg qp.ne']
    simp [Nat.gcd_comm,←Int.natCast_ediv,qp.ne']
  · have cost (k : ℕ) (h : k≤W) : k*(10*(g.1.length+k)+1)≤W*(20*W+1) :=
      Nat.mul_le_mul h (by omega)
    have dx : x.gates≤W*(20*W+1) := xc.trans (cost _ pw)
    have dy : y.gates≤W*(20*W+1) := yc.trans (cost _ qw)
    change g.2+x.gates+y.gates+(canonical x.quotient).2+(canonical y.quotient).2≤_
    rw [(canonical_spec _).2,(canonical_spec _).2,xl,yl]
    unfold gcdBudget at gCost
    nlinarith only [gCost,dx,dy,pw,qw]

/-- Prepare the guarded argument from a signed grid numerator and positive
denominator. A failed distance test skips both gcd reduction and logarithm. -/
def prepare (a A : List Bool) (x : SignedWord) (q : List Bool) (low : ℕ) :
    Option (List Bool × List Bool) × ℕ :=
  let diff := cross ⟨false,a⟩ ⟨false,q⟩ x ⟨false,A⟩
  let den := multiply A q
  let top := List.replicate (low+1) false ++ diff.1.digits
  let pass := BinaryPowerScan.leBits den.1 top
  let work := diff.2+den.2+top.length+pass.2+1
  if pass.1 then
    let r := reduced diff.1.digits den.1
    (some r.1,work+r.2)
  else (none,work)

theorem prepare_spec (a A : List Bool) (x : SignedWord) (q : List Bool) (low W : ℕ)
    (Ap : 0<value A) (qp : 0<value q) (aw : a.length≤W) (Aw : A.length≤W)
    (xw : x.digits.length≤W) (qw : q.length≤W) (lw : low≤W) :
    let d := |(value a:ℚ)/value A-(x.decode:ℚ)/value q|
    let out := prepare a A x q low
    out.1=(if (1/2:ℚ)^(low+1)≤d then some (d.num.natAbs.bits,d.den.bits) else none) ∧
      out.2≤10000*(W+1)^3 := by
  let diff := cross ⟨false,a⟩ ⟨false,q⟩ x ⟨false,A⟩
  let den := multiply A q
  let top := List.replicate (low+1) false++diff.1.digits
  let pass := BinaryPowerScan.leBits den.1 top
  let d := |(value a:ℚ)/value A-(x.decode:ℚ)/value q|
  obtain ⟨ev,ec⟩ := cross_spec ⟨false,a⟩ ⟨false,q⟩ x ⟨false,A⟩ W aw qw xw Aw
  change diff.1.decode=(value a:ℤ)*value q-x.decode*value A at ev; change diff.2≤_ at ec
  obtain ⟨dv,dl,dc⟩ := multiply_spec A q
  change value den.1=_ at dv; change den.1.length≤_ at dl; change den.2≤_ at dc
  have dp : 0<value den.1 := dv ▸ Nat.mul_pos qp Ap
  have pos : 0<(value den.1:ℚ) := by exact_mod_cast dp
  have mag (u : SignedWord) : u.decode.natAbs=value u.digits := by
    cases u with | mk b ds => cases b <;> simp [SignedWord.decode,signed]
  have ratio : d=(value diff.1.digits:ℚ)/value den.1 := by
    have raw : (value a:ℚ)/value A-(x.decode:ℚ)/value q=(diff.1.decode:ℚ)/value den.1 := by
      rw [ev,dv]; push_cast; field_simp
    rw [show d=|_| from rfl,raw,abs_div,abs_of_pos pos]
    exact congrArg (·/(value den.1:ℚ)) (by rw [←mag,←Int.cast_natCast,←Int.abs_eq_natAbs,Int.cast_abs])
  have rl : diff.1.digits.length≤3*W+1 :=
    BinaryReconstruction.cross_length ⟨false,a⟩ ⟨false,q⟩ x ⟨false,A⟩ aw qw xw Aw
  have dw : den.1.length≤3*W+1 := by omega
  have tl : top.length=low+1+diff.1.digits.length := by simp [top]
  have tv : value top=2^(low+1)*value diff.1.digits := BinaryPowerScan.value_low_zeros ..
  have ⟨cmp,cc⟩ := BinaryPowerScan.leBits_spec den.1 top
  change (pass.1=true ↔ _) at cmp; change pass.2=_ at cc
  have guard : pass.1=true ↔ (1/2:ℚ)^(low+1)≤d := by
    rw [cmp,tv,ratio,one_div_pow,div_le_div_iff₀ (by positivity) pos,one_mul,mul_comm (value diff.1.digits:ℚ)]
    exact_mod_cast Iff.rfl
  obtain ⟨re,rc⟩ := reduced_spec diff.1.digits den.1 dp (3*W+1) rl dw
  change (reduced diff.1.digits den.1).1=_ at re
  rw [←ratio] at re
  let work := diff.2+den.2+top.length+pass.2+1
  have dwk : den.2≤16*W^2 := dc.trans (calc _ ≤ W*(W+5*(W+2*W)) := by gcongr
                                             _ = _ := by ring)
  have pwk : pass.2≤7*(4*W+2)+1 := by rw [cc]; omega
  have workBound : work+100*(3*W+1+1)^3≤10000*(W+1)^3 := by
    dsimp only [work]; nlinarith only [ec,dwk,pwk,tl,lw,rl]
  let result : Option (List Bool × List Bool) × ℕ := if pass.1 then
    (some (reduced diff.1.digits den.1).1,work+(reduced diff.1.digits den.1).2) else (none,work)
  change result.1=(if (1/2:ℚ)^(low+1)≤d then some (d.num.natAbs.bits,d.den.bits) else none) ∧ result.2≤_
  dsimp only [result]
  by_cases good : pass.1=true
  · rw [if_pos good,if_pos (guard.mp good)]
    exact ⟨congrArg some re,(Nat.add_le_add_left rc work).trans workBound⟩
  · rw [if_neg good,if_neg (mt guard.mpr good)]
    exact ⟨rfl,(Nat.le_add_right work _).trans workBound⟩

/-- Guard, reduce and evaluate the logarithm directly from a signed rational root. -/
def markLog (a A : List Bool) (x : SignedWord) (q : List Bool) (low bits : ℕ) : Option ℤ × ℕ :=
  let args := prepare a A x q low
  match args.1 with
  | none => (none,args.2)
  | some (u,v) =>
    let y := binaryLog u v bits
    (some y.1,args.2+y.2)

theorem markLog_spec (a A : List Bool) (x : SignedWord) (q : List Bool) (low bits W : ℕ)
    (Ap : 0<value A) (qp : 0<value q) (aw : a.length≤W) (Aw : A.length≤W)
    (xw : x.digits.length≤W) (qw : q.length≤W) (lw : low≤W) :
    let d := |(value a:ℚ)/value A-(x.decode:ℚ)/value q|
    let H := bits+d.num.natAbs.size+d.den.size+8
    let f := markLog a A x q low bits
    f.1.map (fun (z:ℤ)=>(z:ℚ)/2^bits)=RootLogs.markLog (value A) (value a) ((x.decode:ℚ)/value q) low bits ∧
      f.2≤10000*(W+1)^3+16777216*H^5 := by
  intro d H f
  let args := prepare a A x q low
  obtain ⟨eq,cost⟩ := prepare_spec a A x q low W Ap qp aw Aw xw qw lw
  change args.1=(if (1/2:ℚ)^(low+1)≤d then some _ else none) at eq
  change args.2≤_ at cost
  by_cases good : (1/2:ℚ)^(low+1)≤d
  · rw [if_pos good] at eq
    have up : 0<d.num.natAbs := by
      have dp : 0<d := (show (0:ℚ)<(1/2:ℚ)^(low+1) by positivity).trans_le good
      exact Nat.pos_of_ne_zero (by simpa only [Int.natAbs_ne_zero,Rat.num_ne_zero] using dp.ne')
    obtain ⟨val,work⟩ := binaryLog_spec up d.pos bits
    have ff : f=(some (binaryLog d.num.natAbs.bits d.den.bits bits).1,args.2+(binaryLog d.num.natAbs.bits d.den.bits bits).2) := by
      simp only [f,markLog,←show args=prepare a A x q low from rfl,eq] ; rfl
    rw [ff]
    refine ⟨?_,?_⟩
    · change some ((_:ℚ)/2^bits)=(if (1/2:ℚ)^(low+1)≤d then some _ else none)
      rw [if_pos good]; exact congrArg some val
    · exact Nat.add_le_add cost work
  · rw [if_neg good] at eq
    have ff : f=(none,args.2) := by
      simp only [f,markLog,←show args=prepare a A x q low from rfl,eq]
    rw [ff]
    change none=(if (1/2:ℚ)^(low+1)≤d then some _ else none) ∧ args.2≤_
    rw [if_neg good]
    exact ⟨rfl,cost.trans (Nat.le_add_right ..)⟩

end Cogentic.BinaryMarkDistance
