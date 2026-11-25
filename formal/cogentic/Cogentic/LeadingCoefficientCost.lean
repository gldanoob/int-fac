import Cogentic.PrimorialCost
import Cogentic.PowerScanCost
import Cogentic.ConstructionHeight

namespace Cogentic.BinaryLeading
open BinaryDivision BinaryPivot BinarySaturation BinaryPreliminary CandidateRuntime Construction

/-- Multiply canonical binary words, charging a traversal and canonicalization
at every list cell. -/
def product : List (List Bool) → List Bool × ℕ
  | [] => ([true],1)
  | a::xs =>
    let tail := product xs
    let out := natProduct a tail.1
    (out.1,tail.2+out.2+1)

private theorem product_spec (xs : List ℕ) (W : ℕ) (pos : ∀ a∈xs,0<a) (bound : xs.prod ≤ W) :
    (product (xs.map Nat.bits)).1=xs.prod.bits ∧
      (product (xs.map Nat.bits)).2 ≤ 1+xs.length*(30*(W+1)^2+1) := by
  induction xs with
  | nil => exact ⟨by decide,by simp [product]⟩
  | cons a xs ih =>
    have ap := pos a (by simp)
    have tailp : ∀ x∈xs,0<x := fun x hx=>pos x (by simp [hx])
    have pp := List.prod_pos tailp
    simp only [List.prod_cons] at bound
    have small := (Nat.le_mul_of_pos_left _ ap).trans bound
    have aa := (Nat.le_mul_of_pos_right _ pp).trans bound
    obtain ⟨v,c⟩ := ih tailp small
    obtain ⟨e,_,w⟩ := natProduct_spec a xs.prod ((Nat.size_le.mpr Nat.lt_two_pow_self).trans aa)
      ((Nat.size_le.mpr Nat.lt_two_pow_self).trans small)
    simp only [List.map_cons,product,v,List.prod_cons,List.length_cons,Nat.succ_mul xs.length]
    exact ⟨e,by omega⟩

/-- Compare base times a ternary power with the threshold. The input-word
length supplies enough fuel for the first passing power. -/
def firstPower (T base : List Bool) : List Bool → List Bool → List Bool × ℕ
  | [],a => (a,1)
  | _::rest,a =>
    let probe := natProduct base a
    let ok := leq T probe.1
    if ok.1 then (a,probe.2+ok.2+1) else
      let next := natProduct a [true,true]
      let tail := firstPower T base rest next.1
      (tail.1,probe.2+ok.2+next.2+tail.2+2)

private theorem threshold {T base : ℕ} (tp : 0<T) (bp : 0<base) (j : ℕ) (jp : 1 ≤ j) :
    T ≤ base*3^j ↔ max 1 (Nat.clog 3 ((T-1)/base+1)) ≤ j := by
  rw [max_le_iff,and_iff_right jp,Nat.clog_le_iff_le_pow (by decide)]
  have h : (T-1)/base < 3^j ↔ T-1 < 3^j*base := Nat.div_lt_iff_lt_mul bp
  rw [Nat.mul_comm (3^j) base] at h
  omega

set_option maxHeartbeats 1200000 in
private theorem firstPower_spec {T base W : ℕ} (tp : 0<T) (bp : 0<base)
    (tb : T.size ≤ W) (bs : base.size ≤ W) (room : 3*(T+1) ≤ W)
    (fuel : List Bool) {j : ℕ} (jp : 1 ≤ j) (small : j ≤ max 1 (Nat.clog 3 ((T-1)/base+1)))
    (space : max 1 (Nat.clog 3 ((T-1)/base+1)) ≤ j+fuel.length) :
    let G := max 1 (Nat.clog 3 ((T-1)/base+1))
    let out := firstPower T.bits base.bits fuel (3^j).bits
    out.1=(3^G).bits ∧ out.2 ≤ 1+fuel.length*(100*(W+1)^2) := by
  induction fuel generalizing j with
  | nil =>
    simp only [List.length_nil,Nat.add_zero] at space
    rw [le_antisymm small space]; simp [firstPower]
  | cons head rest ih =>
    let G := max 1 (Nat.clog 3 ((T-1)/base+1))
    have qsmall : (T-1)/base+1 ≤ T := by have := Nat.div_le_self (T-1) base; omega
    have size : (3^j).size ≤ W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
      ((Nat.pow_le_pow_right (by decide) small).trans ((clog_three_upper _).trans
        ((Nat.mul_le_mul_left 3 (Nat.succ_le_succ qsmall)).trans room)))
    let probe := natProduct base.bits (3^j).bits
    let ok := leq T.bits probe.1
    have ⟨pv,pl,pc⟩ := natProduct_spec base (3^j) bs size
    change probe.1=_ at pv
    change probe.1.length ≤ _ at pl
    change probe.2 ≤ _ at pc
    obtain ⟨s,c⟩ := leq_spec T.bits probe.1
    change (ok.1=true ↔ _) at s
    change ok.2=_ at c
    rw [pv,value_bits,value_bits,threshold tp bp j jp] at s
    rw [Nat.size_eq_bits_len] at c
    have oc : ok.2 ≤ 21*W+1 := by omega
    have three : (3:ℕ).size ≤ W := by change 2 ≤ _; omega
    let next := natProduct (3^j).bits [true,true]
    obtain ⟨nv,_,nc⟩ := natProduct_spec (3^j) 3 size three
    change next.1=_ at nv
    change next.2 ≤ _ at nc
    rw [←pow_succ] at nv
    let tail := firstPower T.bits base.bits rest next.1
    have call : firstPower T.bits base.bits (head::rest) (3^j).bits =
        if ok.1 then ((3^j).bits,probe.2+ok.2+1) else
          (tail.1,probe.2+ok.2+next.2+tail.2+2) := rfl
    change (firstPower T.bits base.bits (head::rest) (3^j).bits).1=(3^G).bits ∧
      (firstPower T.bits base.bits (head::rest) (3^j).bits).2 ≤ _
    rw [call,List.length_cons,Nat.succ_mul rest.length]
    cases hit : ok.1 with
    | true =>
      have eq := le_antisymm small (s.mp hit)
      exact ⟨congrArg (fun i=>(3^i:ℕ).bits) eq,by change probe.2+ok.2+1 ≤ _; nlinarith only [pc,oc,Nat.zero_le (rest.length*(100*(W+1)^2))]⟩
    | false =>
      have neq : ¬G ≤ j := fun h=>by simpa [hit] using s.mpr h
      have js : j+1 ≤ G := by omega
      change G ≤ j+(rest.length+1) at space
      obtain ⟨v,g⟩ := ih (j:=j+1) (by omega) js (by omega)
      change (firstPower T.bits base.bits rest next.1).1=_ ∧ probe.2+ok.2+next.2+
        (firstPower T.bits base.bits rest next.1).2+2 ≤ _
      rw [nv]
      exact ⟨v,by nlinarith only [pc,oc,nc,g]⟩

def ternaryBound (T base : List Bool) := firstPower T base T [true,true]

theorem ternaryBound_spec {T base W : ℕ} (tp : 0<T) (bp : 0<base)
    (tb : T.size ≤ W) (bs : base.size ≤ W) (room : 3*(T+1) ≤ W) :
    (ternaryBound T.bits base.bits).1=(3^(max 1 (Nat.clog 3 ((T-1)/base+1)))).bits ∧
    (ternaryBound T.bits base.bits).2 ≤ 1+T.size*(100*(W+1)^2) := by
  have q : (T-1)/base+1 ≤ T := by have := Nat.div_le_self (T-1) base; omega
  have upper : T ≤ 3^T.size := (Nat.lt_size_self T).le.trans (Nat.pow_le_pow_left (by decide) _)
  have bd := (Nat.clog_le_iff_le_pow (by decide : 1<3)).mpr (q.trans upper)
  obtain ⟨v,w⟩ := firstPower_spec tp bp tb bs room T.bits (j:=1) le_rfl (le_max_left ..) (by rw [Nat.size_eq_bits_len]; omega)
  simpa only [ternaryBound,pow_one,show (3:ℕ).bits=[true,true] by decide,Nat.size_eq_bits_len] using And.intro v w

/-- The degree, binary input length and fixed schedule words are shared with
the rest of the driver. The product threshold is traversed once. -/
def run (b d K₁ B U A m P : List Bool) : List Bool × ℕ :=
  let threshold := product [[false,true,true],K₁,B,P,m,b,b,U,A]
  let fuel := tokens d
  let power := BinaryPowerScan.exactPower A fuel.1.length
  let normalized := canonical power.1
  let base := natProduct P.tail normalized.1
  let ternary := ternaryBound threshold.1 base.1
  let out := natProduct P.tail ternary.1
  (out.1,threshold.2+fuel.2+power.2+normalized.2+base.2+ternary.2+out.2+7)


/-- The constructor's leading coefficient from its other shared binary
parameters. No numerical search over n or enumeration of possible leading
coefficients is needed. -/
theorem fixed_leading {n : ℕ} (hn : 2 ≤ n) (big : 2 ≤ Fixed.d (n.log2+1)) :
    let b := n.log2+1
    let d := Fixed.d b
    let out := run b.bits d.bits (Fixed.K₁ b).bits (Fixed.B b).bits (Fixed.U b).bits
      (Fixed.A b).bits (Fixed.rootBase n).bits (primorial d).bits
    out.1=(leadingCoefficient n).bits ∧ out.2 ≤ 2^(600025*TwoThirdsCost.scale b) := by
  intro b d out
  let S := TwoThirdsCost.scale b
  let P := primorial d
  let m := Fixed.rootBase n
  let A := Fixed.A b
  let U := Fixed.U b
  let B := Fixed.B b
  let K := Fixed.K₁ b
  let T := 6*K*B*P*m*(b^2*U*A)
  let base := (P/2)*A^d
  let X := 2^(120000*S)
  let W := 4*(X+1)^2
  have bp : 0<b := Nat.succ_pos _
  have dp : 0<d := Fixed.degree_pos bp
  have zp : 0<Fixed.z b := Nat.succ_pos _
  have vs : Fixed.v b ≤ S := (Fixed.scale_bounds bp).1
  have hs : Fixed.h b ≤ S := (Nat.le_mul_of_pos_left _ dp).trans vs
  have ds : d ≤ S := (Nat.le_mul_of_pos_right _ zp).trans hs
  have zs : Fixed.z b ≤ S := (Nat.le_mul_of_pos_left _ dp).trans hs
  have sp : 0<S := zp.trans_le zs
  have within {i j : ℕ} (h : i ≤ j) : 2^(i*S) ≤ 2^(j*S) := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_right S h)
  have sizeSelf (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self
  have pi := primorial_pos d
  have mp : 0<m := by simp [m,Fixed.rootBase]
  have ap : 0<A := Nat.two_pow_pos _
  have kp : 0<K := Nat.two_pow_pos _
  have up : 0<U := Nat.two_pow_pos _
  have bP : 0<B := Nat.two_pow_pos _
  have Tpos : 0<T := by dsimp only [T]; positivity
  have six : 6 ≤ 2^(3*S) := (by decide : 6 ≤ 2^3).trans (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have kc : K ≤ 2^(100*S) := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ hs)
  have bc : B ≤ 2^(1000*S) := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ hs)
  have pc : P ≤ 2^(2*S) := (primorial_le_four_pow _).trans (by change (2^2)^d ≤ _; rw [←pow_mul]; exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have mc : m ≤ 2^(8*S) := (rootBase_bound hn).trans (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ vs))
  have bb : b ≤ 2^S := Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right Nat.zero_lt_two zs)
  have uc : U ≤ 2^(100000*S) := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ vs)
  have ac : A ≤ 2^(10000*S) := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ hs)
  have Tbound : T ≤ X := calc
    T ≤ 2^(3*S)*2^(100*S)*2^(1000*S)*2^(2*S)*2^(8*S)*((2^S)^2*2^(100000*S)*2^(10000*S)) := by dsimp only [T]; gcongr
    _ = 2^(111115*S) := by simp only [←pow_mul,←pow_add]; congr 1; ring
    _ ≤ _ := within (by decide)
  have fullA : A^d ≤ 2^(10000*S) := by
    change (2^(10000*Fixed.h b))^d ≤ _
    rw [←pow_mul,Nat.mul_assoc,show Fixed.h b*d=Fixed.v b from Nat.mul_comm ..]
    exact Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ vs)
  have baseCap : base ≤ X := calc
    (P/2)*A^d ≤ 2^(2*S)*2^(10000*S) := Nat.mul_le_mul ((Nat.div_le_self ..).trans pc) fullA
    _ = 2^(10002*S) := by rw [←pow_add]; congr 1; ring
    _ ≤ _ := within (by decide)
  have AP := (sizeSelf A).trans (ac.trans (within (by decide : 10000 ≤ 120000)))
  have dx : d ≤ X := (Fixed.degree_le_bits b).trans (bb.trans (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
  have xw : X ≤ W := by dsimp [W]; nlinarith only [Nat.zero_le (X^2)]
  have px : P/2 ≤ X := (Nat.div_le_self ..).trans (pc.trans (within (by decide)))
  have two : 2 ≤ P := (show primorial 2=2 by decide).ge.trans (primorial_mono big)
  have hp : 0<P/2 := by omega
  have basePos : 0<base := Nat.mul_pos hp (Nat.pow_pos ap)
  let xs := [6,K,B,P,m,b,b,U,A]
  have prodT : xs.prod=T := by simp only [xs,List.prod_cons,List.prod_nil,mul_one,T]; ring
  obtain ⟨pt,ptc⟩ := product_spec xs X (by simp [xs,kp,bP,pi,mp,bp,up,ap]) (by rwa [prodT])
  rw [prodT] at pt
  let thresh := product [[false,true,true],K.bits,B.bits,P.bits,m.bits,b.bits,b.bits,U.bits,A.bits]
  change thresh.1=T.bits at pt
  change thresh.2 ≤ 1+9*(30*(X+1)^2+1) at ptc
  let fuel := tokens d.bits
  obtain ⟨fl,fc⟩ := token_spec d.bits
  change fuel.1.length=_ at fl
  change fuel.2 ≤ _ at fc
  simp only [value_bits,Nat.size_eq_bits_len] at fl fc
  let pow := BinaryPowerScan.exactPower A.bits fuel.1.length
  let canon := canonical pow.1
  obtain ⟨v,l,g⟩ := BinaryPowerScan.exactPower_spec A.bits d X ((Nat.size_eq_bits_len A).le.trans AP)
  rw [←fl] at v l g
  change value pow.1=_ at v
  change pow.1.length ≤ _ at l
  change pow.2 ≤ _ at g
  rw [fl,value_bits] at v
  rw [fl] at l g
  obtain ⟨nv,nc⟩ := canonical_spec pow.1
  change canon.1=_ at nv
  change canon.2=_ at nc
  rw [v] at nv
  have pHalf : P.bits.tail=(P/2).bits := (Nat.div2_bits_eq_tail _).symm
  let baseW := natProduct P.bits.tail canon.1
  obtain ⟨bv,_,bg⟩ := natProduct_spec (P/2) (A^d) ((sizeSelf _).trans px)
    ((sizeSelf _).trans (fullA.trans (within (by decide : 10000 ≤ 120000))))
  rw [←pHalf,←nv] at bv bg
  change baseW.1=base.bits at bv
  change baseW.2 ≤ _ at bg
  have space : 3*(T+1) ≤ W := by dsimp [W]; nlinarith only [Tbound,Nat.zero_le (X^2)]
  obtain ⟨tv,tg⟩ := ternaryBound_spec Tpos basePos ((sizeSelf _).trans (Tbound.trans xw))
    ((sizeSelf _).trans (baseCap.trans xw)) space
  rw [←pt,←bv] at tv tg
  let tern := ternaryBound thresh.1 baseW.1
  let a := 3^(max 1 (Nat.clog 3 ((T-1)/base+1)))
  change tern.1=a.bits at tv
  change tern.2 ≤ _ at tg
  have ts : (T-1)/base+1 ≤ T := by have := Nat.div_le_self (T-1) base; omega
  have aw : a ≤ W := (clog_three_upper _).trans ((Nat.mul_le_mul_left _ (Nat.succ_le_succ ts)).trans space)
  obtain ⟨ev,_,eg⟩ := natProduct_spec (P/2) a ((sizeSelf _).trans (px.trans xw)) ((sizeSelf _).trans aw)
  rw [←pHalf,←tv] at ev eg
  change (natProduct P.bits.tail tern.1).1=_ ∧ thresh.2+fuel.2+pow.2+canon.2+baseW.2+tern.2+
    (natProduct P.bits.tail tern.1).2+7 ≤ _
  refine ⟨ev,?_⟩
  have lo := l.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (2*X) dx) 1)
  have po := g.trans (show _ ≤ X*(X*(6*(1+2*X*X)+10*X)) by gcongr)
  have tc := tg.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ((sizeSelf _).trans Tbound)) 1)
  have sz := (sizeSelf d).trans dx
  have total : thresh.2+fuel.2+pow.2+canon.2+baseW.2+tern.2+(natProduct P.bits.tail tern.1).2+7 ≤ 2^16*(X+1)^5 := by
    dsimp only [W] at tc eg
    nlinarith only [ptc,fc,po,nc,lo,bg,tc,eg,sz,dx,Nat.zero_le X,Nat.zero_le (X^2),
      Nat.zero_le (X^3),Nat.zero_le (X^4),Nat.zero_le (X^5)]
  have xx : X+1 ≤ 2^(120001*S) := calc
    X+1 ≤ X+X := Nat.add_le_add_left Nat.one_le_two_pow _
    _ = 2^(1+120000*S) := by rw [pow_add,pow_one,two_mul]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  refine total.trans ((Nat.mul_le_mul_left (2^16) (Nat.pow_le_pow_left xx 5)).trans ?_)
  rw [←pow_mul,←pow_add]; exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

end Cogentic.BinaryLeading

#print axioms Cogentic.BinaryLeading.fixed_leading
