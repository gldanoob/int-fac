import Cogentic.ConstructorGridCost

namespace Cogentic.BinaryTargetBase
open BinaryDivision BinaryPivot BinaryPreliminary BinaryConstructorGrid BinaryCorrectedBase Construction

/-- From the local residue-polynomial coefficient words, construct the target
root product, combine both CRT constraints and round every coefficient. -/
def field (d A P ell leading mask : List Bool) (side : Bool) (localWords : List SignedWord) :
    List SignedWord × ℕ :=
  let target := targetProduct d A side
  let out := preliminaryWord d P ell leading target.den mask localWords target.coeffs
  (out.1,target.gates+out.2+1)

def localBase (n ell : ℕ) (side : Bool) :=
  localCoeffs (Fixed.d (n.log2+1)) ell (Fixed.rootBase n) (leadingCoefficient n) side

theorem fixed_preliminary {n ell k : ℕ} (hn : 2 ≤ n) (big : 3 ≤ Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool)
    (localWidth : ∀ z∈localBase n ell side,z.natAbs.size ≤ 2^(k*TwoThirdsCost.scale (n.log2+1))) :
    let b := n.log2+1
    let d := Fixed.d b
    let out := field d.bits (Fixed.A b).bits (primorial d).bits ell.bits (leadingCoefficient n).bits
      (binaryMask d).bits side ((localBase n ell side).map encode)
    out.1=(preliminaryBase n ell side).map encode ∧ out.2 ≤ 2^((445000+4*k)*TwoThirdsCost.scale b) := by
  intro b d out
  let S := TwoThirdsCost.scale b
  let P := primorial d
  let A := Fixed.A b
  let c := leadingCoefficient n
  let H := 2^(12000*S)
  let K := 111125+k
  let W := 2^(K*S)
  let T := 16^d*H
  have bp : 0<b := Nat.succ_pos _
  have zp : 0<Fixed.z b := Nat.succ_pos _
  have dp : 0<d := Fixed.degree_pos bp
  have vs : Fixed.v b ≤ S := (Fixed.scale_bounds bp).1
  have hs : Fixed.h b ≤ S := (Nat.le_mul_of_pos_left _ dp).trans vs
  have ds : d ≤ S := (Nat.le_mul_of_pos_right _ zp).trans hs
  have zs : Fixed.z b ≤ S := (Nat.le_mul_of_pos_left _ dp).trans hs
  have sp : 0<S := zp.trans_le zs
  have within {j l : ℕ} (h : j ≤ l) : 2^(j*S) ≤ 2^(l*S) :=
    Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_right S h)
  have sizeSelf (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
  have b1 : b+1 ≤ 2^S := Nat.succ_le_of_lt (Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two zs))
  have dx : d+1 ≤ 2^S := (Nat.succ_le_succ (Fixed.degree_le_bits b)).trans b1
  have ap : A ≤ 2^(10000*S) := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left 10000 hs)
  have amax : 2*A ≤ 2^(10001*S) := calc
    _ ≤ 2*2^(10000*S) := Nat.mul_le_mul_left _ ap
    _ = 2^(1+10000*S) := by rw [pow_add,pow_one]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have grid : (2*A+d*(2*A)).size ≤ H := (sizeSelf _).trans (calc
    2*A+d*(2*A) = (2*A)*(d+1) := by ring
    _ ≤ 2^(10001*S)*2^S := Nat.mul_le_mul amax dx
    _ = 2^(10002*S) := by rw [←pow_add]; congr 1; omega
    _ ≤ _ := within (by decide))
  have degreeH : 4*d ≤ H := calc
    4*d ≤ 2^2*2^S := Nat.mul_le_mul_left 4 ((Nat.le_succ d).trans dx)
    _ = 2^(2+S) := by rw [pow_add]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have HH : 3 ≤ H := by omega
  have dH := (sizeSelf d).trans (by omega : d ≤ H)
  have aH := (sizeSelf A).trans (ap.trans (within (by decide : 10000 ≤ 12000)))
  let gridOut := targetProduct d.bits A.bits side
  obtain ⟨nums,D,gv,gd,Dp,repr,gh,dh,gc⟩ := targetProduct_spec d A side (W:=H) dp HH dH
    ((sizeSelf _).trans degreeH) aH grid
  change gridOut.coeffs=_ at gv
  change gridOut.den=_ at gd
  change gridOut.gates ≤ _ at gc
  have tBound : T ≤ W := calc
    16^d*H = 2^(4*d+12000*S) := by
      change (2^4)^d*2^(12000*S)=_
      rw [←pow_mul,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by dsimp [K]; rw [Nat.add_mul]; omega)
  have wpos : 0<W := Nat.two_pow_pos _
  have stepBound : P+ell*P ≤ W := by
    have pp : P ≤ 2^(2*S) := (primorial_le_four_pow _).trans (by
      change (2^2)^d ≤ _; rw [←pow_mul]; exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
    have ep := (mem_dyadicTargets.mp target).2.2.trans
      (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left 1000 hs))
    have m := Nat.mul_le_mul ep pp
    rw [←pow_add,show 1000*S+2*S=1002*S by ring] at m
    have p' := pp.trans (within (by decide : 2 ≤ 1002))
    exact (Nat.add_le_add p' m).trans (calc
      _ = 2^(1+1002*S) := by rw [pow_add,pow_one,two_mul]
      _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by dsimp [K]; rw [Nat.add_mul]; omega))
  have lw : c.size ≤ W := (sizeSelf _).trans ((leading_size hn).trans (Nat.pow_le_pow_right Nat.zero_lt_two
    ((Nat.mul_le_mul_left 111120 vs).trans (Nat.mul_le_mul_right S (by dsimp [K]; omega)))))
  have pp : 0<P := primorial_pos _
  have ep := (mem_dyadicTargets.mp target).1.pos
  have d2 : 2 ≤ d := by change 3 ≤ d at big; omega
  have even : 2∣P := Nat.prime_two.dvd_primorial_iff.mpr d2
  have six : 6 ≤ P := (show 6=primorial 3 by decide).le.trans (primorial_mono big)
  have odd := (primorial_half_odd d2).coprime_two_left
  have getWidth (xs : List ℤ) (j : ℕ) (A : ℕ) (small : ∀ z∈xs,z.natAbs.size ≤ A) : (xs.getD j 0).natAbs.size ≤ A := by
    by_cases h : j<xs.length
    · rw [List.getD_eq_getElem _ _ h]; exact small _ (List.getElem_mem _)
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : xs.length ≤ j)]
  have reps (j) : (nums.getD j 0:ℚ)/D=(fromRoots ((targets d side).map ((A:ℚ)*·))).getD j 0 := by
    rw [←repr]; unfold BinaryRootProduct.fractions
    simpa only [Int.cast_zero,zero_div] using (List.getD_map (l:=nums) (d:=(0:ℤ)) (n:=j) (fun a : ℤ=>(a:ℚ)/D)).symm
  obtain ⟨outv,outc⟩ := preliminaryWord_spec (d:=d) (A:=A) (m:=Fixed.rootBase n) (ell:=ell) side
    even (by omega : 1<P/2) odd (target_primorial target) ep Dp lw (dh.trans tBound) stepBound nums
    (fun j _=>reps j) (fun j _=>⟨(getWidth _ _ _ localWidth).trans (within (by dsimp [K]; omega)),
       (getWidth _ _ _ gh).trans tBound⟩)
  rw [←gv,←gd] at outv outc
  let partialWord := preliminaryWord d.bits P.bits ell.bits c.bits gridOut.den (binaryMask d).bits
    ((localBase n ell side).map encode) gridOut.coeffs
  change partialWord.1=_ at outv
  change partialWord.2 ≤ _ at outc
  change partialWord.1=_ ∧ gridOut.gates+partialWord.2+1 ≤ _
  refine ⟨outv,?_⟩
  have dsW : d ≤ W := (Nat.le_succ d).trans (dx.trans (Nat.pow_le_pow_right Nat.zero_lt_two (by dsimp [K]; rw [Nat.add_mul]; omega)))
  have pw : P ≤ W := by omega
  have eprod := Nat.le_mul_of_pos_right ell pp
  have ew : ell ≤ W := by omega
  have cW : coefficientBudget P ell W ≤ 2^40*(W+W+1)*(W+1)^2 := by unfold coefficientBudget; gcongr
  have outCap := outc.trans (show _ ≤ 30*(W+1)^2+W+2*W+3+W*(2^40*(W+W+1)*(W+1)^2+6) by gcongr; exact (sizeSelf d).trans dsW)
  have gridCap := gc.trans (show _ ≤ 2^16*(W+1)^2*(W+1)^2 by gcongr)
  have total : gridOut.gates+partialWord.2+1 ≤ 2^44*(W+1)^4 := by
    nlinarith only [outCap,gridCap,Nat.zero_le (W^4),Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]
  have w1 : W+1 ≤ 2^((K+1)*S) := calc
    W+1 ≤ W+W := Nat.add_le_add_left wpos _
    _ = 2^(1+K*S) := by rw [pow_add,pow_one,two_mul]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by rw [Nat.succ_mul]; omega)
  refine total.trans ((Nat.mul_le_mul_left (2^44) (Nat.pow_le_pow_left w1 4)).trans ?_)
  rw [←pow_mul,←pow_add]
  exact Nat.pow_le_pow_right Nat.zero_lt_two (by dsimp [K]; nlinarith only [sp])


/-- Both target root products, preliminary CRT, and corrected polynomials. The
local residue-polynomial constructor and the input-wide schedule feed this call. -/
def run (n d A m P ell leading mask : List Bool) (left right : List SignedWord) :
    (List SignedWord × List SignedWord) × ℕ :=
  let l := field d A P ell leading mask false left
  let r := field d A P ell leading mask true right
  let result := pairFromPreliminary n m P ell leading l.1 r.1
  (result.1,l.2+r.2+result.2+1)

theorem fixed_corrected {n ell k : ℕ} (hn : 2 ≤ n) (big : 3 ≤ Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (localWidth : ∀ side, ∀ z∈localBase n ell side,z.natAbs.size ≤ 2^(k*TwoThirdsCost.scale (n.log2+1))) :
    let b := n.log2+1
    let d := Fixed.d b
    let out := run n.bits d.bits (Fixed.A b).bits (Fixed.rootBase n).bits (primorial d).bits ell.bits
      (leadingCoefficient n).bits (binaryMask d).bits ((localBase n ell false).map encode) ((localBase n ell true).map encode)
    out.1=(((BinaryPerturbation.correctedBase n ell false).map encode),
      ((BinaryPerturbation.correctedBase n ell true).map encode)) ∧
      out.2 ≤ 2^((610002+4*k)*TwoThirdsCost.scale b) := by
  intro b d out
  let S := TwoThirdsCost.scale b
  let P := primorial d
  let m := Fixed.rootBase n
  let c := leadingCoefficient n
  let result (s : Bool) := field d.bits (Fixed.A b).bits P.bits ell.bits c.bits (binaryMask d).bits s
    ((localBase n ell s).map encode)
  have ⟨lv,lc⟩ := fixed_preliminary hn big target false (localWidth false)
  have ⟨rv,rc⟩ := fixed_preliminary hn big target true (localWidth true)
  change (result false).1=_ at lv
  change (result true).1=_ at rv
  change (result false).2 ≤ _ at lc
  change (result true).2 ≤ _ at rc
  obtain ⟨v,cost⟩ := fixed_from_preliminary hn comp target sieved
  let corrected := pairFromPreliminary n.bits m.bits P.bits ell.bits c.bits (result false).1 (result true).1
  rw [←lv,←rv] at v cost
  change corrected.1=_ at v
  change corrected.2 ≤ _ at cost
  refine ⟨v,?_⟩
  change (result false).2+(result true).2+corrected.2+1 ≤ _
  let K := 610000+4*k
  let X := 2^(K*S)
  have u : 2^((445000+4*k)*S) ≤ X := Nat.pow_le_pow_right Nat.zero_lt_two
    (Nat.mul_le_mul_right S (by dsimp [K]; omega))
  have u' : 2^(610000*S) ≤ X := Nat.pow_le_pow_right Nat.zero_lt_two
    (Nat.mul_le_mul_right S (by dsimp [K]; omega))
  have sp : 0<S := (Nat.succ_pos _ : 0<Fixed.z b).trans_le ((Nat.le_mul_of_pos_left _
    (Fixed.degree_pos (Nat.succ_pos _))).trans ((Nat.le_mul_of_pos_left _
    (Fixed.degree_pos (Nat.succ_pos _))).trans (Fixed.scale_bounds (Nat.succ_pos _)).1))
  have Xp : 0<X := Nat.two_pow_pos _
  have both := Nat.add_le_add (Nat.add_le_add (lc.trans u) (rc.trans u)) (cost.trans u')
  calc (result false).2+(result true).2+corrected.2+1 ≤ 4*X := by omega
       _ = 2^(2+K*S) := by rw [pow_add]; rfl
       _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by dsimp [K]; nlinarith only [sp])

end Cogentic.BinaryTargetBase

#print axioms Cogentic.BinaryTargetBase.fixed_corrected
