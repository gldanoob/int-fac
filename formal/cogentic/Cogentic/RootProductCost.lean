import Cogentic.PreliminaryRoundingCost

namespace Cogentic.BinaryRootProduct
open BinaryDivision BinaryPivot BinaryPerturbation BinaryPreliminary Construction

/-- Ascending integral coefficients of the update by D*X-r. -/
def hom (D r : ℕ) : ℤ → List ℤ → List ℤ
  | prev,[] => [(D:ℤ)*prev]
  | prev,c::cs => ((D:ℤ)*prev-(r:ℤ)*c)::hom D r c cs

@[simp] theorem hom_length (D r : ℕ) (x : ℤ) (cs : List ℤ) : (hom D r x cs).length=cs.length+1 := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih => simp [hom,ih]

def applyFactor (D r : List Bool) : SignedWord → List SignedWord → List SignedWord × ℕ
  | prev,[] =>
    let a := affine D prev (encode 0)
    ([a.1],a.2+1)
  | prev,c::cs =>
    let a := affine D prev (encode 0)
    let b := affine r c (encode 0)
    let head := adjust a.1 b.1.digits b.1.negative
    let tail := applyFactor D r c cs
    (head.1::tail.1,a.2+b.2+head.2+tail.2+3)

theorem applyFactor_spec (D r : ℕ) (prev : ℤ) (cs : List ℤ) {W : ℕ} (wp : 0<W)
    (dw : D.size ≤ W) (rw' : r.size ≤ W) (pw : prev.natAbs.size ≤ W) (height : ∀ z∈cs,z.natAbs.size ≤ W) :
    let s := applyFactor D.bits r.bits (encode prev) (cs.map encode)
    s.1=(hom D r prev cs).map encode ∧ (∀ z∈hom D r prev cs,z.natAbs.size ≤ 16*W) ∧
      s.2 ≤ (cs.length+1)*(5000*(W+1)^2) := by
  induction cs generalizing prev with
  | nil =>
    let a := affine D.bits (encode prev) (encode 0)
    obtain ⟨av,al,ac⟩ := affine_spec D.bits prev 0 ((Nat.size_eq_bits_len _).le.trans dw) pw (by simp)
    simp only [value_bits,zero_add] at av
    change a.1=_ at av
    change a.1.digits.length ≤ _ at al
    change a.2 ≤ _ at ac
    rw [av] at al
    change ((D:ℤ)*prev).natAbs.bits.length ≤ _ at al
    rw [Nat.size_eq_bits_len] at al
    change [a.1]=_ ∧ _ ∧ a.2+1 ≤ _
    refine ⟨by rw [av]; rfl,by simpa only [hom,List.mem_singleton,forall_eq] using (show _ ≤ 16*W from al.trans (by omega)),?_⟩
    simp only [List.length_nil,Nat.zero_add,one_mul]
    nlinarith only [ac,Nat.zero_le W,Nat.zero_le (W^2)]
  | cons c cs ih =>
    have cw := height c (by simp)
    obtain ⟨tail,th,tc⟩ := ih c cw (fun z hz=>height z (by simp [hz]))
    let a := affine D.bits (encode prev) (encode 0)
    let b := affine r.bits (encode c) (encode 0)
    let head := adjust a.1 b.1.digits b.1.negative
    obtain ⟨av,al,ac⟩ := affine_spec D.bits prev 0 ((Nat.size_eq_bits_len _).le.trans dw) pw (by simp)
    obtain ⟨bv,bl,bc⟩ := affine_spec r.bits c 0 ((Nat.size_eq_bits_len _).le.trans rw') cw (by simp)
    change a.1=_ at av
    change b.1=_ at bv
    change a.1.digits.length ≤ _ at al
    change b.1.digits.length ≤ _ at bl
    change a.2 ≤ _ at ac
    change b.2 ≤ _ at bc
    simp only [value_bits,zero_add] at av bv
    obtain ⟨hv,hl,hc⟩ := adjust_spec a.1 b.1.digits b.1.negative
    change head.1=encode (a.1.decode-b.1.decode) at hv
    change head.1.digits.length ≤ _ at hl
    change head.2=_ at hc
    rw [av,bv,decode_encode,decode_encode] at hv
    rw [hv] at hl
    change ((D:ℤ)*prev-(r:ℤ)*c).natAbs.bits.length ≤ _ at hl
    rw [Nat.size_eq_bits_len] at hl
    change head.1::(applyFactor D.bits r.bits (encode c) (cs.map encode)).1=_ ∧ _ ∧
      a.2+b.2+head.2+(applyFactor D.bits r.bits (encode c) (cs.map encode)).2+3 ≤ _
    simp only [hom,List.map_cons,List.length_cons,hv,tail]
    refine ⟨trivial,?_,?_⟩
    · intro z hz; rcases List.mem_cons.mp hz with h|h
      · subst z; omega
      · exact th z h
    · rw [hc,Nat.succ_mul (cs.length+1)]
      have hmax := max_le al bl
      nlinarith only [ac,bc,tc,hmax,Nat.zero_le (W^2),Nat.zero_le W]

def fractions (cs : List ℤ) (D : ℕ) : List ℚ := cs.map fun a : ℤ =>(a:ℚ)/D

private theorem hom_fractions (D r den : ℕ) (dp : 0<D) (yp : 0<den) (prev : ℤ) (cs : List ℤ) :
    fractions (hom D r prev cs) (den*D) =
      linear ((r:ℚ)/D) ((prev:ℚ)/den) (fractions cs den) := by
  have Dn : (D:ℚ)≠0 := by exact_mod_cast dp.ne'
  have yn : (den:ℚ)≠0 := by exact_mod_cast yp.ne'
  induction cs generalizing prev with
  | nil => simp only [fractions,hom,List.map_singleton,List.map_nil,linear,List.cons.injEq,and_true]; push_cast; field_simp
  | cons c cs ih =>
    change ((↑((D:ℤ)*prev-(r:ℤ)*c):ℚ)/↑(den*D))::fractions (hom D r c cs) (den*D) =
      (((prev:ℚ)/den)-(r:ℚ)/D*((c:ℚ)/den))::linear ((r:ℚ)/D) ((c:ℚ)/den) (fractions cs den)
    rw [ih]
    congr 1
    push_cast
    field_simp

structure Product where
  coeffs : List SignedWord
  den : List Bool
  gates : ℕ

/-- Maintain one denominator for all coefficients throughout the product. -/
def build (D : List Bool) : List (List Bool) → List SignedWord → List Bool → Product
  | [],cs,den => ⟨cs,den,1⟩
  | r::rs,cs,den =>
    let p := applyFactor D r (encode 0) cs
    let q := natProduct den D
    let tail := build D rs p.1 q.1
    ⟨tail.coeffs,tail.den,p.2+q.2+tail.gates+3⟩

theorem build_spec (D den : ℕ) (rs : List ℕ) (cs : List ℤ) {W : ℕ} (wp : 0<W)
    (dp : 0<D) (yp : 0<den) (dw : D.size ≤ W) (yw : den.size ≤ W)
    (width : ∀ r∈rs,r.size ≤ W) (height : ∀ z∈cs,z.natAbs.size ≤ W) :
    let result := build D.bits (rs.map Nat.bits) (cs.map encode) den.bits
    let T := 16^rs.length*W
    ∃ (out : List ℤ) (y : ℕ), result.coeffs=out.map encode ∧ result.den=y.bits ∧ 0<y ∧
      fractions out y = (rs.map fun r : ℕ =>(r:ℚ)/D).foldl (fun p a=>linear a 0 p) (fractions cs den) ∧
      (∀ z∈out,z.natAbs.size ≤ T) ∧ y.size ≤ T ∧
      result.gates ≤ 1+rs.length*(rs.length+cs.length+2)*(6000*(T+1)^2) := by
  induction rs generalizing cs den W with
  | nil => exact ⟨cs,den,rfl,rfl,yp,rfl,by simpa using height,by simpa using yw,by simp [build]⟩
  | cons r rs ih =>
    have rw' := width r (by simp)
    obtain ⟨pv,ph,pc⟩ := applyFactor_spec D r 0 cs wp dw rw' (by simp) height
    obtain ⟨qv,ql,qc⟩ := natProduct_spec den D yw dw
    have yl : (den*D).size ≤ 16*W := by rw [qv,Nat.size_eq_bits_len] at ql; omega
    have bigger : W ≤ 16*W := by omega
    obtain ⟨out,y,cv,ev,py,repr,ch,wh,wc⟩ := ih (den:=den*D) (cs:=hom D r 0 cs) (W:=16*W) (by omega)
      (Nat.mul_pos yp dp) (dw.trans bigger) yl (fun k hk=>(width k (by simp [hk])).trans bigger) ph
    let p := applyFactor D.bits r.bits (encode 0) (cs.map encode)
    let q := natProduct den.bits D.bits
    change p.1=_ at pv
    change p.2 ≤ _ at pc
    change q.1=_ at qv
    change q.2 ≤ _ at qc
    have size : 16^(r::rs).length*W=16^rs.length*(16*W) := by rw [List.length_cons,pow_succ,Nat.mul_assoc]
    rw [←pv,←qv] at cv ev wc
    refine ⟨out,y,cv,ev,py,?_,by simpa only [size] using ch,by simpa only [size] using wh,?_⟩
    · simpa only [List.map_cons,List.foldl_cons,hom_fractions D r den dp yp,Int.cast_zero,zero_div] using repr
    · change p.2+q.2+(build D.bits (rs.map Nat.bits) p.1 q.1).gates+3 ≤ _
      rw [hom_length] at wc
      rw [size,List.length_cons]
      let T := 16^rs.length*(16*W)
      have tp : 0<16^rs.length := Nat.pow_pos (by decide)
      have Wle : W ≤ T := bigger.trans (Nat.le_mul_of_pos_left _ tp)
      have lo : 5000*(W+1)^2 ≤ 5000*(T+1)^2 := by gcongr
      have co := pc.trans (Nat.mul_le_mul_left (cs.length+1) lo)
      have qo := qc.trans (show 30*(W+1)^2 ≤ 30*(T+1)^2 by gcongr)
      change (build D.bits (rs.map Nat.bits) p.1 q.1).gates ≤ 1+rs.length*(rs.length+(cs.length+1)+2)*(6000*(T+1)^2) at wc
      change _ ≤ 1+(rs.length+1)*(rs.length+1+cs.length+2)*(6000*(T+1)^2)
      nlinarith only [co,qo,wc,Nat.zero_le (rs.length*T^2),Nat.zero_le (rs.length*T),Nat.zero_le rs.length,
        Nat.zero_le (cs.length*T^2),Nat.zero_le (cs.length*T),Nat.zero_le cs.length,Nat.zero_le (T^2),Nat.zero_le T]

/-- The product represents precisely the rational polynomial used by fromRoots.
Both numerator and denominator widths grow by at most a factor 16 per root. -/
theorem root_product (D : ℕ) (rs : List ℕ) {W : ℕ} (wp : 0<W) (dp : 0<D)
    (dw : D.size ≤ W) (width : ∀ r∈rs,r.size ≤ W) :
    let result := build D.bits (rs.map Nat.bits) [encode 1] [true]
    let T := 16^rs.length*W
    ∃ (out : List ℤ) (y : ℕ), result.coeffs=out.map encode ∧ result.den=y.bits ∧ 0<y ∧
      fractions out y=fromRoots (rs.map fun r : ℕ =>(r:ℚ)/D) ∧ (∀ z∈out,z.natAbs.size ≤ T) ∧
      y.size ≤ T ∧ result.gates ≤ 1+rs.length*(rs.length+3)*(6000*(T+1)^2) := by
  have h := build_spec D 1 rs [1] wp dp (by decide) dw wp width (by simpa)
  simpa only [List.length_singleton,Nat.add_assoc,List.map_singleton,one_add_one_eq_two,
    show (1:ℕ).bits=[true] by decide,show (1:ℕ)+2=3 by decide, fractions,Int.cast_one,Nat.cast_one,div_one,fromRoots] using h

/-- Integral roots leave denominator one throughout, for any stored polynomial. -/
theorem build_one_den (rs : List (List Bool)) (cs : List SignedWord) :
    (build [true] rs cs [true]).den=[true] := by
  induction rs generalizing cs with
  | nil => rfl
  | cons r rs ih =>
    change (build [true] rs _ (natProduct [true] [true]).1).den=_
    have unit : (natProduct [true] [true]).1=[true] := by decide
    rw [unit,ih]

end Cogentic.BinaryRootProduct

#print axioms Cogentic.BinaryRootProduct.root_product
