import Cogentic.Construction

namespace Cogentic.Construction

private def mass : List ℚ → ℚ
  | [] => 0
  | x::xs => |x|+mass xs

private theorem mass_nonneg (p : List ℚ) : 0 ≤ mass p := by
  induction p with
  | nil => rfl
  | cons x xs ih => exact add_nonneg (abs_nonneg _) ih

private theorem mass_linear (r prev : ℚ) (p : List ℚ) :
    mass (linear r prev p) ≤ |prev|+(1+|r|)*mass p := by
  induction p generalizing prev with
  | nil => simp [mass,linear]
  | cons a as ih =>
    have step := ih a
    have head := abs_add_le prev (-(r*a))
    rw [←sub_eq_add_neg, abs_neg] at head
    rw [abs_mul] at head
    simp only [linear,mass]
    linarith [step]

private theorem mass_roots {roots : List ℚ} {A : ℕ} (bound : ∀ r ∈ roots, |r| ≤ A) :
    mass (fromRoots roots) ≤ (1+(A:ℚ))^roots.length := by
  have walk (xs : List ℚ) (p : List ℚ) (h : ∀ r ∈ xs, |r| ≤ A) :
      mass (xs.foldl (fun q r => linear r 0 q) p) ≤ mass p*(1+(A:ℚ))^xs.length := by
    induction xs generalizing p with
    | nil => simp
    | cons r rs ih =>
      have step := ih (linear r 0 p) (fun q hq => h q (by simp [hq]))
      have val := mass_linear r 0 p
      have rb := h r (by simp)
      simp only [List.foldl_cons,List.length_cons,pow_succ]
      apply step.trans
      have small : mass (linear r 0 p) ≤ (1+(A:ℚ))*mass p :=
        (by simpa using val : mass (linear r 0 p) ≤ (1+|r|)*mass p).trans
          (mul_le_mul_of_nonneg_right (by linarith) (mass_nonneg _))
      apply (mul_le_mul_of_nonneg_right small (by positivity)).trans_eq
      ring
  simpa [fromRoots,mass] using walk roots [1] bound

private theorem coeff_le_mass (p : List ℚ) (j : ℕ) : |p.getD j 0| ≤ mass p := by
  induction p generalizing j with
  | nil => simp [mass]
  | cons a as ih =>
    cases j with
    | zero => simpa [mass] using mass_nonneg as
    | succ j => exact (ih j).trans (le_add_of_nonneg_left (abs_nonneg a))

private theorem target_bound {degree A : ℕ} (second : Bool) :
    ∀ r ∈ (targets degree second).map ((A:ℚ)*·), |r| ≤ A := by
  intro r hr
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  have sd := List.mem_range.mp hs
  have dp : (0:ℚ) < degree := by exact_mod_cast (by omega : 0 < degree)
  have divpos : (0:ℚ) < 4*degree := by positivity
  have raw : (2*s + if second then 2 else 1 : ℕ) ≤ 4*degree := by cases second <;> simp <;> omega
  have one : (((2*s + if second then 2 else 1 : ℕ):ℚ)/(4*degree)) ≤ 1 := by
    apply (div_le_one divpos).mpr; exact_mod_cast raw
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg A), abs_of_nonneg (by positivity)]
  simpa using mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (α := ℚ) A)

theorem preliminary_height {degree A m P ell leading : ℕ} (stepPos : 0 < P*ell) (second : Bool)
    {c : ℤ} (mem : c ∈ preliminary degree A m P ell leading second) :
    c.natAbs ≤ leading*(1+A)^degree+P*ell := by
  let roots := (targets degree second).map ((A:ℚ)*·)
  have bound (j : ℕ) : |(fromRoots roots).getD j 0| ≤ (1+(A:ℚ))^degree := by
    apply (coeff_le_mass _ j).trans
    simpa [roots,targets] using mass_roots (target_bound (A := A) (degree := degree) second)
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp mem
  let low := crt 2 (P/2) (bitCoeff (binaryMask degree) j) (if j=0 then 1 else 0)
  let residue := crt P ell low (modulusResidue ((localCoeffs degree ell m leading second).getD j 0) ell)
  let target := (leading:ℚ)*(fromRoots roots).getD j 0
  have err := nearest_error stepPos residue target
  have val : |target| ≤ leading*(1+(A:ℚ))^degree := by
    dsimp [target]; rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left (bound _) (Nat.cast_nonneg _)
  have triangle := abs_add_le ((nearest (P*ell) residue target:ℚ)-target) target
  rw [sub_add_cancel] at triangle
  have out : |(nearest (P*ell) residue target:ℚ)| ≤ leading*(1+(A:ℚ))^degree+ (P:ℚ)*ell := by
    push_cast at err
    linarith [mul_nonneg (Nat.cast_nonneg (α := ℚ) P) (Nat.cast_nonneg ell)]
  change (nearest (P*ell) residue target).natAbs ≤ _
  have integer : |nearest (P*ell) residue target| ≤ (↑(leading*(1+A)^degree+P*ell) : ℤ) := by exact_mod_cast out
  rw [←Int.natCast_natAbs] at integer
  exact_mod_cast integer

theorem corrected_height {m step t cap : ℕ} (hm : 0 < m) (p : List ℤ)
    (bounded : ∀ c ∈ p, c.natAbs ≤ cap) : ∀ c ∈ correctLower m step t p, c.natAbs ≤ cap+step*m := by
  induction p generalizing t with
  | nil => simp [correctLower]
  | cons a as ih =>
    intro c hc
    rcases List.mem_cons.mp hc with eq | mem
    · subst c
      have sz := Int.natAbs_add_le a (-((step:ℤ)*(t%m:ℕ)))
      simp only [←sub_eq_add_neg,Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast] at sz
      exact sz.trans (Nat.add_le_add (bounded a (by simp)) (Nat.mul_le_mul_left _ (Nat.mod_lt t hm).le))
    · exact ih (fun c hc => bounded c (by simp [hc])) c mem

private theorem perturb_height {step m u v cap : ℕ} (p : List ℤ)
    (bounded : ∀ c ∈ p, c.natAbs ≤ cap) :
    ∀ c ∈ perturb step m u v p, c.natAbs ≤ cap+step*(m+1)*(u+v) := by
  intro c hc
  cases p with
  | nil => cases hc
  | cons a as =>
    cases as with
    | nil => exact (bounded c hc).trans (by omega)
    | cons b bs =>
      cases bs with
      | nil => exact (bounded c hc).trans (by omega)
      | cons k ks =>
        have a0 := bounded a (by simp)
        have b0 := bounded b (by simp)
        have k0 := bounded k (by simp)
        simp only [perturb,List.mem_cons] at hc
        rcases hc with rfl | rfl | rfl | tail
        · have e := Int.natAbs_add_le a (-((step:ℤ)*m*u))
          simp only [←sub_eq_add_neg,Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast] at e
          exact e.trans (by simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one] ; omega)
        · have e := Int.natAbs_add_le b ((step:ℤ)*((u:ℤ)-m*v))
          have inner := Int.natAbs_add_le (u:ℤ) (-((m:ℤ)*v))
          simp only [←sub_eq_add_neg,Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast] at inner
          simp only [Int.natAbs_mul,Int.natAbs_natCast] at e
          apply e.trans (Nat.add_le_add b0 ((Nat.mul_le_mul_left step inner).trans _))
          simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.mul_assoc]; omega
        · have e := Int.natAbs_add_le k ((step:ℤ)*v)
          simp only [Int.natAbs_mul,Int.natAbs_natCast] at e
          exact e.trans (by simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]; omega)
        · exact (bounded _ (by simp [tail])).trans (by omega)

private theorem full_height {n m step leading A degree u v : ℕ} (hm : 0 < m) (low : List ℤ)
    (bounded : ∀ c ∈ low, c.natAbs ≤ leading*(1+A)^degree+step) :
    ∀ c ∈ perturb step m u v (corrected n m step leading low),
      c.natAbs ≤ leading*(1+A)^degree+step+step*m+step*(m+1)*(u+v) := by
  apply perturb_height
  intro c hc
  rcases List.mem_append.mp hc with lower | last
  · exact corrected_height hm low bounded _ lower
  · obtain rfl := List.mem_singleton.mp last
    simp only [Int.natAbs_natCast]
    have pos : 0 < (1+A)^degree := Nat.pow_pos (by omega)
    have := Nat.le_mul_of_pos_right leading pos
    omega

private theorem clog_three_upper (q : ℕ) : 3^(max 1 (Nat.clog 3 q)) ≤ 3*(q+1) := by
  by_cases small : q ≤ 1
  · have h := Nat.clog_le_of_le_pow (b := 3) (y := 0) (by simpa using small)
    have : Nat.clog 3 q = 0 := by omega
    simp [this]
  · have q1 : 1 < q := by omega
    have p := Nat.clog_pos (by decide : 1 < 3) q1
    have h := Nat.pow_pred_clog_lt_self (by decide : 1 < 3) q1
    rw [max_eq_right p,show Nat.clog 3 q = (Nat.clog 3 q).pred+1 from (Nat.succ_pred_eq_of_pos p).symm,
      Nat.pow_succ]
    omega

private theorem rootBase_bound {n : ℕ} (hn : 2 ≤ n) :
    let b := n.log2+1
    Fixed.rootBase n ≤ 2^(8*Fixed.v b) := by
  let b := n.log2+1
  have degree := Fixed.degree_pos (b := b) (by simp [b])
  have high := (Fixed.degree_floor b).2
  have upper : b ≤ (8*Fixed.v b)*Fixed.d b := by
    apply high.le.trans
    calc (Fixed.d b+1)^3*Fixed.z b ≤ (2*Fixed.d b)^3*Fixed.z b :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 3)
         _ = _ := by unfold Fixed.v Fixed.h; ring
  have target : n ≤ (2^(8*Fixed.v b))^Fixed.d b := by
    rw [← Nat.pow_mul]
    exact Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) upper)
  have low := (Fixed.rootBase_spec hn).1
  change (Fixed.rootBase n-1)^Fixed.d b < n at low
  have less := (Nat.pow_lt_pow_iff_left degree.ne').mp (low.trans_le target)
  change Fixed.rootBase n ≤ 2^(8*Fixed.v b)
  omega

private def Within (v k x : ℕ) : Prop := x ≤ 2^(k*v)

private theorem Within.mul {v a b x y : ℕ} (ha : Within v a x) (hb : Within v b y) :
    Within v (a+b) (x*y) := by
  unfold Within at *; rw [Nat.add_mul,Nat.pow_add]; exact Nat.mul_le_mul ha hb

private theorem Within.weaken {v a b x : ℕ} (ha : Within v a x) (h : a ≤ b) : Within v b x :=
  ha.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ h))

private theorem Within.add {v k x y : ℕ} (hv : 0 < v) (hx : Within v k x) (hy : Within v k y) :
    Within v (k+1) (x+y) := by
  unfold Within at *
  calc x+y ≤ 2^(k*v)*2 := by omega
       _ = 2^(k*v+1) := (Nat.pow_succ ..).symm
       _ ≤ _ := Nat.pow_le_pow_right (by decide) (by rw [Nat.add_mul]; omega)

private theorem data_bounds {n : ℕ} (hn : 2 ≤ n) :
    let b := n.log2+1; let v := Fixed.v b
    Within v 111120 (leadingCoefficient n) ∧ Within v 10001 ((1+Fixed.A b)^Fixed.d b) ∧
    Within v 2 (primorial (Fixed.d b)) ∧ Within v 8 (Fixed.rootBase n) ∧
    Within v 110004 (4*b^2*Fixed.U b*Fixed.A b) := by
  let b := n.log2+1
  let v := Fixed.v b
  let P := primorial (Fixed.d b)
  let T := 6*Fixed.K₁ b*Fixed.B b*P*Fixed.rootBase n*(b^2*Fixed.U b*Fixed.A b)
  let base := (P/2)*(Fixed.A b)^Fixed.d b
  have bp : 0 < b := by simp [b]
  have dp := Fixed.degree_pos bp
  have zp : 0 < Fixed.z b := by simp [Fixed.z]
  have hd : Fixed.d b ≤ Fixed.h b := Nat.le_mul_of_pos_right _ zp
  have zh : Fixed.z b ≤ Fixed.h b := Nat.le_mul_of_pos_left _ dp
  have hv : Fixed.h b ≤ v := Nat.le_mul_of_pos_left _ dp
  have vp : 0 < v := by omega
  have within4 : Within v 2 4 := Nat.pow_le_pow_right (n := 2) (i := 2) (by decide) (by omega)
  have within6 : Within v 3 6 := (show 6 ≤ 2^3 by decide).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have Psmall : Within v 2 P := by
    apply (primorial_le_four_pow _).trans
    change (2^2)^Fixed.d b ≤ 2^(2*v)
    rw [← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have Ksmall : Within v 100 (Fixed.K₁ b) := Nat.pow_le_pow_right (by decide) (by omega)
  have Bsmall : Within v 1000 (Fixed.B b) := Nat.pow_le_pow_right (by decide) (show 1000*Fixed.h b ≤ 1000*v by omega)
  have Asmall : Within v 10000 (Fixed.A b) := Nat.pow_le_pow_right (by decide) (by omega)
  have Usmall : Within v 100000 (Fixed.U b) := Nat.le_refl _
  have bsmall : Within v 1 b := Nat.lt_log2_self.le.trans
    (Nat.pow_le_pow_right (by decide) (show Fixed.z b ≤ 1*v by omega))
  have b2small : Within v 2 (b^2) := by simpa [sq] using bsmall.mul bsmall
  have msmall : Within v 8 (Fixed.rootBase n) := rootBase_bound hn
  have box := (b2small.mul Usmall).mul Asmall
  have tsmall : Within v 111115 T := by
    exact ((((within6.mul Ksmall).mul Bsmall).mul Psmall).mul msmall).mul box
  have tpos : 0 < T := by
    dsimp [T,P,Fixed.K₁,Fixed.B,Fixed.U,Fixed.A,Fixed.rootBase]
    have pp := primorial_pos (Fixed.d b)
    have bb := bp
    positivity
  have qle : (T-1)/base+1 ≤ T := by have := Nat.div_le_self (T-1) base; omega
  have pow3 : 3^(max 1 (Nat.clog 3 ((T-1)/base+1))) ≤ 8*T :=
    (clog_three_upper _).trans (by omega)
  have eighth : Within v 3 8 := Nat.pow_le_pow_right (n := 2) (i := 3) (by decide) (by omega)
  have leading : Within v 111120 (leadingCoefficient n) := by
    have smallP : Within v 2 (P/2) := (Nat.div_le_self _ _).trans Psmall
    exact (Nat.mul_le_mul_left (P/2) pow3).trans (smallP.mul (eighth.mul tsmall))
  have Abig : 0 < Fixed.A b := Nat.pow_pos (by decide)
  have factor : (1+Fixed.A b)^Fixed.d b ≤ (2*Fixed.A b)^Fixed.d b :=
    Nat.pow_le_pow_left (by omega) _
  have Apow : Within v 10001 ((1+Fixed.A b)^Fixed.d b) := by
    apply factor.trans
    change (2^1*2^(10000*Fixed.h b))^Fixed.d b ≤ 2^(10001*v)
    rw [← Nat.pow_add,← Nat.pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    have dv : Fixed.h b*Fixed.d b = v := Nat.mul_comm ..
    rw [Nat.add_mul,Nat.mul_assoc,dv]; omega
  exact ⟨leading,Apow,Psmall,msmall,by
    change Within v 110004 (4*b^2*Fixed.U b*Fixed.A b)
    exact ((within4.mul b2small).mul Usmall).mul Asmall⟩

/-- Both coefficient lists pass the advertised height cap throughout the actual box. -/
theorem box_height {n ell u₀ u₁ v₀ v₁ : ℕ} (hn : 2 ≤ n)
    (big : 130000 ≤ Fixed.d (n.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b := n.log2+1
      u₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ u₁ ≤ 2*b^2*Fixed.U b ∧
      v₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ v₁ ≤ 2*b^2*Fixed.U b) :
    let pair := construct n ell u₀ u₁ v₀ v₁
    (∀ c ∈ pair.first, c.natAbs ≤ 2^(n.log2+1)) ∧ (∀ c ∈ pair.second, c.natAbs ≤ 2^(n.log2+1)) := by
  let b := n.log2+1
  let v := Fixed.v b
  let P := primorial (Fixed.d b)
  let m := Fixed.rootBase n
  let lead := leadingCoefficient n
  obtain ⟨lb,ab,pb,mb,wb⟩ := data_bounds hn
  change Within v 111120 lead at lb
  change Within v 2 P at pb
  change Within v 8 m at mb
  change Within v 10001 ((1+Fixed.A b)^Fixed.d b) at ab
  change Within v 110004 (4*b^2*Fixed.U b*Fixed.A b) at wb
  have dp : 0 < Fixed.d b := by change 130000 ≤ Fixed.d b at big; omega
  have hv : Fixed.h b ≤ v := Nat.le_mul_of_pos_left _ dp
  have vp : 0 < v := by change 0 < Fixed.d b*(Fixed.d b*Fixed.z b); unfold Fixed.z; positivity
  have ellData := mem_dyadicTargets.mp target
  have eb : Within v 1000 ell := ellData.2.2.trans
    (Nat.pow_le_pow_right (by decide) (show 1000*Fixed.h b ≤ 1000*v by omega))
  have sb := pb.mul eb
  have b1 : Within v 8 1 := Nat.one_le_two_pow
  have m1 := Within.add vp mb b1
  have l₁ := Within.add vp (lb.mul ab) (sb.weaken (by decide : 2+1000 ≤ 111120+10001))
  have l₂ := Within.add vp l₁ ((sb.mul mb).weaken (by decide : 2+1000+8 ≤ 111120+10001+1))
  have total : 121124*v ≤ b := by
    calc 121124*v ≤ Fixed.d b * v := Nat.mul_le_mul_right _ (by change 130000 ≤ Fixed.d b at big; omega)
         _ = (Fixed.d b)^3*Fixed.z b := by dsimp [v,Fixed.v,Fixed.h]; ring
         _ ≤ b := (Fixed.degree_floor b).1
  have pos : 0 < P*ell := Nat.mul_pos (primorial_pos _) ellData.1.pos
  have mp : 0 < m := by simp [m,Fixed.rootBase]
  have ap : 0 < Fixed.A b := Nat.pow_pos (by decide)
  have side (second : Bool) (a z : ℕ) (ha : a ≤ 2*b^2*Fixed.U b*Fixed.A b) (hz : z ≤ 2*b^2*Fixed.U b) :
      ∀ c ∈ perturb (P*ell) m a z (corrected n m (P*ell) lead
        (preliminary (Fixed.d b) (Fixed.A b) m P ell lead second)), c.natAbs ≤ 2^b := by
    have zz := hz.trans (Nat.le_mul_of_pos_right (2*b^2*Fixed.U b) ap)
    have sum : Within v 110004 (a+z) := (show a+z ≤ 4*b^2*Fixed.U b*Fixed.A b by
      calc a+z ≤ 2*b^2*Fixed.U b*Fixed.A b+2*b^2*Fixed.U b*Fixed.A b := Nat.add_le_add ha zz
           _ = _ := by ring).trans wb
    have l₃ := Within.add vp l₂ (((sb.mul m1).mul sum).weaken
      (by decide : 2+1000+(8+1)+110004 ≤ 111120+10001+1+1))
    intro c hc
    exact (full_height mp _ (fun _ h => preliminary_height pos second h) c hc).trans
      (l₃.trans (Nat.pow_le_pow_right (by decide) total))
  exact ⟨side false u₀ u₁ box.1 box.2.1,side true v₀ v₁ box.2.2.1 box.2.2.2⟩

private theorem horner_cast {R : Type*} [CommRing R] (x : ℤ) (p : List ℤ) :
    (Marking.horner (x:R) p).1 = ((eval x p : ℤ):R) := by
  induction p with
  | nil => simp [Marking.horner,eval]
  | cons c cs ih => simp [Marking.horner,eval,ih]

private theorem perturb_shape {step m u v : ℕ} (p : List ℤ) (hp : 4 ≤ p.length) :
    (perturb step m u v p).length = p.length ∧ (perturb step m u v p).getLast? = p.getLast? := by
  rcases p with _ | ⟨a,as⟩ <;> simp only [List.length_nil,List.length_cons] at hp
  · omega
  rcases as with _ | ⟨b,bs⟩ <;> simp only [List.length_nil,List.length_cons] at hp
  · omega
  rcases bs with _ | ⟨c,cs⟩ <;> simp only [List.length_nil,List.length_cons] at hp
  · omega
  rcases cs with _ | ⟨d,ds⟩ <;> simp_all [perturb]

theorem shape {n ell : ℕ} (big : 3 ≤ Fixed.d (n.log2+1)) (second : Bool) (a z : ℕ) :
    let b := n.log2+1
    let P := primorial (Fixed.d b)
    let m := Fixed.rootBase n
    let c := leadingCoefficient n
    let cs := perturb (P*ell) m a z (corrected n m (P*ell) c (preliminary (Fixed.d b) (Fixed.A b) m P ell c second))
    cs.length = Fixed.d b+1 ∧ cs.getLast? = some (c:ℤ) := by
  let b := n.log2+1
  let P := primorial (Fixed.d b)
  let m := Fixed.rootBase n
  let c := leadingCoefficient n
  let base := corrected n m (P*ell) c (preliminary (Fixed.d b) (Fixed.A b) m P ell c second)
  have len : base.length = Fixed.d b+1 := by simp [base,corrected,preliminary]
  have last : base.getLast? = some (c:ℤ) := by simp [base,corrected]
  have ready : 4 ≤ base.length := by rw [len]; change 3 ≤ Fixed.d b at big; omega
  have h := perturb_shape (step := P*ell) (m := m) (u := a) (v := z) base ready
  exact ⟨h.1.trans len,h.2.trans last⟩

/-- These are the same two decidable polynomial guards evaluated by Step 1. -/
theorem box_polynomialGuards {n ell u₀ u₁ v₀ v₁ : ℕ} (hn : 2 ≤ n)
    (big : 130000 ≤ Fixed.d (n.log2+1)) (composite : ¬n.Prime)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1))
      (Fixed.rootBase n) = Option.none)
    (box : let b := n.log2+1
      u₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ u₁ ≤ 2*b^2*Fixed.U b ∧
      v₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ v₁ ≤ 2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
    s.polynomialGuard s.first ∧ s.polynomialGuard s.second := by
  have ht := box_height hn big target box
  have roots := roots_of_surviving_input hn composite target none u₀ u₁ v₀ v₁
  have degree : 3 ≤ Fixed.d (n.log2+1) := by omega
  have first := shape (ell := ell) degree false u₀ u₁
  have second := shape (ell := ell) degree true v₀ v₁
  have root (p : List ℤ) (h : (n:ℤ) ∣ eval (Fixed.rootBase n:ℤ) p) :
      (Marking.horner (Fixed.rootBase n : ZMod n) p).1 = 0 := by
    simpa using (horner_cast (R := ZMod n) (Fixed.rootBase n) p).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr h)
  exact ⟨⟨first.1,first.2,ht.1,root _ roots.1⟩,⟨second.1,second.2,ht.2,root _ roots.2⟩⟩

private theorem leading_ok {n : ℕ} (big : 3 ≤ Fixed.d (n.log2+1))
    (cop : (primorial (Fixed.d (n.log2+1))).Coprime n) :
    1 ≤ leadingCoefficient n ∧ (leadingCoefficient n).Coprime n := by
  let P := primorial (Fixed.d (n.log2+1))
  have two : 2 ∣ P := Nat.prime_two.dvd_primorial_iff.mpr (by omega)
  have three : 3 ∣ P := Nat.prime_three.dvd_primorial_iff.mpr big
  have hp : 0 < P := primorial_pos _
  have hhalf : 0 < P/2 := Nat.div_pos (Nat.le_of_dvd hp two) (by decide)
  have h3 : Nat.Coprime 3 n := cop.of_dvd_left three
  have pHalf : (P/2).Coprime n := cop.of_dvd_left (Nat.div_dvd_of_dvd two)
  unfold leadingCoefficient
  refine ⟨Nat.mul_pos hhalf (Nat.pow_pos (by decide)),Nat.coprime_mul_iff_left.mpr ⟨pHalf,h3.pow_left _⟩⟩

/-- Every sufficiently large composite surviving the preliminary divisor search
    passes the *entire* Step 1 input guard at every tested point. -/
theorem box_inputGuard {n ell u₀ u₁ v₀ v₁ : ℕ} (hn : 2 ≤ n)
    (big : 130000 ≤ Fixed.d (n.log2+1)) (composite : ¬n.Prime)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1))
      (Fixed.rootBase n) = Option.none)
    (box : let b := n.log2+1
      u₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ u₁ ≤ 2*b^2*Fixed.U b ∧
      v₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ v₁ ≤ 2*b^2*Fixed.U b) :
    (TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)).guard := by
  let b := n.log2+1
  have pair := box_polynomialGuards hn big composite target none box
  have guards := Fixed.stage_guards hn (by omega : 10004 ≤ Fixed.d (n.log2+1))
  obtain ⟨n9,d10,b10,k16,b20⟩ := guards.parameters
  obtain ⟨nh,mh,ah,bh,kh⟩ := guards.heights
  have cop := (Nat.coprime_mul_iff_left.mp (surviving_coprime hn composite target none)).1
  obtain ⟨lead,leadCoprime⟩ := leading_ok (by omega : 3 ≤ Fixed.d (n.log2+1)) cop
  have ap : 1 ≤ Fixed.A b := Nat.one_le_two_pow
  have hpos : 0 < Fixed.h b := Nat.mul_pos (Fixed.degree_pos (by simp [b])) (by simp [Fixed.z])
  have a2 : 2 ≤ Fixed.A b := Nat.pow_le_pow_right (n := 2) (i := 1) (by decide)
    (show 1 ≤ 10000*Fixed.h b by omega)
  have mp : 2 ≤ Fixed.rootBase n := (show 2 ≤ 4*Fixed.d b*Fixed.A b by
    have dPos := Fixed.degree_pos (b := b) (by simp [b])
    have := Nat.le_mul_of_pos_right (4*Fixed.d b) ap
    omega).trans guards.markRange
  exact ⟨n9,mp,(by decide : 9 ≤ 10).trans d10,lead,a2,(by decide : 4 ≤ 20).trans b20,k16,b10,nh,leadCoprime,mh,ah,bh,kh,pair⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.box_polynomialGuards
