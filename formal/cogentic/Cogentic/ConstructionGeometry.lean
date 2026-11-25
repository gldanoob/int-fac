import Cogentic.ConstructionTarget
import Cogentic.RootLogs

namespace Cogentic.Construction

/-- The ideal coefficient list before nearest-progression rounding. -/
def targetCoefficients (d A : ℕ) (side : Bool) :=
  fromRoots ((targets d side).map ((A:ℚ)*·))

private theorem preliminary_error {d j : ℕ} (A m P ell c : ℕ) (side : Bool) (ij : j < d)
    (step : 0 < P*ell) :
    |(((preliminary d A m P ell c side).getD j 0 : ℤ):ℚ) -
      c*(targetCoefficients d A side).getD j 0| ≤ (P:ℚ)*ell/2 := by
  simp only [preliminary,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,ij,
    Option.map_some,Option.getD_some]
  simpa only [Nat.cast_mul,targetCoefficients,List.getD_eq_getElem?_getD] using
    nearest_error step _ ((c:ℚ)*(targetCoefficients d A side).getD j 0)

private theorem correctLower_error {m step : ℕ} (mp : 0 < m) (t : ℕ) (p : List ℤ) (j : ℕ) :
    |(((correctLower m step t p).getD j 0:ℤ):ℚ) - (p.getD j 0:ℤ)| ≤ (step:ℚ)*(m-1) := by
  have m1 : (1:ℚ) ≤ m := by exact_mod_cast mp
  have md : (0:ℚ) ≤ ((t%m:ℕ):ℚ) := Nat.cast_nonneg _
  induction p generalizing t j with
  | nil => simp [correctLower]; exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  | cons a as ih =>
    cases j with
    | zero =>
      change |((a-(step:ℤ)*(t%m:ℕ):ℤ):ℚ)-(a:ℚ)| ≤ _
      simp only [Int.cast_sub,Int.cast_mul,Int.cast_natCast]
      rw [sub_sub_cancel_left,abs_neg,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) md)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have h : ((t%m:ℕ):ℚ)+1 ≤ m := by exact_mod_cast Nat.mod_lt t mp
      linarith
    | succ j => exact ih _ _ (Nat.cast_nonneg _)

private theorem eval_sum {R : Type*} [CommRing R] (x : R) (p : List R) :
    eval x p = ∑ j ∈ Finset.range p.length, p.getD j 0*x^j := by
  induction p with
  | nil => simp [eval]
  | cons a as ih =>
    rw [eval,ih,List.length_cons,Finset.sum_range_succ',Finset.mul_sum]
    simp only [pow_zero,mul_one]
    change a + _ = _ + a
    rw [add_comm a]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change x*(as.getD i 0*x^i) = as.getD i 0*x^(i+1)
    ring

private theorem rat_getD (cs : List ℤ) (j : ℕ) :
    ((cs.map (fun c : ℤ => (c:ℚ))).getD j 0) = (cs.getD j 0:ℤ) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases cs[j]? <;> simp

theorem raw_eval_error {n m P ell A M d c : ℕ} (dp : 0 < d) (mp : 0 < m)
    (step : 0 < P*ell) (ap : 1 ≤ M) (side : Bool) (x : ℚ) (bound : |x| ≤ M) :
    |eval x ((corrected n m (P*ell) c (preliminary d A m P ell c side)).map (fun z : ℤ => (z:ℚ))) -
      c*eval x (targetCoefficients d A side)| ≤ d*((P:ℚ)*ell*m)*M^(d-1) := by
  let pre := preliminary d A m P ell c side
  let model := targetCoefficients d A side
  let t := correction (P*ell) n (eval (m:ℤ) (pre++[(c:ℤ)]))
  let low := correctLower m (P*ell) t pre
  have lowLen : low.length = d := by simp [low,pre,preliminary]
  have scheme := fromRoots_shape ((targets d side).map ((A:ℚ)*·))
  obtain ⟨lo,split⟩ : ∃ lo, model = lo++[1] := List.getLast?_eq_some_iff.mp scheme.2
  have len : lo.length = d := by
    have h : model.length = d+1 := by simpa [model,targetCoefficients,targets] using scheme.1
    rw [split,List.length_append,List.length_singleton] at h; omega
  have each (j : ℕ) (hj : j < d) :
      |((low.getD j 0:ℤ):ℚ) - c*lo.getD j 0| ≤ (P:ℚ)*ell*m := by
    have left := correctLower_error (step := P*ell) mp t pre j
    have right := preliminary_error A m P ell c side hj step
    have ideq : model.getD j 0 = lo.getD j 0 := by
      simp [split,List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega : j < lo.length)]
    change |((pre.getD j 0:ℤ):ℚ) - c*model.getD j 0| ≤ _ at right
    rw [ideq] at right
    change |((low.getD j 0:ℤ):ℚ) - (pre.getD j 0:ℤ)| ≤ _ at left
    have tri := abs_sub_le ((low.getD j 0:ℤ):ℚ) ((pre.getD j 0:ℤ):ℚ) ((c:ℚ)*lo.getD j 0)
    push_cast at left
    linarith [mul_nonneg (Nat.cast_nonneg (α := ℚ) P) (Nat.cast_nonneg ell)]
  have terms : ∀ j ∈ Finset.range d,
      |(((low.getD j 0:ℤ):ℚ)-c*lo.getD j 0)*x^j| ≤ ((P:ℚ)*ell*m)*M^(d-1) := by
    intro j hj
    have jd := Finset.mem_range.mp hj
    rw [abs_mul,abs_pow]
    apply mul_le_mul (each j jd) _ (by positivity) (by positivity)
    exact (pow_le_pow_left₀ (abs_nonneg x) bound j).trans
      (pow_le_pow_right₀ (by exact_mod_cast ap) (by omega))
  have sumBounds := (Finset.abs_sum_le_sum_abs (fun j : ℕ => (((low.getD j 0:ℤ):ℚ)-c*lo.getD j 0)*x^j)
    (Finset.range d)).trans (Finset.sum_le_sum terms)
  have eq : eval x ((corrected n m (P*ell) c pre).map (fun z : ℤ => (z:ℚ))) -
      c*eval x model = ∑ j ∈ Finset.range d, (((low.getD j 0:ℤ):ℚ)-c*lo.getD j 0)*x^j := by
    change eval x ((low++[(c:ℤ)]).map (fun z : ℤ => (z:ℚ))) - _ = _
    rw [split,List.map_append,eval_append,eval_append]
    simp only [List.map_singleton,eval,List.length_map,lowLen,len,Int.cast_natCast,mul_zero,add_zero,mul_one]
    rw [eval_sum x (low.map (fun z : ℤ => (z:ℚ))),eval_sum x lo,List.length_map,lowLen,len,
      mul_add,Finset.mul_sum]
    simp only [rat_getD]
    calc _ = (∑ j ∈ Finset.range d, ((low.getD j 0:ℤ):ℚ)*x^j) -
          (∑ j ∈ Finset.range d, c*(lo.getD j 0*x^j)) := by ring
         _ = _ := by rw [←Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro _ _; ring
  change |eval x ((corrected n m (P*ell) c pre).map _) - c*eval x model| ≤ _
  rw [eq]
  simpa [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_assoc] using sumBounds

private theorem perturb_eval {step m a z : ℕ} (base : List ℤ) (length : 3 ≤ base.length) (x : ℚ) :
    eval x ((perturb step m a z base).map (fun c : ℤ => (c:ℚ))) =
      eval x (base.map (fun c : ℤ => (c:ℚ))) + step*(x-m)*(a+z*x) := by
  rcases base with _ | ⟨p,ps⟩ <;> simp only [List.length_nil,List.length_cons] at length
  · omega
  rcases ps with _ | ⟨q,qs⟩ <;> simp only [List.length_nil,List.length_cons] at length
  · omega
  rcases qs with _ | ⟨r,rs⟩ <;> simp only [List.length_nil,List.length_cons] at length
  · omega
  simp [perturb,eval]
  ring

/-- Minimality of the selected power of three gives the amplitude required
    by the schedule for all perturbations. -/
theorem leading_amplitude {n : ℕ} (hd : 2 ≤ Fixed.d (n.log2+1)) :
    let b := n.log2+1
    6*Fixed.K₁ b*Fixed.B b*primorial (Fixed.d b)*Fixed.rootBase n*(b^2*Fixed.U b*Fixed.A b)
      ≤ leadingCoefficient n*(Fixed.A b)^Fixed.d b := by
  let b := n.log2+1
  let P := primorial (Fixed.d b)
  let T := 6*Fixed.K₁ b*Fixed.B b*P*Fixed.rootBase n*(b^2*Fixed.U b*Fixed.A b)
  let base := (P/2)*(Fixed.A b)^Fixed.d b
  let q := (T-1)/base+1
  have ppos : 0 < P := primorial_pos _
  have half := Nat.div_pos (Nat.le_of_dvd ppos (Nat.prime_two.dvd_primorial_iff.mpr hd)) (by decide)
  have basePos : 0 < base := Nat.mul_pos half (Nat.pow_pos (Nat.pow_pos (by decide)))
  have rem := Nat.mod_lt (T-1) basePos
  have split := Nat.mod_add_div (T-1) base
  have h : T ≤ base*q := by dsimp [q]; rw [Nat.mul_add,Nat.mul_one]; omega
  have ceil := (Nat.le_pow_clog (by decide : 1 < 3) q).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_right 1 (Nat.clog 3 q)))
  apply h.trans ((Nat.mul_le_mul_left base ceil).trans_eq _)
  change (P/2*(Fixed.A b)^Fixed.d b)*3^(max 1 (Nat.clog 3 q)) =
    (P/2*3^(max 1 (Nat.clog 3 q)))*(Fixed.A b)^Fixed.d b
  ring

/-- The ideal comparison product evaluated at a normalized coordinate. -/
def center (d : ℕ) (side : Bool) (j : ℕ) : ℚ := ((2*j + if side then 2 else 1 : ℕ):ℚ)/(4*d)

def idealValue (d : ℕ) (side : Bool) (t : ℚ) : ℚ :=
  ∏ i ∈ Finset.range d, (t-center d side i)

private theorem scaled_model (d A : ℕ) (side : Bool) (t : ℚ) :
    eval (A*t) (targetCoefficients d A side) = (A:ℚ)^d*idealValue d side t := by
  let points := targets d side
  have val := mapped_eval_roots (RingHom.id ℚ) ((A:ℚ)*t) (points.map ((A:ℚ)*·))
  simp only [RingHom.id_apply] at val
  have prod (n : ℕ) (f : ℕ → ℚ) : ((List.range n).map f).prod = ∏ j ∈ Finset.range n, f j := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ,List.prod_append,Finset.prod_range_succ,ih]
  change eval (A*t) (fromRoots (points.map ((A:ℚ)*·))) = _
  simp only [List.map_map,Function.comp_def] at val
  rw [show eval (A*t) (fromRoots (points.map ((A:ℚ)*·))) = (points.map (fun y : ℚ => A*t-A*y)).prod by simpa using val]
  change (((List.range d).map (center d side)).map (fun y : ℚ => A*t-A*y)).prod = _
  simp only [List.map_map,Function.comp_def,←mul_sub]
  rw [prod,Finset.prod_mul_distrib]
  simp [idealValue]

private theorem normalized_eq_eval (A : ℕ) (p : List ℤ) (t : ℚ) :
    RootLogs.normalized A p t = eval (A*t) (p.map (fun z : ℤ => (z:ℚ))) := by
  induction p with
  | nil => rfl
  | cons a as ih => change (a:ℚ)+(A*t)*RootLogs.normalized A as t = (a:ℚ)+(A*t)*_; rw [ih]

/-- Throughout the four-dimensional search box the normalized values of each
    actual polynomial track the ideal target polynomial on [-1,1]. -/
theorem normalized_error {n ell a z : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool)
    (box : let b := n.log2+1; a ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ z ≤ 2*b^2*Fixed.U b)
    (t : ℚ) (ht : |t| ≤ 1) :
    let b := n.log2+1
    let d := Fixed.d b
    let A := Fixed.A b
    let m := Fixed.rootBase n
    let P := primorial d
    let c := leadingCoefficient n
    let pre := preliminary d A m P ell c side
    let f := perturb (P*ell) m a z (corrected n m (P*ell) c pre)
    |RootLogs.normalized A f t - c*(A:ℚ)^d*idealValue d side t| ≤ c*(A:ℚ)^d/(Fixed.K₁ b) := by
  let b := n.log2+1
  let d := Fixed.d b
  let A := Fixed.A b
  let m := Fixed.rootBase n
  let P := primorial d
  let c := leadingCoefficient n
  let Q := b^2*Fixed.U b*A
  let x : ℚ := A*t
  let pre := preliminary d A m P ell c side
  let base := corrected n m (P*ell) c pre
  change |RootLogs.normalized A (perturb (P*ell) m a z base) t - c*(A:ℚ)^d*idealValue d side t| ≤ _
  have guards := Fixed.stage_guards hn big
  have dpos : 0 < d := by change 10004 ≤ d at big; omega
  have ap : 1 ≤ A := Nat.one_le_two_pow
  have mp : 0 < m := by simp [m,Fixed.rootBase]
  have kp : (0:ℚ) < Fixed.K₁ b := by exact_mod_cast Nat.pow_pos (by decide : 0 < 2) (n := 100*Fixed.h b)
  have ab : |x| ≤ (A:ℚ) := by
    dsimp [x]; rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    simpa using mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (α := ℚ) A)
  have step := Nat.mul_pos (primorial_pos d) (mem_dyadicTargets.mp target).1.pos
  have len : 3 ≤ base.length := by simp [base,pre,corrected,preliminary]; change 10004 ≤ d at big; omega
  have raw := raw_eval_error (n := n) (c := c) (A := A) dpos mp step ap side x ab
  have id : d*A^(d-1) ≤ Q := by
    apply (Nat.mul_le_mul_left d (Nat.pow_le_pow_right ap (Nat.sub_le ..))).trans
    have ub := (guards.gaussian).2
    have bp : 0 < b := by simp [b]
    have up : Fixed.U b ≤ b^2*Fixed.U b := Nat.le_mul_of_pos_left _ (Nat.pow_pos bp)
    exact ub.trans (up.trans (Nat.le_mul_of_pos_right _ ap))
  have rawCap : (d:ℚ)*((P:ℚ)*ell*m)*A^(d-1) ≤ (P:ℚ)*ell*m*Q := by
    have cast : (d:ℚ)*(A:ℚ)^(d-1) ≤ Q := by exact_mod_cast id
    calc _ = ((P:ℚ)*ell*m)*(d*A^(d-1)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left cast (by positivity)
  have mr : 4*A ≤ m := by
    apply (Nat.mul_le_mul_right A (show 4 ≤ 4*d by omega)).trans guards.markRange
  have delta : |x-(m:ℚ)| ≤ 5*(m:ℚ)/4 := by
    have h := abs_add_le x (-(m:ℚ))
    simp only [←sub_eq_add_neg,abs_neg,abs_of_nonneg (Nat.cast_nonneg (α := ℚ) m)] at h
    have h4 : (4:ℚ)*A ≤ m := by exact_mod_cast mr
    linarith
  have params : (a:ℚ)+(z:ℚ)*A ≤ 4*Q := by
    obtain ⟨ha,hz⟩ := box
    have h : a+z*A ≤ 4*Q := by
      calc _ ≤ 2*b^2*Fixed.U b*A+(2*b^2*Fixed.U b)*A := Nat.add_le_add ha (Nat.mul_le_mul_right _ hz)
           _ = _ := by dsimp [Q]; ring
    exact_mod_cast h
  have poly : |(a:ℚ)+z*x| ≤ 4*Q := by
    have h := abs_add_le (a:ℚ) ((z:ℚ)*x)
    simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℚ) a),abs_of_nonneg (Nat.cast_nonneg (α := ℚ) z)] at h
    exact h.trans ((add_le_add_right (mul_le_mul_of_nonneg_left ab (Nat.cast_nonneg z)) _).trans params)
  have pert : |((P*ell:ℕ):ℚ)*(x-m)*(a+z*x)| ≤ 5*((P:ℚ)*ell*m*Q) := by
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),Nat.cast_mul]
    calc _ ≤ (P:ℚ)*ell*(5*m/4)*(4*Q) :=
          mul_le_mul (mul_le_mul_of_nonneg_left delta (by positivity)) poly (abs_nonneg _) (by positivity)
         _ = _ := by ring
  have amp := leading_amplitude (n := n) (by omega : 2 ≤ Fixed.d (n.log2+1))
  have ellBound : ell ≤ Fixed.B b := (mem_dyadicTargets.mp target).2.2
  have cap : 6*((P:ℚ)*ell*m*Q) ≤ (c:ℚ)*A^d/(Fixed.K₁ b) := by
    apply (le_div_iff₀ kp).mpr
    have h : 6*((P:ℚ)*Fixed.B b*m*Q)*(Fixed.K₁ b) ≤ (c:ℚ)*A^d := by
      have cast : (6:ℚ)*(Fixed.K₁ b)*(Fixed.B b)*P*m*Q ≤ c*(A:ℚ)^d := by exact_mod_cast amp
      convert cast using 1; ring
    have small : (ell:ℚ) ≤ Fixed.B b := by exact_mod_cast ellBound
    apply le_trans _ h
    gcongr
  rw [normalized_eq_eval,perturb_eval base len]
  change |eval x (base.map (fun q : ℤ => (q:ℚ))) + ((P*ell:ℕ):ℚ)*(x-m)*(a+z*x) - _| ≤ _
  have norm : (c:ℚ)*eval x (targetCoefficients d A side) = c*A^d*idealValue d side t := by
    rw [show x = (A:ℚ)*t from rfl,scaled_model]; ring
  change |eval x (base.map _) - (c:ℚ)*eval x (targetCoefficients d A side)| ≤ _ at raw
  rw [norm] at raw
  calc _ = |(eval x (base.map (fun q : ℤ => (q:ℚ))) - c*A^d*idealValue d side t) +
            ((P*ell:ℕ):ℚ)*(x-m)*(a+z*x)| := by congr 1; ring
       _ ≤ |eval x (base.map (fun q : ℤ => (q:ℚ))) - c*A^d*idealValue d side t|+
            |((P*ell:ℕ):ℚ)*(x-m)*(a+z*x)| := abs_add_le _ _
       _ ≤ (P:ℚ)*ell*m*Q+5*((P:ℚ)*ell*m*Q) := add_le_add (raw.trans rawCap) pert
       _ ≤ _ := (by linarith [cap])

end Cogentic.Construction

#print axioms Cogentic.Construction.normalized_error
