import Cogentic.ConstructionBrackets
import Cogentic.ConstructionPrimitive

namespace Cogentic.Construction

/-- The dyadic schedule makes the leading coefficient at least four times
    the total of the per-coefficient rounding bounds scaled to the base. -/
theorem leading_margin {n : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1)) :
    let b := n.log2+1; let d := Fixed.d b
    4*d*primorial d*Fixed.B b ≤ leadingCoefficient n := by
  let b := n.log2+1
  let d := Fixed.d b
  let A := Fixed.A b
  let P := primorial d
  let Q := b^2*Fixed.U b*A
  have ap : 0 < A := Nat.pow_pos (by decide)
  have bp : 0 < b := by simp [b]
  have mp : 0 < Fixed.rootBase n := by simp [Fixed.rootBase]
  have kp : 0 < Fixed.K₁ b := Nat.pow_pos (by decide)
  have gauss := (Fixed.stage_guards hn big).gaussian.2
  have cap : d*A^d ≤ Q := gauss.trans (((Nat.le_mul_of_pos_left _ (Nat.pow_pos bp))).trans (Nat.le_mul_of_pos_right _ ap))
  have leading := leading_amplitude (n := n) (by omega : 2 ≤ Fixed.d (n.log2+1))
  change 4*d*P*Fixed.B b ≤ leadingCoefficient n
  apply Nat.le_of_mul_le_mul_right (c := A^d) _ (Nat.pow_pos ap)
  calc _ = 4*Fixed.B b*P*(d*A^d) := by ring
       _ ≤ 4*Fixed.B b*P*Q := Nat.mul_le_mul_left _ cap
       _ ≤ 6*Fixed.K₁ b*Fixed.B b*P*Fixed.rootBase n*Q := by
         apply Nat.mul_le_mul_right Q
         calc _ ≤ 6*Fixed.K₁ b*Fixed.B b*P := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
              _ ≤ _ := Nat.le_mul_of_pos_right _ mp
       _ ≤ _ := leading

private theorem bernoulli_lower {m e : ℚ} {d : ℕ} (mp : 0 < m) (ep : 0 ≤ e)
    (dp : 0 < d) (small : 4*d*e ≤ m) :
    (3/4:ℚ)*m^d ≤ (m-e)^d := by
  have positive : (0:ℚ) ≤ d := by positivity
  have de : e ≤ d*e := by
    simpa using mul_le_mul_of_nonneg_right (show (1:ℚ) ≤ d by exact_mod_cast dp) ep
  have denom : -2 ≤ -(e/m) := by
    have h : e/m ≤ 2 := (div_le_iff₀ mp).mpr (by linarith); linarith
  have lower := one_add_mul_le_pow denom d
  have ratio : (d:ℚ)*(e/m) ≤ 1/4 := by
    rw [←mul_div_assoc,div_le_iff₀ mp]
    linarith
  have b : (3/4:ℚ) ≤ (1+ -(e/m))^d := (show 3/4 ≤ 1+(d:ℚ)*-(e/m) by linarith).trans lower
  have eq : m-e = (1+ -(e/m))*m := by field_simp; ring
  rw [eq,mul_pow]
  exact mul_le_mul_of_nonneg_right b (pow_nonneg mp.le _)

private theorem model_at_base {m A d : ℕ} (dp : 0 < d) (ap : 0 < A) (mp : 0 < m)
    (big : 4*d*A ≤ m) (side : Bool) :
    (3/4:ℚ)*(m:ℚ)^d ≤ eval (m:ℚ) (targetCoefficients d A side) ∧
      eval (m:ℚ) (targetCoefficients d A side) ≤ (m:ℚ)^d := by
  let rs := (targets d side).map ((A:ℚ)*·)
  have val := mapped_eval_roots (RingHom.id ℚ) (m:ℚ) rs
  simp only [RingHom.id_apply,(show (⇑(RingHom.id ℚ)) = id from rfl),List.map_id] at val
  change _ ≤ eval (m:ℚ) (fromRoots rs) ∧ eval (m:ℚ) (fromRoots rs) ≤ _
  rw [val]
  have roots (r : ℚ) (hr : r ∈ rs) : 0 ≤ r ∧ r ≤ A := by
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hy
    have smaller := List.mem_range.mp hi
    have one : (((2*i + if side then 2 else 1 : ℕ):ℚ)/(4*d)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by exact_mod_cast (by cases side <;> simp <;> omega : 2*i+(if side then 2 else 1) ≤ 4*d))
    exact ⟨by positivity,by simpa using mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (α := ℚ) A)⟩
  have aSmall : A ≤ m := (Nat.le_mul_of_pos_left A (by positivity : 0 < 4*d)).trans big
  have diff : (0:ℚ) ≤ m-(A:ℚ) := by exact sub_nonneg.mpr (by exact_mod_cast aSmall)
  have bounds (l : List ℚ) (h : ∀ r ∈ l, 0 ≤ r ∧ r ≤ A) :
      ((m:ℚ)-A)^l.length ≤ (l.map (fun r => (m:ℚ)-r)).prod ∧
      (l.map (fun r => (m:ℚ)-r)).prod ≤ (m:ℚ)^l.length := by
    induction l with
    | nil => simp
    | cons r rs ih =>
      obtain ⟨lo,hi⟩ := ih (fun t ht => h t (by simp [ht]))
      have range := h r (by simp)
      simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ']
      exact ⟨mul_le_mul (by linarith) lo (pow_nonneg diff _) (by linarith),
        mul_le_mul (by linarith) hi ((pow_nonneg diff _).trans lo) (by positivity)⟩
  have range := bounds rs roots
  have len : rs.length = d := by simp [rs,targets]
  rw [len] at range
  exact ⟨(bernoulli_lower (by exact_mod_cast mp) (Nat.cast_nonneg A) dp (by exact_mod_cast big)).trans range.1,range.2⟩

/-- On a survivor the two exact cofactors are positive and below twice the
    leading coefficient, as required by the local sieve. -/
theorem cofactor_bounds {n ell : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1))
      (Fixed.rootBase n) = Option.none) (u₀ u₁ v₀ v₁ : ℕ) :
    let p := construct n ell u₀ u₁ v₀ v₁
    let ratio := fun cs => eval (Fixed.rootBase n:ℤ) cs/(n:ℤ)
    (1 ≤ ratio p.first ∧ ratio p.first < 2*leadingCoefficient n) ∧
    (1 ≤ ratio p.second ∧ ratio p.second < 2*leadingCoefficient n) := by
  let b := n.log2+1
  let d := Fixed.d b
  let P := primorial d
  let m := Fixed.rootBase n
  let A := Fixed.A b
  let c := leadingCoefficient n
  have dp : 0 < d := by change 10004 ≤ d at big; omega
  have mp : 0 < m := by simp [m,Fixed.rootBase]
  have ap : 0 < A := Nat.pow_pos (by decide)
  have ep := (mem_dyadicTargets.mp target).1.pos
  have step : 0 < P*ell := Nat.mul_pos (primorial_pos d) ep
  have mr := (Fixed.stage_guards hn big).markRange
  change 4*d*A ≤ m at mr
  have me : 4*d ≤ m := (Nat.le_mul_of_pos_right _ ap).trans mr
  have lc : 4*d*P*ell ≤ c := (Nat.mul_le_mul_left _ (mem_dyadicTargets.mp target).2.2).trans (leading_margin hn big)
  have cp : 0 < c := (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) dp) (primorial_pos d)) ep).trans_le lc
  have valN := (Fixed.rootBase_spec hn).1
  change (m-1)^d < n at valN
  have near : (3/4:ℚ)*m^d < n := by
    have h := bernoulli_lower (d := d) (m := m) (e := 1) (by exact_mod_cast mp) (by norm_num) dp
      (by simpa using (show (4:ℚ)*d ≤ m by exact_mod_cast me))
    have strict : ((m-1:ℕ):ℚ)^d < n := by exact_mod_cast valN
    rw [Nat.cast_sub (by omega),Nat.cast_one] at strict
    exact h.trans_lt strict
  have co := surviving_coprime hn composite target none
  have side (second : Bool) (a z : ℕ) :
      let base := corrected n m (P*ell) c (preliminary d A m P ell c second)
      let ratio := eval (m:ℤ) (perturb (P*ell) m a z base)/(n:ℤ)
      1 ≤ ratio ∧ ratio < 2*c := by
    let base := corrected n m (P*ell) c (preliminary d A m P ell c second)
    let y := eval (m:ℤ) base
    have dv : (n:ℤ) ∣ y := corrected_at_base (by omega : 0 < n) mp co _ (by simpa [preliminary] using (Fixed.rootBase_spec hn).2.1)
    have castEval (p : List ℤ) : eval (m:ℚ) (p.map (fun z : ℤ => (z:ℚ))) = ((eval (m:ℤ) p:ℤ):ℚ) := by
      induction p with
      | nil => simp [eval]
      | cons v vs ih => simp [eval,ih]
    have raw := raw_eval_error (A := A) (M := m) (c := c) (n := n) dp mp step mp second (m:ℚ)
      (le_of_eq (abs_of_nonneg (Nat.cast_nonneg m)))
    rw [castEval] at raw
    have bound : (d:ℚ)*((P:ℚ)*ell*m)*m^(d-1) ≤ (c:ℚ)*m^d/4 := by
      have l : (4:ℚ)*d*P*ell ≤ c := by exact_mod_cast lc
      have power : (m:ℚ)^d = m^(d-1)*(m:ℚ) := by
        conv_lhs => rw [show d = (d-1)+1 by omega,pow_succ]
      rw [power]
      nlinarith [mul_le_mul_of_nonneg_right l (show (0:ℚ) ≤ m^(d-1)*(m:ℚ) by positivity)]
    have error := abs_le.mp (raw.trans bound)
    change -(↑c*(m:ℚ)^d/4) ≤ (y:ℚ)-c*eval (m:ℚ) (targetCoefficients d A second) ∧ _ at error
    have ⟨lo,hi⟩ := model_at_base dp ap mp mr second
    have l := mul_le_mul_of_nonneg_left lo (Nat.cast_nonneg (α := ℚ) c)
    have h := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (α := ℚ) c)
    have cPos : (0:ℚ) < c := by exact_mod_cast cp
    have pos : (0:ℚ) < y := by nlinarith [mul_pos cPos (pow_pos (show (0:ℚ) < m by exact_mod_cast mp) d)]
    have high : (y:ℚ) < 2*c*n := by
      nlinarith [mul_lt_mul_of_pos_left near cPos,mul_pos cPos (pow_pos (show (0:ℚ) < m by exact_mod_cast mp) d)]
    have yy : 0 < y := by exact_mod_cast pos
    have yu : y < (2:ℤ)*c*n := by exact_mod_cast high
    have np : (0:ℤ) < n := by exact_mod_cast (by omega : 0 < n)
    have id := Int.ediv_mul_cancel dv
    change 1 ≤ eval (m:ℤ) (perturb (P*ell) m a z base)/(n:ℤ) ∧ _
    rw [perturb_at_base]
    change 1 ≤ y/(n:ℤ) ∧ y/(n:ℤ) < 2*c
    exact ⟨by by_contra! h; have := mul_nonpos_of_nonpos_of_nonneg (show y/(n:ℤ) ≤ 0 by omega) np.le; omega,
      lt_of_mul_lt_mul_right (id.trans_lt yu) np.le⟩
  exact ⟨side false u₀ u₁,side true v₀ v₁⟩

/-- Product removed by the mark and factor-base sieves. Its value is
    independent of all four coefficient perturbations. -/
def markModulus (n ell : ℕ) : ℕ :=
  let p := construct n ell 0 0 0 0
  let k := fun cs => ((eval (Fixed.rootBase n:ℤ) cs)/(n:ℤ)).natAbs
  k p.first * k p.second

theorem markModulus_eq (n ell u₀ u₁ v₀ v₁ : ℕ) :
    let p := construct n ell u₀ u₁ v₀ v₁
    let k := fun cs => ((eval (Fixed.rootBase n:ℤ) cs)/(n:ℤ)).natAbs
    markModulus n ell = k p.first * k p.second := by
  simp only [markModulus,construct,perturb_at_base]

theorem constructed_marks_iff (n ell u₀ u₁ v₀ v₁ a : ℕ) :
    a ∈ (construct n ell u₀ u₁ v₀ v₁).marks ↔
      1 ≤ a ∧ a ≤ Fixed.A (n.log2+1) ∧
      onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a ∧
      ((a:ℤ)-Fixed.rootBase n).natAbs.Coprime (markModulus n ell) := by
  simp only [construct,markModulus,perturb_at_base,List.mem_filter,List.mem_range',
    Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i,hi,eq⟩,grid,guard⟩
    exact ⟨by omega,by omega,grid,guard⟩
  · rintro ⟨lo,hi,grid,guard⟩
    exact ⟨⟨a-1,by omega,by omega⟩,grid,guard⟩

theorem constructed_factorBase_iff (n ell u₀ u₁ v₀ v₁ q : ℕ) :
    q ∈ (construct n ell u₀ u₁ v₀ v₁).factorBase ↔
      q.Prime ∧ q ≤ Fixed.B (n.log2+1) ∧ Fixed.B (n.log2+1) < q^2 ∧ ¬q ∣ markModulus n ell := by
  simp only [construct,markModulus,perturb_at_base,List.mem_filter,List.mem_range',decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i,hi,eq⟩,prime,sq,guard⟩
    exact ⟨prime,by omega,sq,guard⟩
  · rintro ⟨prime,hi,sq,guard⟩
    have := prime.two_le
    exact ⟨⟨q-2,by omega,by omega⟩,prime,sq,guard⟩

/-- Arithmetic inputs of the fixed mark sieve. Every prime removed by its
    cofactor filter exceeds the degree and differs from the target. -/
theorem markModulus_spec {n ell : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1))
      (Fixed.rootBase n) = Option.none) :
    let k := markModulus n ell
    let d := Fixed.d (n.log2+1)
    0 < k ∧ k < (2*leadingCoefficient n)^2 ∧
      k.Coprime (primorial d*ell) ∧ ∀ q ∈ k.primeFactors, d < q ∧ q ≠ ell := by
  let b := n.log2+1
  let d := Fixed.d b
  let m := Fixed.rootBase n
  let p := construct n ell 0 0 0 0
  let k := markModulus n ell
  let P := primorial d
  let ratio := fun cs => eval (m:ℤ) cs/(n:ℤ)
  have dv := constructed_root hn (surviving_coprime hn composite target none) 0 0 0 0
  have congr := values_mod_primorial (by omega : 2 ≤ Fixed.d (n.log2+1)) target 0 0 0 0 (m:ℤ)
  have c := cofactor_bounds hn big composite target none 0 0 0 0
  have member := (Marking.mem_base.mp (target_in_base hn (by omega) composite target none 0 0 0 0)).1
  have keep := (constructed_factorBase_iff n ell 0 0 0 0 ell).mp member
  have cop (f : List ℤ) (val : (n:ℤ) ∣ eval (m:ℤ) f) (good : (P:ℤ) ∣ eval (m:ℤ) f-1) :
      (ratio f).natAbs.Coprime P := by
    apply Nat.coprime_of_dvd'
    intro q prime qk qp
    have qratio : (q:ℤ) ∣ ratio f := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr qk)
    have qval := qratio.trans (show ratio f ∣ eval (m:ℤ) f from ⟨n,(Int.ediv_mul_cancel val).symm⟩)
    have qdiff := (Int.natCast_dvd_natCast.mpr qp).trans good
    have one : (q:ℤ) ∣ 1 := by simpa using dvd_sub qval qdiff
    exact_mod_cast one
  have kcop : k.Coprime P := Nat.coprime_mul_iff_left.mpr ⟨cop p.first dv.1 congr.1,cop p.second dv.2 congr.2⟩
  have ecop : k.Coprime ell := ((mem_dyadicTargets.mp target).1.coprime_iff_not_dvd.mpr keep.2.2.2).symm
  have sizes (f : List ℤ) (h : 1 ≤ ratio f ∧ ratio f < 2*(leadingCoefficient n:ℤ)) :
      0 < (ratio f).natAbs ∧ (ratio f).natAbs < 2*leadingCoefficient n := by
    have cast := Int.natAbs_of_nonneg (show 0 ≤ ratio f by omega)
    exact ⟨by exact_mod_cast (cast ▸ (by omega : (0:ℤ) < ratio f)),by exact_mod_cast (cast ▸ h.2)⟩
  obtain ⟨fp,fl⟩ := sizes _ c.1
  obtain ⟨gp,gl⟩ := sizes _ c.2
  have kp : 0 < k := Nat.mul_pos fp gp
  refine ⟨kp,?_,Nat.coprime_mul_iff_right.mpr ⟨kcop,ecop⟩,?_⟩
  · rw [pow_two]
    exact Nat.mul_lt_mul_of_lt_of_lt fl gl
  · intro q hq
    obtain ⟨prime,qk,_⟩ := Nat.mem_primeFactors.mp hq
    have okP := prime.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left qk kcop)
    exact ⟨lt_of_not_ge (fun le => okP (prime.dvd_primorial_iff.mpr le)),fun eq => keep.2.2.2 (eq ▸ qk)⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.cofactor_bounds
#print axioms Cogentic.Construction.markModulus_spec
