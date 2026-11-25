import Cogentic.AdmissionMoments
import Cogentic.MomentRows
import Cogentic.SmoothBox
import Cogentic.ClassBalance

namespace Cogentic.Construction
open Real Finset Cogentic.Window
open scoped Classical
noncomputable section

/-- Candidate ordinary coordinates before testing which residues are polynomial roots. -/
abbrev BandRow (b : ℕ) := Bool × (Σ p : ↥(primeBand b), Fin p.val)

def bandRowPrime {b : ℕ} (i : BandRow b) : ℕ := i.2.1.val

/-- Root admission costs one factor of p; the diagonal row mass supplies p^(-α). -/
def bandRowWeight {b : ℕ} (α : ℝ) (i : BandRow b) : ℝ :=
  (bandRowPrime i : ℝ)^(-α)/(bandRowPrime i:ℝ)

theorem band_row_weight_sum {b : ℕ} {α u : ℝ} (large : 1<(Fixed.B b:ℝ)) (ap : 0≤α)
    (saddle : saddleMean (primeBand b) α=log (Fixed.B b)*u) :
    ∑ i : BandRow b, bandRowWeight α i ≤ 8*u := by
  let H := log (Fixed.B b)
  have hp : 0<H := log_pos large
  have base : 0<(Fixed.B b:ℝ) := zero_lt_one.trans large
  have cmp := (tilted_mean_bounds (primeBand b) H α hp.le ap (by
    intro p h
    obtain ⟨pr,cap,sq⟩ := mem_primeBand.mp h
    have low := log_le_log base (show (Fixed.B b:ℝ) ≤ (p:ℝ)^2 by exact_mod_cast sq.le)
    rw [log_pow] at low
    norm_num at low
    exact ⟨pr.one_le,by dsimp only [H]; linarith,log_le_log (by exact_mod_cast pr.pos) (by exact_mod_cast cap)⟩)).1
  rw [saddle] at cmp
  have mass : ∑ p∈primeBand b,(p:ℝ)^(-α) ≤ 4*u := by
    apply le_of_mul_le_mul_left (a:=H) _ hp
    change H/4*_≤H*u at cmp
    linarith only [cmp]
  have one (side : Bool) : ∑ i : Σ p : ↥(primeBand b), Fin p.val, bandRowWeight α (side,i) =
      ∑ p∈primeBand b,(p:ℝ)^(-α) := by
    rw [Fintype.sum_sigma]
    trans ∑ p : ↥(primeBand b), (p.val:ℝ)^(-α)
    swap
    · exact sum_coe_sort (primeBand b) (fun p : ℕ => (p:ℝ)^(-α))
    apply sum_congr rfl
    intro p _
    have pos : (p.val:ℝ)≠0 := by exact_mod_cast (mem_primeBand.mp p.property).1.ne_zero
    simp [bandRowWeight,bandRowPrime]
    field_simp
  rw [Fintype.sum_prod_type,Fintype.sum_bool,one,one]
  linarith only [mass]

/-- On the original coefficient law the second moment of an admitted
centered row score costs at most four divided by its prescribed modulus product. -/
theorem admitted_second_bound {n ell : ℕ} {ι : Type*} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (X : Finset ι) (w : ι→ℝ) (E F : ι→ℤ×ℤ→Prop) (V : ℝ) (vp : 0≤V)
    (conditional : twoFieldSecond R T X w E F≤V) :
    let S := PrescribedRows.unrestricted n ell
    let Q : ℝ := prodPrimes R.primes*prodPrimes T.primes
    let l := fun i (k : ℤ×ℤ) => R.compatible false k.1 k.2 ∧ E i k
    let r := fun i (k : ℤ×ℤ) => T.compatible true k.1 k.2 ∧ F i k
    twoFieldSecond S S X w l r ≤ 4*V/Q := by
  intro S Q l r
  obtain ⟨A,apos,close,moments⟩ := twoField_admission_moments (ι:=ι) R T target
  let b := n.log2+1
  let η := 72*exp (-(Fixed.U b:ℝ))
  have degree := Fixed.degree_pos (b:=b) (Nat.succ_pos _)
  have vpos : 0<Fixed.v b := Nat.mul_pos degree (Nat.mul_pos degree (Nat.succ_pos _))
  have uc : 72≤(Fixed.U b:ℝ) := by
    exact_mod_cast (by decide : 72≤2^7).trans (Nat.pow_le_pow_right (by decide : 0<2)
      (by omega))
  have en : 0≤η := by dsimp only [η]; positivity
  have e1 : η≤1 := by
    dsimp only [η]; rw [exp_neg,←div_eq_mul_inv,div_le_one (exp_pos _)]
    linarith [add_one_le_exp (Fixed.U b),uc]
  have qp : 0<Q := by
    have p := (R.subprod_bounds (s:=R.primes) Subset.rfl).1
    have q := (T.subprod_bounds (s:=T.primes) Subset.rfl).1
    dsimp only [Q]; positivity
  change |Q*A-1|≤2*η+η^2 at close
  have cap : Q*A≤4 := by nlinarith only [(abs_le.mp close).2,mul_nonneg (sub_nonneg.mpr e1) en,e1]
  rw [(moments X w E F).2,le_div_iff₀ qp]
  calc _ ≤ A*V*Q := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left conditional apos.le) qp.le
       _ = (Q*A)*V := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right cap vp

/-- The expected weighted diagonal and squared off-diagonal Frobenius error
are polynomial in saddle mass even when the band contains exponentially many
candidate rows. A zero entry can stand for a masked same-prime pair. -/
theorem ordinary_gram_error_budget {b : ℕ} {α u ε : ℝ}
    (large : 1<(Fixed.B b:ℝ)) (ap : 0≤α)
    (saddle : saddleMean (primeBand b) α=log (Fixed.B b)*u) (ep : 0≤ε)
    (D : BandRow b→ℝ) (F : BandRow b→BandRow b→ℝ)
    (diag : ∀ i, D i ≤ ε*bandRowWeight α i)
    (off : ∀ i j, F i j ≤ ε*(bandRowWeight α i*bandRowWeight α j)) :
    ∑ i,D i ≤ 8*u*ε ∧ ∑ i,∑ j,F i j ≤ 64*u^2*ε := by
  let m := ∑ i : BandRow b, bandRowWeight α i
  have mp : 0 ≤ m := sum_nonneg (fun i _ => by dsimp [bandRowWeight]; positivity)
  have le := band_row_weight_sum large ap saddle
  change m≤8*u at le
  have ds := sum_le_sum (s:=univ) (fun i _ => diag i)
  rw [←mul_sum] at ds
  have fs := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ => off i j))
  simp only [←mul_sum,←sum_mul] at fs
  constructor
  · exact ds.trans ((mul_le_mul_of_nonneg_left le ep).trans_eq (mul_comm ..))
  · calc _ ≤ ε*(m*m) := fs
         _ ≤ ε*((8*u)*(8*u)) := mul_le_mul_of_nonneg_left (mul_self_le_mul_self mp le) ep
         _ = _ := by ring

/-- The tolerance required by the empirical Gram comparison fits the two-field
search-box budget for the actual 2d+1 cells and the saddle window u ≤ 110d. -/
theorem ordinary_gram_schedule_budget (C : ℝ) (cp : 0≤C) :
    ∃ b₀ : ℕ, ∀ b≥b₀, ∀ u : ℝ, 0<u → u≤110*(Fixed.d b:ℝ) →
    let τ := 1/(768*u*(2*(Fixed.d b:ℝ)+1))
    let ε := C*exp (-7*(Fixed.z b:ℝ)^2)
    ((8*u+64*u^2)*ε)/τ^2+2432*(Fixed.B b:ℝ)^2*exp (-π*((b:ℝ)^2)^2/2)<1 := by
  let A : ℝ := 8*110+64*110^2
  let D : ℝ := 768*110*3
  obtain ⟨m,save⟩ := fixed_class_accuracy (A*D^2*C)
  refine ⟨max m 1000,?_⟩
  intro b big u up ub τ ε
  obtain ⟨sm,bt⟩ := max_le_iff.mp big
  let t : ℝ := b
  let z : ℝ := Fixed.z b
  let d : ℝ := Fixed.d b
  have dt : d≤t := by dsimp only [d,t]; exact_mod_cast Fixed.degree_le_bits b
  have tp : 1≤t := by dsimp only [t]; exact_mod_cast (by omega : 1≤b)
  have tn := zero_le_one.trans tp
  have z1 : 1≤z := by dsimp [z,Fixed.z]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le b.log2)
  have tz : t≤exp z := by
    have n : t≤(2:ℝ)^(Fixed.z b) := by dsimp only [t]; exact_mod_cast (Nat.lt_log2_self.le : b ≤ 2^(Fixed.z b))
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
      (by linarith [exp_one_gt_d9] : (2:ℝ) ≤ exp 1) (Fixed.z b)
    rw [←exp_nat_mul,mul_one] at h
    exact n.trans h
  have ut : u≤110*t := by change u≤110*d at ub; linarith only [ub,dt]
  have bs : 8*u+64*u^2≤A*t^2 := by
    have u2 := pow_le_pow_left₀ up.le ut 2
    dsimp only [A]
    nlinarith only [ut,u2,mul_nonneg tn (sub_nonneg.mpr tp)]
  have cells : 2*d+1≤3*t := by linarith only [dt,tp]
  have cpos : 0≤2*d+1 := by dsimp only [d]; positivity
  have norm : 768*u*(2*d+1)≤D*t^2 := calc
    _ ≤ (768*(110*t))*(3*t) := mul_le_mul (by linarith only [ut]) cells cpos (by positivity)
    _ = _ := by dsimp only [D]; ring
  have norm2 := pow_le_pow_left₀ (mul_nonneg (by positivity : 0≤768*u) cpos) norm 2
  have poly : (8*u+64*u^2)*(768*u*(2*d+1))^2 ≤ A*D^2*t^6 := calc
    _ ≤ (A*t^2)*(D*t^2)^2 := mul_le_mul bs norm2 (sq_nonneg _) (by dsimp only [A]; positivity)
    _ = _ := by ring
  have pot := pow_le_pow_left₀ tn tz 6
  rw [←exp_nat_mul] at pot
  have ex := mul_le_mul_of_nonneg_right pot (exp_pos (-7*z^2)).le
  rw [←exp_add] at ex
  have e : t^6*exp (-7*z^2) ≤ exp (-z^2) := ex.trans (exp_le_exp.mpr (by
    norm_num; nlinarith only [mul_nonneg (zero_le_one.trans z1) (sub_nonneg.mpr z1)]))
  have s : ((8*u+64*u^2)*ε)/τ^2 ≤ 1/2 := calc
    _ = ((8*u+64*u^2)*(768*u*(2*d+1))^2)*(C*exp (-7*z^2)) := by
      dsimp only [τ,ε,d,z]; simp only [one_div,inv_pow,div_inv_eq_mul]; ring
    _ ≤ (A*D^2*t^6)*(C*exp (-7*z^2)) := mul_le_mul_of_nonneg_right poly (mul_nonneg cp (exp_pos _).le)
    _ = (A*D^2*C)*(t^6*exp (-7*z^2)) := by ring
    _ ≤ (A*D^2*C)*exp (-z^2) := mul_le_mul_of_nonneg_left e (by dsimp only [A,D]; positivity)
    _ ≤ _ := save b sm
  have bp : 2≤(Fixed.B b:ℝ) := by
    have hd := Fixed.degree_pos (b:=b) (by omega)
    have hz : 0<Fixed.z b := Nat.succ_pos _
    have hh : 0<Fixed.h b := Nat.mul_pos hd hz
    have expo : 0<Fixed.beta b := Nat.mul_pos (by decide : 0<1000) hh
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) expo : 2^1 ≤ Fixed.B b)
  have tail := coefficient_tail_lt_half_mark bt
  have inv : (1:ℝ)/(2*(Fixed.B b:ℝ))≤1/4 := by
    rw [div_le_div_iff₀ (by positivity : 0<2*(Fixed.B b:ℝ)) (by norm_num : (0:ℝ)<4)]; linarith only [bp]
  linarith only [s,tail.trans_le inv]

/-- The diagonal input score includes the square root of its prime's saddle
weight. For off-diagonal entries the input is the centered normalized Gram
score. All scores here are evaluated on the same unrestricted boxed tuple. -/
theorem ordinary_gram_simultaneous_box {n ell : ℕ} {ι : Type*}
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (α u ε τ : ℝ) :
    let b := n.log2+1
    let I := BandRow b
    let S := PrescribedRows.unrestricted n ell
    1<(Fixed.B b:ℝ) → 0≤α → saddleMean (primeBand b) α=log (Fixed.B b)*u →
    0≤ε → 0<τ →
    ∀ (X : I ⊕ (I×I) → Finset ι) (w : I ⊕ (I×I) → ι→ℝ)
      (E F : I ⊕ (I×I) → ι→ℤ×ℤ→Prop) (d : I ⊕ (I×I) → ℝ),
    let M := fun j => twoFieldSecond S S (X j) (w j) (E j) (F j) -
      2*d j*twoFieldMean S S (X j) (w j) (E j) (F j)+(d j)^2
    (∀ i, M (.inl i) ≤ ε*bandRowWeight α i) →
    (∀ i j, M (.inr (i,j)) ≤ ε*(bandRowWeight α i*bandRowWeight α j)) →
    ((8*u+64*u^2)*ε)/τ^2 + 2432*(Fixed.B b:ℝ)^2*exp (-π*((b:ℝ)^2)^2/2)<1 →
    ∃ x y : ℤ×ℤ, inCoefficientBox n x ∧ inCoefficientBox n y ∧
      let err := fun j => twoFieldScore (X j) (w j) (E j) (F j) x y - d j
      (∑ i, (err (.inl i))^2)+(∑ i,∑ j,(err (.inr (i,j)))^2)<τ^2 ∧
      ∀ v : I→ℝ, |∑ i,∑ j,v i*err (.inr (i,j))*v j|≤τ*(∑ i,(v i)^2) := by
  intro b I S large ap saddle ep tp X w E F d M diag off budget
  obtain ⟨gd,gf⟩ := ordinary_gram_error_budget large ap saddle ep
    (fun i => M (.inl i)) (fun i j => M (.inr (i,j))) diag off
  have upper : (∑ j,M j)≤(8*u+64*u^2)*ε := by
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type (fun ij : I×I => M (.inr ij)),add_mul]
    exact add_le_add gd gf
  have fits : (∑ j,M j/τ^2)+2432*(Fixed.B b:ℝ)^2*exp (-π*((b:ℝ)^2)^2/2)<1 := by
    rw [←sum_div]
    exact (add_le_add_left (div_le_div_of_nonneg_right upper (sq_nonneg _)) _).trans_lt budget
  obtain ⟨x,y,_,_,bx,by',small⟩ := twoField_simultaneous_box_energy S S target univ X w E F d (fun _=>τ) fits
  let err := fun j => twoFieldScore (X j) (w j) (E j) (F j) x y - d j
  change (∑ j,(err j)^2/τ^2)<1 at small
  rw [←sum_div,div_lt_one (sq_pos_of_pos tp),Fintype.sum_sum_type,Fintype.sum_prod_type (fun ij : I×I => (err (.inr ij))^2)] at small
  refine ⟨x,y,bx,by',small,?_⟩
  intro v
  have nn : (0:ℝ)≤∑ i, (err (.inl i))^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  exact Cogentic.gram_frobenius_error (fun i j => err (.inr (i,j))) v τ tp.le
    ((le_add_of_nonneg_left nn).trans small.le)


end
end Cogentic.Construction

#print axioms Cogentic.Construction.ordinary_gram_simultaneous_box
#print axioms Cogentic.Construction.admitted_second_bound
