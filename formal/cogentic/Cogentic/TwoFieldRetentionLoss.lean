import Cogentic.TwoFieldMoments
import Cogentic.CoprimeFamilies
import Cogentic.SmoothDerivative

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

/-- Probability of a joint event, including events coupling the two fields. -/
def twoFieldProbability {n ell : ℕ} (R T : PrescribedRows n ell) (G : (ℤ×ℤ)→(ℤ×ℤ)→Prop) : ℝ :=
  ∑' k : R.CoeffPoint false × T.CoeffPoint true, if G k.1.val k.2.val then twoFieldWeight R T k else 0

/-- Disintegrate a coupled event by fixing the actual coefficient tuple in the first field. -/
theorem twoField_probability_fubini {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (G : (ℤ×ℤ)→(ℤ×ℤ)→Prop) :
    HasSum (fun x : R.CoeffPoint false => R.pointMass false x*prescribedProbability T true (G x.val))
      (twoFieldProbability R T G) := by
  let V (k : R.CoeffPoint false × T.CoeffPoint true) := if G k.1.val k.2.val then twoFieldWeight R T k else 0
  have wp (k) : 0≤twoFieldWeight R T k := mul_nonneg (R.pointMass_nonneg ..) (T.pointMass_nonneg ..)
  have vs : Summable V := Summable.of_nonneg_of_le
    (fun k => by dsimp only [V]; split <;> first | exact wp k | rfl)
    (fun k => by dsimp only [V]; split <;> first | exact wp k | rfl) (twoField_total R T target).summable
  change HasSum _ (∑' k,V k)
  rw [vs.tsum_prod]
  apply vs.prod.hasSum.congr_fun
  intro x
  have h := ((T.point_event true target (G x.val)).mul_left (R.pointMass false x)).tsum_eq
  rw [←h]
  apply tsum_congr
  intro y
  by_cases g : G x.val y.val <;> simp [V,twoFieldWeight,g]

private theorem probability_nonneg {n ell : ℕ} (R : PrescribedRows n ell) (s : Bool)
    (P : ℤ×ℤ→Prop) [DecidablePred P] : 0≤prescribedProbability R s P := by
  apply div_nonneg
  · exact tsum_nonneg (fun k => by split <;> first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | rfl)
  · exact tsum_nonneg (fun k => mul_nonneg (exp_pos _).le (exp_pos _).le)

private theorem probability_mono_on {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (s : Bool) (A B : ℤ×ℤ→Prop)
    [DecidablePred A] [DecidablePred B] (sub : ∀ x : R.CoeffPoint s, A x.val → B x.val) :
    prescribedProbability R s A≤prescribedProbability R s B := by
  have ha := R.point_event s target A
  have hb := R.point_event s target B
  rw [←ha.tsum_eq,←hb.tsum_eq]
  apply ha.summable.tsum_le_tsum _ hb.summable
  intro x
  by_cases a : A x.val
  · simp only [if_pos a,if_pos (sub x a),le_refl]
  · simp only [if_neg a]; split <;> first | exact R.pointMass_nonneg .. | rfl

private theorem probability_disjoint_loss {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (s : Bool) (A B G : ℤ×ℤ→Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred G]
    (sub : ∀ x : R.CoeffPoint s, B x.val → A x.val)
    (miss : ∀ x : R.CoeffPoint s, G x.val → A x.val ∧ ¬B x.val) :
    prescribedProbability R s G≤prescribedProbability R s A-prescribedProbability R s B := by
  have ha := R.point_event s target A
  have hb := R.point_event s target B
  have hg := R.point_event s target G
  have both := hg.add hb
  apply le_sub_iff_add_le.mpr
  rw [←both.tsum_eq,←ha.tsum_eq]
  apply both.summable.tsum_le_tsum _ ha.summable
  intro x
  by_cases g : G x.val
  · simp only [if_pos g,if_pos (miss x g).1,if_neg (miss x g).2,add_zero,le_refl]
  · by_cases b : B x.val
    · simp only [if_neg g,if_pos b,if_pos (sub x b),zero_add,le_refl]
    · simp only [if_neg g,if_neg b,add_zero]; split <;> first | exact R.pointMass_nonneg .. | rfl

private theorem twoField_loss_rows {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (A L B : ℤ×ℤ→Prop)
    [DecidablePred A] [DecidablePred L] [DecidablePred B]
    (G : (ℤ×ℤ)→(ℤ×ℤ)→Prop) (s t : ℝ)
    (first : prescribedProbability R false (fun x=>A x ∧ ¬L x ) ≤ s*prescribedProbability R false A)
    (rows : ∀ x : R.CoeffPoint false, prescribedProbability T true (G x.val) ≤
      (if A x.val ∧ ¬L x.val then prescribedProbability T true B else 0)+
      (if A x.val then t*prescribedProbability T true B else 0)) :
    twoFieldProbability R T G≤(s+t)*(prescribedProbability R false A*prescribedProbability T true B) := by
  let p := prescribedProbability T true B
  have hb := R.point_event false target (fun x=>A x ∧ ¬L x)
  have ha := R.point_event false target A
  have gs := twoField_probability_fubini R T target G
  have upper := (hb.mul_right p).add (ha.mul_right (t*p))
  have pt (x : R.CoeffPoint false) := mul_le_mul_of_nonneg_left (rows x) (R.pointMass_nonneg false x)
  have cmp := gs.summable.tsum_le_tsum (fun x => by
    by_cases a : A x.val <;> by_cases l : L x.val <;> simpa [a,l,p,mul_add] using pt x) upper.summable
  rw [gs.tsum_eq,upper.tsum_eq] at cmp
  have h := mul_le_mul_of_nonneg_right first (probability_nonneg T true B)
  linarith only [cmp,h]

/-- Executable field value at a single coefficient point. -/
def boxedFieldValue (n ell a : ℕ) (s : Bool) (x : ℤ×ℤ) : ℕ :=
  let inp := TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat x.1.toNat x.2.toNat)
  Marking.value (inp.coeffs s) a

private theorem boxed_value_facts {n ell a : ℕ} (R : PrescribedRows n ell) (s : Bool)
    (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (x : R.CoeffPoint s) (box : inCoefficientBox n x.val) :
    let J := sieveBand n ell (R.prefactor a s)
    let v := boxedFieldValue n ell a s x.val
    let i := R.intercept a s x.val.1 x.val.2
    (supportedValue J i → v≠0 ∧ 4*v.primeFactors.card≤n.log2+1) ∧
    (∀ m : ℕ, m≠0 → m.Coprime (R.prefactor a s) →
      (supportedValue (J\m.primeFactors) i ↔ supportedValue J i ∧ m.Coprime v)) := by
  intro J v i
  let b := n.log2+1
  have uu := Int.toNat_of_nonneg box.1.le
  have vv := Int.toNat_of_nonneg box.2.2.1.le
  have bounds : x.val.1.toNat≤2*b^2*Fixed.U b*Fixed.A b ∧ x.val.2.toNat≤2*b^2*Fixed.U b := by
    exact ⟨by exact_mod_cast uu.trans_le box.2.1,by exact_mod_cast vv.trans_le box.2.2.2⟩
  have ok : R.compatible s x.val.1.toNat x.val.2.toNat := by rw [uu,vv]; exact x.property
  obtain ⟨amin,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  have large : 10004≤Fixed.d (n.log2+1) := le_trans (by decide) big
  have eq := R.box_smooth_iff hn large comp target absent cap grid bounds s ok
  rw [uu,vv] at eq
  refine ⟨fun h => ⟨(eq.mp h).1, mark_sparsity hn big comp target absent amin cap ⟨bounds.1,bounds.2,bounds⟩ s (eq.mp h)⟩,?_⟩
  intro m nz mc
  have cut := R.box_smooth_coprime_iff hn large comp target absent cap grid bounds s ok nz mc
  rw [uu,vv] at cut
  exact cut.trans (and_congr_left (fun _ => eq.symm))

/-- Both boxed field values are smooth, but share a prime. -/
def boxedSharedPrime {n ell : ℕ} (R T : PrescribedRows n ell) (a : ℕ) (x y : ℤ×ℤ) : Prop :=
  supportedValue (sieveBand n ell (R.prefactor a false)) (R.intercept a false x.1 x.2) ∧
  supportedValue (sieveBand n ell (T.prefactor a true)) (T.intercept a true y.1 y.2) ∧
  inCoefficientBox n x ∧ inCoefficientBox n y ∧
  ¬(boxedFieldValue n ell a false x).Coprime (boxedFieldValue n ell a true y)

/-- Under the original independent coefficient laws, sharing any prime costs
only a small relative fraction of the two smoothness marginals. The first
exclusion removes forced factors in the other field. The second uses the
actual first value's factor set, whose size is at most b/4. -/
theorem twoField_shared_prime_loss (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R T : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks →
    (R.prefactor a false).Coprime (T.prefactor a true) →
    let p := prescribedProbability R false (fun k=>
      supportedValue (sieveBand n ell (R.prefactor a false)) (R.intercept a false k.1 k.2))
    let q := prescribedProbability T true (fun k=>
      supportedValue (sieveBand n ell (T.prefactor a true)) (T.intercept a true k.1 k.2))
    twoFieldProbability R T (boxedSharedPrime R T a) ≤
      (36*(3+(b:ℝ)/4)*(Fixed.B b:ℝ)^(-199/400:ℝ)+720*exp (-(Fixed.U b:ℝ)))*(p*q) := by
  obtain ⟨b₁,avoid⟩ := PrescribedRows.smooth_probability_avoid_sharp line 1
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 130000
  refine ⟨max 3 (max b₁ b₂),?_⟩
  intro n ell a R T b huge hn comp target absent mark forced p q
  obtain ⟨three,hb,hdeg⟩ := (max_le_iff.trans (and_congr_right (fun _ => max_le_iff))).mp huge
  have big := degree b hdeg
  let J := sieveBand n ell (R.prefactor a false)
  let K := sieveBand n ell (T.prefactor a true)
  let P := (T.prefactor a true).primeFactors
  let A (x : ℤ×ℤ) := supportedValue J (R.intercept a false x.1 x.2)
  let B (y : ℤ×ℤ) := supportedValue K (T.intercept a true y.1 y.2)
  let L (x : ℤ×ℤ) := supportedValue (J\P) (R.intercept a false x.1 x.2)
  let G := boxedSharedPrime R T a
  let power := (Fixed.B b:ℝ)^(-199/400:ℝ)
  let e := exp (-(Fixed.U b:ℝ))
  let s := 36*3*power+360*e
  let t := 36*((b:ℝ)/4)*power+360*e
  have pp : 0≤p := probability_nonneg R false A
  have qp : 0≤q := probability_nonneg T true B
  have pw : 0≤power := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have tp : 0≤t := by dsimp only [t,e]; positivity
  have nz : T.prefactor a true≠0 := (T.pre_bounds target a true).1.ne'
  have counts : P.card≤3 := T.prefactor_primeFactors_card_le_three target a true
  have first : prescribedProbability R false (fun x=>A x ∧ ¬L x) ≤ s*p := by
    have hl := (avoid R hb hn comp target absent mark false P (by simpa only [pow_one] using counts.trans three)).2.2
    have sub (x : R.CoeffPoint false) (h : L x.val) : A x.val :=
      ((supportedValue_exclude_primeFactors J (fun _ hp => (mem_primeBand.mp (mem_filter.mp hp).1).1) _ nz).mp h).1
    have difference := probability_disjoint_loss R target false A L (fun x=>A x ∧ ¬L x) sub (fun _ h=>h)
    have small : (36*(P.card:ℝ)*power+360*e)*p ≤ s*p := by
      apply mul_le_mul_of_nonneg_right _ pp
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast counts) (by norm_num)) pw
    exact difference.trans (hl.trans small)
  have rows (x : R.CoeffPoint false) : prescribedProbability T true (G x.val) ≤
      (if A x.val ∧ ¬L x.val then q else 0)+(if A x.val then t*q else 0) := by
    have noneRow (no : ∀ y, ¬G x.val y) : prescribedProbability T true (G x.val)=0 := by
      unfold prescribedProbability
      simp only [if_neg (no _),tsum_zero,zero_div]
    by_cases ax : A x.val
    · by_cases lx : L x.val
      · simp only [ax,lx,not_true_eq_false,true_and,if_false,if_true,zero_add]
        by_cases box : inCoefficientBox n x.val
        · let m := boxedFieldValue n ell a false x.val
          have data := boxed_value_facts R false hn big comp target absent mark x box
          have ⟨nonzero,card⟩ := data.1 ax
          have cop : m.Coprime (T.prefactor a true) := ((data.2 _ nz forced.symm).mp lx).2.symm
          have mc : 4*m.primeFactors.card≤b := card
          let cut := fun y : ℤ×ℤ => supportedValue (K\m.primeFactors) (T.intercept a true y.1 y.2)
          have loss := (avoid T hb hn comp target absent mark true m.primeFactors (by rw [pow_one]; omega)).2.2
          have sub (y : T.CoeffPoint true) (h : cut y.val) : B y.val :=
            ((supportedValue_exclude_primeFactors K (fun _ hp => (mem_primeBand.mp (mem_filter.mp hp).1).1) _ nonzero).mp h).1
          have miss (y : T.CoeffPoint true) (h : G x.val y.val) : B y.val ∧ ¬cut y.val := by
            have cy := (boxed_value_facts T true hn big comp target absent mark y h.2.2.2.1).2 m nonzero cop
            exact ⟨h.2.1,fun ev=>h.2.2.2.2 ((cy.mp ev).2)⟩
          have difference := probability_disjoint_loss T target true B cut (G x.val) sub miss
          have cast : 4*(m.primeFactors.card:ℝ)≤b := by exact_mod_cast mc
          have small : (36*(m.primeFactors.card:ℝ)*power+360*e)*q ≤ t*q := by
            apply mul_le_mul_of_nonneg_right _ qp
            apply add_le_add _ le_rfl
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [cast]) (by norm_num)) pw
          exact difference.trans (loss.trans small)
        · rw [noneRow (fun _ h=>box h.2.2.1)]
          exact mul_nonneg tp qp
      · simp only [ax,lx,not_false_eq_true,true_and,if_true]
        exact (probability_mono_on T target true (G x.val) B (fun _ h=>h.2.1)).trans (le_add_of_nonneg_right (mul_nonneg tp qp))
    · simp only [ax,false_and,if_false,zero_add]
      exact (noneRow (fun _ h=>ax h.1)).le
  have est := twoField_loss_rows R T target A L B G s t first rows
  change twoFieldProbability R T G ≤ (s+t)*(p*q) at est
  exact est.trans_eq (by dsimp only [s,t,power,e]; ring)

private theorem twoField_event_sum {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (G : (ℤ×ℤ)→(ℤ×ℤ)→Prop) :
    HasSum (fun k : R.CoeffPoint false × T.CoeffPoint true =>
      if G k.1.val k.2.val then twoFieldWeight R T k else 0) (twoFieldProbability R T G) := by
  have wp (k) : 0≤twoFieldWeight R T k := mul_nonneg (R.pointMass_nonneg ..) (T.pointMass_nonneg ..)
  apply Summable.hasSum
  exact Summable.of_nonneg_of_le (fun k => by split <;> first | exact wp k | rfl)
    (fun k => by split <;> first | exact wp k | rfl) (twoField_total R T target).summable

theorem twoField_probability_rectangle {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (A B : ℤ×ℤ→Prop)
    [DecidablePred A] [DecidablePred B] :
    twoFieldProbability R T (fun x y=>A x∧B y)=prescribedProbability R false A*prescribedProbability T true B := by
  rw [←(twoField_rectangle R T target A B).tsum_eq]
  apply tsum_congr
  intro k
  by_cases both : A k.1.val∧B k.2.val <;> simp [both]

theorem twoField_probability_cover {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (G A B : (ℤ×ℤ)→(ℤ×ℤ)→Prop)
    (cover : ∀ x : R.CoeffPoint false, ∀ y : T.CoeffPoint true, G x.val y.val → A x.val y.val ∨ B x.val y.val) :
    twoFieldProbability R T G ≤ twoFieldProbability R T A+twoFieldProbability R T B := by
  have hg := twoField_event_sum R T target G
  have hab := (twoField_event_sum R T target A).add (twoField_event_sum R T target B)
  rw [←hg.tsum_eq,←hab.tsum_eq]
  apply hg.summable.tsum_le_tsum _ hab.summable
  intro k
  have pos : 0≤twoFieldWeight R T k := mul_nonneg (R.pointMass_nonneg ..) (T.pointMass_nonneg ..)
  have ab := cover k.1 k.2
  by_cases g : G k.1.val k.2.val <;> by_cases a : A k.1.val k.2.val <;> by_cases b : B k.1.val k.2.val <;>
    first | exact False.elim ((ab g).elim a b) | simp [g,a,b,pos]

/-- Boxed doubly smooth coefficients that share a prime or have an ordinary
derivative failure away from the corresponding field's slope modulus. -/
def boxedSharedOrSingular {n ell : ℕ} (R T : PrescribedRows n ell) (a : ℕ) (x y : ℤ×ℤ) : Prop :=
  supportedValue (sieveBand n ell (R.prefactor a false)) (R.intercept a false x.1 x.2) ∧
  supportedValue (sieveBand n ell (T.prefactor a true)) (T.intercept a true y.1 y.2) ∧
  inCoefficientBox n x ∧ inCoefficientBox n y ∧
  (¬(boxedFieldValue n ell a false x).Coprime (boxedFieldValue n ell a true y) ∨
    boxedOrdinarySingular R false a x ∨ boxedOrdinarySingular T true a y)

theorem twoField_shared_or_singular_loss (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R T : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks →
    (R.prefactor a false).Coprime (T.prefactor a true) →
    let p := prescribedProbability R false (fun k=>
      supportedValue (sieveBand n ell (R.prefactor a false)) (R.intercept a false k.1 k.2))
    let q := prescribedProbability T true (fun k=>
      supportedValue (sieveBand n ell (T.prefactor a true)) (T.intercept a true k.1 k.2))
    twoFieldProbability R T (boxedSharedOrSingular R T a) ≤
      (36*(3+(b:ℝ)/4)*(Fixed.B b:ℝ)^(-199/400:ℝ)+720*exp (-(Fixed.U b:ℝ))+
        2*((b:ℝ)/2^(500*Fixed.h b)))*(p*q) := by
  obtain ⟨b₁,shared⟩ := twoField_shared_prime_loss line
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 130000
  refine ⟨max b₁ b₂,?_⟩
  intro n ell a R T b huge hn comp target absent mark cop p q
  have big := degree b (max_le_iff.mp huge).2
  let e := (b:ℝ)/2^(500*Fixed.h b)
  let h := 36*(3+(b:ℝ)/4)*(Fixed.B b:ℝ)^(-199/400:ℝ)+720*exp (-(Fixed.U b:ℝ))
  let A (x : ℤ×ℤ) := supportedValue (sieveBand n ell (R.prefactor a false)) (R.intercept a false x.1 x.2)
  let B (y : ℤ×ℤ) := supportedValue (sieveBand n ell (T.prefactor a true)) (T.intercept a true y.1 y.2)
  let L (x : ℤ×ℤ) := A x ∧ boxedOrdinarySingular R false a x
  let D (y : ℤ×ℤ) := B y ∧ boxedOrdinarySingular T true a y
  let U (x y : ℤ×ℤ) := (L x ∧ B y) ∨ (A x ∧ D y)
  have one := shared R T (max_le_iff.mp huge).1 hn comp target absent mark cop
  change twoFieldProbability R T (boxedSharedPrime R T a)≤h*(p*q) at one
  have ll := R.boxed_ordinary_singular_loss_sharp hn big comp target absent mark false (fun _=>True)
  have rr := T.boxed_ordinary_singular_loss_sharp hn big comp target absent mark true (fun _=>True)
  simp only [true_and] at ll rr
  change prescribedProbability R false L≤e*p at ll
  change prescribedProbability T true D≤e*q at rr
  have rect := twoField_probability_cover R T target U (fun x y=>L x∧B y) (fun x y=>A x∧D y) (fun _ _ h=>h)
  rw [twoField_probability_rectangle R T target L B,twoField_probability_rectangle R T target A D] at rect
  have lp := mul_le_mul_of_nonneg_right ll (probability_nonneg T true B)
  have rp := mul_le_mul_of_nonneg_left rr (probability_nonneg R false A)
  have second : twoFieldProbability R T U≤2*e*(p*q) := by
    change twoFieldProbability R T U ≤ prescribedProbability R false L*q+p*prescribedProbability T true D at rect
    change prescribedProbability R false L*q ≤ e*p*q at lp
    change p*prescribedProbability T true D ≤ p*(e*q) at rp
    linarith only [rect,lp,rp]
  have cover := twoField_probability_cover R T target (boxedSharedOrSingular R T a) (boxedSharedPrime R T a) U (by
    intro x y ev
    rcases ev with ⟨ax,by',bx,bybox,sh | ls | rs⟩
    · exact Or.inl ⟨ax,by',bx,bybox,sh⟩
    · exact Or.inr (Or.inl ⟨⟨ax,ls⟩,by'⟩)
    · exact Or.inr (Or.inr ⟨ax,by',rs⟩))
  change twoFieldProbability R T (boxedSharedOrSingular R T a)≤(h+2*e)*(p*q)
  linarith only [cover,one,second]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.twoField_shared_prime_loss

#print axioms Cogentic.Construction.twoField_shared_or_singular_loss
