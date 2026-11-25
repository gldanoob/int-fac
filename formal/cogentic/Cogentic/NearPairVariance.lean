import Cogentic.TwoFieldMoments
import Cogentic.MarkIntervals
import Cogentic.GaussianMeans
import Cogentic.SmoothBox

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

/-- The exact integer separation cutoff in the conditional two-mark estimate. -/
def nearRadius (b : ℕ) : ℕ := 2^(9950*Fixed.h b)

theorem nearRadius_schedule (b : ℕ) :
    nearRadius b*(dyadicUnit b)^50=Fixed.A b ∧ nearRadius b*(dyadicUnit b)^47=cellMarkCount b ∧
    (Fixed.B b)^3≤nearRadius b := by
  dsimp only [nearRadius,dyadicUnit,Fixed.A,cellMarkCount,Fixed.B,Fixed.beta]
  simp only [←Nat.pow_mul,←Nat.pow_add]
  refine ⟨?_,?_,Nat.pow_le_pow_right (by decide) (by omega)⟩ <;> congr 1 <;> omega

theorem nearRadius_iff {b x y : ℕ} :
    x.dist y≤nearRadius b ↔ |(y:ℝ)-x| *(dyadicUnit b:ℝ)^50≤(Fixed.A b:ℝ) := by
  have eq : ((x.dist y:ℕ):ℝ)=|(y:ℝ)-x| := by
    rcases le_total x y with xy | yx
    · rw [Nat.dist_eq_sub_of_le xy,Nat.cast_sub xy,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast xy))]
    · rw [Nat.dist_eq_sub_of_le_right yx,Nat.cast_sub yx,abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast yx))]
      ring
  have up : 0<(dyadicUnit b:ℝ)^50 := by dsimp [dyadicUnit]; positivity
  rw [←eq,←(nearRadius_schedule b).1,Nat.cast_mul,Nat.cast_pow,mul_le_mul_iff_left₀ up]
  exact_mod_cast Iff.rfl

private theorem count_residue {X : Finset ℕ} {lo len q r : ℕ} (qpos : 0<q)
    (here : ∀ x∈X, x∈Ico lo (lo+len) ∧ x ≡ r [MOD q]) :
    (X.card:ℝ)*q ≤ len+q := by
  have sub : X⊆(Ico lo (lo+len)).filter (fun x=>x ≡ r [MOD q]) :=
    fun x hx => mem_filter.mpr (here x hx)
  have h := (abs_le.mp (interval_residue_error (Nat.le_add_right lo len) qpos r)).2
  simp only [Nat.cast_add,add_sub_cancel_left] at h
  have size : (X.card:ℝ)≤((Ico lo (lo+len)).filter (fun x=>x ≡ r [MOD q])).card :=
    Nat.cast_le.mpr (card_le_card sub)
  have qp : 0<(q:ℝ) := by exact_mod_cast qpos
  have := (le_div_iff₀ qp).mp (show (X.card:ℝ)-1≤len/q by linarith only [h,size])
  linarith

/-- Uniformly in the first mark, a target residue class contains at most
(2r+1)/q+1 candidate marks within integer distance r. -/
theorem near_neighbors_in_class (Y : Finset ℕ) (a r q v : ℕ) (qp : 0<q)
    (res : ∀ y∈Y, y ≡ v [MOD q]) :
    (((Y.filter (fun y=>a.dist y≤r)).card:ℝ)*q)≤2*(r:ℝ)+1+q := by
  have h := count_residue (X:=Y.filter (fun y=>a.dist y≤r)) (lo:=a-r) (len:=2*r+1) qp
    (r:=v) (fun y hy => by
      obtain ⟨hm,close⟩ := mem_filter.mp hy
      refine ⟨mem_Ico.mpr ⟨?_,?_⟩,res y hm⟩ <;> unfold Nat.dist at close <;> omega)
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using h

/-- A pair of residue classes within constructor cells preserves the fixed
X⁻⁴⁷ close-pair saving, even after both reciprocal class densities are
removed. The right-hand class may belong to any cell. -/
theorem near_pair_cell_sum (b : ℕ) (cell : Option (Bool × Fin (Fixed.d b))) (X Y : Finset ℕ)
    (q s u v : ℕ) (qp : 0<q) (sp : 0<s) (qr : q≤(Fixed.B b)^3) (sr : s≤(Fixed.B b)^3)
    (inside : ∀ a∈X, a∈Ico (firstCellMark b cell) (firstCellMark b cell+cellMarkCount b) ∧ a ≡ u [MOD q])
    (classY : ∀ y∈Y, y ≡ v [MOD s]) (f : ℕ→ℕ→ℝ) (D : ℝ) (dp : 0≤D)
    (bound : ∀ a∈X, ∀ y∈Y, a.dist y≤nearRadius b → |f a y|≤D) :
    ((q:ℝ)*s)*|∑ a∈X, ∑ y∈Y.filter (fun y=>a.dist y≤nearRadius b), f a y|/(cellMarkCount b:ℝ)^2 ≤
      8*D/(dyadicUnit b:ℝ)^47 := by
  let M : ℝ := cellMarkCount b
  let r : ℝ := nearRadius b
  let z : ℝ := (dyadicUnit b:ℝ)^47
  have mp : 0<M := by dsimp [M,cellMarkCount]; positivity
  have rp : 1≤r := by dsimp [r,nearRadius]; exact_mod_cast Nat.one_le_two_pow
  have zp : 1≤z := by dsimp [z,dyadicUnit]; exact_mod_cast (Nat.one_le_pow 47 (2^(Fixed.h b)) (Nat.one_le_two_pow))
  have eq : r*z=M := by dsimp [r,z,M]; exact_mod_cast (nearRadius_schedule b).2.1
  have qm : (q:ℝ)≤M := by
    have h : (q:ℝ)≤r := by dsimp [r]; exact_mod_cast qr.trans (nearRadius_schedule b).2.2
    exact h.trans (eq ▸ le_mul_of_one_le_right (by linarith) zp)
  have sm : (s:ℝ)≤r := by dsimp [r]; exact_mod_cast sr.trans (nearRadius_schedule b).2.2
  have cx := count_residue qp inside
  change (X.card:ℝ)*q ≤ M+q at cx
  have cardx : (X.card:ℝ)*q≤2*M := by linarith only [cx,qm]
  let close (a : ℕ) := Y.filter (fun y=>a.dist y≤nearRadius b)
  have inner (a : ℕ) (ha : a∈X) : (s:ℝ)*|∑ y∈close a,f a y|≤4*r*D := by
    have cnt := near_neighbors_in_class Y a (nearRadius b) s v sp classY
    change ((close a).card:ℝ)*s≤2*r+1+s at cnt
    have row : |∑ y∈close a,f a y|≤((close a).card:ℝ)*D := by
      apply (abs_sum_le_sum_abs ..).trans
      apply le_trans (sum_le_sum (fun y hy => bound a ha y (mem_filter.mp hy).1 (mem_filter.mp hy).2))
      rw [sum_const,nsmul_eq_mul]
    have sc := mul_le_mul_of_nonneg_left row (Nat.cast_nonneg (α:=ℝ) s)
    have ch := mul_le_mul_of_nonneg_right (show ((close a).card:ℝ)*s≤4*r by linarith only [cnt,sm,rp]) dp
    linarith only [sc,ch]
  have agg : (s:ℝ)*|∑ a∈X, ∑ y∈close a,f a y|≤(X.card:ℝ)*(4*r*D) := by
    apply (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs ..) (Nat.cast_nonneg (α:=ℝ) s)).trans
    rw [Finset.mul_sum]
    exact (sum_le_sum inner).trans_eq (by rw [sum_const,nsmul_eq_mul])
  have all := mul_le_mul_of_nonneg_left agg (Nat.cast_nonneg (α:=ℝ) q)
  have rad := mul_le_mul_of_nonneg_right cardx (show 0≤4*r*D by positivity)
  have total : ((q:ℝ)*s)*|∑ a∈X, ∑ y∈close a,f a y|≤8*M*r*D := by linarith only [all,rad]
  change _/M^2≤8*D/z
  apply (div_le_div_iff₀ (sq_pos_of_pos mp) (by linarith : 0<z)).mpr
  apply (mul_le_mul_of_nonneg_right total (by linarith : 0≤z)).trans_eq
  rw [show 8*M*r*D*z=8*D*M*(r*z) by ring,eq]
  ring

/-- The actual executable mark set in a fixed cell. -/
def constructorCellMarks (n ell : ℕ) (cell : Option (Bool × Fin (Fixed.d (n.log2+1)))) : Finset ℕ :=
  let b := n.log2+1
  let lo := firstCellMark b cell
  (Ico lo (lo+cellMarkCount b)).filter (fun a=>a∈(construct n ell 0 0 0 0).marks)

/-- Covariance of the two rectangular mark indicators under the two
independent prescribed coefficient laws. -/
def twoFieldIndicatorCovariance {ι : Type*} {n ell : ℕ} (R T : PrescribedRows n ell)
    (E F : ι→ℤ×ℤ→Prop) (i j : ι) : ℝ :=
  prescribedProbability R false (fun k=>E i k ∧ E j k)*prescribedProbability T true (fun k=>F i k ∧ F j k)-
    (prescribedProbability R false (E i)*prescribedProbability T true (F i))*
    (prescribedProbability R false (E j)*prescribedProbability T true (F j))

theorem PrescribedRows.probability_unit {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool) (E : ℤ×ℤ→Prop) [DecidablePred E] :
    prescribedProbability R side E∈Set.Icc (0:ℝ) 1 := by
  let W := fun k : R.CoeffPoint side => coefficientWeight n k.val
  let Z := ∑' k,W k
  have zp : 0<Z := (R.weight_normalizer target side).1
  have ws : Summable W := by by_contra h; exact zp.ne' (tsum_eq_zero_of_not_summable h)
  have wp (k) : 0≤W k := mul_nonneg (exp_pos _).le (exp_pos _).le
  let V := fun k : R.CoeffPoint side => if E k.val then W k else 0
  have bounds (k) : 0≤V k ∧ V k≤W k := by dsimp only [V]; split <;> simp [wp]
  have vs := Summable.of_nonneg_of_le (fun k => (bounds k).1) (fun k => (bounds k).2) ws
  exact ⟨div_nonneg (tsum_nonneg (fun k => (bounds k).1)) zp.le,
    (div_le_one zp).mpr (vs.tsum_le_tsum (fun k => (bounds k).2) ws)⟩

theorem twoFieldIndicatorCovariance_bound {ι : Type*} {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (E F : ι→ℤ×ℤ→Prop) (i j : ι) :
    |twoFieldIndicatorCovariance R T E F i j|≤1 := by
  have product {u v : ℝ} (h : u∈Set.Icc (0:ℝ) 1) (k : v∈Set.Icc (0:ℝ) 1) :
      u*v∈Set.Icc (0:ℝ) 1 := ⟨mul_nonneg h.1 k.1,(mul_le_mul h.2 k.2 k.1 zero_le_one).trans_eq (one_mul _)⟩
  let p := fun i => product (R.probability_unit target false (E i)) (T.probability_unit target true (F i))
  have pp := product (p i) (p j)
  have joint := product (R.probability_unit target false (fun k=>E i k ∧ E j k))
    (T.probability_unit target true (fun k=>F i k ∧ F j k))
  unfold twoFieldIndicatorCovariance
  exact abs_le.mpr ⟨by linarith only [pp.2,joint.1],by linarith only [joint.2,pp.1]⟩

/-- In actual constructor cells the complete near-band covariance of any
two-field indicator score, divided by cell length squared, has an explicit
X⁻⁴⁷ saving. The diagonal is included. -/
theorem cell_near_indicator_covariance {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (cell cell' : Option (Bool × Fin (Fixed.d (n.log2+1)))) (w w' : ℕ→ℝ)
    (E F : ℕ→ℤ×ℤ→Prop) (D D' : ℝ) (dp : 0≤D) (dp' : 0≤D') :
    let b := n.log2+1
    let X := constructorCellMarks n ell cell
    let Y := constructorCellMarks n ell cell'
    (∀ a∈X, |w a|≤D) → (∀ y∈Y, |w' y|≤D') →
    |∑ a∈X, ∑ y∈Y.filter (fun y=>a.dist y≤nearRadius b),
      w a*w' y*twoFieldIndicatorCovariance R T E F a y|/(cellMarkCount b:ℝ)^2 ≤
      8*(D*D')/(dyadicUnit b:ℝ)^47 := by
  intro b X Y wx wy
  have one : 1≤(Fixed.B b)^3 := Nat.one_le_pow _ _ Nat.one_le_two_pow
  have h := near_pair_cell_sum b cell X Y 1 1 0 0 (by decide) (by decide) one one
    (fun a ha => ⟨(mem_filter.mp ha).1,Nat.modEq_one⟩) (fun _ _ => Nat.modEq_one)
    (fun a y=>w a*w' y*twoFieldIndicatorCovariance R T E F a y) (D*D') (mul_nonneg dp dp') (by
      intro a ha y hy _
      rw [abs_mul,abs_mul]
      apply (mul_le_mul (mul_le_mul (wx a ha) (wy y hy) (abs_nonneg _) dp)
        (twoFieldIndicatorCovariance_bound R T target E F a y) (abs_nonneg _) (mul_nonneg dp dp')).trans_eq (mul_one _))
  simpa only [Nat.cast_one,one_mul] using h

/-- Even when the reference density is as small as B⁻², the diagonal alone
has normalized size at most D²/X⁵⁹⁹⁷. -/
theorem cell_diagonal_density_covariance {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (cell : Option (Bool × Fin (Fixed.d (n.log2+1)))) (w : ℕ→ℝ)
    (E F : ℕ→ℤ×ℤ→Prop) (D : ℝ) (dp : 0≤D) :
    let b := n.log2+1
    let X := constructorCellMarks n ell cell
    (∀ a∈X, |w a|≤D) →
    |∑ a∈X, (w a)^2*twoFieldIndicatorCovariance R T E F a a|/((cellMarkCount b:ℝ)/(Fixed.B b:ℝ)^2)^2
      ≤ D^2/(dyadicUnit b:ℝ)^5997 := by
  intro b X wx
  let M : ℝ := cellMarkCount b
  let B : ℝ := Fixed.B b
  let z : ℝ := (dyadicUnit b:ℝ)^5997
  have mp : 0<M := by dsimp [M,cellMarkCount]; positivity
  have bp : 0<B := by dsimp [B,Fixed.B]; positivity
  have zp : 0<z := by dsimp [z,dyadicUnit]; positivity
  have eq : B^4*z=M := by
    dsimp only [M,z,B,cellMarkCount,dyadicUnit,Fixed.B,Fixed.beta]
    push_cast
    rw [←pow_mul,←pow_mul,←pow_add]
    congr 1
    omega
  have sz : X.card≤cellMarkCount b := by
    apply (card_le_card (filter_subset ..)).trans
    simp [Nat.card_Ico,b]
  have single (a : ℕ) (ha : a∈X) : |(w a)^2*twoFieldIndicatorCovariance R T E F a a|≤D^2 := by
    rw [abs_mul,←sq_abs (w a),abs_of_nonneg (sq_nonneg _)]
    apply (mul_le_mul (sq_le_sq₀ (abs_nonneg _) dp|>.mpr (wx a ha))
      (twoFieldIndicatorCovariance_bound R T target E F a a) (abs_nonneg _) (sq_nonneg _)).trans_eq (mul_one _)
  have s := (abs_sum_le_sum_abs ..).trans (sum_le_sum single)
  rw [sum_const,nsmul_eq_mul] at s
  have lim := s.trans (mul_le_mul_of_nonneg_right (show (X.card:ℝ)≤M by dsimp [M]; exact_mod_cast sz) (sq_nonneg D))
  change _/(M/B^2)^2≤D^2/z
  apply (div_le_div_iff₀ (sq_pos_of_pos (div_pos mp (sq_pos_of_pos bp))) zp).mpr
  apply (mul_le_mul_of_nonneg_right lim zp.le).trans_eq
  conv_rhs => rw [←eq]
  field_simp
  rw [←eq]
  ring

/-- An unconditional density-normalized contribution for pairs at distance
at most X⁵⁹⁵⁰. Even the elementary bound on an indicator covariance covers
this whole band at the reference mass M/B². -/
theorem cell_very_close_density_covariance {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (cell cell' : Option (Bool × Fin (Fixed.d (n.log2+1)))) (w w' : ℕ→ℝ)
    (E F : ℕ→ℤ×ℤ→Prop) (D D' : ℝ) (dp : 0≤D) (dp' : 0≤D') :
    let b := n.log2+1
    let X := constructorCellMarks n ell cell
    let Y := constructorCellMarks n ell cell'
    let r := (dyadicUnit b)^5950
    (∀ a∈X, |w a|≤D) → (∀ y∈Y, |w' y|≤D') →
    |∑ a∈X, ∑ y∈Y.filter (fun y=>a.dist y≤r), w a*w' y*twoFieldIndicatorCovariance R T E F a y|/
      ((cellMarkCount b:ℝ)/(Fixed.B b:ℝ)^2)^2 ≤ 4*(D*D')/(dyadicUnit b:ℝ)^47 := by
  intro b X Y r wx wy
  let M : ℝ := cellMarkCount b
  let B : ℝ := Fixed.B b
  let z : ℝ := (dyadicUnit b:ℝ)^47
  have bp : 0<B := by dsimp [B,Fixed.B]; positivity
  have mp : 0<M := by dsimp [M,cellMarkCount]; positivity
  have zp : 0<z := by dsimp [z,dyadicUnit]; positivity
  have rp : 1≤(r:ℝ) := by
    rw [←Nat.cast_one (R:=ℝ)]
    exact Nat.cast_le.mpr (Nat.one_le_pow _ _ Nat.one_le_two_pow)
  have eq : (r:ℝ)*z*B^4=M := by
    dsimp only [M,z,r,B,cellMarkCount,dyadicUnit,Fixed.B,Fixed.beta]
    push_cast
    simp only [←pow_mul,←pow_add]
    congr 1
    omega
  have sz : X.card≤cellMarkCount b := by
    apply (card_le_card (filter_subset ..)).trans
    simp [Nat.card_Ico,b]
  let close (a : ℕ) := Y.filter (fun y=>a.dist y≤r)
  let f := fun a y=>w a*w' y*twoFieldIndicatorCovariance R T E F a y
  have row (a : ℕ) (ha : a∈X) : |∑ y∈close a,f a y|≤4*(r:ℝ)*(D*D') := by
    have count := near_neighbors_in_class Y a r 1 0 (by decide) (fun _ _ => Nat.modEq_one)
    simp only [Nat.cast_one,mul_one] at count
    have cn : ((close a).card:ℝ)≤4*(r:ℝ) := by linarith only [count,rp]
    have h (y : ℕ) (hy : y∈close a) : |f a y|≤D*D' := by
      dsimp only [f]
      rw [abs_mul,abs_mul]
      apply (mul_le_mul (mul_le_mul (wx a ha) (wy y (mem_filter.mp hy).1) (abs_nonneg _) dp)
        (twoFieldIndicatorCovariance_bound R T target E F a y) (abs_nonneg _) (mul_nonneg dp dp')).trans_eq (mul_one _)
    have sum := (abs_sum_le_sum_abs ..).trans (sum_le_sum h)
    rw [sum_const,nsmul_eq_mul] at sum
    exact sum.trans (mul_le_mul_of_nonneg_right cn (mul_nonneg dp dp'))
  have agg := (abs_sum_le_sum_abs ..).trans (sum_le_sum row)
  rw [sum_const,nsmul_eq_mul] at agg
  have lim := agg.trans (mul_le_mul_of_nonneg_right (show (X.card:ℝ)≤M by dsimp [M]; exact_mod_cast sz)
    (show 0≤4*(r:ℝ)*(D*D') by positivity))
  change _/(M/B^2)^2≤4*(D*D')/z
  apply (div_le_div_iff₀ (sq_pos_of_pos (div_pos mp (sq_pos_of_pos bp))) zp).mpr
  apply (mul_le_mul_of_nonneg_right lim zp.le).trans_eq
  rw [←eq]
  field_simp

private theorem probability_inter_le {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool) (E F : ℤ×ℤ→Prop) :
    prescribedProbability R side (fun k=>E k∧F k)≤prescribedProbability R side E := by
  let W := fun k : R.CoeffPoint side => coefficientWeight n k.val
  let Z := ∑' k,W k
  let V (P : ℤ×ℤ→Prop) [DecidablePred P] (k : R.CoeffPoint side) := if P k.val then W k else 0
  have zp : 0<Z := (R.weight_normalizer target side).1
  have ws : Summable W := by by_contra h; exact zp.ne' (tsum_eq_zero_of_not_summable h)
  have wp (k) : 0≤W k := mul_nonneg (exp_pos _).le (exp_pos _).le
  have vs (P : ℤ×ℤ→Prop) [DecidablePred P] : Summable (V P) := Summable.of_nonneg_of_le
    (fun k => by dsimp only [V]; split <;> first | exact wp k | rfl)
    (fun k => by dsimp only [V]; split <;> first | exact wp k | rfl) ws
  change (∑' k,V (fun z=>E z∧F z) k)/Z ≤ (∑' k,V E k)/Z
  apply (div_le_div_iff_of_pos_right zp).mpr
  apply (vs (fun k=>E k ∧ F k)).tsum_le_tsum _ (vs E)
  intro k
  by_cases h : E k.val <;> by_cases f : F k.val <;> simp [V,h,f,wp]

private theorem covariance_le_occurrence {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (E F : ℕ→ℤ×ℤ→Prop) (a y : ℕ) :
    |twoFieldIndicatorCovariance R T E F a y|≤prescribedProbability R false (E a)*prescribedProbability T true (F a) := by
  have joint := mul_le_mul (probability_inter_le R target false (E a) (E y))
    (probability_inter_le T target true (F a) (F y)) (T.probability_unit target true _).1 (R.probability_unit target false _).1
  have unit := (mul_le_mul (R.probability_unit target false (E y)).2 (T.probability_unit target true (F y)).2
    (T.probability_unit target true _).1 zero_le_one).trans_eq (one_mul _)
  have h := mul_le_mul_of_nonneg_left unit (mul_nonneg (R.probability_unit target false (E a)).1
    (T.probability_unit target true (F a)).1)
  rw [mul_one] at h
  dsimp only [twoFieldIndicatorCovariance]
  apply abs_le.mpr
  constructor
  · linarith only [h,mul_nonneg (R.probability_unit target false (fun k=>E a k∧E y k)).1
        (T.probability_unit target true (fun k=>F a k∧F y k)).1]
  · have pp (i) := mul_nonneg (R.probability_unit target false (E i)).1 (T.probability_unit target true (F i)).1
    linarith only [joint,mul_nonneg (pp a) (pp y)]

/-- Bounding a covariance by the first mark's occurrence probability removes
one density loss from the sum over close neighbors. -/
theorem near_covariance_by_cell_mean {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (X Y : Finset ℕ) (r : ℕ)
    (w w' : ℕ→ℝ) (E F : ℕ→ℤ×ℤ→Prop) (D D' : ℝ) (dp : 0≤D) (dp' : 0≤D')
    (wx : ∀ a∈X, |w a|≤D) (wy : ∀ y∈Y, |w' y|≤D') :
    |∑ a∈X, ∑ y∈Y.filter (fun y=>a.dist y≤r), w a*w' y*twoFieldIndicatorCovariance R T E F a y| ≤
      (2*(r:ℝ)+2)*(D*D')*twoFieldMean R T X (fun _=>1) E F := by
  let p := fun i => prescribedProbability R false (E i)*prescribedProbability T true (F i)
  let close (a : ℕ) := Y.filter (fun y=>a.dist y≤r)
  let f := fun a y=>w a*w' y*twoFieldIndicatorCovariance R T E F a y
  have p0 (i : ℕ) : 0≤p i := mul_nonneg (R.probability_unit target false _).1 (T.probability_unit target true _).1
  have row (a : ℕ) (ha : a∈X) : |∑ y∈close a,f a y|≤(2*(r:ℝ)+2)*(D*D')*p a := by
    have cnt := near_neighbors_in_class Y a r 1 0 (by decide) (fun _ _ => Nat.modEq_one)
    simp only [Nat.cast_one,mul_one] at cnt
    have size : ((close a).card:ℝ)≤2*(r:ℝ)+2 := by linarith only [cnt]
    have h (y : ℕ) (hy : y∈close a) : |f a y|≤(D*D')*p a := by
      dsimp only [f]
      rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (wx a ha) (wy y (mem_filter.mp hy).1) (abs_nonneg _) dp)
        (covariance_le_occurrence R T target E F a y) (abs_nonneg _) (mul_nonneg dp dp')
    have sum := (abs_sum_le_sum_abs ..).trans (sum_le_sum h)
    rw [sum_const,nsmul_eq_mul] at sum
    exact (sum.trans (mul_le_mul_of_nonneg_right size (mul_nonneg (mul_nonneg dp dp') (p0 a)))).trans_eq (mul_assoc ..).symm
  have h := (abs_sum_le_sum_abs ..).trans (sum_le_sum row)
  simpa only [twoFieldMean,one_mul,←Finset.mul_sum,p] using h

private theorem probability_decidable_eq {n ell : ℕ} (R : PrescribedRows n ell) (s : Bool) (E : ℤ×ℤ→Prop)
    (d e : DecidablePred E) : @prescribedProbability n ell R s E d = @prescribedProbability n ell R s E e := by
  rw [Subsingleton.elim d e]

/-- The two-field smooth mark score in an actual cell has enough expected
mass to control every pair out to X⁷⁹⁵⁰ at its own squared expectation. -/
theorem cell_smooth_relative_close (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ ell ∈ dyadicTargets (Fixed.beta (n.log2+1)),
    2≤n → ¬n.Prime → presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ (R T : PrescribedRows n ell) (cell cell' : Option (Bool × Fin (Fixed.d b))) (w w' : ℕ→ℝ)
      (D D' : ℝ), 0≤D → 0≤D' →
    let X := constructorCellMarks n ell cell; let Y := constructorCellMarks n ell cell'
    let E := fun (a : ℕ) (k : ℤ×ℤ) => supportedValue (sieveBand n ell (R.prefactor a false)) (R.intercept a false k.1 k.2)
    let F := fun (a : ℕ) (k : ℤ×ℤ) => supportedValue (sieveBand n ell (T.prefactor a true)) (T.intercept a true k.1 k.2)
    let μ := twoFieldMean R T X (fun _=>1) E F
    (∀ a∈X, |w a|≤D) → (∀ y∈Y, |w' y|≤D') →
    0<μ ∧ |∑ a∈X, ∑ y∈Y.filter (fun y=>a.dist y≤(dyadicUnit b)^7950),
      w a*w' y*twoFieldIndicatorCovariance R T E F a y|/μ^2 ≤ 4*(D*D')/(dyadicUnit b:ℝ)^47 := by
  obtain ⟨n₁,count⟩ := grid_cells_have_marks line
  obtain ⟨b₁,marg⟩ := PrescribedRows.smooth_probability_margin line
  refine ⟨max n₁ (2^b₁),?_⟩
  intro n large ell target hn comp absent b R T cell cell' w w' D D' dp dp' X Y E F μ wx wy
  let M : ℝ := cellMarkCount b
  let B : ℝ := Fixed.B b
  let r := (dyadicUnit b)^7950
  let z : ℝ := (dyadicUnit b:ℝ)^47
  have bp : 0<B := by dsimp [B,Fixed.B]; positivity
  have mp : 0<M := by dsimp [M,cellMarkCount]; positivity
  have zp : 0<z := by dsimp [z,dyadicUnit]; positivity
  have bn : b₁≤b := ((Nat.le_log2 (by omega : n≠0)).mpr ((max_le_iff.mp large).2)).trans (Nat.le_succ _)
  have cnt := count n (max_le_iff.mp large).1 ell target comp absent 1 0 0 0 0 0 cell (by decide)
    (Nat.one_le_pow _ _ Nat.one_le_two_pow) (fun p hp h => (Nat.prime_of_mem_primeFactors hp).not_dvd_one h |> False.elim)
  have card : M/8≤(X.card:ℝ) := by
    simpa only [M,X,b,constructorCellMarks,Nat.modEq_one,Finset.filter_true,Nat.cast_one,div_one] using cnt
  have each (a : ℕ) (ha : a∈X) : (8/B)^2≤prescribedProbability R false (E a)*prescribedProbability T true (F a) := by
    have mark : a∈(construct n ell 0 0 0 0).marks := (mem_filter.mp ha).2
    rw [pow_two]
    exact mul_le_mul (marg R bn hn comp target absent mark false) (marg T bn hn comp target absent mark true)
      (by positivity) (R.probability_unit target false (E a)).1
  have low : M/B^2≤μ := by
    have total := sum_le_sum each
    rw [sum_const,nsmul_eq_mul] at total
    have tot : (X.card:ℝ)*(8/B)^2≤μ := by
      apply total.trans_eq
      dsimp only [μ,twoFieldMean]
      simp only [one_mul]
      apply sum_congr rfl
      intro i _
      exact congrArg₂ (·*·) (probability_decidable_eq ..) (probability_decidable_eq ..)
    have h := (mul_le_mul_of_nonneg_right card (sq_nonneg (8/B))).trans tot
    apply le_trans _ h
    field_simp
    linarith only [mp]
  have mup := (div_pos mp (sq_pos_of_pos bp)).trans_le low
  have eq : (r:ℝ)*z*B^2=M := by
    dsimp only [M,z,r,B,cellMarkCount,dyadicUnit,Fixed.B,Fixed.beta]
    push_cast
    simp only [←pow_mul,←pow_add]
    congr 1
    omega
  have rp : 1≤(r:ℝ) := by exact Nat.one_le_cast.mpr (Nat.one_le_pow 7950 (dyadicUnit b) Nat.one_le_two_pow)
  have gain : (2*(r:ℝ)+2)*z≤4*μ := by
    have rbound : (2*(r:ℝ)+2)*z≤4*((r:ℝ)*z) := by nlinarith only [mul_le_mul_of_nonneg_right rp zp.le]
    have q : (r:ℝ)*z≤μ := by
      apply le_trans _ low
      exact (le_div_iff₀ (sq_pos_of_pos bp)).mpr eq.le
    linarith only [rbound,q]
  have est := near_covariance_by_cell_mean R T target X Y r w w' E F D D' dp dp' wx wy
  refine ⟨mup,(div_le_div_iff₀ (sq_pos_of_pos mup) zp).mpr ?_⟩
  apply (mul_le_mul_of_nonneg_right est zp.le).trans
  have sz := mul_le_mul_of_nonneg_right gain (mul_nonneg (mul_nonneg dp dp') mup.le)
  change (2*(r:ℝ)+2)*(D*D')*μ*z ≤ _
  linarith only [sz]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.near_pair_cell_sum

#print axioms Cogentic.Construction.cell_diagonal_density_covariance

#print axioms Cogentic.Construction.cell_very_close_density_covariance

#print axioms Cogentic.Construction.cell_smooth_relative_close
