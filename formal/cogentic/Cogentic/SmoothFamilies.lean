import Cogentic.SmoothBox
import Cogentic.PolynomialSmooth
import Cogentic.MarkIntervals

namespace Cogentic.Construction
open Finset Real

/-- Averaging the one-mark lower bounds finds one coefficient pair that
realizes a positive fraction of a finite family in the original box. -/
theorem many_events_in_box {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool)
    (X : Finset ℕ) (hx : X.Nonempty) (E : ℕ→ℤ×ℤ→Prop) [∀ i, DecidablePred (E i)]
    (big : 1000 ≤ n.log2+1)
    (lower : ∀ i∈X, 1/(Fixed.B (n.log2+1):ℝ) ≤ prescribedProbability R side (E i)) :
    ∃ k : ℤ×ℤ, R.compatible side k.1 k.2 ∧ inCoefficientBox n k ∧
      (X.card:ℝ)/(2*Fixed.B (n.log2+1)) ≤ ((X.filter (fun i => E i k)).card:ℝ) := by
  classical
  let b := n.log2+1; let B : ℝ := Fixed.B b
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  let W := fun k : C => coefficientWeight n k.val
  let Z := ∑' k, W k
  let m : ℝ := X.card
  let cut := m/(2*B)
  let G := fun k : ℤ×ℤ => cut ≤ ((X.filter (fun i => E i k)).card:ℝ)
  let A := fun i (k : C) => if E i k.val then W k else 0
  let F := fun k : C => if G k.val then W k else 0
  have zp : 0<Z := (R.weight_normalizer target side).1
  have ws : Summable W := by by_contra h; exact zp.ne' (tsum_eq_zero_of_not_summable h)
  have wn (k : C) : 0≤W k := mul_nonneg (exp_pos _).le (exp_pos _).le
  have eb (k : C) (i : ℕ) : 0≤A i k ∧ A i k≤W k := by dsimp [A]; split <;> simp [wn]
  have es (i : ℕ) := Summable.of_nonneg_of_le (fun k => (eb k i).1) (fun k => (eb k i).2) ws
  have fb (k : C) : 0≤F k ∧ F k≤W k := by dsimp [F]; split <;> simp [wn]
  have fs := Summable.of_nonneg_of_le (fun k => (fb k).1) (fun k => (fb k).2) ws
  have bp : 0<B := by dsimp [B,Fixed.B]; positivity
  have mp : 0 < m := by dsimp only [m]; exact_mod_cast card_pos.mpr hx
  have cp : 0≤cut := by dsimp [cut]; positivity
  have agg (k : C) : (∑ i∈X, A i k) ≤ cut*W k+m*F k := by
    rw [show (∑ i∈X, A i k) = ((X.filter (fun i => E i k.val)).card:ℝ)*W k by
      simp only [A,←sum_filter,sum_const,nsmul_eq_mul]]
    by_cases g : G k.val
    · have card : ((X.filter (fun i => E i k.val)).card:ℝ) ≤ m := by dsimp only [m]; exact_mod_cast card_le_card (filter_subset ..)
      simp only [F,if_pos g]
      linarith only [mul_le_mul_of_nonneg_right card (wn k),mul_nonneg cp (wn k)]
    · simp only [F,if_neg g,mul_zero,add_zero]
      change ¬cut ≤ ((X.filter (fun i => E i k.val)).card:ℝ) at g
      exact mul_le_mul_of_nonneg_right (le_of_not_ge g) (wn k)
  have above := (summable_sum (s:=X) (fun i _ => es i)).tsum_le_tsum agg ((ws.mul_left cut).add (fs.mul_left m))
  rw [Summable.tsum_finsetSum (fun i _ => es i),(ws.mul_left cut).tsum_add (fs.mul_left m),tsum_mul_left,tsum_mul_left] at above
  have each (i : ℕ) (hi : i∈X) : (1/B)*Z ≤ ∑' k, A i k := by
    apply (le_div_iff₀ zp).mp
    exact lower i hi
  have sum := sum_le_sum each
  simp only [sum_const,nsmul_eq_mul] at sum
  have bound : m*((1/B)*Z) ≤ cut*Z + m*(∑' k,F k) := sum.trans above
  have prob : 1/(2*B) ≤ prescribedProbability R side G := by
    change 1/(2*B) ≤ (∑' k,F k)/Z
    apply (le_div_iff₀ zp).mpr
    apply le_of_mul_le_mul_left _ mp
    change m*((1/(2*B))*Z) ≤ m*(∑' k,F k)
    have eq₁ : m*((1/B)*Z) = 2*(m*((1/(2*B))*Z)) := by field_simp
    have eq₂ : cut*Z = m*((1/(2*B))*Z) := by dsimp only [cut]; ring
    rw [eq₁,eq₂] at bound
    linarith only [bound]
  exact R.box_witness target side G ((coefficient_tail_lt_half_mark big).trans_le prob)

/-- Some *single* enumerated tuple makes both field values smooth on at
least 1/(4B²) of any specified nonempty collection of eligible marks. -/
theorem many_smooth_at_marks (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ X : Finset ℕ, X.Nonempty → (∀ a∈X, a∈(construct n ell 0 0 0 0).marks) →
    ∃ (u v w z : ℕ) (Y : Finset ℕ), Y ⊆ X ∧ (X.card:ℝ)/(4*(Fixed.B b:ℝ)^2) ≤ Y.card ∧
      u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
      w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b ∧
      R.compatible false u v ∧ T.compatible true w z ∧
      let s := TryPair.fixedInput n ell (construct n ell u v w z)
      ∀ a∈Y, Marking.SquarefreeSmooth s.base (Marking.value s.first a) ∧
        Marking.SquarefreeSmooth s.base (Marking.value s.second a) := by
  classical
  obtain ⟨b₁,prob⟩ := PrescribedRows.smooth_probability_lower line
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ (max 1000 b₂),?_⟩
  intro n ell R T b huge hn comp target absent X nonempty marks
  have ⟨one,rest⟩ := max_le_iff.mp huge
  have ⟨big,two⟩ := max_le_iff.mp rest
  let B : ℝ := Fixed.B b
  have bp : 0<B := by dsimp [B,Fixed.B]; positivity
  have select (A : Finset ℕ) (non : A.Nonempty) (sub : A⊆X) (Q : PrescribedRows n ell) (s : Bool) :
      ∃ (u v : ℕ) (Y : Finset ℕ), Y⊆A ∧ (A.card:ℝ)/(2*B)≤Y.card ∧
      (u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b) ∧ Q.compatible s u v ∧
      ∀ a∈Y, let I := TryPair.fixedInput n ell (construct n ell u v u v)
        Marking.SquarefreeSmooth I.base (Marking.value (I.coeffs s) a) := by
    let E := fun a (k : ℤ×ℤ) => supportedValue (sieveBand n ell (Q.prefactor a s)) (Q.intercept a s k.1 k.2)
    obtain ⟨k,ok,box,count⟩ := many_events_in_box Q target s A non E big
      (fun a ha => prob Q one hn comp target absent (marks a (sub ha)) s)
    obtain ⟨x,hx,y,hy⟩ := box
    let u := k.1.toNat; let v := k.2.toNat
    have uu : (u:ℤ)=k.1 := Int.toNat_of_nonneg x.le
    have vv : (v:ℤ)=k.2 := Int.toNat_of_nonneg y.le
    have ub : u≤2*b^2*Fixed.U b*Fixed.A b := by exact_mod_cast (uu.trans_le hx)
    have vb : v≤2*b^2*Fixed.U b := by exact_mod_cast (vv.trans_le hy)
    have cp : Q.compatible s u v := by rwa [uu,vv]
    refine ⟨u,v,A.filter (fun i => E i k),filter_subset ..,count,⟨ub,vb⟩,cp,?_⟩
    intro a h
    obtain ⟨ha,ev⟩ := mem_filter.mp h
    obtain ⟨_,cap,grid,_⟩ := (constructed_marks_iff n ell 0 0 0 0 a).mp (marks a (sub ha))
    apply (Q.box_smooth_iff hn (degree b two) comp target absent cap grid ⟨ub,vb⟩ s cp).mp
    rw [uu,vv]
    exact ev
  obtain ⟨u,v,S,subS,first,boxR,r,lh⟩ := select X nonempty Subset.rfl R false
  have spos : S.Nonempty := by
    have x : (0:ℝ)<X.card := by exact_mod_cast card_pos.mpr nonempty
    have pos := (div_pos x (show 0<2*B by positivity)).trans_le first
    exact card_pos.mp (by exact_mod_cast pos)
  obtain ⟨w,z,Y,subY,second,boxT,t,rh⟩ := select S spos subS T true
  refine ⟨u,v,w,z,Y,subY.trans subS,?_,boxR.1,boxR.2,boxT.1,boxT.2,r,t,fun a h => ⟨lh a (subY h),rh a h⟩⟩
  refine le_trans ?_ ((div_le_div_of_nonneg_right first (by positivity : 0≤2*B)).trans second)
  change (X.card:ℝ)/(4*B^2) ≤ X.card/(2*B)/(2*B)
  rw [div_div,show (2*B)*(2*B)=4*B^2 by ring]

/-- In every eligible residue class of every nominal cell, one actual
search tuple makes both polynomial values squarefree and smooth at
at least M/(32 q B²) distinct marks in that class. -/
theorem many_smooth_in_grid_cell (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ ell ∈ dyadicTargets (Fixed.beta (n.log2+1)),
    ¬n.Prime → presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ (R T : PrescribedRows n ell) (cell : Option (Bool × Fin (Fixed.d b))) (q r : ℕ),
    0<q → q≤(Fixed.B b)^4 →
    (∀ p ∈ (markModulus n ell).primeFactors, p ∣ q → ¬r ≡ Fixed.rootBase n [MOD p]) →
    let lo := firstCellMark b cell; let M := cellMarkCount b
    ∃ (u v w z : ℕ) (Y : Finset ℕ),
      (M:ℝ)/(32*q*(Fixed.B b:ℝ)^2) ≤ Y.card ∧
      u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
      w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b ∧
      R.compatible false u v ∧ T.compatible true w z ∧
      let pair := construct n ell u v w z
      let s := TryPair.fixedInput n ell pair
      ∀ a∈Y, a∈Ico lo (lo+M) ∧ a ≡ r [MOD q] ∧ a∈pair.marks ∧
        Marking.SquarefreeSmooth s.base (Marking.value s.first a) ∧
        Marking.SquarefreeSmooth s.base (Marking.value s.second a) := by
  classical
  obtain ⟨n₁,grid⟩ := grid_cells_have_marks line
  obtain ⟨b₁,many⟩ := many_smooth_at_marks line
  refine ⟨max n₁ (2^(b₁+1)),?_⟩
  intro n hn ell target comp absent b R T cell q r qp qcap eligible lo M
  obtain ⟨first,pw⟩ := max_le_iff.mp hn
  have npos := (Nat.pow_pos (by decide : 0<2)).trans_le pw
  have hn2 : 2≤n := (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_add_left 1 b₁)).trans pw
  have logs := (Nat.le_log2 npos.ne').mpr pw
  have big : b₁≤b := by dsimp only [b]; omega
  let X := ((Ico lo (lo+M)).filter (fun a => a ≡ r [MOD q])).filter
    (fun a => a∈(construct n ell 0 0 0 0).marks)
  have cnt := grid n first ell target comp absent q r 0 0 0 0 cell qp qcap eligible
  change (M:ℝ)/q/8 ≤ X.card at cnt
  have Mp : 0<M := Nat.pow_pos (by decide)
  have pos : (0:ℝ)<X.card := (show 0<(M:ℝ)/q/8 by positivity).trans_le cnt
  have non := card_pos.mp (show 0<X.card by exact_mod_cast pos)
  obtain ⟨u,v,w,z,Y,sub,hs,ub,vb,wb,zb,rc,tc,smooth⟩ :=
    many R T big hn2 comp target absent X non (fun _ h => (mem_filter.mp h).2)
  refine ⟨u,v,w,z,Y,?_,ub,vb,wb,zb,rc,tc,?_⟩
  · apply le_trans _ ((div_le_div_of_nonneg_right cnt (by positivity : 0≤4*(Fixed.B b:ℝ)^2)).trans hs)
    rw [div_div,div_div]
    apply le_of_eq; congr 1; ring
  · intro pair inp a h
    obtain ⟨atClass,mark⟩ := mem_filter.mp (sub h)
    obtain ⟨atCell,qr⟩ := mem_filter.mp atClass
    exact ⟨atCell,qr,mark,smooth a h⟩

end Cogentic.Construction
