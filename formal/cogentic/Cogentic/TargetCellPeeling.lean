import Cogentic.OrdinaryMass
import Cogentic.TargetPeeling

namespace Cogentic.Construction
open Finset Real
open scoped Classical
noncomputable section

/-- A single residue survives every sufficiently small set of deleted ordinary
rows on the indicated draw. The error scores are the baseline-cell terms of
`protected_interaction_error_budget`; the class mass comes from
`target_class_mass_count_test`. -/
theorem retained_target_after_peeling (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤ b → 2≤ n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (r : ℕ) (x y : ℤ×ℤ),
    inCoefficientBox n x → inCoefficientBox n y →
    ∀ (D : Finset (BandRow b)), D⊆admittedOrdinaryRows n ell x y →
    ∀ (α cap energy : ℝ), α≤1 →
    let O := PrescribedRows.unrestricted n ell
    let X := constructorCellMarks n ell cell
    let R := fun i=>singleOrdinaryPrescription (n:=n) (ell:=ell) i false
    let T := fun i=>singleOrdinaryPrescription (n:=n) (ell:=ell) i true
    let mass := fun i : BandRow b=>(bandRowPrime i:ℝ)^(-α)
    let err := fun i=>twoFieldScore X
      (overlapContrast (R i) (T i) ell (bandRowPrime i) r i.2.2.val (fun _=>1))
      (fun a g=>(R i).compatible false g.1 g.2 ∧ smoothMarkEvent (R i) false a g)
      (fun a g=>(T i).compatible true g.1 g.2 ∧ smoothMarkEvent (T i) true a g) x y
    let wt := fun a=>(smoothMarkProbability O O a)⁻¹
    let total := twoFieldScore X wt (smoothMarkEvent O false) (smoothMarkEvent O true) x y
    let A := (1+C)*(3*(1760*(Fixed.d b:ℝ)+4)^4)^2
    (∑ i∈D,mass i)≤ cap → (∑ i∈D,mass i*(err i)^2)≤ energy →
    ∀ Y : Finset ℕ, (∀ a∈Y, a∈X ∧ a ≡ r [MOD ell] ∧ smoothMarkEvent O false a x ∧ smoothMarkEvent O true a y) →
    A*(sqrt (cap*energy)+cap*(8*total))<ell*(∑ a∈Y,wt a) →
    ∃ a∈Y, ∀ i∈D, ¬a ≡ i.2.2.val [MOD bandRowPrime i] := by
  obtain ⟨C,cp,b₀,upper⟩ := physical_pair_upper_for_peeling line
  refine ⟨C,cp,b₀,?_⟩
  intro n ell b large hn comp target absent cell r x y bx by' D adm α cap energy al O X R T mass err wt total A limit small Y ys gap
  have wp (a) : 0≤ wt a := inv_nonneg.mpr (mul_nonneg (O.probability_unit target false _).1
    (O.probability_unit target true _).1)
  have tn : 0≤ total := sum_nonneg (fun a _=>mul_nonneg (wp a) (by split <;> norm_num))
  have An : 0≤ A := by dsimp only [A]; positivity
  apply target_survives_ordinary_deletion Y D wt (fun i a=>a ≡ i.2.2.val [MOD bandRowPrime i])
    mass err ell A (8*total) cap energy (fun a _=>wp a)
    (fun i _=>rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _) An (by positivity) limit small _ gap
  intro i hi
  obtain ⟨_,left,right⟩ := (mem_filter.mp (adm hi)).2
  let q := bandRowPrime i
  let s := i.2.2.val
  let U := Y.filter (fun a=>a ≡ s [MOD q])
  have un : ∀ a∈U, a∈X := fun a ha=>(ys a (mem_filter.mp ha).1).1
  let term := fun a=>1*(residueEntry ell r a*residueEntry q s a)/smoothMarkProbability O O a*
    (if smoothMarkEvent O false a x ∧ smoothMarkEvent O true a y then 1 else 0)
  have nonneg (a) : 0≤ term a := by
    change 0≤1*(residueEntry ell r a*residueEntry q s a)*(smoothMarkProbability O O a)⁻¹*_
    unfold residueEntry
    split <;> split <;> split <;> simp_all only [mul_one,one_mul,mul_zero,zero_mul,le_refl]
    exact wp a
  have sumU : (∑ a∈U,wt a)≤∑ a∈X,term a := by
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg un (fun a _ _=>nonneg a))
    apply sum_le_sum; intro a ha
    obtain ⟨ay,hit⟩ := mem_filter.mp ha
    obtain ⟨_,atR,es,fs⟩ := ys a ay
    simp [term,residueEntry,atR,hit,es,fs,wt]
  have actual := upper large hn comp target absent cell (R i) (T i) ⟨x,left⟩ ⟨y,right⟩ bx by'
    ell q r s (fun _=>1) (fun _ _=>zero_le_one)
  have orig : twoFieldScore X (overlapContrast (R i) (T i) ell q r s (fun _=>1))
      (smoothMarkEvent (R i) false) (smoothMarkEvent (T i) true) x y = err i := by
    change (R i).compatible false x.1 x.2 at left
    change (T i).compatible true y.1 y.2 at right
    simp only [err,twoFieldScore,left,right,true_and,q,s]
  change ((ell*q:ℕ):ℝ)*(∑ a∈X,term a)≤ A*(_+8*_) at actual
  rw [orig] at actual
  simp only [one_div,Nat.cast_mul] at actual
  change (ell:ℝ)*q*(∑ a∈X,term a)≤ A*(err i+8*total) at actual
  have qp : (1:ℝ)≤ q := by exact_mod_cast (mem_primeBand.mp i.2.1.property).1.one_le
  have positive := zero_lt_one.trans_le qp
  have invBound : (q:ℝ)⁻¹≤ mass i := by
    rw [←rpow_neg_one]
    exact rpow_le_rpow_of_exponent_le qp (by linarith)
  have raw := (mul_le_mul_of_nonneg_left sumU (mul_nonneg (Nat.cast_nonneg (α:=ℝ) ell) positive.le)).trans actual
  have larger : (ell:ℝ)*q*∑ a∈U,wt a ≤ A*(|err i|+8*total) :=
    raw.trans (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) le_rfl) An)
  have div := mul_le_mul_of_nonneg_right larger (inv_nonneg.mpr positive.le)
  change (ell:ℝ)*(∑ a∈U,wt a)≤_
  calc _ = ((ell:ℝ)*q*(∑ a∈U,wt a))*(q:ℝ)⁻¹ := by field_simp
       _ ≤ (A*(|err i|+8*total))*(q:ℝ)⁻¹ := div
       _ ≤ (A*(|err i|+8*total))*mass i := mul_le_mul_of_nonneg_left invBound (by positivity)
       _ = _ := by ring

/-- A low-expectation test preserves every protected residue against any
subsequent ordinary deletion satisfying its mass budget. -/
theorem target_peeling_test (line : DirichletLZerosOnLine) :
    ∃ C H : ℝ, 0<C ∧ 0<H ∧ ∃ n₀ : ℕ, ∀ n≥n₀,
    ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let d := Fixed.d b
    ∀ (α u : ℝ), 0≤α → α≤1 → 0≤ u → Window.saddleMean (primeBand b) α=log (Fixed.B b)*u →
    let A := (1+C)*(3*(1760*(d:ℝ)+4)^4)^2
    let V := 1+2048*u*(d:ℝ)*overlapError b 1 H 1 1
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∃ (test : Ω→ℝ) (μ : ℝ), (∀ t,0≤ test t) ∧ HasSum (fun t=>twoFieldWeight O O t*test t) μ ∧ μ≤3/64 ∧
      ∀ t : Ω, let x := t.1.val; let y := t.2.val
      inCoefficientBox n x → inCoefficientBox n y → test t<1 →
      ∃ rel, Marking.stageOne (TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat))=some rel ∧
      ∀ cap : ℝ, 0≤ cap → A*(sqrt (cap*(64*V))+512*cap)<1/16 →
      ∀ D⊆admittedOrdinaryRows n ell x y, (∑ i∈D,(bandRowPrime i:ℝ)^(-α))≤ cap →
      ∀ r∈wanted d ell (Fixed.rootBase n), ∃ a∈rel.marks, a ≡ r [MOD ell] ∧
        ∀ i∈D, ¬a ≡ i.2.2.val [MOD bandRowPrime i] := by
  classical
  obtain ⟨C,cp,b₁,keep⟩ := retained_target_after_peeling line
  obtain ⟨H,hp,n₂,inter⟩ := protected_interaction_error_budget line 1 le_rfl
  obtain ⟨n₃,classes⟩ := target_class_mass_count_test line 64 (by decide)
  obtain ⟨b₄,means⟩ := cell_count_score_error line 1 (by decide)
  refine ⟨C,H,cp,hp,max (max n₂ n₃) (max 2 (2^(max b₁ b₄))),?_⟩
  intro n large ell target comp absent b d α u ap al un saddle A V O Ω
  obtain ⟨two,three⟩ := max_le_iff.mp (max_le_iff.mp large).1
  obtain ⟨hn,lg⟩ := max_le_iff.mp (max_le_iff.mp large).2
  obtain ⟨one,four⟩ := max_le_iff.mp (((Nat.le_log2 (by omega : n≠0)).mpr lg).trans (Nat.le_succ _))
  let X := constructorCellMarks n ell none
  let N : ℝ := X.card
  let M : ℝ := cellMarkCount b
  have mp : 0<M := by dsimp [M,cellMarkCount];positivity
  have nm : N≤ M := by
    dsimp only [N,M,X,constructorCellMarks]
    exact_mod_cast (card_filter_le ..).trans_eq (by simp [b])
  have dp : 0<d := Fixed.degree_pos (Nat.succ_pos _)
  let : NeZero d := ⟨dp.ne'⟩
  let roots := wanted d ell (Fixed.rootBase n)
  let len : roots.length=d := (wanted_spec (target_gt_degree target) (Fixed.rootBase n)).1
  let row := fun j : Fin d=>roots.get (Fin.cast len.symm j)
  obtain ⟨test,μ,tn,et,rate,passes⟩ := classes n three ell target comp absent (Fin d)
    (by change Fintype.card (Fin d)≤4*d+4; simp only [Fintype.card_fin];omega) (fun _=>none) row
  let mix := fun c : Option (Bool×Fin d)=>if c=none then (1:ℝ) else 0
  have mx c : 0≤ mix c := by dsimp only [mix];split <;> norm_num
  obtain ⟨ξ,ei,ib⟩ := inter n two ell target comp absent α u ap saddle mix mx (by simp [mix])
  let R := fun i=>singleOrdinaryPrescription (n:=n) (ell:=ell) i false
  let T := fun i=>singleOrdinaryPrescription (n:=n) (ell:=ell) i true
  let idx := univ.filter (OrdinaryAdmissible (n:=n) (ell:=ell))
  let m := fun i : BandRow b=>(bandRowPrime i:ℝ)^(-α)
  let err := fun r i (t : Ω)=>twoFieldScore X (overlapContrast (R i) (T i) ell (bandRowPrime i) r i.2.2.val (fun _=>1))
    (fun a g=>(R i).compatible false g.1 g.2 ∧ smoothMarkEvent (R i) false a g)
    (fun a g=>(T i).compatible true g.1 g.2 ∧ smoothMarkEvent (T i) true a g) t.1.val t.2.val
  let E := fun t : Ω=>∑ r∈roots.toFinset,∑ i∈idx,m i*(err r i t/N)^2
  have ei' : HasSum (fun t : Ω=>twoFieldWeight O O t*E t) ξ := by
    simpa [E,err,idx,m,roots,N,X,mix,R,T] using ei
  have ep (t) : 0≤ E t := sum_nonneg (fun r _=>sum_nonneg (fun i _=>mul_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)))
  have vp : 0<V := by dsimp [V,overlapError];positivity
  let w := fun a=>(smoothMarkProbability O O a)⁻¹
  let total := fun t : Ω=>twoFieldScore X w (smoothMarkEvent O false) (smoothMarkEvent O true) t.1.val t.2.val
  have wn a : 0≤ w a := inv_nonneg.mpr (mul_nonneg (O.probability_unit target false _).1 (O.probability_unit target true _).1)
  have pn t : 0≤ total t := sum_nonneg (fun a _=>mul_nonneg (wn a) (by split <;> norm_num))
  have mean := (means O O four hn comp target absent none).1
  change twoFieldMean O O X w (smoothMarkEvent O false) (smoothMarkEvent O true)=N at mean
  have es : HasSum (fun t : Ω=>twoFieldWeight O O t*total t) N := by
    rw [←mean]
    exact twoField_score_mean O O target X w (smoothMarkEvent O false) (smoothMarkEvent O true)
  let score := fun t : Ω=>test t+E t/(64*V)+total t/(64*M)
  refine ⟨score,μ+ξ/(64*V)+N/(64*M),fun t=>by dsimp only [score];exact add_nonneg (add_nonneg (tn t) (div_nonneg (ep t) (by positivity))) (div_nonneg (pn t) (by positivity)),?_,?_,?_⟩
  · apply ((et.add (ei'.div_const (64*V))).add (es.div_const (64*M))).congr_fun
    intro t; dsimp only [score];ring
  · have eb : ξ/(64*V)≤1/64 := (div_le_iff₀ (by positivity)).mpr (by dsimp only [V];linarith only [ib])
    have sb : N/(64*M)≤1/64 := (div_le_iff₀ (by positivity)).mpr (by linarith only [nm])
    norm_num at rate
    linarith only [rate,eb,sb]
  intro t x y bx by' fit
  have etiny : 0≤ E t/(64*V) := div_nonneg (ep t) (by positivity)
  have ptiny : 0≤ total t/(64*M) := div_nonneg (pn t) (by positivity)
  change test t+E t/(64*V)+total t/(64*M)<1 at fit
  obtain ⟨rel,stage,supply⟩ := passes t bx by' (by linarith only [fit,etiny,ptiny])
  refine ⟨rel,stage,?_⟩
  intro cap cn gap D admit ds r hr
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hr
  let j' := Fin.cast len j
  have rj : row j'=r := hj
  have supplyR := (supply j').2
  rw [rj] at supplyR
  let Y := (X.filter (fun a=>a ≡ r [MOD ell] ∧ a∈rel.marks)).filter
    (fun a=>smoothMarkEvent O false a x ∧ smoothMarkEvent O true a y)
  change M/(16*(ell:ℝ))≤∑ a∈Y,w a at supplyR
  have massPos i : 0≤ m i := rpow_nonneg (Nat.cast_nonneg _) _
  have ed (i) : i∈D → i∈idx := fun hi=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (admit hi)).2.1⟩
  have restricted := (sum_le_sum_of_subset_of_nonneg ed (fun i _ _=>mul_nonneg (massPos i) (sq_nonneg (err r i t/N)))).trans
    (single_le_sum (s:=roots.toFinset) (f:=fun s=>∑ i∈idx,m i*(err s i t/N)^2)
      (fun s _=>sum_nonneg (fun i _=>mul_nonneg (massPos i) (sq_nonneg _))) (List.mem_toFinset.mpr hr))
  have ecap : E t<64*V := (div_lt_one (by positivity)).mp (by linarith only [fit,tn t,ptiny])
  have npos : 0<N := by
    by_contra! neg
    have nz : (X.card:ℝ)=0 := le_antisymm neg (Nat.cast_nonneg _)
    have empty : X=∅ := card_eq_zero.mp (by exact_mod_cast nz)
    have emptyY : Y=∅ := by simp [Y,empty]
    rw [emptyY,sum_empty] at supplyR
    have epos : 0<(ell:ℝ) := by exact_mod_cast (mem_dyadicTargets.mp target).1.pos
    exact (not_le_of_gt (div_pos mp (by positivity))) supplyR
  have ene : (∑ i∈D,m i*(err r i t)^2)≤64*V*M^2 := by
    change _ ≤ E t at restricted
    have eq : (∑ i∈D,m i*(err r i t/N)^2)*N^2=∑ i∈D,m i*(err r i t)^2 := by
      rw [sum_mul];apply sum_congr rfl;intro i _;field_simp
    rw [←eq]
    exact mul_le_mul (restricted.trans ecap.le) (pow_le_pow_left₀ npos.le nm 2) (sq_nonneg _) (by positivity)
  have pcap : total t≤64*M := ((div_lt_one (by positivity)).mp (by linarith only [fit,tn t,etiny])).le
  have ellp : (0:ℝ)<ell := by exact_mod_cast (mem_dyadicTargets.mp target).1.pos
  have lower := (div_le_iff₀ (by positivity : 0<16*(ell:ℝ))).mp supplyR
  have margin : A*(sqrt (cap*(64*V*M^2))+cap*(8*total t))<ell*(∑ a∈Y,w a) := by
    have sq : sqrt (cap*(64*V*M^2))=sqrt (cap*(64*V))*M := by
      rw [←mul_assoc,Real.sqrt_mul (mul_nonneg cn (by positivity)),Real.sqrt_sq mp.le]
    rw [sq]
    apply lt_of_le_of_lt _ (lt_of_lt_of_le (mul_lt_mul_of_pos_right gap mp) (by linarith only [lower]))
    have bounded := mul_le_mul_of_nonneg_left pcap (mul_nonneg cn (by norm_num : (0:ℝ)≤8))
    calc _ ≤ A*((sqrt (cap*(64*V))+512*cap)*M) := mul_le_mul_of_nonneg_left (by nlinarith only [bounded]) (by dsimp only [A];positivity)
         _ = _ := by ring
  obtain ⟨a,ay,miss⟩ := keep one hn comp target absent none r x y bx by' D admit α cap (64*V*M^2) al ds
    ene Y (fun a ha=>by
      obtain ⟨inX,sx⟩ := mem_filter.mp ha
      obtain ⟨inX,atR,_⟩ := mem_filter.mp inX
      exact ⟨inX,atR,sx⟩) margin
  exact ⟨a,(mem_filter.mp (mem_filter.mp ay).1).2.2,(mem_filter.mp (mem_filter.mp ay).1).2.1,miss⟩

/-- The exponential ordinary-row mass cap meets the protected target
budget uniformly over the construction's saddle window. -/
theorem target_peeling_gap (C H : ℝ) (cp : 0<C) (hp : 0<H) :
    ∃ b₀ : ℕ, ∀ b≥b₀, ∀ u : ℝ, 0≤ u → u≤110*(Fixed.d b:ℝ) →
    let d := Fixed.d b; let cap := exp (-(Fixed.z b:ℝ)^2)
    let A := (1+C)*(3*(1760*(d:ℝ)+4)^4)^2
    let V := 1+2048*u*(d:ℝ)*overlapError b 1 H 1 1
    A*(sqrt (cap*(64*V))+512*cap)<1/16 := by
  let a := (1+C)*(3*(1764:ℝ)^4)^2
  let o := 4*H+(2*(1+2*exp 6))^2*exp 8+16
  let v := 1+2048*110*o
  let K := a*(8*sqrt v+512)
  obtain ⟨b₁,save⟩ := Window.fixed_band_power_savings 50 (by norm_num)
  refine ⟨max b₁ (max (2^20) ⌈32*K⌉₊),?_⟩
  intro b large u un bound d cap A V
  obtain ⟨bs,rest⟩ := max_le_iff.mp large
  obtain ⟨lg,kb⟩ := max_le_iff.mp rest
  let z : ℝ := Fixed.z b
  have posb : 0<b := (by decide : 0<2^20).trans_le lg
  have dn : (1:ℝ)≤ d := by exact_mod_cast Fixed.degree_pos posb
  have zn : 20≤ z := by dsimp only [z,Fixed.z];exact_mod_cast (Nat.le_log2 posb.ne').mpr lg |>.trans (Nat.le_succ _)
  have bz : (b:ℝ)≤ exp z := by
    have n : (b:ℝ) ≤ (2:ℝ)^(Fixed.z b) := by exact_mod_cast Nat.lt_log2_self.le
    have t := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (by linarith [exp_one_gt_d9] : (2:ℝ)≤ exp 1) (Fixed.z b)
    rw [←exp_nat_mul,mul_one] at t;exact n.trans t
  have dz := (show (d:ℝ)≤ b by exact_mod_cast Fixed.degree_le_bits b).trans bz
  have bn : 1≤(Fixed.B b:ℝ) := by exact_mod_cast (Nat.pow_pos (by decide) : 0<Fixed.B b)
  have inv : 1/(Fixed.B b:ℝ)≤ exp (-50*z^2) := calc
    _ = (Fixed.B b:ℝ)^(-(1:ℝ)) := by rw [rpow_neg (by positivity : (0:ℝ)≤ Fixed.B b),rpow_one,one_div]
    _ ≤ (Fixed.B b:ℝ)^(-17/200:ℝ) := rpow_le_rpow_of_exponent_le bn (by norm_num)
    _ ≤ _ := save b bs
  have tail := mul_le_mul_of_nonneg_right inv (exp_pos (48*z)).le
  rw [←exp_add] at tail
  have one : exp (-50*z^2+48*z)≤1 := exp_le_one_iff.mpr (by nlinarith only [zn,mul_nonneg (sub_nonneg.mpr zn) (by linarith only [zn] : 0≤ z)])
  have ce : cap≤1 := exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  have cn : 0≤ cap := (exp_pos _).le
  have ob : overlapError b 1 H 1 1≤ o := by
    dsimp only [overlapError,o]
    simp only [one_pow,mul_one,neg_one_mul]
    change 4*H*cap + (2*(1+2*exp 6)*cap)^2*exp (8/(d:ℝ)) + 16/(Fixed.B b:ℝ)*exp (48*z)≤_
    have t := tail.trans one
    have e := exp_le_exp.mpr (div_le_self (by norm_num : (0:ℝ)≤8) dn)
    have h := mul_le_mul (pow_le_pow_left₀ (by positivity : 0≤2*(1+2*exp 6)*cap)
      (mul_le_of_le_one_right (by positivity) ce) 2) e (exp_pos _).le (sq_nonneg _)
    have ht : 16/(Fixed.B b:ℝ)*exp (48*z)≤16 := by
      calc
        _ = 16*(1/(Fixed.B b:ℝ)*exp (48*z)) := by ring
        _ ≤ 16 := mul_le_of_le_one_right (by norm_num) t
    have hh : (2*(1+2*exp 6)*cap)^2*exp (8/(d:ℝ)) ≤
        (2*(1+2*exp 6))^2*exp 8 := h
    have hc : 4*H*cap≤4*H := mul_le_of_le_one_right (by positivity : 0≤4*H) ce
    nlinarith only [ht,hh,hc]
  have aa : A≤ a*(d:ℝ)^8 := by
    have le : 1760*(d:ℝ)+4≤1764*d := by linarith only [dn]
    dsimp only [A,a]
    calc _ ≤ (1+C)*(3*(1764*(d:ℝ))^4)^2 := by gcongr
         _ = _ := by ring
  have op : 0≤ o := by dsimp only [o];positivity
  have vv : V≤ v*(d:ℝ)^2 := by
    have upper := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bound (by norm_num : (0:ℝ)≤2048)) (Nat.cast_nonneg (α:=ℝ) d)) ob (by dsimp [overlapError];positivity) (by positivity)
    dsimp only [V,v];nlinarith only [upper,dn,sq_nonneg ((d:ℝ)-1)]
  have vp : 0≤ v := by dsimp only [v];positivity
  have vp' : 0≤ V := by dsimp [V,overlapError];positivity
  have hcap : cap≤ sqrt cap := by
    apply Real.le_sqrt_of_sq_le; nlinarith only [mul_nonneg cn (sub_nonneg.mpr ce)]
  have sc : sqrt (cap*(64*V))≤ sqrt cap*(8*sqrt v*d) := by
    rw [Real.sqrt_mul cn]
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith only [vv,Real.sq_sqrt vp,
      show (8*sqrt v*d)^2=64*v*(d:ℝ)^2 by rw [mul_pow,mul_pow,Real.sq_sqrt vp];ring]⟩
  have d9 := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) d) dz 9
  have shrink : (d:ℝ)^9*sqrt cap≤ exp (-z) := by
    rw [show cap=exp (-z^2) from rfl]
    have sqexp : sqrt (exp (-z^2))=exp (-z^2/2) := by
      apply (Real.sqrt_eq_iff_mul_self_eq (le_of_lt (exp_pos _)) (le_of_lt (exp_pos _))).2
      rw [←exp_add]; congr 1 <;> ring
    rw [sqexp]
    change (d:ℝ)^9 * exp (-z^2/2) ≤ exp (-z)
    have dz9 := d9
    rw [←exp_nat_mul] at dz9
    norm_num at dz9
    calc
      _ ≤ exp (9*z)*exp (-z^2/2) := mul_le_mul_of_nonneg_right dz9 (exp_pos _).le
      _ = exp (9*z-z^2/2) := by rw [←exp_add]; congr 1 <;> ring
      _ ≤ exp (-z) := exp_le_exp.mpr (by nlinarith only [zn, mul_nonneg (sub_nonneg.mpr zn) (by linarith only [zn] : 0≤z)])
  have kp : 0≤ K := by dsimp [K,a];positivity
  have kexp := (Nat.le_ceil (32*K)).trans ((by exact_mod_cast kb : (⌈32*K⌉₊:ℝ)≤ b).trans bz)
  have residual := mul_le_mul_of_nonneg_right kexp (exp_pos (-z)).le
  rw [←exp_add,add_neg_cancel,exp_zero] at residual
  calc
    _ ≤ (a*(d:ℝ)^8)*(sqrt cap*(8*sqrt v*d)+512*(sqrt cap*d)) := by
      apply mul_le_mul aa _ (by positivity) (by dsimp [a];positivity)
      exact add_le_add sc (mul_le_mul_of_nonneg_left (hcap.trans (le_mul_of_one_le_right (sqrt_nonneg _) dn)) (by norm_num))
    _ = K*((d:ℝ)^9*sqrt cap) := by dsimp only [K];ring
    _ ≤ K*exp (-z) := mul_le_mul_of_nonneg_left shrink kp
    _ < _ := by linarith only [residual]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.retained_target_after_peeling

#print axioms Cogentic.Construction.target_peeling_test

#print axioms Cogentic.Construction.target_peeling_gap
