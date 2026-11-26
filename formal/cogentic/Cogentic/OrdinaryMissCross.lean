import Cogentic.EmpiricalBranchObservable
import Cogentic.PairHitReference
import Cogentic.AuxiliaryBranchPrime
import Cogentic.RawLogProfiles
import Cogentic.RawGramTransfer

namespace Cogentic.Construction
open Finset Real Window
open scoped Classical
noncomputable section

/-- The target-miss first moment of one ordinary row, before multiplication
by its square-root mass. The denominator is shared by all protected rows. -/
def missCrossCenter (n ell : ℕ) (i : BandRow (n.log2+1)) (β : ℝ)
    (h : Option (Bool×Fin (Fixed.d (n.log2+1)))) : ℝ :=
  let b := n.log2+1
  let M := cellMarkCount b
  let p := (bandRowPrime i:ℝ)
  let C := Option (Bool×Fin (Fixed.d b))
  (∑ c : C, ∑ j∈range M,
    let a := firstCellMark b c+j
    (1-(Fixed.d b:ℝ)/ell)*nominalLogFactor b h a*
      (fullBandInsertion b (bandRowPrime i) (branchMeshSaddle n ell a false i.1)/(p*p^(-β)))) /
    ((Fintype.card C:ℝ)*M)

def missCrossWeight (n ell : ℕ) (i : BandRow (n.log2+1)) (β : ℝ)
    (h : Option (Bool×Fin (Fixed.d (n.log2+1)))) (a : ℕ) : ℝ :=
  let O := PrescribedRows.unrestricted n ell
  pooledMarkWeight univ (constructorCellMarks n ell) (fun _ t=>
    (if t ≡ i.2.2.val [MOD bandRowPrime i] ∧ hitsTarget n ell t false = false then
      nominalLogFactor (n.log2+1) h t / (bandRowPrime i:ℝ)^(-β) else 0) - missCrossCenter n ell i β h) a /
    smoothMarkProbability O O a

private theorem single_cross_cover {n ell : ℕ} (i : BandRow (n.log2+1))
    (hi : OrdinaryAdmissible (n:=n) (ell:=ell) i) (q : ℕ) (pq : bandRowPrime i≠q) :
    let R := singleOrdinaryPrescription (n:=n) (ell:=ell) i
    ∀ U∈[R false,R true], U.primes⊆{bandRowPrime i,q} ∧
      (bandRowPrime i∈U.primes → U.residue (bandRowPrime i) ≡ i.2.2.val [MOD bandRowPrime i]) ∧
      (q∈U.primes → U.residue q ≡ 0 [MOD q]) := by
  intro R U hu
  have one (s) : (R s).primes⊆{bandRowPrime i,q} ∧
      (bandRowPrime i∈(R s).primes → (R s).residue (bandRowPrime i) ≡ i.2.2.val [MOD bandRowPrime i]) ∧
      (q∈(R s).primes → (R s).residue q ≡ 0 [MOD q]) := by
    by_cases color : i.1=s <;>
      simp [R,singleOrdinaryPrescription,hi,color,PrescribedRows.unrestricted,pq,Ne.symm pq,Nat.ModEq.refl]
  rcases List.mem_cons.mp hu with rfl | ht
  · exact one false
  · obtain rfl := List.mem_singleton.mp ht
    exact one true

private theorem single_miss_numerator (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ell∈dyadicTargets (Fixed.beta b) →
    ∀ (i : BandRow b) (hi : OrdinaryAdmissible (n:=n) (ell:=ell) i)
      (q : ℕ), bandRowPrime i≠q →
    ∀ (β : ℝ) (h : Option (Bool×Fin (Fixed.d b))),
    let p := bandRowPrime i; let R := singleOrdinaryPrescription (n:=n) (ell:=ell) i
    let B := Bool×Bool×Bool; let M := cellMarkCount b; let L := firstCellMark b
    let m := (p:ℝ)^(-β); let d := (Fixed.d b:ℝ)
    let Z := fun c (k : B) j=>if k.1 && !k.2.2 then nominalLogFactor b h (L c+j)/m else 0
    let μ := fun k : B=>residueBranchMass (p:ℝ)⁻¹ k.1 * residueBranchMass (q:ℝ)⁻¹ k.2.1 *
      residueBranchMass (d/ell) k.2.2
    let F := fun c (k : B) j=>
      fullBandInsertion b ((R false).pairBranchProduct p q k.1 k.2.1) (branchMeshSaddle n ell (L c+j) k.2.2 false)*
      fullBandInsertion b ((R true).pairBranchProduct p q k.1 k.2.1) (branchMeshSaddle n ell (L c+j) k.2.2 true)
    (∑ c,∑ k : B, μ k*(∑ j∈range M,Z c k j*F c k j))/
      ((Fintype.card (Option (Bool×Fin (Fixed.d b))):ℝ)*M)=missCrossCenter n ell i β h := by
  obtain ⟨b₁,single⟩ := ordinary_single_hit_reference
  obtain ⟨b₂,saddles⟩ := canonical_mesh_saddle_range line
  refine ⟨max b₁ b₂,?_⟩
  intro n ell b big hn target i hi q pq β h p R B M L m d Z μ F
  congr 1
  apply sum_congr rfl
  intro c _
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j jm
  let a := L c+j
  let α := branchMeshSaddle n ell a false
  let f := nominalLogFactor b h a
  have range (s : Bool) := saddles (le_trans (le_max_right ..) big) hn target c false s j (mem_range.mp jm)
  let mass := fun hp hq=>residueBranchMass (p:ℝ)⁻¹ hp * residueBranchMass (q:ℝ)⁻¹ hq
  let fi := fun hp hq=>fullBandInsertion b ((R false).pairBranchProduct p q hp hq) (α false)*
    fullBandInsertion b ((R true).pairBranchProduct p q hp hq) (α true)
  have v := single (le_trans (le_max_left ..) big) i hi q pq α β (f/m)
    (fun s=>(range s).1.1) (fun s=>(range s).2)
  change (∑ hp : Bool,∑ hq : Bool,mass hp hq*(if hp then f/m else 0)*fi hp hq)=
    f/m*m*(fullBandInsertion b p (α i.1)/((p:ℝ)*m)) at v
  have nz : m≠0 := (rpow_pos_of_pos (Nat.cast_pos.mpr (mem_primeBand.mp i.2.1.property).1.pos : (0:ℝ)<p) _).ne'
  rw [div_mul_cancel₀ _ nz] at v
  trans (1-d/ell)*(∑ hp : Bool,∑ hq : Bool,mass hp hq*(if hp then f/m else 0)*fi hp hq)
  · simp only [Fintype.sum_prod_type,Fintype.sum_bool,B,μ,F,Z,fi,mass,α,a,f,
      Bool.not_false,Bool.not_true,Bool.and_true,Bool.and_false,
      if_true,Bool.false_eq_true,if_false,zero_mul,mul_zero,add_zero,zero_add,residueBranchMass]
    ring
  · rw [v];ring

/-- Uniform profile error after division by the total raw mesh size. -/
def missCrossScale (b : ℕ) : ℝ :=
  6*(3*(Fixed.h b:ℝ)+1)

theorem missCrossScale_le (b : ℕ) : missCrossScale b ≤ 24*((b:ℝ)+1)^2 := by
  have small : Fixed.d b≤b+1 := (Fixed.degree_le_bits b).trans (Nat.le_succ _)
  have z : Fixed.z b≤b+1 := Nat.add_le_add_right (Nat.log2_le_self b) 1
  have hb : (Fixed.h b:ℝ)≤((b:ℝ)+1)^2 := by
    exact_mod_cast (show Fixed.h b≤(b+1)^2 by rw [pow_two];exact Nat.mul_le_mul small z)
  dsimp [missCrossScale];nlinarith only [hb,Nat.cast_nonneg (α:=ℝ) b,sq_nonneg (b:ℝ)]

/-- Every singleton and protected coordinate has a physical centered moment
with constants independent of the ordinary prime. -/
theorem ordinary_miss_cross_second (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let Cell := Option (Bool×Fin (Fixed.d b))
    let count := (Fintype.card Cell:ℝ)*cellMarkCount b
    ∀ (i : BandRow b), OrdinaryAdmissible (n:=n) (ell:=ell) i → ∀ (β : ℝ), β≤1 → ∀ h : Cell,
    let R := singleOrdinaryPrescription (n:=n) (ell:=ell) i
    twoFieldSecond (R false) (R true) (univ.biUnion (constructorCellMarks n ell)) (missCrossWeight n ell i β h)
      (smoothMarkEvent (R false) false) (smoothMarkEvent (R true) true) ≤
        C*(count*missCrossScale b)^2*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨C,cp,n₁,phys⟩ := physical_pair_mesh_numerator_sharp line K hk
  obtain ⟨b₁,aux⟩ := auxiliary_ordinary_prime line
  obtain ⟨b₂,mean⟩ := single_miss_numerator line
  obtain ⟨b₃,deg⟩ := Fixed.degree_grows 10004
  refine ⟨C,cp,max n₁ (max 2 (2^(max b₁ (max b₂ b₃)))),?_⟩
  intro n large ell target comp sieve b Cell count i hi β βle h R
  obtain ⟨old,big⟩ := max_le_iff.mp large
  obtain ⟨hn,cut⟩ := max_le_iff.mp big
  obtain ⟨baux,more⟩ := max_le_iff.mp (((Nat.le_log2 (by omega : n≠0)).mpr cut).trans (Nat.le_succ _))
  obtain ⟨bmean,bdeg⟩ := max_le_iff.mp more
  let p := bandRowPrime i
  let L := firstCellMark b; let M := cellMarkCount b; let m := (p:ℝ)^(-β)
  obtain ⟨q,qm,qp,qe⟩ := aux baux hn comp target sieve p
  let B := Bool×Bool×Bool
  let U := 3*(Fixed.h b:ℝ)+1
  let Z := fun c (k : B) j=>if k.1 && !k.2.2 then nominalLogFactor b h (L c+j)/m else 0
  let D := fun (_ : Cell) (k : B)=>if k.1 && !k.2.2 then U/m else 0
  have pp : 1≤(p:ℝ) := by exact_mod_cast (mem_primeBand.mp i.2.1.property).1.one_le
  have pp' : (0:ℝ)<p := lt_of_lt_of_le zero_lt_one pp
  have mp : 0 < m := rpow_pos_of_pos pp' _
  have up : 1≤U := by dsimp only [U];linarith only [Nat.cast_nonneg (α:=ℝ) (Fixed.h b)]
  have profile (c : Cell) : (∀ j<M,|nominalLogFactor b h (L c+j)|≤U) ∧
      (∑ j∈range (M-1),|nominalLogFactor b h (L c+(j+1))-nominalLogFactor b h (L c+j)|)≤U := by
    cases h with
    | none => simpa [nominalLogFactor,up] using (by linarith only [up] : 0≤U)
    | some k =>
      obtain ⟨size,var,_⟩ := (raw_log_profile_bounds hn (deg b bdeg) c).1 k.1 k.2
      exact ⟨fun j hj=>(size j hj).trans (by dsimp only [U];linarith),var.trans up⟩
  have reg c k : 0≤D c k ∧ (∀ j<M,|Z c k j|≤D c k) ∧
      (∑ j∈range (M-1),|Z c k (j+1)-Z c k j|)≤D c k := by
    by_cases mask : (k.1 && !k.2.2) = true
    · simp only [Z,D,mask,if_true,←sub_div,abs_div,abs_of_pos mp,←sum_div]
      exact ⟨div_nonneg (zero_le_one.trans up) mp.le,fun j hj=>div_le_div_of_nonneg_right ((profile c).1 j hj) mp.le,
        div_le_div_of_nonneg_right (profile c).2 mp.le⟩
    · simp only [Z,D,if_neg mask];simp
  have v := (phys n old ell target comp sieve hi.1 qm qp.symm hi.2.1 qe i.2.2.val 0
    (R false) (R true) (single_cross_cover i hi q qp.symm) Z D reg).2
  rw [mean bmean hn target i hi q qp.symm β h] at v
  let O := PrescribedRows.unrestricted n ell
  let branch := fun a=>(decide (a ≡ i.2.2.val [MOD p]),decide (a ≡ 0 [MOD q]),hitsTarget n ell a false)
  have weight : (fun a=>pooledMarkWeight univ (constructorCellMarks n ell)
      (fun c t=>Z c (branch t) (t-L c)-missCrossCenter n ell i β h) a/smoothMarkProbability O O a) =
      missCrossWeight n ell i β h := by
    funext a;unfold missCrossWeight;congr 1
    unfold pooledMarkWeight
    apply sum_congr rfl; intro c _
    by_cases mem : a∈constructorCellMarks n ell c
    · simp only [if_pos mem]
      have lo : L c≤a := (mem_Ico.mp (mem_filter.mp mem).1).1
      simp only [Z,branch,Nat.add_sub_of_le lo,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq];rfl
    · simp only [if_neg mem]
  rw [weight] at v
  apply v.trans
  let d := (Fixed.d b:ℝ)
  let E := fun k : B=>residueBranchEnvelope (p:ℝ)⁻¹ k.1*residueBranchEnvelope (q:ℝ)⁻¹ k.2.1*
    residueBranchEnvelope (d/ell) k.2.2
  let N := ∑ c : Cell, ∑ k : B,E k*D c k
  have qpos : 1≤(q:ℝ) := by exact_mod_cast (mem_primeBand.mp (mem_filter.mp qm).1).1.one_le
  have qm1 := inv_le_one_of_one_le₀ qpos
  have elm : 1+d/ell≤2 := by
    have dlt : (Fixed.d b:ℝ)≤ell := by exact_mod_cast (target_gt_degree target).le
    have pos : (0:ℝ)<ell := by exact_mod_cast (mem_dyadicTargets.mp target).1.pos
    linarith only [(div_le_one pos).mpr dlt,show d=(Fixed.d b:ℝ) from rfl]
  have pm : (p:ℝ)⁻¹ ≤ m := by
    dsimp only [m];rw [←rpow_neg_one];exact rpow_le_rpow_of_exponent_le pp (by linarith)
  have cell (c : Cell) : (∑ k : B,E k*D c k)≤6*U := by
    simp only [B,Fintype.sum_prod_type,Fintype.sum_bool,E,D,residueBranchEnvelope,Bool.not_true,Bool.not_false,
      Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,if_true,Bool.false_eq_true,if_false,
      mul_zero,add_zero,zero_add]
    calc
      _ = ((p:ℝ)⁻¹/m)*((1+2*(q:ℝ)⁻¹)*(1+d/ell))*U := by ring
      _ ≤ 1*(3*2)*U := by gcongr <;> first | exact (div_le_one mp).mpr pm | exact elm | linarith only [qm1]
      _ = _ := by ring
  have nb : N≤Fintype.card Cell*(6*U) := by
    simpa only [sum_const,nsmul_eq_mul,card_univ,N] using sum_le_sum (s:=univ) (fun c _=>cell c)
  have nonnegE (k : B) : 0≤E k := by dsimp [E,residueBranchEnvelope,d];split_ifs <;> positivity
  have nn : 0≤N := sum_nonneg (fun c _=>sum_nonneg (fun k _=>mul_nonneg (nonnegE k) (reg c k).1))
  change C*(N*M)^2*_≤_
  have bound : N*M≤count*missCrossScale b := (mul_le_mul_of_nonneg_right nb (Nat.cast_nonneg _)).trans_eq
    (by dsimp only [count,missCrossScale,M,U];ring)
  gcongr

/-- The squared Frobenius error of the ordinary-to-protected block, including
the intercept. A single pair of integer coefficient draws is used in every
entry, and rows outside its admitted set contribute zero. -/
def boxedMissCrossCost (n ell : ℕ) (β : ℝ) (x y : ℤ×ℤ) : ℝ :=
  let b := n.log2+1
  let H := Option (Bool×Fin (Fixed.d b))
  let count := (Fintype.card H:ℝ)*cellMarkCount b
  (∑ h : H, boxedPhysicalSingleCost (n:=n) (ell:=ell) β (fun i=>missCrossWeight n ell i.val β h) x y)/count^2

/-- Each diagonal tolerance can be charged to the intercept summand. -/
theorem boxedMissCross_single_le (n ell : ℕ) (β : ℝ) (x y : ℤ×ℤ) (h : Option (Bool×Fin (Fixed.d (n.log2+1)))) :
    let b := n.log2+1; let H := Option (Bool×Fin (Fixed.d b))
    boxedPhysicalSingleCost (n:=n) (ell:=ell) β (fun i=>missCrossWeight n ell i.val β h) x y /
      ((Fintype.card H:ℝ)*cellMarkCount b)^2 ≤ boxedMissCrossCost n ell β x y := by
  intro b H
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact single_le_sum (f:=fun h : H=>boxedPhysicalSingleCost (n:=n) (ell:=ell) β (fun i=>missCrossWeight n ell i.val β h) x y)
    (fun _ _=>sum_nonneg (fun i _=>mul_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))) (mem_univ h)

theorem admitted_miss_cross_budget (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let H := Option (Bool×Fin (Fixed.d b))
    ∀ (β u : ℝ), 0≤β → β≤1 → saddleMean (primeBand b) β=log (Fixed.B b)*u →
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∃ μ : ℝ, (∀ t : Ω,0≤boxedMissCrossCost n ell β t.1.val t.2.val) ∧
      HasSum (fun t : Ω=>twoFieldWeight O O t*boxedMissCrossCost n ell β t.1.val t.2.val) μ ∧
      μ≤Fintype.card H*(32*u)*(C*(missCrossScale b)^2*exp (-K*(Fixed.z b:ℝ)^2)) := by
  obtain ⟨C,cp,n₁,mom⟩ := ordinary_miss_cross_second line K hk
  obtain ⟨b₁,grow⟩ := Fixed.degree_grows 10004
  refine ⟨C,cp,max n₁ (max 2 (2^b₁)),?_⟩
  intro n large ell target comp absent b H β u bp βle saddle O Ω
  obtain ⟨old,big⟩ := max_le_iff.mp large
  obtain ⟨hn,lg⟩ := max_le_iff.mp big
  have hd := grow b (((Nat.le_log2 (by omega : n≠0)).mpr lg).trans (Nat.le_succ _))
  let count := (Fintype.card H:ℝ)*cellMarkCount b
  have countp : 0<count := mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr (Nat.pow_pos (by decide : 0<2)))
  let eps := C*(count*missCrossScale b)^2*exp (-K*(Fixed.z b:ℝ)^2)
  have ep : 0≤eps := by dsimp only [eps];positivity
  let cost := fun h (t : Ω)=>boxedPhysicalSingleCost (n:=n) (ell:=ell) β (fun i=>missCrossWeight n ell i.val β h) t.1.val t.2.val
  have cols (h : H) : ∃ a : ℝ, (∀ t,0≤cost h t) ∧ HasSum (fun t : Ω=>twoFieldWeight O O t*cost h t) a ∧ a≤32*u*eps :=
    admitted_physical_single_budget hn hd comp target absent β u eps bp ep saddle
      (fun i=>missCrossWeight n ell i.val β h) (fun i=>mom n old ell target comp absent i.val (mem_filter.mp i.prop).2 β βle h)
  choose mass nonneg measure bound using cols
  have both := (hasSum_sum (s:=univ) (fun h _=>measure h)).div_const (count^2)
  refine ⟨_,fun t=>div_nonneg (sum_nonneg (fun h _=>nonneg h t)) (sq_nonneg _),both.congr_fun (fun t=>?_ ),?_⟩
  · symm
    change (∑ h : H,twoFieldWeight O O t*cost h t)/count^2 = twoFieldWeight O O t*((∑ h : H,cost h t)/count^2)
    rw [←mul_sum,mul_div_assoc]
  · apply (div_le_div_of_nonneg_right (sum_le_sum (s:=univ) (fun h _=>bound h)) (sq_nonneg (count))).trans_eq
    simp only [sum_const,nsmul_eq_mul,card_univ,eps]
    field_simp <;> ring

/-- The mixed reference entry in the raw Gram equals the singleton center
times the square root of that row's saddle mass. -/
theorem miss_grid_cross_entry {n ell : ℕ} {I : Type*}
    (row : I→BandRow (n.log2+1)) (β : ℝ) :
    let b := n.log2+1
    let s := fun (a : GridPosition b)=>firstCellMark b (a.1.map gridPlace)+a.2.val
    let m := fun i : I=>(bandRowPrime (row i):ℝ)^(-β)
    let first := fun a (i : I)=>sqrt (m i)*
      (fullBandInsertion b (bandRowPrime (row i)) (branchMeshSaddle n ell (s a) false (row i).1)/
        ((bandRowPrime (row i):ℝ)*m i))
    ∀ (R : GridPosition b→I→I→ℝ) (h : Option (Fin (2*Fixed.d b))) (i : I),
      missGridGram (1-(Fixed.d b:ℝ)/ell) first R (.inl h) (.inr i) =
        sqrt (m i)*missCrossCenter n ell (row i) β (h.map gridPlace) := by
  intro b s m first R h i
  let miss := 1-(Fixed.d b:ℝ)/ell
  let F := fun (c : Option (Bool×Fin (Fixed.d b))) (j : ℕ)=>
    let a := firstCellMark b c+j
    miss*nominalLogFactor b (h.map gridPlace) a*
      (fullBandInsertion b (bandRowPrime (row i)) (branchMeshSaddle n ell a false (row i).1) /
        ((bandRowPrime (row i):ℝ)*m i))
  have logSame (a : GridPosition b) :
      gridLogColumn a h = nominalLogFactor b (h.map gridPlace) (s a) := by
    cases h with
    | none => rfl
    | some j =>
      change log |rawGridPoint b a.1 a.2-nominalCenter (Fixed.d b) j| =
        log |(s a:ℝ)/Fixed.A b-(center (Fixed.d b) (gridPlace j).1 (gridPlace j).2.val:ℝ)|
      rw [gridPlace_center];rfl
  let w := (cellMarkCount b:ℝ)⁻¹/(2*(Fixed.d b:ℝ)+1)
  change miss*(∑ a : GridPosition b,w*(gridLogColumn a h*first a i))=sqrt (m i)*missCrossCenter n ell (row i) β (h.map gridPlace)
  have ref : (∑ a : GridPosition b,w*F (a.1.map gridPlace) a.2.val)=missCrossCenter n ell (row i) β (h.map gridPlace) :=
    grid_position_average F
  rw [←ref,mul_sum,mul_sum]
  apply sum_congr rfl;intro a _
  rw [logSame]
  dsimp only [F,first,s]
  ring

/-- Repeated incidence on one row squares to itself. The diagonal reference
therefore uses the intercept profile with the full row mass divisor. -/
theorem miss_grid_diagonal_entry {n ell : ℕ} {I : Type*} [DecidableEq I]
    (row : I→BandRow (n.log2+1)) (β : ℝ) :
    let b := n.log2+1
    let s := fun (a : GridPosition b)=>firstCellMark b (a.1.map gridPlace)+a.2.val
    let p := fun i=>bandRowPrime (row i)
    let w := fun i=>sqrt ((p i:ℝ)^(-β))
    let ins := fun a (side : Bool) (q : ℕ)=>fullBandInsertion b q (branchMeshSaddle n ell (s a) false side)/
      ((q:ℝ)*(q:ℝ)^(-β))
    let R := fun a=>ordinaryRawEntry p (fun i=>(row i).1) w (ins a)
    ∀ (m : GridPosition b→I→ℝ) (i : I),
      missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inr i) (.inr i) = missCrossCenter n ell (row i) β none := by
  intro b s p w ins R m i
  let miss := 1-(Fixed.d b:ℝ)/ell
  let F := fun (c : Option (Bool×Fin (Fixed.d b))) (j : ℕ)=>
    miss*(fullBandInsertion b (p i) (branchMeshSaddle n ell (firstCellMark b c+j) false (row i).1)/
      ((p i:ℝ)*(p i:ℝ)^(-β)))
  have ref := grid_position_average F
  simp only [missCrossCenter,nominalLogFactor,mul_one]
  rw [←ref]
  simp only [missGridGram,missMomentEntry,R,ordinaryRawEntry,if_true]
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  dsimp only [F,ins,s,p,miss]
  ring


end
end Cogentic.Construction

#print axioms Cogentic.Construction.admitted_miss_cross_budget
