import Cogentic.EmpiricalBranchObservable
import Cogentic.PairHitReference
import Cogentic.RawGramTransfer

namespace Cogentic.Construction
open Finset Real Window
open scoped Classical
noncomputable section

/-- The physical Gram error is summed with one saddle mass per admitted row.
Dividing a pair hit by the two full masses here supplies the remaining
square-root factors for the normalized Frobenius norm. -/
def pairMissAmplitude (β : ℝ) (p q : ℕ) (hp hq ht : Bool) : ℝ :=
  if hp && hq && !ht then ((p:ℝ)^(-β)*(q:ℝ)^(-β))⁻¹ else 0

private theorem pair_hit_envelope {β t : ℝ} {p q : ℕ} (bp : β≤1) (pp : 1≤p) (qp : 1≤q)
    (tp : 0≤t) (cap : t≤1) :
    (∑ h : Bool×Bool×Bool, residueBranchEnvelope (p:ℝ)⁻¹ h.1 *
      residueBranchEnvelope (q:ℝ)⁻¹ h.2.1 * residueBranchEnvelope t h.2.2 *
      pairMissAmplitude β p q h.1 h.2.1 h.2.2) ≤ 3 := by
  have one (k : ℕ) (kp : 1≤k) : (k:ℝ)⁻¹*((k:ℝ)^(-β))⁻¹≤1 := by
    rw [←div_eq_mul_inv,div_le_one (rpow_pos_of_pos (by exact_mod_cast show 0<k from kp : (0:ℝ)<k) _)]
    rw [←Real.rpow_neg_one]
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast kp) (by linarith)
  have pq := mul_le_mul (one p pp) (one q qp) (by positivity) zero_le_one
  have bound := mul_le_mul pq (show 1+t≤3 by linarith) (by linarith only [tp]) (by norm_num : (0:ℝ)≤1*1)
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,residueBranchEnvelope,pairMissAmplitude,
    Bool.not_false,Bool.not_true,if_true,if_false,Bool.and_false,Bool.and_true,Bool.false_eq_true,
    mul_zero,zero_add,add_zero,mul_inv_rev] at *
  linarith only [bound]

def pairMissCenter {n ell : ℕ} (β : ℝ) (a : ↥(admissibleOrdinaryPairs n ell)) : ℝ :=
  let b := n.log2+1
  let Cell := Option (Bool×Fin (Fixed.d b))
  let p := bandRowPrime a.val.1; let q := bandRowPrime a.val.2
  let M := cellMarkCount b
  let F := fun (c : Cell) (h : Bool×Bool×Bool) j (side : Bool)=>
    fullBandInsertion b ((ordinaryPairOnField a side).pairBranchProduct p q h.1 h.2.1)
      (branchMeshSaddle n ell (firstCellMark b c+j) h.2.2 side)
  (∑ c : Cell,∑ h : Bool×Bool×Bool,residueBranchMass (p:ℝ)⁻¹ h.1*residueBranchMass (q:ℝ)⁻¹ h.2.1*
    residueBranchMass ((Fixed.d b:ℝ)/ell) h.2.2*(∑ j∈range M,
      pairMissAmplitude β p q h.1 h.2.1 h.2.2*(F c h j false*F c h j true)))/((Fintype.card Cell:ℝ)*M)

/-- The normalized center is the target-miss raw Gram entry averaged over
all positions in all constructor cells, with the common target-miss density. -/
theorem pair_miss_center_reference (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ell∈dyadicTargets (Fixed.beta b) →
    ∀ (a : ↥(admissibleOrdinaryPairs n ell)) (β : ℝ),
    let w := fun i : BandRow b=>sqrt ((bandRowPrime i:ℝ)^(-β))
    let Cell := Option (Bool×Fin (Fixed.d b)); let M := cellMarkCount b
    let I := fun k side (Q : ℕ)=>fullBandInsertion b Q (branchMeshSaddle n ell k false side)/((Q:ℝ)*(Q:ℝ)^(-β))
    (w a.val.1*w a.val.2)*pairMissCenter β a =
      (∑ c : Cell,∑ j∈range M,(1-(Fixed.d b:ℝ)/ell)*
        ordinaryRawEntry bandRowPrime Prod.fst w (I (firstCellMark b c+j)) a.val.1 a.val.2)/
        ((Fintype.card Cell:ℝ)*M) := by
  obtain ⟨b₁,ref⟩ := ordinary_pair_hit_reference
  obtain ⟨b₂,rangeLaw⟩ := canonical_mesh_saddle_range line
  refine ⟨max b₁ b₂,?_⟩
  intro n ell b big hn target a β w Cell M I
  obtain ⟨bref,bmesh⟩ := max_le_iff.mp big
  let i := a.val.1; let j := a.val.2
  let p := bandRowPrime i; let q := bandRowPrime j
  let m := fun k : ℕ=>(k:ℝ)^(-β)
  let R := ordinaryPairOnField a
  let d := (Fixed.d b:ℝ)
  let A := w i*w j
  obtain ⟨hi,hj,pq⟩ := admissible_pair_spec a
  have pos (t : BandRow b) : 0<w t := sqrt_pos.mpr
    (rpow_pos_of_pos (Nat.cast_pos.mpr (mem_primeBand.mp t.2.1.property).1.pos) _)
  have aa : A≠0 := (mul_pos (pos i) (pos j)).ne'
  have sq : m p*m q=A^2 := by
    dsimp only [m,A,w,p,q]
    rw [mul_pow,sq_sqrt (rpow_nonneg (Nat.cast_nonneg _) _),sq_sqrt (rpow_nonneg (Nat.cast_nonneg _) _)]
  have scale : A*(m p*m q)⁻¹=A⁻¹ := by rw [sq];field_simp
  unfold pairMissCenter
  rw [←mul_div_assoc]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro c _
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  let k := firstCellMark b c+t
  let α := branchMeshSaddle n ell k false
  let mass := fun hp hq=>residueBranchMass (p:ℝ)⁻¹ hp*residueBranchMass (q:ℝ)⁻¹ hq
  let F := fun hp hq=>fullBandInsertion b ((R false).pairBranchProduct p q hp hq) (α false)*
    fullBandInsertion b ((R true).pairBranchProduct p q hp hq) (α true)
  have valid side := rangeLaw bmesh hn target c false side t (mem_range.mp ht)
  have e := ref bref i j hi hj pq α β (fun s=>(valid s).1.1) (fun s=>(valid s).2)
  change (∑ hp : Bool,∑ hq : Bool,mass hp hq*(if hp && hq then A⁻¹ else 0)*F hp hq)=
    ordinaryRawEntry bandRowPrime Prod.fst w (I k) i j at e
  rw [←e]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,pairMissAmplitude,F,mass,residueBranchMass,
    Bool.not_true,Bool.not_false,Bool.and_true,Bool.and_false,Bool.false_and,Bool.true_and,
    if_true,Bool.false_eq_true,if_false,mul_zero,zero_mul,zero_add,add_zero]
  change A*((p:ℝ)⁻¹*(q:ℝ)⁻¹*(1-d/ell)*((m p*m q)⁻¹*F true true)) =
    (1-d/ell)*((p:ℝ)⁻¹*(q:ℝ)⁻¹*A⁻¹*F true true)
  linear_combination (p:ℝ)⁻¹*(q:ℝ)⁻¹*(1-d/ell)*F true true*scale

/-- Reindex the two admitted coordinates by the surviving row type. On distinct
primes the ordinary entry depends only on their field and prime labels. -/
theorem pair_miss_center_grid (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ell∈dyadicTargets (Fixed.beta b) →
    ∀ (a : ↥(admissibleOrdinaryPairs n ell)) (β : ℝ) {ι : Type*} [DecidableEq ι]
      (p : ι→ℕ) (side : ι→Bool) (i j : ι),
    p i=bandRowPrime a.val.1 → p j=bandRowPrime a.val.2 → side i=a.val.1.1 → side j=a.val.2.1 →
    let w := fun k : ι=>sqrt ((p k:ℝ)^(-β))
    let α := fun (z : GridPosition b)=>branchMeshSaddle n ell (firstCellMark b (z.1.map gridPlace)+z.2.val) false
    let I := fun z s (Q : ℕ)=>fullBandInsertion b Q (α z s)/((Q:ℝ)*(Q:ℝ)^(-β))
    let R := fun z=>ordinaryRawEntry p side w (I z)
    ∀ m : GridPosition b→ι→ℝ, w i*w j*pairMissCenter β a =
      missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inr i) (.inr j) := by
  obtain ⟨b₀,ref⟩ := pair_miss_center_reference line
  refine ⟨b₀,?_⟩
  intro n ell b big hn target a β ι _ p side i j pi' pj si sj w α I R m
  let miss := 1-(Fixed.d b:ℝ)/ell
  let W := fun v : BandRow b=>sqrt ((bandRowPrime v:ℝ)^(-β))
  let At := fun c t (s : Bool) (Q : ℕ)=>
    fullBandInsertion b Q (branchMeshSaddle n ell (firstCellMark b c+t) false s)/((Q:ℝ)*(Q:ℝ)^(-β))
  let f := fun c t=>ordinaryRawEntry bandRowPrime Prod.fst W (At c t) a.val.1 a.val.2
  have pq := (admissible_pair_spec a).2.2
  have eq (z : GridPosition b) : R z i j=f (z.1.map gridPlace) z.2.val := by
    simp only [R,f,ordinaryRawEntry,w,W,pi',pj,si,sj,if_neg pq]
    rfl
  have r := ref big hn target a β
  change (W a.val.1*W a.val.2)*pairMissCenter β a=
    (∑ c,∑ t∈range (cellMarkCount b),miss*f c t)/_ at r
  change w i*w j*pairMissCenter β a =
    miss*(∑ z : GridPosition b,(cellMarkCount b:ℝ)⁻¹/(2*(Fixed.d b:ℝ)+1)*R z i j)
  rw [show w i=W a.val.1 by simp only [w,W,pi'],show w j=W a.val.2 by simp only [w,W,pj],r]
  simp only [eq,grid_position_average f,←mul_sum,←mul_div_assoc] <;> rfl

def physicalPairMissWeight {n ell : ℕ} (β : ℝ) (a : ↥(admissibleOrdinaryPairs n ell)) (k : ℕ) : ℝ :=
  let p := bandRowPrime a.val.1; let q := bandRowPrime a.val.2
  let O := PrescribedRows.unrestricted n ell
  pooledMarkWeight univ (constructorCellMarks n ell)
    (fun _ y=>pairMissAmplitude β p q (decide (y ≡ a.val.1.2.2.val [MOD p]))
      (decide (y ≡ a.val.2.2.2.val [MOD q])) (hitsTarget n ell y false)-pairMissCenter β a) k/smoothMarkProbability O O k

/-- Aggregate all distinct ordinary pairs on the unrestricted law with the
physical row-hit observable, centered at its explicit raw-grid numerator. -/
theorem physical_pair_miss_entries_budget (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let d := (Fixed.d b:ℝ); let M := (cellMarkCount b:ℝ)
    let Cell := Option (Bool×Fin (Fixed.d b))
    let ε := C*(3*(Fintype.card Cell:ℝ)*M)^2*exp (-K*(Fixed.z b:ℝ)^2)
    ∀ β∈Set.Icc (0:ℝ) 1, ∀ u : ℝ, saddleMean (primeBand b) β=log (Fixed.B b)*u →
    let O := PrescribedRows.unrestricted n ell
    let Ω := O.CoeffPoint false × O.CoeffPoint true
    let cost := boxedPhysicalPairCost β (physicalPairMissWeight (n:=n) (ell:=ell) β)
    ∃ μ : ℝ, (∀ t : Ω,0≤cost t.1.val t.2.val) ∧
      HasSum (fun t : Ω=>twoFieldWeight O O t*cost t.1.val t.2.val) μ ∧ μ≤256*u^2*ε := by
  obtain ⟨C,cp,n₁,bound⟩ := physical_pair_mesh_numerator_sharp line K hk
  obtain ⟨b₁,grows⟩ := Fixed.degree_grows 10004
  refine ⟨C,cp,max n₁ (max 2 (2^b₁)),?_⟩
  intro n big ell target comp absent b d M Cell ε β βb u saddle O Ω cost
  obtain ⟨old,bign⟩ := max_le_iff.mp big
  obtain ⟨hn,lg⟩ := max_le_iff.mp bign
  have deg := grows b (((Nat.le_log2 (by omega : n≠0)).mpr lg).trans (Nat.le_succ _))
  apply admitted_physical_gram_budget hn deg comp target absent β u ε βb.1 (by dsimp [ε];positivity)
    saddle (physicalPairMissWeight β)
  intro a
  let i := a.val.1; let j := a.val.2
  let p := bandRowPrime i; let q := bandRowPrime j
  let R := ordinaryPairOnField a
  let r := i.2.2.val; let s := j.2.2.val
  obtain ⟨hi,hj,pq⟩ := admissible_pair_spec a
  have adm := ordinary_pair_admission i j hi hj pq
  have cover : ∀ U∈[R false,R true], U.primes⊆{p,q} ∧
      (p∈U.primes → U.residue p ≡ r [MOD p]) ∧ (q∈U.primes → U.residue q ≡ s [MOD q]) := by
    intro U h
    have each (side : Bool) := adm.2.1 side
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    obtain rfl|rfl := h
    all_goals
      first | exact ⟨(each false).1,fun _=>(each false).2.1 ▸ Nat.ModEq.refl _,fun _=>(each false).2.2 ▸ Nat.ModEq.refl _⟩
            | exact ⟨(each true).1,fun _=>(each true).2.1 ▸ Nat.ModEq.refl _,fun _=>(each true).2.2 ▸ Nat.ModEq.refl _⟩
  let Bit := Bool×Bool×Bool
  let amp := fun h : Bit=>pairMissAmplitude β p q h.1 h.2.1 h.2.2
  have nn (h : Bit) : 0≤amp h := by dsimp only [amp,pairMissAmplitude];split <;> positivity
  have cert := bound n old ell target comp absent hi.1 hj.1 pq hi.2.1 hj.2.1 r s (R false) (R true) cover
    (fun _ h _=>amp h) (fun _ h=>amp h)
    (fun _ h=>⟨nn h,fun _ _=>(abs_of_nonneg (nn h)).le,by simp [nn]⟩)
  let N := ∑ c : Cell,∑ h : Bit,residueBranchEnvelope (p:ℝ)⁻¹ h.1*residueBranchEnvelope (q:ℝ)⁻¹ h.2.1*
    residueBranchEnvelope (d/ell) h.2.2*amp h
  have pp := (mem_primeBand.mp i.2.1.property).1.one_le
  have qp := (mem_primeBand.mp j.2.1.property).1.one_le
  have ep : (0:ℝ)<ell := by exact_mod_cast (mem_dyadicTargets.mp target).1.pos
  have tcap : d/(ell:ℝ)≤1 := (div_le_one ep).mpr (by dsimp only [d];exact_mod_cast (target_gt_degree target).le)
  have en := pair_hit_envelope (p:=p) (q:=q) βb.2 pp qp (by positivity : 0≤d/(ell:ℝ)) tcap
  have ncap : N≤3*(Fintype.card Cell:ℝ) := by
    dsimp only [N,amp]
    rw [sum_const,nsmul_eq_mul,card_univ,mul_comm (3:ℝ)]
    exact mul_le_mul_of_nonneg_left en (Nat.cast_nonneg _)
  have env (x : ℝ) (hx : 0≤x) (v : Bool) : 0≤residueBranchEnvelope x v := by cases v <;> simp [residueBranchEnvelope,hx] <;> linarith
  have npos : 0≤N := sum_nonneg (fun _ _=>sum_nonneg (fun h _=>mul_nonneg
    (mul_nonneg (mul_nonneg (env _ (by positivity) _) (env _ (by positivity) _)) (env _ (by positivity) _)) (nn h)))
  apply cert.2.trans
  change C*(N*M)^2*_≤_
  dsimp only [ε]
  gcongr

end
end Cogentic.Construction

#print axioms Cogentic.Construction.physical_pair_miss_entries_budget
