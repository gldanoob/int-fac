import Cogentic.BranchInsertionProfiles
import Cogentic.OrdinaryBranchNormalizer

namespace Cogentic.Construction
open Finset Real Window
open scoped Classical
noncomputable section

/-- Centering by the unconditional raw-mesh numerator incurs only the mass
drift of the conditional model. This uses the same scalar center across all
cells, target root classes, and ordinary prescriptions. -/
theorem mesh_numerator_center_error {C B : Type*} [Fintype C] [Fintype B]
    (M : ℕ) (mp : 0<M) [Nonempty C] (f z : C→B→ℕ→ℝ) (μ : B→ℝ) (η : ℝ)
    (norm : ∀ c j, j<M → |(∑ h,μ h*f c h j)-1|≤η) :
    let count := (Fintype.card C:ℝ)*M
    let θ := (∑ c,∑ h,μ h*(∑ j∈range M,z c h j*f c h j))/count
    |∑ c,∑ h,μ h*(∑ j∈range M,(z c h j-θ)*f c h j)|≤|θ| * count*η := by
  intro count θ
  have cp : 0<count := mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr mp)
  let d := ∑ c : C,∑ h : B,μ h*(∑ j∈range M,f c h j)
  have drift : |d-count|≤count*η := by
    have eq : d-count=∑ c : C,∑ j∈range M,((∑ h : B,μ h*f c h j)-1) := by
      dsimp only [d,count]
      simp only [mul_sum,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,mul_one,card_univ]
      congr 1
      apply sum_congr rfl;intro c _
      exact sum_comm
    rw [eq]
    apply (abs_sum_le_sum_abs ..).trans
    trans ∑ c : C,∑ j∈range M,|(∑ h : B,μ h*f c h j)-1|
    · apply sum_le_sum;intro c _;exact abs_sum_le_sum_abs ..
    have v := sum_le_sum (s:=univ) (fun (c:C) _=>sum_le_sum (s:=range M) (fun j hj=>norm c j (mem_range.mp hj)))
    simpa only [sum_const,card_range,nsmul_eq_mul,card_univ,count,mul_assoc] using v
  have numerator : (∑ c,∑ h,μ h*(∑ j∈range M,z c h j*f c h j))=θ*count := by
    dsimp only [θ];field_simp
  have id : (∑ c : C, ∑ h : B, μ h*(∑ j∈range M,(z c h j-θ)*f c h j))=θ*(count-d) := by
    simp only [sub_mul,sum_sub_distrib,mul_sub,←mul_sum,sum_sub_distrib]
    rw [numerator];dsimp only [d]
    simp only [mul_sum,mul_left_comm]
  rw [id,abs_mul,abs_sub_comm count d]
  exact (mul_le_mul_of_nonneg_left drift (abs_nonneg _)).trans_eq (mul_assoc ..).symm

/-- Each cell and ordinary/target hit pattern may carry a different observable.
On a fixed prescribed pair, cancellation of its explicit independent mesh mean
bounds its physical Gaussian second moment, with no loss in the sizes of the
two ordinary primes. The rare hit weights enter its amplitude through their
CRT densities. -/
theorem physical_pair_centered_observable (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ {p q : ℕ}, p∈sieveBand n ell 1 → q∈sieveBand n ell 1 → p≠q → p≠ell → q≠ell →
    ∀ (r s : ℕ) (R T : PrescribedRows n ell),
    (∀ U∈[R,T], U.primes⊆{p,q} ∧ (p∈U.primes → U.residue p ≡ r [MOD p]) ∧ (q∈U.primes → U.residue q ≡ s [MOD q])) →
    let b := n.log2+1; let M := cellMarkCount b; let L := firstCellMark b; let d := (Fixed.d b:ℝ)
    let A := 3*(1760*d+4)^4; let V := 40*d^2*(1760*d+4)^4*(24+32*sqrt (110*d))
    let P := 3*A^2+2*A*V; let e := exp (-K*(Fixed.z b:ℝ)^2)
    let Cell := Option (Bool×Fin (Fixed.d b)); let Bit := Bool×Bool×Bool
    let μ := fun (g : ℝ→Bool→ℝ) (h : Bit)=>g (p:ℝ)⁻¹ h.1*g (q:ℝ)⁻¹ h.2.1*g (d/ell) h.2.2
    let X := univ.biUnion (constructorCellMarks n ell)
    let O := PrescribedRows.unrestricted n ell
    let branch := fun a=>(decide (a ≡ r [MOD p]),decide (a ≡ s [MOD q]),hitsTarget n ell a false)
    let F := fun (c : Cell) (h : Bit) j=>
      fullBandInsertion b (R.pairBranchProduct p q h.1 h.2.1) (branchMeshSaddle n ell (L c+j) h.2.2 false)*
      fullBandInsertion b (T.pairBranchProduct p q h.1 h.2.1) (branchMeshSaddle n ell (L c+j) h.2.2 true)
    ∀ (Z : Cell→Bit→ℕ→ℝ) (D : Cell→Bit→ℝ),
    (∀ c h, 0≤D c h ∧ (∀ j<M, |Z c h j|≤D c h) ∧
      (∑ j∈range (M-1),|Z c h (j+1)-Z c h j|)≤D c h) →
    let N := ∑ c : Cell,∑ h : Bit,μ residueBranchEnvelope h*D c h
    let δ := ∑ c : Cell,∑ h : Bit,μ residueBranchMass h*(∑ j∈range M,Z c h j*F c h j)
    |δ|≤N*P*M*e →
    let w := pooledMarkWeight univ (constructorCellMarks n ell) (fun c a=>Z c (branch a) (a-L c))
    twoFieldSecond R T X (fun a=>w a/smoothMarkProbability O O a) (smoothMarkEvent R false) (smoothMarkEvent T true)
      ≤ C*(N*P*M)^2*e := by
  obtain ⟨C,H,cp,hp,n₁,phys⟩ := physical_pair_branch_second line K hk
  obtain ⟨B,bp,b₂,save⟩ := profileMomentBound_cancellation K C H hk cp.le
  obtain ⟨b₃,profiles⟩ := two_field_branch_profiles line
  refine ⟨B,bp,max n₁ (max 2 (2^(max b₂ b₃))),?_⟩
  intro n big ell target comp sieve p q pm qm pq pe qe r s R T cover b M L d A V P e Cell Bit μ X O branch F Z D regular N δ small w
  obtain ⟨old,rest⟩ := max_le_iff.mp big
  obtain ⟨hn,lg⟩ := max_le_iff.mp rest
  have ⟨bs,bprof⟩ := max_le_iff.mp (((Nat.le_log2 (by omega : n≠0)).mpr lg).trans (Nat.le_succ _))
  obtain ⟨α,β,law,moment⟩ := phys n old ell target comp sieve pm qm pq pe qe r s
  obtain ⟨γ,same,_,actual,size,variation⟩ := profiles bprof hn target (mem_filter.mp pm).1 (mem_filter.mp qm).1 pq r s R T cover α β law
  let G := fun c (h : Bit) j=>fullBandInsertion b (R.pairBranchProduct p q h.1 h.2.1) (γ c h.2.2 false j)*
      fullBandInsertion b (T.pairBranchProduct p q h.1 h.2.1) (γ c h.2.2 true j)
  let f := fun c (h : Bit) a=>Z c h (a-L c)*G c h (a-L c)
  let fa := fun c h a=>|f c h a|
  let Bnd := fun c h=>D c h*A^2
  have agrees c h j (jm : j<M) : G c h j=F c h j := by
    simp only [G,F,same _ _ _ _ jm,L,b]
  have obsN (h : Bit) : 0≤μ residueBranchEnvelope h := by
    have one (x : ℝ) (xn : 0≤x) (h : Bool) : 0≤residueBranchEnvelope x h := by cases h <;> simp [residueBranchEnvelope,xn] <;> linarith
    dsimp only [μ];exact mul_nonneg (mul_nonneg (one _ (by positivity) _) (one _ (by positivity) _)) (one _ (by positivity) _)
  have np : 0≤N := sum_nonneg (fun c _=>sum_nonneg (fun h _=>mul_nonneg (obsN _) (regular _ _).1))
  have Ap : 0≤A := by dsimp [A];positivity
  have Vp : 0≤V := by dsimp [V];positivity
  have AP : A^2≤P := by dsimp only [P];nlinarith only [mul_nonneg Ap Vp,sq_nonneg A]
  have Pp := (sq_nonneg A).trans AP
  have inside c a (ha : a∈constructorCellMarks n ell c) : a-L c<M := by
    have u : a<L c+M := (mem_Ico.mp (mem_filter.mp ha).1).2
    have l : L c≤a := (mem_Ico.mp (mem_filter.mp ha).1).1
    omega
  have fbd c h : 0≤Bnd c h ∧ ∀ a∈constructorCellMarks n ell c, |f c h a|≤Bnd c h := by
    refine ⟨mul_nonneg (regular _ _).1 (sq_nonneg _),fun a ha=>?_⟩
    dsimp only [f];rw [abs_mul]; exact mul_le_mul ((regular _ _).2.1 _ (inside c a ha)) (size c h _ (inside c a ha)) (abs_nonneg _) (regular _ _).1
  have obs a (ha : a∈X) :
      w a*(fullBandInsertion b (R.hitProduct a) (α a)*fullBandInsertion b (T.hitProduct a) (β a)) =
        ∑ c : Cell, if a∈constructorCellMarks n ell c then f c (branch a) a else 0 := by
    dsimp only [w,pooledMarkWeight];rw [sum_mul];apply sum_congr rfl;intro c _
    split_ifs with hc
    · rw [←actual c a hc]
    · simp
  have q := moment R T w f Bnd fbd obs
  let cellV := fun (g : Cell→Bit→ℕ→ℝ)=>∑ c : Cell,∑ h : Bit,μ residueBranchEnvelope h*meshVariation (L c) M (g c h)
  let raw := fun (t : ℝ→Bool→ℝ) (g : Cell→Bit→ℕ→ℝ)=>∑ c : Cell,∑ h : Bit,μ t h*(∑ j∈range M,g c h (L c+j))
  let sup := ∑ c : Cell,∑ h : Bit,μ residueBranchEnvelope h*Bnd c h
  have scale (h : ℝ) : (∑ c : Cell,∑ k : Bit,μ residueBranchEnvelope k*(D c k*h))=N*h := by
    simp only [N,sum_mul,mul_assoc]
  have supLim : |sup|≤N*P := by
    have eq : sup=N*A^2 := scale _
    rw [eq,abs_of_nonneg (mul_nonneg np (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left AP np
  have vlim (g : Cell→Bit→ℕ→ℝ) (hg : ∀ c h, meshVariation (L c) M (g c h) ≤ meshVariation (L c) M (f c h)) :
      |cellV g|≤N*P := by
    have vn c h : 0 ≤ meshVariation (L c) M (g c h) := by dsimp only [meshVariation];positivity
    rw [abs_of_nonneg (show 0≤cellV g from sum_nonneg (fun c _=>sum_nonneg (fun h _=>mul_nonneg (obsN _) (vn _ _)))),←scale]
    apply sum_le_sum;intro c _;apply sum_le_sum;intro h _
    apply mul_le_mul_of_nonneg_left _ (obsN _)
    apply (hg c h).trans
    have mp : 0<M := Nat.pow_pos (by decide : 0<2)
    have last : M-1<M := by omega
    let y := G c h
    let z := Z c h
    have zs j (jm : j<M) : |z j|≤D c h := (regular c h).2.1 _ jm
    have ys j (jm : j<M) : |y j|≤A^2 := size c h j jm
    have step j (hj : j∈range (M-1)) : |z (j+1)*y (j+1)-z j*y j|≤
        D c h*|y (j+1)-y j|+A^2*|z (j+1)-z j| := by
      have hj' := mem_range.mp hj
      rw [show z (j+1)*y (j+1)-z j*y j=z j*(y (j+1)-y j)+y (j+1)*(z (j+1)-z j) by ring]
      apply (abs_add_le ..).trans;rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right (zs j (by omega)) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (ys (j+1) (by omega)) (abs_nonneg _))
    have dv := sum_le_sum step
    rw [sum_add_distrib,←mul_sum,←mul_sum] at dv
    have dvG := variation c h
    change meshVariation (L c) M (fun a=>y (a-L c))≤A^2+2*A*V at dvG
    simp only [meshVariation,Nat.add_sub_cancel_left] at dvG
    have dy := mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left (abs_nonneg _)).trans dvG) (regular c h).1
    have dz := mul_le_mul_of_nonneg_left (regular c h).2.2 (sq_nonneg A)
    have ed := mul_le_mul (zs _ last) (ys _ last) (abs_nonneg _) (regular _ _).1
    change meshVariation (L c) M (fun a=>z (a-L c)*y (a-L c))≤D c h*P
    simp only [meshVariation,Nat.add_sub_cancel_left]
    rw [abs_mul];dsimp only [P]
    change A^2*(∑ j∈range (M-1),|z (j+1)-z j|)≤_ at dz
    nlinarith only [dy,dz,dv,ed]
  have absvar c h : meshVariation (L c) M (fa c h) ≤ meshVariation (L c) M (f c h) := by
    simp only [fa,meshVariation,abs_abs];apply add_le_add le_rfl;apply sum_le_sum;intro j _;exact abs_abs_sub_abs_le_abs_sub ..
  have signed : raw residueBranchMass f=δ := by
    apply sum_congr rfl;intro c _;apply sum_congr rfl;intro h _
    congr 1;apply sum_congr rfl;intro j hj;simp only [f,Nat.add_sub_cancel_left,agrees c h j (mem_range.mp hj)]
  have unsgn : |raw residueBranchEnvelope fa|≤N*P*M := by
    have pos : 0≤raw residueBranchEnvelope fa := sum_nonneg (fun c _=>sum_nonneg (fun h _=>mul_nonneg (obsN _) (sum_nonneg (fun j _=>abs_nonneg _))))
    rw [abs_of_nonneg pos]
    calc _ ≤ ∑ c : Cell,∑ h : Bit,μ residueBranchEnvelope h*(D c h*(P*M)) := by
           apply sum_le_sum;intro c _;apply sum_le_sum;intro h _
           apply mul_le_mul_of_nonneg_left _ (obsN _)
           have sum := sum_le_sum (s:=range M) (fun j hj=>mul_le_mul ((regular c h).2.1 j (mem_range.mp hj)) ((size c h j (mem_range.mp hj)).trans AP) (abs_nonneg _) (regular _ _).1)
           simp only [sum_const,card_range,nsmul_eq_mul] at sum
           simpa only [fa,f,G,Nat.add_sub_cancel_left,abs_mul,mul_assoc,mul_comm,mul_left_comm] using sum
         _ = _ := (scale _).trans (by ring)
  have savings := save b bs (Nat.succ_pos n.log2) sup (N*P) (raw residueBranchMass f) (cellV f)
    (raw residueBranchEnvelope fa) (cellV fa) (mul_nonneg np Pp) supLim (vlim f (fun _ _=>le_rfl))
    (vlim fa absvar) (signed ▸ small) unsgn
  exact q.trans savings

end
end Cogentic.Construction
#print axioms Cogentic.Construction.physical_pair_centered_observable
