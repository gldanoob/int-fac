import Cogentic.OrdinaryModelBlocks
import Cogentic.TargetBranchEnergy
import Cogentic.AuxiliaryBranchPrime

namespace Cogentic.Construction
open Finset Real Window
noncomputable section

/-- The conditional mean and full raw covariance on one target branch, using
the actual singleton and double-prime saddle insertions on one common scale.
The equal-prime premise pays for at most twice the degree many listed rows at
each prime, as in `grid_same_prime_compensation`. -/
theorem grid_ordinary_conditional_uniform :
    ∃ b₀ : ℕ, ∀ {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] {n : ℕ}, let b := n.log2+1
    b₀≤b → ∀ (α : Bool→ℝ) (β : ℝ), 1/2≤β → (∀ k, 199/200≤α k) →
    InMarkSaddleRange n (saddleMean (primeBand b) β) →
    (∀ k, InMarkSaddleRange n (saddleMean (primeBand b) (α k))) →
    ∀ (p : ι→ℕ) (side : ι→Bool), (∀ i, p i∈primeBand b) →
    ∀ ell∈primeBand b, ∀ (x : ℝ) (v : ι→ℝ) (t : κ→ℝ),
    let d := (Fixed.d b:ℝ); let μ := fun i=>(p i:ℝ)^(-β)
    let w := fun i=>sqrt (μ i)
    let I := fun k (q : ℕ)=>fullBandInsertion b q (α k)/((q:ℝ)*(q:ℝ)^(-β))
    let V := fun k=>saddleVariance (primeBand b) (primeProbability (α k)) (fun q=>log q)
    let m := fun i=>w i*I (side i) (p i)
    let h := fun i=>m i*log (p i)
    let E := fun i j=>if p i=p j then m i*m j-(if side i=side j then (h i)*(h j)/V (side i) else 0) else 0
    let F := ∑ i,(v i)^2; let T := ∑ r,(t r)^2
    let s := ∑ i,m i*v i
    let B := (∑ i,∑ j,v i*ordinaryRawEntry p side w I i j*v j)-s^2
    (∑ i,μ i)≤15000*d → (Fintype.card κ:ℝ)*x^2≤1 →
    (∀ k : Bool, (∑ i,if side i=k then w i*log (p i)*v i else 0)+
      (if k then 0 else x*log ell*(∑ r,t r))=0) →
    64*|∑ i,∑ j,v i*E i j*v j|≤F →
    s^2≤60000*d*F ∧ (7/8)*F-(1/32)*T≤B := by
  obtain ⟨C,cp,b₁,atoms⟩ := grid_scale_insertions
  obtain ⟨b₂,curve⟩ := joint_target_curvature_uniform
  obtain ⟨b₃,grows⟩ := Fixed.degree_grows (max 10004 ⌈256*C⌉₊)
  refine ⟨max b₁ (max b₂ b₃),?_⟩
  intro ι κ _ _ _ n b big α β ba aa mb ma p side pm ell em x v t d μ w I V m h E F T s B mass sparse perp blocks
  obtain ⟨one,other⟩ := max_le_iff.mp big
  obtain ⟨two,three⟩ := max_le_iff.mp other
  have deg := grows b three
  have dr : (10004:ℝ)≤d := by dsimp only [d];exact_mod_cast (le_max_left ..).trans deg
  have cg : 256*C≤d := (Nat.le_ceil _).trans (by dsimp only [d];exact_mod_cast (le_max_right ..).trans deg)
  let u := 90*d
  let τ := (Fintype.card κ:ℝ)*x^2
  have dp : 0<d := by linarith only [dr]
  have up : 0<u := by dsimp only [u];positivity
  have fnn : 0≤F := sum_nonneg fun i _=>sq_nonneg _
  have tnn : 0≤T := sum_nonneg fun r _=>sq_nonneg _
  have znn : 0≤τ := by dsimp only [τ];positivity
  have mn (i : ι) : 0≤μ i := rpow_nonneg (Nat.cast_nonneg _) _
  have wp (i : ι) : 0≤w i := sqrt_nonneg _
  have ws (i : ι) : (w i)^2=μ i := sq_sqrt (mn i)
  have drift (k : Bool) (i : ι) : |I k (p i)-1|≤1/64 :=
    (atoms one (α k) β (aa k) (by linarith only [ba]) (ma k) mb (p i) (pm i) (p i) (pm i)).1.trans
      ((div_le_iff₀ up).mpr (by dsimp only [u];linarith only [dr]))
  have singleton (i : ι) : 63/64≤I (side i) (p i) ∧ (I (side i) (p i))^2≤4 := by
    have hp := abs_le.mp (drift (side i) i)
    exact ⟨by linarith only [hp.1],(sq_le_sq' (by linarith only [hp.1] : -(2:ℝ)≤_) (by linarith only [hp.2])).trans_eq (by norm_num)⟩
  have msum : (∑ i,(m i)^2)≤4*(∑ i,μ i) := by
    rw [mul_sum];apply sum_le_sum;intro i _
    rw [show (m i)^2=μ i*(I (side i) (p i))^2 by dsimp only [m];rw [mul_pow,ws]]
    exact (mul_le_mul_of_nonneg_left (singleton i).2 (mn i)).trans_eq (mul_comm ..)
  constructor
  · apply (sum_mul_sq_le_sq_mul_sq univ m v).trans
    exact (mul_le_mul_of_nonneg_right (msum.trans (mul_le_mul_of_nonneg_left mass (by norm_num))) fnn).trans_eq (by ring)
  let cur := fun k=>(∑ i,if side i=k then h i*v i else 0)^2/V k
  let R := fun i j=>if side i=side j ∧ p i≠p j then
    w i*w j*(I (side i) (p i*p j)-I (side i) (p i)*I (side i) (p j)*(1-log (p i)*log (p j)/V (side i))) else 0
  let quad := fun (A : ι→ι→ℝ)=>∑ i,∑ j,v i*A i j*v j
  have rem (i j : ι) : |R i j| ≤ (C/u^2)*w i*w j := by
    dsimp only [R];split
    · rw [abs_mul,abs_mul,abs_of_nonneg (wp i),abs_of_nonneg (wp j)]
      exact (mul_le_mul_of_nonneg_left (atoms one (α (side i)) β (aa _) (by linarith only [ba])
        (ma _) mb (p i) (pm i) (p j) (pm j)).2 (mul_nonneg (wp i) (wp j))).trans_eq (by ring)
    · rw [abs_zero];positivity
  have rawR := covariance_remainder R v w (C/u^2) (by positivity) rem
  simp only [ws] at rawR
  have rate : (C/u^2)*(15000*d)≤1/64 := by
    rw [show C/u^2*(15000*d)=15000*C*d/u^2 by ring,div_le_iff₀ (sq_pos_of_pos up)]
    dsimp only [u];nlinarith only [mul_le_mul_of_nonneg_right cg dp.le,sq_nonneg d]
  have remB : |quad R|≤F/64 :=
    (rawR.trans (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left mass (by positivity : 0≤C/u^2)).trans rate) fnn)).trans_eq (by ring)
  have curveRate : (8*88^2/u^3)*(15000*d)≤1/64 := by
    rw [show 8*88^2/u^3*(15000*d)=(8*88^2*15000*d)/u^3 by ring,div_le_iff₀ (pow_pos up _)]
    have sq : (10004:ℝ)^2≤d^2 := sq_le_sq' (by linarith only [dr]) dr
    dsimp only [u];nlinarith only [mul_le_mul_of_nonneg_right sq dp.le,dp]
  have targetRate : (8/u)*τ≤1/64 :=
    (mul_le_mul_of_nonneg_left sparse (by positivity : 0≤8/u)).trans
      (by rw [mul_one,div_le_iff₀ up];dsimp only [u];linarith only [dr])
  have cb (k : Bool) : cur k≤F/64+T/64 := by
    let v' := fun i=>if side i=k then v i else 0
    let t' := fun r=>if k then 0 else t r
    have norm : (∑ i,w i*log (p i)*v' i)+x*log ell*(∑ r,t' r)=0 := by
      cases k
      · simpa [v',t',mul_ite] using perp false
      · simpa [v',t',mul_ite] using perp true
    have est := curve two (α k) β (aa k) (by linarith only [ba]) (ma k) mb p pm ell em x v' t' norm
    have fv : (∑ i,(v' i)^2)≤F := sum_le_sum (fun i _=>by dsimp only [v'];split <;> simp [sq_nonneg])
    have tv : (∑ r,(t' r)^2)≤T := sum_le_sum (fun r _=>by dsimp only [t'];split <;> simp [sq_nonneg])
    have head : (8*88^2/u^3)*(∑ i,μ i)*(∑ i,(v' i)^2)≤(1/64)*F :=
      mul_le_mul ((mul_le_mul_of_nonneg_left mass (by positivity)).trans curveRate) fv
        (sum_nonneg (fun i _=>sq_nonneg _)) (by norm_num)
    have tail : (8/u)*τ*(∑ r,(t' r)^2)≤(1/64)*T := mul_le_mul targetRate tv
      (sum_nonneg (fun r _=>sq_nonneg _)) (by norm_num)
    have first : cur k=(∑ i,I k (p i)*(w i*log (p i))*v' i)^2/V k := by
      dsimp only [cur];congr 2;apply sum_congr rfl;intro i _
      dsimp only [v'];split <;> simp_all only [h,m] <;> ring
    rw [first];exact (est.trans (add_le_add head tail)).trans_eq (by ring)
  have both : (∑ k,cur k)≤F/32+T/32 := by rw [Fintype.sum_bool];linarith only [cb false,cb true]
  have dg : (63/64)*F≤∑ i,I (side i) (p i)*(v i)^2 := by
    dsimp only [F];rw [mul_sum];exact sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (singleton i).1 (sq_nonneg _)
  have eq := ordinary_raw_quadratic p side w v I V
  change _=s^2+_-(∑ k,cur k)+quad R-quad E at eq
  dsimp only [B];rw [eq]
  nlinarith only [both,dg,(abs_le.mp remB).1,(le_abs_self (quad E)),blocks,fnn]

/-- The unconditional reference Gram on every raw mesh position. The same
finite vector is used on both target branches, on all listed ordinary rows
and all target residues. Only the two executable field norm equations and
the total admitted ordinary mass constrain the vector and the tuple. -/
theorem raw_grid_model_margin :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → ell∈dyadicTargets (Fixed.beta b) → ∀ a c e f : ℕ,
    let input := TryPair.fixedInput n ell (construct n ell a c e f)
    ∀ A : Finset Marking.Row, A⊆input.rows.toFinset → (∀ i∈A,i.q∈primeBand b) →
    ∀ (α : Bool→Bool→ℝ) (β : ℝ), 1/2≤β → (∀ hit k, 199/200≤α hit k) →
    InMarkSaddleRange n (saddleMean (primeBand b) β) →
    (∀ hit k, InMarkSaddleRange n (saddleMean (primeBand b) (α hit k))) →
    let d := (Fixed.d b:ℝ); let x := (sqrt (ell:ℝ))⁻¹
    let p := fun i : A=>i.val.q; let side := fun i : A=>i.val.second
    let μ := fun i : A=>(p i:ℝ)^(-β); let w := fun i=>sqrt (μ i)
    let I := fun hit k (q : ℕ)=>fullBandInsertion b q (α hit k)/((q:ℝ)*(q:ℝ)^(-β))
    (∑ i,μ i)≤15000*d →
    ∀ (g : ℝ) (v : A→ℝ) (t : Fin (Fixed.d b)→ℝ),
    (∀ k : Bool, (∑ i,if side i=k then w i*log (p i)*v i else 0)+
      (if k then 0 else x*log ell*(∑ r,t r))=0) →
    let F := (∑ i,(v i)^2)+(∑ r,(t r)^2)
    let τ := d*x^2
    let s := fun hit=>∑ i,w i*I hit (side i) (p i)*v i
    let B := fun hit=>(∑ i,∑ j,v i*ordinaryRawEntry p side w (I hit) i j*v j)-(s hit)^2
    let m := (1-τ)*s false+τ*s true+x*∑ r,t r
    let Q := (1-τ)*((g+s false)^2+B false)+τ*B true+∑ r,(x*(g+s true)+t r)^2
    m^2≤120000*d*F ∧ (g+m)^2+(13/16)*F≤Q := by
  classical
  -- The finite row types depend on the input. The degree thresholds used
  -- in the scalar curvature bound are obtained uniformly below.
  obtain ⟨b₁,same⟩ := grid_same_prime_compensation
  obtain ⟨b₂,large⟩ := Fixed.degree_grows 10004
  obtain ⟨b₃,ordinary⟩ := grid_ordinary_conditional_uniform
  refine ⟨max b₁ (max b₂ b₃),?_⟩
  intro n ell b big target a c e f input A sub rows α β ba aa mb ma d x p side μ w I mass g v t perp F τ s B m Q
  obtain ⟨one,other⟩ := max_le_iff.mp big
  obtain ⟨two,three⟩ := max_le_iff.mp other
  have dr : (10004:ℝ)≤d := by dsimp only [d];exact_mod_cast large b two
  have dp : 0<d := by linarith only [dr]
  have em := dyadic_target_in_primeBand (Nat.succ_pos n.log2) target
  have ep : (0:ℝ)≤ell := Nat.cast_nonneg _
  have bound := single_prime_row_mass (Nat.succ_pos n.log2) em (le_refl (1/2:ℝ))
  rw [rpow_neg ep,←sqrt_eq_rpow] at bound
  change x≤1/(65536*d) at bound
  have xp : 0≤x := inv_nonneg.mpr (sqrt_nonneg _)
  have num := (le_div_iff₀ (by positivity : 0<65536*d)).mp bound
  have sq := sq_le_sq' (by nlinarith only [mul_nonneg xp dp.le] : -(1:ℝ)≤x*(65536*d)) num
  have oneT : τ≤1/64 := by
    have le : τ≤d*τ := by apply le_mul_of_one_le_left (by dsimp only [τ];positivity);linarith only [dr]
    dsimp only [τ] at le ⊢
    nlinarith only [sq,le,sq_nonneg (d*x)]
  have tiny : 8192*τ*(60000*d)≤1 := by dsimp only [τ];nlinarith only [sq,sq_nonneg (d*x)]
  let v' := fun i : Marking.Row=>if hi : i∈A then v ⟨i,hi⟩ else 0
  have val (i : A) : v' i.val=v i := by simp only [v',dif_pos i.property]
  have model (h : Bool) : (s h)^2≤60000*d*(∑ i,(v i)^2) ∧
      (7/8)*(∑ i,(v i)^2)-(1/32)*(∑ r,(t r)^2)≤B h := by
    apply ordinary (ι:=↥A) (κ:=Fin (Fixed.d b)) three (α h) β ba (aa h) mb (ma h) p side
      (fun i=>rows i i.property) ell em x v t mass (by simpa only [Fintype.card_fin] using oneT.trans (by norm_num : (1/64:ℝ)≤1)) perp
    let V := fun k=>saddleVariance (primeBand b) (primeProbability (α h k)) (fun q=>log q)
    let W := fun k q=>I h k q
    let E' := fun i j : Marking.Row=>if i.q=j.q then (i.q:ℝ)^(-β)*W i.second i.q*W j.second j.q*
      (if i.second=j.second then 1-(log i.q)^2/V i.second else 1) else 0
    have ctrl := (same one target a c e f A sub rows (α h) β ba (aa h) mb (ma h)).2 v'
    change 64*|∑ i∈A,∑ j∈A,v' i*E' i j*v' j|≤∑ i∈A,(v' i)^2 at ctrl
    have coe (z : Marking.Row→ℝ) : (∑ i∈A,z i)=∑ i : A,z i.val := (sum_coe_sort A z).symm
    simp only [coe,val] at ctrl
    apply le_trans _ ctrl
    apply le_of_eq
    congr 2
    apply sum_congr rfl;intro i _
    apply sum_congr rfl;intro j _
    congr 2
    have ws : (w i)^2=μ i := sq_sqrt (rpow_nonneg (Nat.cast_nonneg _) _)
    dsimp only [E']
    by_cases sameP : p i=p j
    · have sameQ : i.val.q=j.val.q := sameP
      have weights : w j=w i := by dsimp only [w,μ];rw [sameP]
      rw [if_pos sameP,if_pos sameQ]
      change (w i*W (side i) (p i))*(w j*W (side j) (p j))-
        (if side i=side j then (w i*W (side i) (p i)*log (p i))*(w j*W (side j) (p j)*log (p j))/V (side i) else 0)=
        μ i*W (side i) (p i)*W (side j) (p j)*(if side i=side j then 1-(log (p i))^2/V (side i) else 1)
      rw [weights]
      dsimp only [W]
      rw [←ws,←sameP]
      split <;> ring
    · simp only [if_neg sameP,show i.val.q≠j.val.q from sameP,if_false]
  obtain ⟨m₀,c₀⟩ := model false
  obtain ⟨m₁,c₁⟩ := model true
  have total := mixed_target_gram_margin x g (s false) (s true) (B false) (B true)
    (∑ i,(v i)^2) (60000*d) t
  simp only [Fintype.card_fin] at total
  obtain ⟨mean,score⟩ := total oneT (sum_nonneg (fun i _=>sq_nonneg _)) (by linarith only [dr]) tiny m₀ m₁ c₀ c₁
  exact ⟨mean.trans_eq (by ring),score⟩

end
end Cogentic.Construction

#print axioms Cogentic.Construction.grid_ordinary_conditional_uniform
#print axioms Cogentic.Construction.raw_grid_model_margin
