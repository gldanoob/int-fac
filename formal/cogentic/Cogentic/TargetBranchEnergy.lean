import Cogentic.Rank

namespace Cogentic.Construction
open Finset Real
noncomputable section

/-- On the miss branch the ordinary score is `s₀`. On each of the equally
weighted target roots it is `s₁`, and the normalized target coordinate is
`v i / x`, where `x² = 1 / ell`. Completing the square separates the mean
from the target variance before averaging over physical mesh positions. -/
theorem target_branch_energy {ι : Type*} [Fintype ι] (x g s₀ s₁ : ℝ) (v : ι → ℝ) :
    let t := (Fintype.card ι : ℝ)*x^2
    let m := (1-t)*s₀+t*s₁+x*∑ i,v i
    let F := ∑ i,(v i)^2
    let Q := (1-t)*(g+s₀)^2+∑ i,(x*(g+s₁)+v i)^2
    t ≤ 1/64 →
    m^2 ≤ 2*((1-t)*s₀^2+t*s₁^2)+2*t*F ∧
    (g+m)^2+(15/16)*F ≤ Q+32*t*(s₁-s₀)^2 := by
  intro t m F Q rare
  let Δ := s₁-s₀
  let w := fun i => v i+x*Δ
  let W := ∑ i,(w i)^2
  have tn : 0≤t := by dsimp [t]; positivity
  have t1 : t≤1 := by linarith only [rare]
  have cs (z : ι→ℝ) : (x*∑ i,z i)^2 ≤ t*∑ i,(z i)^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _=> (1:ℝ)) z
    simpa only [t,mul_pow,one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one,
      mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left h (sq_nonneg x)
  have mean : ((1-t)*s₀+t*s₁)^2 ≤ (1-t)*s₀^2+t*s₁^2 := by
    nlinarith only [mul_nonneg (mul_nonneg tn (sub_nonneg.mpr t1)) (sq_nonneg Δ)]
  constructor
  · have base := sq_nonneg (((1-t)*s₀+t*s₁)-x*∑ i,v i)
    change (((1-t)*s₀+t*s₁)+x*∑ i,v i)^2≤_
    nlinarith only [base,mean,cs v]
  have shiftSum : ∑ i,w i=(∑ i,v i)+(Fintype.card ι:ℝ)*(x*Δ) := by
    simp only [w,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul]
  have shifted : m=s₀+x*(∑ i,w i) := by
    rw [shiftSum]; dsimp [m,t,Δ];ring
  have sqsplit : ∑ i,(x*(g+s₁)+v i)^2 =
      (Fintype.card ι:ℝ)*(x*(g+s₀))^2+2*x*(g+s₀)*(∑ i,w i)+W := by
    have pt (i : ι) : (x*(g+s₁)+v i)^2 = (x*(g+s₀))^2+2*x*(g+s₀)*w i+(w i)^2 := by
      dsimp [w,Δ];ring
    simp only [pt,W,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,mul_sum]
  have exactQ : Q=(g+m)^2+W-(x*∑ i,w i)^2 := by
    dsimp only [Q];rw [sqsplit,shifted];dsimp only [t];ring
  have rows (i : ι) : (31/32)*(v i)^2 ≤ (w i)^2+31*(x*Δ)^2 := by
    dsimp only [w]
    nlinarith only [sq_nonneg (v i+32*x*Δ)]
  have total := Finset.sum_le_sum (s:=univ) (fun i _=>rows i)
  simp only [←mul_sum,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul] at total
  change (31/32)*F ≤ W+31*((Fintype.card ι:ℝ)*(x*Δ)^2) at total
  have loss : t*W≤(1/64)*W := mul_le_mul_of_nonneg_right rare (sum_nonneg fun i _=>sq_nonneg _)
  have vw := cs w
  change (x*∑ i,w i)^2≤t*W at vw
  have nonneg := mul_nonneg tn (sq_nonneg Δ)
  rw [exactQ]
  change _ ≤ _+32*t*Δ^2
  rw [show 31*((Fintype.card ι:ℝ)*(x*Δ)^2)=31*t*Δ^2 by dsimp only [t];ring] at total
  nlinarith only [total,loss,vw,nonneg,sum_nonneg (s:=univ) (fun (i:ι) _=>sq_nonneg (v i))]

/-- Ordinary means and conditional variances on the two target branches give
a single centered model for the intercept, logarithms, and all finite rows.
`x²` is the density of a specified target residue. -/
theorem mixed_target_gram_margin {ι : Type*} [Fintype ι]
    (x g s₀ s₁ B₀ B₁ F M : ℝ) (v : ι→ℝ) :
    let t := (Fintype.card ι:ℝ)*x^2
    let T := ∑ i,(v i)^2
    let m := (1-t)*s₀+t*s₁+x*∑ i,v i
    let Q := (1-t)*((g+s₀)^2+B₀)+t*B₁+∑ i,(x*(g+s₁)+v i)^2
    t≤1/64 → 0≤F → 1≤M → 8192*t*M≤1 →
    s₀^2≤M*F → s₁^2≤M*F →
    (7/8)*F-(1/32)*T≤B₀ → (7/8)*F-(1/32)*T≤B₁ →
    m^2≤2*M*(F+T) ∧ (g+m)^2+(13/16)*(F+T)≤Q := by
  intro t T m Q rare fp M1 small left right miss hit
  have tn : 0≤t := by dsimp only [t];positivity
  have Tn : 0≤T := sum_nonneg fun i _=>sq_nonneg _
  have co : 0≤1-t := by linarith only [rare]
  have b := target_branch_energy x g s₀ s₁ v rare
  have avg := add_le_add (mul_le_mul_of_nonneg_left left co) (mul_le_mul_of_nonneg_left right tn)
  have tc := mul_le_mul_of_nonneg_right (show t≤M by linarith only [rare,M1]) Tn
  constructor
  · have first := b.1
    change m^2 ≤ 2*((1-t)*s₀^2+t*s₁^2)+2*t*T at first
    nlinarith only [first,avg,tc]
  · have jump : (s₁-s₀)^2≤4*M*F := by nlinarith only [left,right,sq_nonneg (s₁+s₀)]
    have cost : 32*t*(s₁-s₀)^2 ≤ F/64 := by
      nlinarith only [mul_le_mul_of_nonneg_left jump (mul_nonneg (by norm_num : (0:ℝ)≤32) tn),
        mul_le_mul_of_nonneg_right small fp]
    have margin := add_le_add (mul_le_mul_of_nonneg_left miss co) (mul_le_mul_of_nonneg_left hit tn)
    have core := b.2
    change (g+m)^2+(15/16)*T ≤ (1-t)*(g+s₀)^2+(∑ i,(x*(g+s₁)+v i)^2)+32*t*(s₁-s₀)^2 at core
    dsimp only [Q];nlinarith only [margin,core,cost,fp,Tn]

/-- Common-scale raw ordinary Gram entry on a mesh position and target branch. -/
def ordinaryRawEntry {ι : Type*} [DecidableEq ι] (p : ι→ℕ) (side : ι→Bool)
    (w : ι→ℝ) (I : Bool→ℕ→ℝ) (i j : ι) : ℝ :=
  if p i=p j then (if i=j then I (side i) (p i) else 0)
  else if side i=side j then w i*w j*I (side i) (p i*p j)
  else (w i*I (side i) (p i))*(w j*I (side j) (p j))

/-- Exact raw second moment of the ordinary rows. Equal-prime pairs contribute
their diagonal alone. Distinct primes on the same side use a joint insertion,
whereas different sides use the product of their singleton insertions. -/
theorem ordinary_raw_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι→ℕ) (side : ι→Bool) (w v : ι→ℝ) (I : Bool→ℕ→ℝ) (V : Bool→ℝ) :
    let m := fun i=>w i*I (side i) (p i)
    let h := fun i=>(m i)*log (p i)
    let curv := fun i j=>if side i=side j then (h i)*(h j)/V (side i) else 0
    let P := ordinaryRawEntry p side w I
    let R := fun i j=>if side i=side j ∧ p i≠p j then
      w i*w j*(I (side i) (p i*p j)-I (side i) (p i)*I (side i) (p j)*
        (1-log (p i)*log (p j)/V (side i))) else 0
    let E := fun i j=>if p i=p j then m i*m j-curv i j else 0
    (∑ i,∑ j,v i*P i j*v j) =
      (∑ i,m i*v i)^2+(∑ i,I (side i) (p i)*(v i)^2)-
      (∑ k : Bool,(∑ i,if side i=k then h i*v i else 0)^2/V k)+
      (∑ i,∑ j,v i*R i j*v j)-(∑ i,∑ j,v i*E i j*v j) := by
  intro m h curv P R E
  let D := fun i j : ι=>if i=j then I (side i) (p i) else 0
  have pair (i j : ι) : P i j = m i*m j+D i j-curv i j+R i j-E i j := by
    by_cases same : p i=p j
    · simp [P,ordinaryRawEntry,R,E,D,same,m]
    · have ne : i≠j := fun eq=>same (congrArg p eq)
      by_cases eq : side i=side j <;>
        simp [P,ordinaryRawEntry,R,E,D,curv,h,m,same,ne,eq] <;> ring
  have mean : (∑ i,∑ j,v i*(m i*m j)*v j)=(∑ i,m i*v i)^2 := by
    rw [sq];simp only [mul_sum,sum_mul];apply sum_congr rfl;intro i _;apply sum_congr rfl;intro j _;ring
  have diag : (∑ i,∑ j,v i*D i j*v j)=∑ i,I (side i) (p i)*(v i)^2 := by
    apply sum_congr rfl;intro i _
    rw [sum_eq_single i];simp [D];ring
    · intro j _ ne;simp [D,Ne.symm ne]
    · simp
  have ce : (∑ i,∑ j,v i*curv i j*v j)=∑ k : Bool,(∑ i,if side i=k then h i*v i else 0)^2/V k := by
    have entry (i j : ι) : v i*curv i j*v j = ∑ k : Bool,
        (if side i=k then h i*v i else 0)*(if side j=k then h j*v j else 0)/V k := by
      cases si : side i <;> cases sj : side j <;> simp [curv,si,sj] <;> ring
    simp only [entry]
    rw [sum_comm]
    conv_lhs => enter [2,j];rw [sum_comm]
    rw [sum_comm]
    apply sum_congr rfl;intro k _
    rw [sq,Finset.sum_mul];simp only [mul_sum,div_eq_mul_inv,Finset.sum_mul]
    rw [sum_comm]
  simp only [pair,mul_add,add_mul,mul_sub,sub_mul,sum_add_distrib,sum_sub_distrib,mean,diag,ce]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.target_branch_energy
#print axioms Cogentic.Construction.ordinary_raw_quadratic
#print axioms Cogentic.Construction.mixed_target_gram_margin
