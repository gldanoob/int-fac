import Cogentic.JointSmoothMoment
import Cogentic.ObservedScalar

namespace Cogentic.Construction
open Real Cogentic.Window
noncomputable section

/-- The projected Gaussian tail on each shifted lattice, normalized by its nominal mass. -/
theorem first_gaussian_tail (c H μ S T : ℝ) (hp : 0<H) (wide : 1≤S/H) (tp : 0≤T) :
    H/S*(∑' i : ℤ, if T*S ≤ |c+H*i-μ| then coeffGaussian (c+H*i) μ S else 0) ≤
      8*exp (-π*T^2/2) := by
  let θ := (μ-c)/H
  have sp : 0<S := by have := (le_div_iff₀ hp).mp wide; linarith
  have eq (i : ℤ) : T*S ≤ |c+H*i-μ| ↔ T*(S/H) ≤ |(i:ℝ)-θ| := by
    rw [show c+H*i-μ = ((i:ℝ)-θ)*H by dsimp [θ]; field_simp; ring,
      abs_mul,abs_of_pos hp,← div_le_iff₀ hp,mul_div_assoc]
  simp_rw [eq,coeffGaussian_progression _ _ _ _ _ hp]
  have tail := mul_le_mul_of_nonneg_left (lattice_gaussian_tail θ (S/H) T wide tp)
    (div_nonneg hp.le sp.le)
  exact tail.trans_eq (by field_simp [sp.ne',hp.ne'])

/-- The probability of an observation outside the bulk under the original prescribed
coefficient measure, uniformly in every set of root residues. -/
theorem PrescribedRows.first_observation_tail {n ell a : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (cap : a≤Fixed.A (n.log2+1))
    (side : Bool) (T : ℝ) (tp : 0≤T) :
    prescribedProbability R side (fun k =>
      T*projectionScale n a ≤ |((k.1+(a:ℤ)*k.2:ℤ):ℝ)-lineCenter n a|) ≤
      (1+90*exp (-(Fixed.U (n.log2+1):ℝ)))*(8*exp (-π*T^2/2)) := by
  classical
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  let H := R.hitProduct a
  let M := prodPrimes (R.miss a)
  let S := projectionScale n a
  let t := conditionalScale n a
  let μ : ℝ := lineCenter n a
  let bad (x : ℤ) := T*S ≤ |(x:ℝ)-μ|
  let E (k : ℤ×ℤ) := bad (k.1+(a:ℤ)*k.2)
  obtain ⟨c,r,e,coords,ws,_,_,events⟩ := R.coefficient_law target side cap
  let x := fun i : ℤ => c+(H:ℤ)*i
  let y := fun i j : ℤ => r i+(M:ℤ)*j
  let W := fun k : ℤ×ℤ => coeffGaussian (x k.1) μ S *
    coeffGaussian (y k.1 k.2) (projectedConditionalCenter n a (x k.1)) t
  let V := fun k : ℤ×ℤ => if bad (x k.1) then W k else 0
  have pos (k : ℤ×ℤ) : 0≤W k := mul_nonneg (exp_pos _).le (exp_pos _).le
  have summ : Summable W := ws
  have vs : Summable V := Summable.of_nonneg_of_le
    (fun k => by dsimp only [V]; split <;> first | exact pos k | rfl)
    (fun k => by dsimp only [V]; split <;> first | exact pos k | rfl) summ
  have weights (k : ℤ×ℤ) : coefficientWeight n (e k).val=W k := by
    rw [show (e k).val = _ from coords k.1 k.2]
    exact coefficient_weight_projection ..
  have den := (e.tsum_eq (fun k : C => coefficientWeight n k.val)).symm.trans (tsum_congr weights)
  have num := events E
  change prescribedProbability R side E = _ at num
  have eq : prescribedProbability R side E = (∑' k,V k)/(∑' k,W k) := by
    rw [num,den]
    congr 1
    apply tsum_congr
    intro k
    simp only [E,sub_add_cancel]
    rfl
  rw [vs.tsum_prod,summ.tsum_prod] at eq
  have inner (i : ℤ) : (∑' j : ℤ, V (i,j))=if bad (x i) then ∑' j : ℤ, W (i,j) else 0 := by
    by_cases hi : bad (x i) <;> simp [V,hi]
  simp_rw [inner] at eq
  let ref := (H:ℝ)/S*(∑' i : ℤ, if bad (x i) then coeffGaussian (x i) μ S else 0)
  have bounds := R.probability_scales cap
  have hp : 0<(H:ℝ) := by exact_mod_cast (R.subprod_bounds (s:=R.hit a) (Finset.filter_subset ..)).1
  have mp : 0<(M:ℝ) := by exact_mod_cast (R.subprod_bounds (s:=R.miss a) Finset.sdiff_subset).1
  have wide : 2≤S/(H:ℝ) := bounds.1
  have sp : 0<S := by have := (le_div_iff₀ hp).mp wide; linarith
  have nn : 0≤ref := mul_nonneg (div_nonneg hp.le sp.le)
    (tsum_nonneg (fun i => by split <;> first | exact (exp_pos _).le | rfl))
  have marg := gaussian_first_marginal c H S M t μ (fun i => (r i:ℝ))
    (fun i => projectedConditionalCenter n a (x i)) hp mp wide bounds.2.1 (fun i => bad (x i))
  have err : |prescribedProbability R side E-ref| ≤ 90*exp (-(Fixed.U (n.log2+1):ℝ))*ref := by
    rw [eq]
    apply le_trans _ (mul_le_mul_of_nonneg_right bounds.2.2.1 nn)
    simpa only [ref,W,x,y,Int.cast_add,Int.cast_mul,Int.cast_natCast] using marg
  have tail : ref ≤ 8*exp (-π*T^2/2) := by
    simpa only [ref,bad,x,Int.cast_add,Int.cast_mul,Int.cast_natCast] using
      first_gaussian_tail c H μ S T hp (by linarith) tp
  apply le_trans _ (mul_le_mul_of_nonneg_left tail (by positivity : 0≤1+90*exp (-(Fixed.U (n.log2+1):ℝ))))
  change prescribedProbability R side E ≤ _
  linarith only [(abs_le.mp err).2]

/-- Two coefficient events that agree inside the first-observation bulk have
probabilities within the first-coordinate tail bound. -/
theorem PrescribedRows.observation_cut_error {n ell a : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (cap : a≤Fixed.A (n.log2+1))
    (side : Bool) (T : ℝ) (tp : 0≤T) (A B : ℤ×ℤ→Prop) [DecidablePred A] [DecidablePred B]
    (agree : ∀ k : ℤ×ℤ, |((k.1+(a:ℤ)*k.2:ℤ):ℝ)-lineCenter n a|<T*projectionScale n a →
      (A k ↔ B k)) :
    |prescribedProbability R side A-prescribedProbability R side B| ≤
      (1+90*exp (-(Fixed.U (n.log2+1):ℝ)))*(8*exp (-π*T^2/2)) := by
  classical
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  let W (k : C) := coefficientWeight n k.val
  let Z := ∑' k, W k
  let bad (k : ℤ×ℤ) := T*projectionScale n a≤|((k.1+(a:ℤ)*k.2:ℤ):ℝ)-lineCenter n a|
  let G (E : ℤ×ℤ→Prop) [DecidablePred E] (k : C) := if E k.val then W k else 0
  have wn (k : C) : 0≤W k := mul_nonneg (exp_pos _).le (exp_pos _).le
  obtain ⟨_,_,_,_,_,zp,_,_⟩ := R.coefficient_law target side cap
  change 0<Z at zp
  have ws : Summable W := by by_contra h; exact zp.ne' (tsum_eq_zero_of_not_summable h)
  have gs (E : ℤ×ℤ→Prop) [DecidablePred E] : Summable (G E) := Summable.of_nonneg_of_le
    (fun k => by dsimp only [G]; split <;> first | exact wn k | rfl)
    (fun k => by dsimp only [G]; split <;> first | exact wn k | rfl) ws
  have cover (E F : ℤ×ℤ→Prop) [DecidablePred E] [DecidablePred F]
      (h : ∀ k, E k → ¬bad k → F k) : prescribedProbability R side E ≤
        prescribedProbability R side F+prescribedProbability R side bad := by
    change (∑' k,G E k)/Z ≤ (∑' k,G F k)/Z+(∑' k,G bad k)/Z
    rw [←add_div,div_le_div_iff_of_pos_right zp,←(gs F).tsum_add (gs bad)]
    apply (gs E).tsum_le_tsum _ ((gs F).add (gs bad))
    intro k
    by_cases he : E k.val <;> by_cases hf : F k.val <;> by_cases hb : bad k.val <;>
      first | exact (hf (h k.val he hb)).elim | simp [G,he,hf,hb,wn]
  have ab := cover A B (fun k hk good => (agree k (lt_of_not_ge good)).mp hk)
  have ba := cover B A (fun k hk good => (agree k (lt_of_not_ge good)).mpr hk)
  have tail := R.first_observation_tail target cap side T tp
  change prescribedProbability R side bad ≤ _ at tail
  exact abs_le.mpr ⟨by linarith only [ba,tail],by linarith only [ab,tail]⟩

/-- Integer lattice indices whose observation lies in a bounded interval. -/
def observationIndices (c H μ radius : ℝ) : Finset ℤ :=
  Finset.Icc ⌈(μ-radius-c)/H⌉ ⌊(μ+radius-c)/H⌋

theorem mem_observationIndices {c H μ radius : ℝ} (hp : 0<H) (i : ℤ) :
    i ∈ observationIndices c H μ radius ↔ |c+H*i-μ|≤radius := by
  rw [observationIndices,Finset.mem_Icc,Int.ceil_le,Int.le_floor,div_le_iff₀ hp,
    le_div_iff₀ hp,abs_le]
  constructor <;> rintro ⟨lo,hi⟩ <;> constructor <;> linarith

/-- The nominal density for one gcd class at the second mark, in the units
of scalarMass. Ineligible gcd classes have zero density. -/
def secondNominalDensity (n ell a' pre : ℕ) (side : Bool) (s : ℤ) (g : ℕ) (α : ℝ) : ℝ :=
  let b := n.log2+1
  let J := sieveBand n ell pre
  let band := J.filter (fun p=>¬p∣s.natAbs)
  let q := s.natAbs/g
  let Y := (exactMean n ell a' side:ℝ)/((pre:ℝ)*g)
  if g∈squarefreeSupport J then
    ((q:ℝ)/q.totient)*Y^(α-1)*eulerMass band α*
      omittedMass (primeBand b) (primeBand b\band) (primeProbability α) (fun p=>log p)
        (log (Fixed.B b)) 0/(2*π)
  else 0

private theorem real_scalar_bound {z : ℂ} {v ε : ℝ}
    (h : ‖(2*π:ℝ) • z-(v:ℂ)‖ ≤ ε*v) : |z.re-v/(2*π)| ≤ ε*(v/(2*π)) := by
  have p : 0<2*π := by positivity
  have hr := (Complex.abs_re_le_norm ((2*π:ℝ) • z-(v:ℂ))).trans h
  simp only [Complex.sub_re,Complex.smul_re,smul_eq_mul,Complex.ofReal_re] at hr
  rw [show z.re-v/(2*π) = ((2*π)*z.re-v)/(2*π) by field_simp,
    abs_div,abs_of_pos p,←mul_div_assoc,div_le_div_iff_of_pos_right p]
  exact hr

private theorem finite_nominal_transfer (I : Finset ℤ) (w m d : ℤ→ℝ) (L η ε actual : ℝ)
    (lp : 0≤L) (np : 0≤η) (wp : ∀ i ∈ I, 0≤w i) (dp : ∀ i ∈ I, 0≤d i)
    (pointwise : ∀ i ∈ I, |m i-d i|≤ε*d i)
    (joint : |actual-L*(∑ i ∈ I,w i*m i)|≤η*(L*(∑ i ∈ I,w i*m i))) :
    let nominal := L*(∑ i ∈ I,w i*d i)
    0≤nominal ∧ |actual-nominal|≤(η*(1+ε)+ε)*nominal := by
  let M := L*(∑ i ∈ I,w i*m i)
  let D := L*(∑ i ∈ I,w i*d i)
  have diff : |M-D|≤ε*D := by
    dsimp only [M,D]
    rw [←mul_sub,←Finset.sum_sub_distrib,abs_mul,abs_of_nonneg lp,mul_left_comm ε L]
    apply mul_le_mul_of_nonneg_left _ lp
    rw [Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum ?_)
    intro i hi
    rw [←mul_sub,abs_mul,abs_of_nonneg (wp i hi),mul_left_comm]
    exact mul_le_mul_of_nonneg_left (pointwise i hi) (wp i hi)
  have top : M≤(1+ε)*D := by linarith only [(abs_le.mp diff).2]
  refine ⟨mul_nonneg lp (Finset.sum_nonneg (fun i hi => mul_nonneg (wp i hi) (dp i hi))),?_⟩
  change |actual-D| ≤ _
  rw [show actual-D=(actual-M)+(M-D) by ring]
  apply (abs_add_le ..).trans
  have hj : |actual-M|≤η*M := joint
  have bound := mul_le_mul_of_nonneg_left top np
  linarith only [hj,diff,bound]

/-- On the full first-observation bulk, the actual two-mark probability is a
finite Gaussian-weighted sum of nominal gcd-class densities. Every supported
class uses a saddle for the exact center at the second mark. -/
theorem PrescribedRows.joint_bulk_nominal (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a≤Fixed.A b → a'∈(construct n ell 0 0 0 0).marks → a'≠a →
    (Fixed.A b:ℝ) ≤ |(a':ℝ)-a| * (dyadicUnit b:ℝ)^50 →
    ∀ side : Bool,
    let H := R.hitProduct a; let S := projectionScale n a; let μ : ℝ := lineCenter n a
    let radius := (b:ℝ)^3*S
    let J := sieveBand n ell (R.prefactor a side)
    let pre := R.prefactor a' side; let J' := sieveBand n ell pre; let s := R.secondStep a a' side
    ∃ (c : ℤ) (r : ℤ→ℤ) (α : ℤ→ℝ),
    let x := fun i : ℤ => c+(H:ℤ)*i
    let g := fun i : ℤ => commonDivisor (R.intercept a' side (x i-a*r i) (r i)) s
    let I := (observationIndices c H μ radius).filter (fun i => supportedValue J (R.intercept a side (x i) 0))
    (∀ i, R.compatible side (x i-a*r i) (r i)) ∧
    (∀ i ∈ I, g i∈squarefreeSupport J' → α i∈Set.Icc (199/200:ℝ) 1 ∧
      saddleMean (primeBand b) (α i)=log ((exactMean n ell a' side:ℝ)/((pre:ℝ)*g i))) ∧
    let D := (H:ℝ)/S*∑ i ∈ I, coeffGaussian (x i) μ S*secondNominalDensity n ell a' pre side s (g i) (α i)
    let p := prescribedProbability R side (fun k =>
      (|((k.1+(a:ℤ)*k.2:ℤ):ℝ)-μ|≤radius ∧ supportedValue J (R.intercept a side k.1 k.2)) ∧
      supportedValue J' (R.intercept a' side k.1 k.2))
    let η := 18*exp (-(Fixed.U b:ℝ))
    let ε := C*exp (-K*(Fixed.z b:ℝ)^2)
    let full := prescribedProbability R side (fun k =>
      supportedValue J (R.intercept a side k.1 k.2) ∧ supportedValue J' (R.intercept a' side k.1 k.2))
    0≤D ∧ |p-D|≤(η*(1+ε)+ε)*D ∧ |full-D|≤(η*(1+ε)+ε)*D+
      (1+90*exp (-(Fixed.U b:ℝ)))*(8*exp (-π*((b:ℝ)^3)^2/2)) := by
  classical
  obtain ⟨C,cp,b₁,observed⟩ := observed_second_scalar line K hK
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 10004
  refine ⟨C,cp,max b₁ b₂,?_⟩
  intro n ell a a' R b huge hn comp target absent cap mark diff clean side H S μ radius J pre J' s
  have big := degree b (max_le_iff.mp huge).2
  have am := mark_range hn big ((constructed_marks_iff ..).mp mark).2.1
  obtain ⟨c,r,ok,joint⟩ := R.joint_smooth_probability (le_trans (by decide : 3≤10004) big) target cap am diff side
  let x := fun i : ℤ => c+(H:ℤ)*i
  let g := fun i : ℤ => commonDivisor (R.intercept a' side (x i-a*r i) (r i)) s
  let I := (observationIndices c H μ radius).filter (fun i => supportedValue J (R.intercept a side (x i) 0))
  let F := fun u : ℤ => |(u:ℝ)-μ|≤radius
  let w := fun i : ℤ => coeffGaussian (x i) μ S
  let m := fun i : ℤ => (scalarMass J' (R.intercept a' side (x i-a*r i) (r i)) s
    (conditionalMean n ell a a' side (x i)/pre) (twoWidth n ell a a'/pre)).re
  let d := fun i α => secondNominalDensity n ell a' pre side s (g i) α
  let ε := C*exp (-K*(Fixed.z b:ℝ)^2)
  let η := 18*exp (-(Fixed.U b:ℝ))
  let Y := fun i => (exactMean n ell a' side:ℝ)/((pre:ℝ)*g i)
  have hp : 0<(H:ℝ) := by exact_mod_cast (R.subprod_bounds (s:=R.hit a) (Finset.filter_subset ..)).1
  have sp : 0<S := by dsimp [S,projectionScale,Fixed.A,Fixed.U]; positivity
  have mem (i : ℤ) : i∈I ↔ F (x i) ∧ supportedValue J (R.intercept a side (x i) 0) := by
    simp only [I,Finset.mem_filter,mem_observationIndices hp,F,x,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  have branches (i : ℤ) : ∃ α : ℝ,
      (i∈I → g i∈squarefreeSupport J' → α∈Set.Icc (199/200:ℝ) 1 ∧ saddleMean (primeBand b) α=log (Y i)) ∧
      (i∈I → 0≤d i α ∧ |m i-d i α|≤ε*d i α) := by
    by_cases hi : i∈I
    · let u := x i-(a:ℤ)*r i
      have obsEq : (u:ℝ)+(a:ℝ)*(r i:ℝ)=(x i:ℝ) := by simp [u]
      have bulk := (mem i|>.mp hi).1
      have h := observed R (max_le_iff.mp huge).1 hn comp target absent cap mark clean side u (r i) (ok i)
      dsimp only at h
      rw [obsEq] at h
      obtain ⟨zero,hit⟩ := h bulk
      by_cases gi : g i∈squarefreeSupport J'
      · obtain ⟨α,ha,mean,pos,estimate⟩ := hit gi
        refine ⟨α,fun _ _ => ⟨ha,mean⟩,fun _ => ?_⟩
        dsimp only [d,secondNominalDensity]
        rw [if_pos gi]
        refine ⟨div_nonneg pos.le (by positivity),?_⟩
        apply real_scalar_bound
        simpa only [ε,mul_right_comm] using estimate
      · refine ⟨1,fun _ h => (gi h).elim,fun _ => ?_⟩
        have mz : m i=0 := congrArg Complex.re (zero gi)
        have dz : d i 1=0 := by dsimp only [d,secondNominalDensity]; rw [if_neg gi]
        simp only [mz,dz,sub_self,abs_zero,mul_zero,le_refl,and_self]
    · exact ⟨1,fun h => (hi h).elim,fun h => (hi h).elim⟩
  choose α saddle point using branches
  refine ⟨c,r,α,ok,saddle,?_⟩
  obtain ⟨_,law⟩ := joint F
  have cut : (∑' i : ℤ, if F (x i) ∧ supportedValue J (R.intercept a side (x i) 0)
      then w i*m i else 0) = ∑ i ∈ I,w i*m i := by
    rw [tsum_eq_sum (s:=I) (fun i hi => if_neg (fun h => hi ((mem i).mpr h)))]
    exact Finset.sum_congr rfl (fun i hi => if_pos ((mem i).mp hi))
  change |_-((H:ℝ)/S*_ )| ≤ η*((H:ℝ)/S*_) at law
  rw [cut] at law
  have transferred := finite_nominal_transfer I w m (fun i => d i (α i)) ((H:ℝ)/S) η ε _
    (div_nonneg hp.le sp.le) (by dsimp [η]; positivity) (fun _ _ => (exp_pos _).le)
    (fun i hi => (point i hi).1) (fun i hi => (point i hi).2) law
  let full := fun k : ℤ×ℤ => supportedValue J (R.intercept a side k.1 k.2) ∧
    supportedValue J' (R.intercept a' side k.1 k.2)
  let bulk := fun k : ℤ×ℤ => (F (k.1+(a:ℤ)*k.2) ∧ supportedValue J (R.intercept a side k.1 k.2)) ∧
    supportedValue J' (R.intercept a' side k.1 k.2)
  have tail := R.observation_cut_error target cap side ((b:ℝ)^3) (by positivity) full bulk (by
    intro k hk
    have h : F (k.1+(a:ℤ)*k.2) := hk.le
    simp only [full,bulk,h,true_and])
  refine ⟨transferred.1,transferred.2,?_⟩
  let D := (H:ℝ)/S*∑ i ∈ I, w i*d i (α i)
  change |prescribedProbability R side full-D| ≤ _
  rw [show prescribedProbability R side full-D = (prescribedProbability R side full-
    prescribedProbability R side bulk)+(prescribedProbability R side bulk-D) by ring]
  apply (abs_add_le ..).trans
  exact (add_le_add tail transferred.2).trans_eq (add_comm ..)

end
end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.first_observation_tail

#print axioms Cogentic.Construction.PrescribedRows.joint_bulk_nominal
