import Cogentic.CenteredResidueContrast
import Cogentic.SimultaneousScoreBudget
import Cogentic.InsertionVariation

namespace Cogentic.Construction
open Finset Real
noncomputable section

/-- Ordinary row entry at a mark, expressed as a real scalar. -/
def residueEntry (p r a : ℕ) : ℝ := if a ≡ r [MOD p] then 1 else 0

theorem matrix_row_residueEntry (rel : Marking.Relations) (i : Fin rel.rows.length)
    (k : Fin rel.marks.length) (hr : (rel.rows.get i).r < (rel.rows.get i).q) :
    (rel.matrix i.succ k : ℝ) = residueEntry (rel.rows.get i).q (rel.rows.get i).r (rel.marks.get k) := by
  change ((if _ then 1 else 0 : ℤ):ℝ) = _
  simp only [residueEntry,Nat.ModEq,Nat.mod_eq_of_lt hr]
  split <;> norm_num

theorem residueEntry_product {p q : ℕ} (cop : p.Coprime q) (r s a : ℕ) :
    residueEntry p r a * residueEntry q s a = residueEntry (p*q) (crt p q r s) a := by
  have h := crt_spec cop r s
  have test : a ≡ crt p q r s [MOD p*q] ↔ a ≡ r [MOD p] ∧ a ≡ s [MOD q] := by
    rw [←Nat.modEq_and_modEq_iff_modEq_mul cop]
    exact ⟨fun t=>⟨t.1.trans h.1,t.2.trans h.2⟩,fun t=>⟨t.1.trans h.1.symm,t.2.trans h.2.symm⟩⟩
  simp only [residueEntry,test]
  split_ifs <;> simp_all

/-- The weighted off-diagonal entry of the executable mark matrix is the weighted
count in one CRT class. Repeated marks retain their multiplicities. -/
theorem matrix_overlap_crt (rel : Marking.Relations) (i j : Fin rel.rows.length)
    (w : Fin rel.marks.length → ℝ) (hi : (rel.rows.get i).r < (rel.rows.get i).q)
    (hj : (rel.rows.get j).r < (rel.rows.get j).q) (cop : (rel.rows.get i).q.Coprime (rel.rows.get j).q) :
    let u := rel.rows.get i; let v := rel.rows.get j
    ∑ k, w k*((rel.matrix i.succ k:ℝ)*(rel.matrix j.succ k:ℝ)) =
    ∑ k, w k*residueEntry (u.q*v.q) (crt u.q v.q u.r v.r) (rel.marks.get k) := by
  intro u v
  apply sum_congr rfl
  intro k _
  rw [matrix_row_residueEntry rel i k hi,matrix_row_residueEntry rel j k hj,residueEntry_product cop]

private theorem correction_coprime_band {b p q : ℕ} (hp : p∈pairCorrectionPrimes b) (hq : q∈primeBand b) : p.Coprime q := by
  obtain ⟨pp,_,lim⟩ := mem_pairCorrectionPrimes.mp hp
  obtain ⟨qp,_,large⟩ := mem_primeBand.mp hq
  apply (Nat.coprime_primes pp qp).mpr
  rintro rfl
  apply large.not_ge
  calc p^2 ≤ (2^(200*Fixed.h b))^2 := Nat.pow_le_pow_left lim _
       _ = 2^(200*Fixed.h b*2) := (Nat.pow_mul ..).symm
       _ ≤ Fixed.B b := Nat.pow_le_pow_right (by decide) (by dsimp [Fixed.beta];omega)

def meshVariation (L M : ℕ) (f : ℕ → ℝ) : ℝ :=
  |f (L+(M-1))| + ∑ j∈range (M-1), |f (L+(j+1))-f (L+j)|

/-- The local contrast is the joint ordinary row hit, centered by the same
mark profile. The denominator is the prescribed smooth marginal. -/
def overlapContrast {n ell : ℕ} (R T : PrescribedRows n ell) (p q r s : ℕ) (f : ℕ→ℝ) (a : ℕ) : ℝ :=
  (((p*q:ℕ):ℝ)*(residueEntry p r a*residueEntry q s a)-1)*f a/smoothMarkProbability R T a

def overlapError (b : ℕ) (K C D V : ℝ) : ℝ :=
  let e := exp (-K*(Fixed.z b:ℝ)^2)
  4*D^2*C*e + (2*V*(1+2*exp 6)*e)^2*exp (8/(Fixed.d b:ℝ)) +
    16*D^2/(Fixed.B b:ℝ)*exp (48*(Fixed.z b:ℝ))

/-- One-cell second moment under the unrestricted original coefficient law.
Admission contributes the joint prescribed modulus in the denominator. Both
row primes are taken from the constructor's actual unforced factor base. -/
theorem admitted_distinct_prime_overlap (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ R T : PrescribedRows n ell, let b := n.log2+1
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (p q r s : ℕ), p∈sieveBand n ell 1 → q∈sieveBand n ell 1 → p≠q →
    let L := firstCellMark b cell; let M := cellMarkCount b; let X := constructorCellMarks n ell cell
    ∀ (f : ℕ→ℝ) (D : ℝ), 0≤D → (∀ a∈X, |f a|≤D) →
    let O := PrescribedRows.unrestricted n ell
    let l := fun a (k : ℤ×ℤ) => R.compatible false k.1 k.2 ∧ smoothMarkEvent R false a k
    let t := fun a (k : ℤ×ℤ) => T.compatible true k.1 k.2 ∧ smoothMarkEvent T true a k
    twoFieldSecond O O X (overlapContrast R T p q r s f) l t ≤
      4*(overlapError b K C D (meshVariation L M f)*(M:ℝ)^2) /
        ((prodPrimes R.primes:ℝ)*(prodPrimes T.primes:ℝ)) := by
  obtain ⟨C,cp,n₀,localMoment⟩ := centered_residue_score_second line K hK
  refine ⟨C,cp,n₀,?_⟩
  intro n large ell target comp absent R T b cell p q r s hp hq diff L M X f D dp fb O l t
  obtain ⟨pb,pok,_⟩ := mem_filter.mp hp
  obtain ⟨qb,qok,_⟩ := mem_filter.mp hq
  obtain ⟨pp,pbnd,_⟩ := mem_primeBand.mp pb
  obtain ⟨qp,qbnd,_⟩ := mem_primeBand.mp qb
  have cop := (Nat.coprime_primes pp qp).mpr diff
  have bound : p*q≤(Fixed.B b)^3 := (Nat.mul_le_mul pbnd qbnd).trans (by
    rw [←sq];exact Nat.pow_le_pow_right (Nat.pow_pos (by decide)) (by decide))
  have clean := Nat.coprime_mul_iff_left.mpr ⟨pp.coprime_iff_not_dvd.mpr pok,qp.coprime_iff_not_dvd.mpr qok⟩
  have small h (hx : h∈pairCorrectionPrimes b) : h.Coprime (p*q) :=
    Nat.coprime_mul_iff_right.mpr ⟨correction_coprime_band hx pb,correction_coprime_band hx qb⟩
  have est := localMoment n large ell target comp absent R T cell (p*q) (crt p q r s)
    (Nat.mul_pos pp.pos qp.pos) ((Nat.squarefree_mul cop).mpr ⟨pp.squarefree,qp.squarefree⟩) bound clean small
    f f D dp (fun a ha=>⟨fb a ha,fb a ha⟩) rfl
  let v := overlapContrast R T p q r s f
  have matchWeight : (fun a=>((if a ≡ crt p q r s [MOD p*q] then ((p*q:ℕ):ℝ)*f a else 0)-f a)/
      smoothMarkProbability R T a) = v := by
    funext a
    dsimp only [v,overlapContrast]
    rw [residueEntry_product cop,residueEntry]
    split <;> ring
  change _ ≤ _ at est
  rw [matchWeight,(twoField_score_second R T target X v (smoothMarkEvent R false) (smoothMarkEvent T true)).tsum_eq] at est
  let U := overlapError b K C D (meshVariation L M f)*(M:ℝ)^2
  have cond : twoFieldSecond R T X v (smoothMarkEvent R false) (smoothMarkEvent T true) ≤ U :=
    est.trans_eq (by dsimp [U,overlapError,meshVariation,L,M,b];ring)
  have up : 0≤U := by dsimp [U,overlapError];positivity
  exact admitted_second_bound R T target X v (smoothMarkEvent R false) (smoothMarkEvent T true) U up cond

/-- The same scalar weight on every column can be represented by taking a
profile proportional to the prescribed marginal. This identity isolates the
profile whose bounded variation would be needed for the common-weight Gram. -/
theorem overlapContrast_common_weight {n ell : ℕ} (R T : PrescribedRows n ell)
    (p q r s a : ℕ) (w : ℕ→ℝ) (hm : smoothMarkProbability R T a ≠ 0) :
    overlapContrast R T p q r s (fun x=>smoothMarkProbability R T x*w x) a =
    (((p*q:ℕ):ℝ)*(residueEntry p r a*residueEntry q s a)-1)*w a := by
  dsimp [overlapContrast]
  field_simp

/-- With the pair's admission modulus p*q, the normalized overlap contributes
the product of row weights required by ordinary_gram_simultaneous_box. -/
theorem normalized_overlap_budget {n ell b : ℕ} (R T : PrescribedRows n ell)
    (i j : BandRow b) (α U M : ℝ) (mp : 0<M) (X : Finset ℕ) (w : ℕ→ℝ) (E F : ℕ→ℤ×ℤ→Prop)
    (h : twoFieldSecond R T X w E F ≤
      4*(U*M^2)/((bandRowPrime i:ℝ)*(bandRowPrime j:ℝ))) :
    let c := sqrt (((bandRowPrime i:ℝ)^(-α))*((bandRowPrime j:ℝ)^(-α)))/M
    twoFieldSecond R T X (fun a=>c*w a) E F ≤ 4*U*(bandRowWeight α i*bandRowWeight α j) := by
  intro c
  have pi : 0<(bandRowPrime i:ℝ) := by exact_mod_cast (mem_primeBand.mp i.2.1.property).1.pos
  have pj : 0<(bandRowPrime j:ℝ) := by exact_mod_cast (mem_primeBand.mp j.2.1.property).1.pos
  have sc : twoFieldSecond R T X (fun a=>c*w a) E F = c^2*twoFieldSecond R T X w E F := by
    simp only [twoFieldSecond,mul_sum]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro y _
    ring
  rw [sc]
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg c)).trans_eq
  dsimp only [c,bandRowWeight]
  rw [div_pow,Real.sq_sqrt (mul_nonneg (rpow_nonneg pi.le _) (rpow_nonneg pj.le _))]
  field_simp

private theorem mesh_product_variation {L M : ℕ} (mp : 0<M) (f g : ℕ→ℝ) (A J : ℝ) (ap : 0≤A)
    (fb : ∀ i<M, |f i|≤A) (gb : ∀ i<M, |g i|≤A)
    (fv : (∑ j∈range (M-1), |f (j+1)-f j|)≤J)
    (gv : (∑ j∈range (M-1), |g (j+1)-g j|)≤J) :
    meshVariation L M (fun a=> f (a-L)*g (a-L)) ≤ A^2+2*A*J := by
  have m : M-1<M := by omega
  have step j (hj : j∈range (M-1)) : |f (j+1)*g (j+1)-f j*g j|≤A*|g (j+1)-g j|+A*|f (j+1)-f j| := by
    obtain hj := mem_range.mp hj
    rw [show f (j+1)*g (j+1)-f j*g j=f (j+1)*(g (j+1)-g j)+(f (j+1)-f j)*g j by ring]
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right (fb _ (by omega)) (abs_nonneg _)) (by
      rw [mul_comm];exact mul_le_mul_of_nonneg_right (gb j (by omega)) (abs_nonneg _))
  have sum := sum_le_sum step
  rw [sum_add_distrib,←mul_sum,←mul_sum] at sum
  have tail := sum.trans (add_le_add (mul_le_mul_of_nonneg_left gv ap) (mul_le_mul_of_nonneg_left fv ap))
  dsimp only [meshVariation]
  simp only [Nat.add_sub_cancel_left,abs_mul (f (M-1))]
  exact (add_le_add (mul_le_mul (fb _ m) (gb _ m) (abs_nonneg _) ap) tail).trans_eq (by ring)

private theorem overlapError_mono {b : ℕ} {K C D u v : ℝ} (up : 0≤u) (uv : u≤v) :
    overlapError b K C D u ≤ overlapError b K C D v := by
  dsimp only [overlapError]
  gcongr

/-- On each fixed branch of the two target parts and the two ordinary-hit
products, the actual saddle insertions give a polynomially bounded profile
in the one-cell off-diagonal overlap moment. -/
theorem insertion_distinct_prime_overlap (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (D₀ D₁ : ℝ),
    D₀∈Set.Icc 1 ((Fixed.A b:ℝ)*(Fixed.B b:ℝ)^40) →
    D₁∈Set.Icc 1 ((Fixed.A b:ℝ)*(Fixed.B b:ℝ)^40) →
    let L := firstCellMark b cell; let M := cellMarkCount b; let d := (Fixed.d b:ℝ)
    let A := 3*(1760*d+4)^4; let J := 40*d^2*(1760*d+4)^4*(24+32*sqrt (110*d))
    ∃ α β : ℕ→ℝ, (∀ j<M, α j∈Set.Icc (199/200:ℝ) 1 ∧ β j∈Set.Icc (199/200:ℝ) 1 ∧
      Window.saddleMean (primeBand b) (α j)=log ((exactMean n ell (L+j) false:ℝ)/D₀) ∧
      Window.saddleMean (primeBand b) (β j)=log ((exactMean n ell (L+j) true:ℝ)/D₁)) ∧
    ∀ Q₀ Q₁ : ℕ, 0<Q₀ → log Q₀≤2*log (Fixed.B b:ℝ) → 0<Q₁ → log Q₁≤2*log (Fixed.B b:ℝ) →
    let f := fun a=>fullBandInsertion b Q₀ (α (a-L))*fullBandInsertion b Q₁ (β (a-L))
    (∀ j<M, |f (L+j)|≤A^2) ∧ meshVariation L M f ≤ A^2+2*A*J ∧
    ∀ (R T : PrescribedRows n ell) (p q r s : ℕ), p∈sieveBand n ell 1 → q∈sieveBand n ell 1 → p≠q →
    let O := PrescribedRows.unrestricted n ell
    let l := fun a (k : ℤ×ℤ) => R.compatible false k.1 k.2 ∧ smoothMarkEvent R false a k
    let t := fun a (k : ℤ×ℤ) => T.compatible true k.1 k.2 ∧ smoothMarkEvent T true a k
    twoFieldSecond O O (constructorCellMarks n ell cell) (overlapContrast R T p q r s f) l t ≤
      4*(overlapError b K C (A^2) (A^2+2*A*J)*(M:ℝ)^2) /
        ((prodPrimes R.primes:ℝ)*(prodPrimes T.primes:ℝ)) := by
  obtain ⟨C,cp,n₁,moment⟩ := admitted_distinct_prime_overlap line K hK
  obtain ⟨b₀,ins⟩ := constructor_cell_insertion_total_variation line
  refine ⟨C,cp,max n₁ (max 2 (2^b₀)),?_⟩
  intro n large ell target comp absent b cell D₀ D₁ left right L M d A J
  obtain ⟨old,more⟩ := max_le_iff.mp large
  obtain ⟨hn,lim⟩ := max_le_iff.mp more
  have big : b₀≤b := ((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _)
  obtain ⟨α,ha,ib⟩ := ins big hn target cell false D₀ left.1 left.2
  obtain ⟨β,hb,jb⟩ := ins big hn target cell true D₁ right.1 right.2
  refine ⟨α,β,fun j hj=>⟨(ha j hj).1,(hb j hj).1,(ha j hj).2,(hb j hj).2⟩,?_⟩
  intro Q₀ Q₁ q₀ h₀ q₁ h₁ f
  have ap : 0≤A := by dsimp only [A];positivity
  have mp : 0<M := Nat.pow_pos (by decide)
  obtain ⟨ab,av⟩ := ib Q₀ q₀ h₀
  obtain ⟨bb,bv⟩ := jb Q₁ q₁ h₁
  have sup (j) (hj : j<M) : |f (L+j)|≤A^2 := by
    dsimp only [f];rw [Nat.add_sub_cancel_left,abs_mul,pow_two]
    exact mul_le_mul (ab j hj) (bb j hj) (abs_nonneg _) ap
  have variation : meshVariation L M f ≤ A^2+2*A*J := mesh_product_variation mp _ _ A J ap ab bb av bv
  refine ⟨sup,variation,?_⟩
  intro R T p q r s pin qin diff O l t
  apply (moment n old ell target comp absent R T cell p q r s pin qin diff f (A^2) (sq_nonneg _) ?_).trans
  · have pos : 0 ≤ meshVariation L M f := add_nonneg (abs_nonneg _) (sum_nonneg (fun _ _=>abs_nonneg _))
    gcongr
    exact overlapError_mono pos variation
  · intro a ha'
    obtain ⟨lo,hi⟩ := mem_Ico.mp (mem_filter.mp ha').1
    have edge : L≤a := lo
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le edge
    exact sup j (by change L+j<L+M at hi;omega)

end
end Cogentic.Construction

#print axioms Cogentic.Construction.admitted_distinct_prime_overlap
#print axioms Cogentic.Construction.normalized_overlap_budget
#print axioms Cogentic.Construction.insertion_distinct_prime_overlap
