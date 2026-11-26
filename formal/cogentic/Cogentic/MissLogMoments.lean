import Cogentic.RawProtectedMoments
import Cogentic.OrdinaryBranchMasks

namespace Cogentic.Construction
open Finset Real
open scoped Classical
noncomputable section

private theorem combined_second {J : Type*} [Fintype J] {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (X : Finset ℕ) (E F : ℕ→ℤ×ℤ→Prop)
    (f : J→ℕ→ℝ) (c : J→ℝ) (w : ℕ→ℝ) (M : ℝ)
    (eqn : ∀ a,w a=∑ i,c i*f i a)
    (parts : ∀ i,twoFieldSecond R T X (f i) E F≤M) :
    twoFieldSecond R T X w E F≤(∑ i,|c i|)^2*M := by
  let Ω := R.CoeffPoint false×T.CoeffPoint true
  let p := twoFieldWeight R T
  let H := ∑ i, |c i|
  have hn : 0≤H := sum_nonneg fun i _=>abs_nonneg _
  let score := fun (g : ℕ→ℝ) (k : Ω)=>twoFieldScore X g E F k.1.val k.2.val
  let B := fun i=>twoFieldSecond R T X (f i) E F
  have law i := ((twoField_score_second R T target X (f i) E F).mul_left |c i|).mul_left H
  have upper := hasSum_sum (s:=univ) (fun i _=>law i)
  have total := twoField_score_second R T target X w E F
  have bound (k : Ω) : (score w k)^2≤H*∑ i, |c i| *(score (f i) k)^2 := by
    have sc : score w k=∑ i,c i*score (f i) k := by
      simp only [score,twoFieldScore,eqn,sum_mul,mul_sum]
      rw [sum_comm]
      simp only [mul_assoc]
    rw [sc]
    exact sum_sq_le_sum_mul_sum_of_sq_le_mul univ (fun i _=>abs_nonneg _) (fun i _=>mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun i _=>by rw [mul_pow,←mul_assoc,←sq,sq_abs])
  have raw : twoFieldSecond R T X w E F≤∑ i,H*(|c i| *B i) := by
    apply hasSum_le _ total upper
    intro k
    have pp : 0≤p k := mul_nonneg (R.pointMass_nonneg ..) (T.pointMass_nonneg ..)
    apply (mul_le_mul_of_nonneg_left (bound k) pp).trans_eq
    simp only [mul_sum,p,score,H,mul_comm,mul_assoc,mul_left_comm]
  rw [←mul_sum] at raw
  apply raw.trans
  have h := sum_le_sum (s:=univ) (fun i _=>mul_le_mul_of_nonneg_left (parts i) (abs_nonneg (c i)))
  rw [←sum_mul] at h
  exact (mul_le_mul_of_nonneg_left h hn).trans_eq (by dsimp only [H];ring)

/-- Every entry of the intercept/logarithm block after restriction to the
target misses. Its center is the miss density times the raw mesh mean. -/
theorem miss_log_gram_second (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let Cell := Option (Bool×Fin (Fixed.d b))
    let M := cellMarkCount b; let L := firstCellMark b; let Y := constructorCellMarks n ell
    let O := PrescribedRows.unrestricted n ell; let D := 3*(Fixed.h b:ℝ)+1
    ∀ (i k : Cell),
    let f := fun a=>nominalLogFactor b i a*nominalLogFactor b k a
    let count := (Fintype.card Cell:ℝ)*M
    let θ := (∑ c : Cell,∑ j∈range M,f (L c+j))/count
    let miss := 1-(Fixed.d b:ℝ)/ell
    let w := pooledMarkWeight univ Y (fun _ a=>(if hitsTarget n ell a false then 0 else f a)-miss*θ)
    twoFieldSecond O O (univ.biUnion Y) (fun a=>w a/smoothMarkProbability O O a)
      (smoothMarkEvent O false) (smoothMarkEvent O true) ≤
      C*(2*(D^2+2*D)*count)^2*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨C,cp,n₁,each⟩ := protected_log_gram_second line K hk
  obtain ⟨b₀,deg⟩ := Fixed.degree_grows 3
  refine ⟨4*C,by positivity,max n₁ (max 2 (2^b₀)),?_⟩
  intro n large ell target comp absent b Cell M L Y O D i k f count θ miss w
  obtain ⟨old,more⟩ := max_le_iff.mp large
  obtain ⟨hn,lim⟩ := max_le_iff.mp more
  have hd := deg b (((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _))
  let roots := wanted (Fixed.d b) ell (Fixed.rootBase n)
  let S := roots.toFinset; let J := Option S
  let co : J→ℝ := Option.elim' 1 (fun _=> -(ell:ℝ)⁻¹)
  let W (q r a : ℕ) := pooledMarkWeight univ Y (fun _ t=>(if t ≡ r [MOD q] then (q:ℝ)*f t else 0)-θ) a
  let v : J→ℕ→ℝ := Option.elim' (W 1 0) (fun r=>W ell r.val)
  let P := smoothMarkProbability O O
  let err := C*(2*(D^2+2*D)*count)^2*exp (-K*(Fixed.z b:ℝ)^2)
  have ep : (0:ℝ)<ell := by exact_mod_cast (mem_dyadicTargets.mp target).1.pos
  have dlt := target_gt_degree target
  have spec := wanted_spec dlt (Fixed.rootBase n)
  have card : Fintype.card S=Fixed.d b := by rw [Fintype.card_coe,List.toFinset_card_of_nodup spec.2.1,spec.1]
  have weight (a : ℕ) : w a/P a=∑ j : J,co j*(v j a/P a) := by
    simp only [J,Fintype.sum_option,co,v,Option.elim'_none,Option.elim'_some,one_mul,←mul_div_assoc,←sum_div,←add_div]
    congr 1
    dsimp only [w,W,pooledMarkWeight]
    simp only [mul_sum]
    rw [sum_comm (s:=univ (α:=S)),←sum_add_distrib]
    apply sum_congr rfl;intro c _
    by_cases ac : a∈Y c
    · simp only [ac,if_true,Nat.modEq_one,Nat.cast_one,one_mul,mul_sub,sum_sub_distrib,sum_const,card_univ,card,nsmul_eq_mul]
      have masks : (∑ r : S,if a ≡ r.val [MOD ell] then f a else 0)=if hitsTarget n ell a false then f a else 0 := by
        rw [sum_coe_sort S (fun r : ℕ=>if a ≡ r [MOD ell] then f a else 0)]
        have same r (hr : r∈S) : (a ≡ r [MOD ell]) ↔ r=a%ell := by
          rw [Nat.ModEq,Nat.mod_eq_of_lt (spec.2.2 r (List.mem_toFinset.mp hr)).1,eq_comm]
        have hit := (target_part_residues hd target a).1
        have h : hitsTarget n ell a false=decide (a%ell∈S) := Bool.eq_iff_iff.mpr (by simpa [S,roots] using hit)
        calc
          _ = ∑ r∈S,if r=a%ell then f a else 0 := sum_congr rfl (fun r hr=>if_congr (same r hr) rfl rfl)
          _ = _ := by simp [h]
      have val (r : S) : -(ell:ℝ)⁻¹*(if a ≡ r.val [MOD ell] then (ell:ℝ)*f a else 0)=
          -(if a ≡ r.val [MOD ell] then f a else 0) := by split_ifs <;> field_simp <;> ring
      simp only [val,sum_neg_distrib,masks]
      dsimp only [miss];split <;> ring
    · simp [ac]
  have cost (j : J) : twoFieldSecond O O (univ.biUnion Y) (fun a=>v j a/P a) (smoothMarkEvent O false) (smoothMarkEvent O true)≤err := by
    cases j with
    | none => exact each n old ell target comp absent i k 1 0 (Or.inl rfl)
    | some r => exact each n old ell target comp absent i k ell r.val (Or.inr rfl)
  have norm : (∑ j : J,|co j|)≤2 := by
    simp only [J,Fintype.sum_option,co,Option.elim'_none,Option.elim'_some,abs_one,abs_neg,abs_inv,abs_of_pos ep,
      sum_const,card_univ,card,nsmul_eq_mul]
    have de : (Fixed.d b:ℝ)≤ell := by exact_mod_cast dlt.le
    linarith only [show (Fixed.d b:ℝ)*(ell:ℝ)⁻¹≤1 by rw [←div_eq_mul_inv];exact (div_le_one ep).mpr de]
  have law := combined_second O O target (univ.biUnion Y) _ _ (fun j a=>v j a/P a) co _ err weight cost
  have small := pow_le_pow_left₀ (sum_nonneg (fun j _=>abs_nonneg (co j))) norm 2
  exact law.trans ((mul_le_mul_of_nonneg_right small (by dsimp only [err];positivity)).trans_eq (by dsimp only [err];ring))

end
end Cogentic.Construction
#print axioms Cogentic.Construction.miss_log_gram_second
