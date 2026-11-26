import Cogentic.PhysicalMeshScore
import Cogentic.RankErrorBudget
import Cogentic.RetainedBoxRank
import Cogentic.RawGramTransfer
import Cogentic.OrdinaryMass
import Cogentic.MissOverlapBounds
import Cogentic.ConstructorPriorDensity
import Cogentic.SmoothOverlapPeeling

namespace Cogentic.Construction
open Finset Real Marking Window
open scoped Classical
noncomputable section

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
/-- On the smooth misses, remove the bad rows from stage one and then peel
unstable rows. The same small mass budget controls the lost column energy. -/
theorem miss_draw_peeling (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ x y : ℤ×ℤ, retainedDenominatorGood n ell (meshMix n ell) x y →
    let b := n.log2+1; let e := exp (-(Fixed.z b:ℝ)^2)
    let s := TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat)
    ∀ {rel}, stageOne s=some rel → ∀ (A₀ : Finset Row), A₀⊆rel.rows.toFinset →
    (∀ i∈A₀,i.q∈primeBand b ∧ i.q≠ell) →
    ∀ (α : GridPosition b→Bool→ℝ) (β : ℝ), 0≤β → (∀ j k,199/200≤α j k) →
    InMarkSaddleRange n (saddleMean (primeBand b) β) →
    (∀ j k,InMarkSaddleRange n (saddleMean (primeBand b) (α j k))) →
    let μ := fun i : Row=>(i.q:ℝ)^(-β)
    let scale := fun i : Row=>(sqrt (μ i))⁻¹
    RejectedRowControl n ell (meshMix n ell) μ scale x y →
    let S := smoothMesh n ell x y
    let X := S.filter (fun a=>hitsTarget n ell a false=false)
    let Q := ∑ a∈S,meshWeight n ell a
    let weight := fun a=>meshWeight n ell a/Q
    let p := fun i : A₀=>i.val.q; let side := fun i : A₀=>i.val.second
    let w := fun i : A₀=>sqrt (μ i.val)
    let I := fun j k (q : ℕ)=>fullBandInsertion b q (α j k)/((q:ℝ)*(q:ℝ)^(-β))
    let m := fun j i=>w i*I j (side i) (p i); let R := fun j=>ordinaryRawEntry p side w (I j)
    let Z := retainedMissColumn s A₀ (fun i=>scale i.val) (fun k i=>(center s.degree k i.val:ℝ))
    let err := fun i j=>missGridGram (1-(Fixed.d b:ℝ)/ell) m R i j-∑ a∈X,weight a*Z a i*Z a j
    (∑ i : A₀,μ i.val*(err (.inr i) (.inr i))^2)≤256*e^6 →
    (∑ i,∑ j,(if i=j then 0 else err i j)^2)≤1024*e^6 →
    ∃ D : Finset A₀, (∑ i∈D,μ i.val)≤e ∧
      (∀ i∉D, |err (.inr i) (.inr i)|<e^2) ∧
      let A := A₀ \ D.image Subtype.val
      let Y := X.filter (fun a=>a∈rel.marks ∧ ∀ i∈D,a%i.val.q≠i.val.r)
      let Z' := retainedMissColumn s A (fun i=>scale i.val) (fun k i=>(center s.degree k i.val:ℝ))
      (∀ a,0≤weight a) ∧ (∑ a∈Y,weight a)≤1 ∧
      ∀ (v : Option (Fin (2*s.degree)) ⊕ A → ℝ), (∑ a∈X\Y,weight a*(∑ i,Z' a i*v i)^2)≤
        exp (-(1/4)*(Fixed.z b:ℝ)^2)*(∑ i,(v i)^2) := by
  classical
  obtain ⟨nb,norm⟩ := normalized_mesh_score line
  obtain ⟨b₁,model⟩ := miss_grid_ordinary_upper
  obtain ⟨b₂,deg⟩ := Fixed.degree_grows 130000
  obtain ⟨b₃,tiny⟩ := rank_polynomial_savings 1024 1 (by norm_num : (0:ℝ)<1)
  obtain ⟨b₄,saving⟩ := rank_polynomial_savings 1077 4 (by norm_num : (1/4:ℝ)<1)
  let B := max (max b₁ b₂) (max b₃ b₄)
  refine ⟨max nb (max 2 (2^B)),?_⟩
  intro n nn ell target nc absent x y good b e s rel stage A₀ listed band α β bp ap mb ma μ scale rejection S X Q weight p side w I m R Z err diag off
  obtain ⟨ng,hn,nbound⟩ := max_le_iff.mp nn |>.imp_right max_le_iff.mp
  have bg : B≤b := ((Nat.le_log2 (by omega : n≠0)).mpr nbound).trans (Nat.le_succ _)
  obtain ⟨⟨bm,bd⟩,⟨bt,bs⟩⟩ := (max_le_iff.mp bg).imp max_le_iff.mp max_le_iff.mp
  have hd := deg b bd
  have hd' : 10004≤Fixed.d b := by omega
  have bpos : (1:ℝ)≤b := by dsimp only [b]; exact_mod_cast Nat.succ_pos n.log2
  have ep : 0<e := exp_pos _
  have small : 1024*(b:ℝ)*e≤1 := by
    have h := tiny b bt
    rw [show exp (-1*(Fixed.z b:ℝ)^2)=e by simp only [e,neg_mul,one_mul]] at h
    simpa only [pow_one,zero_mul,neg_zero,exp_zero] using h
  have se : 1024*e≤1 := (by nlinarith only [mul_nonneg (show 0≤(b:ℝ)-1 by linarith only [bpos]) ep.le] : 1024*e≤1024*(b:ℝ)*e).trans small
  have e1 : e≤1 := by linarith only [se]
  obtain ⟨ql,_,wn,wsum,_⟩ := norm n ng ell target nc absent x y good
  change 1/2≤Q at ql
  have qp : 0<Q := by linarith only [ql]
  have dp : Fixed.d b≤ell := by
    have pow : Fixed.d b≤2^(Fixed.beta b-1) := by
      have dh : Fixed.d b≤Fixed.h b := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      have db : Fixed.d b≤Fixed.beta b-1 := by change _≤1000*Fixed.h b-1; omega
      exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) db)
    exact pow.trans (mem_dyadicTargets.mp target).2.1.le
  have missPos : 0≤1-(Fixed.d b:ℝ)/ell :=
    sub_nonneg.mpr ((div_le_one (Nat.cast_pos.mpr (mem_dyadicTargets.mp target).1.pos)).mpr (by exact_mod_cast dp))
  have missLe : 1-(Fixed.d b:ℝ)/ell≤1 := sub_le_self _ (by positivity)
  obtain ⟨single₀,pair₀⟩ := model bm α β _ bp missPos missLe ap mb ma p side (fun i=>(band _ i.prop).1)
  have single (i : A₀) : missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inr i) (.inr i)≤8 :=
    (single₀ i).trans (by norm_num)
  have pair (i j : A₀) (ne : i≠j) : missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inr i) (.inr j)≤8*w i*w j :=
    (pair₀ i j ne).trans (by
      have := mul_nonneg (sqrt_nonneg (μ i.val)) (sqrt_nonneg (μ j.val))
      change 0≤w i*w j at this
      nlinarith only [this])
  have mp (i : A₀) : 0<μ i.val := rpow_pos_of_pos
    (Nat.cast_pos.mpr (mem_primeBand.mp (band _ i.prop).1).1.pos) _
  have wp (i : A₀) : 0<w i := sqrt_pos.mpr (mp i)
  have w2 (i : A₀) : (w i)^2=μ i.val := sq_sqrt (mp i).le
  have listed' (i : A₀) : i.val∈s.rows := by
    have clean : i.val∈s.clean := (rows_and_guards stage).2.2.2.1 ▸ List.mem_toFinset.mp (listed i.prop)
    exact (mem_clean.mp clean).1
  let O := PrescribedRows.unrestricted n ell
  let rejected := (univ.biUnion (constructorCellMarks n ell)).filter (fun a=>rejectedSmoothMark O O a x y)
  let z := fun i : Row=>fun a : ℕ=>if a%i.q=i.r then scale i else 0
  let rawRows := s.rows.toFinset.filter (fun i=>i.q≠ell)
  let bad := rawRows.filter (fun i=>e≤∑ a∈rejected,meshWeight n ell a*(z i a)^2)
  let initial := (univ : Finset A₀).filter (fun i=>i.val∈bad)
  have rejMass : (∑ a∈rejected,meshWeight n ell a)<e^3 := rejection.1
  have badMass : (∑ i∈bad,μ i)≤b*e^2 := rejection.2.1
  have initSum : (∑ i∈initial,μ i.val)≤e/4 := by
    have img : initial.image Subtype.val⊆bad := by
      rintro i hi
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      exact (mem_filter.mp hj).2
    rw [←sum_image (f:=μ) Subtype.val_injective.injOn]
    apply (sum_le_sum_of_subset_of_nonneg img (fun r _ _=>rpow_nonneg (Nat.cast_nonneg _) _)).trans (badMass.trans ?_)
    have t := mul_le_mul_of_nonneg_right small ep.le
    nlinarith only [t,ep]
  let dj := fun i : A₀=>err (.inr i) (.inr i)
  let E := fun i j : A₀=>if i=j then 0 else err (.inr i) (.inr j)
  have diagSmall : (∑ i : A₀,μ i.val*(dj i)^2)≤(e^2)^2*(e/4) := by
    refine diag.trans ?_
    have t := mul_le_mul_of_nonneg_right se (pow_nonneg ep.le 5)
    nlinarith only [t]
  have offOrd : (∑ i,∑ j,(E i j)^2)≤1024*e^6 := by
    apply le_trans _ off
    simp only [Fintype.sum_sum_type, Sum.inr.injEq, E]
    refine le_trans ?_ (le_add_of_nonneg_left ?_)
    · apply sum_le_sum
      intro i _
      exact le_add_of_nonneg_left (sum_nonneg (fun _ _=>sq_nonneg _))
    · exact sum_nonneg (fun _ _=>add_nonneg (sum_nonneg (fun _ _=>sq_nonneg _)) (sum_nonneg (fun _ _=>sq_nonneg _)))
  have offSmall : 8*(∑ i,∑ j,(E i j)^2)≤(e^2)^2 := by
    have t := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ep.le (show e≤1/1024 by linarith only [se]) 2) (pow_nonneg ep.le 4)
    have h := mul_le_mul_of_nonneg_left offOrd (by norm_num : (0:ℝ)≤8)
    change 8*(∑ i,∑ j,(E i j)^2)≤_ at h
    have nn := pow_nonneg ep.le 4
    nlinarith only [h,t,nn]
  have rawEntry (i j : A₀) :
      (∑ a∈X,weight a*Z a (.inr i)*Z a (.inr j)) =
      (∑ a∈X with a%i.val.q=i.val.r ∧ a%j.val.q=j.val.r,weight a)/(w i*w j) := by
    rw [sum_div, sum_filter (s:=X) (p:=fun a=>a%i.val.q=i.val.r ∧ a%j.val.q=j.val.r)]
    apply sum_congr rfl; intro a _
    change weight a*z i.val a*z j.val a=_
    by_cases hi : a%i.val.q=i.val.r <;> by_cases hj : a%j.val.q=j.val.r
    · simp only [hi,hj,true_and,if_true,z,scale,w,div_eq_mul_inv,mul_inv_rev]
      ring
    all_goals simp [hi,hj,z]
  have empUpper (i j : A₀) :
      (∑ a∈X with a%i.val.q=i.val.r ∧ a%j.val.q=j.val.r,weight a) ≤
        (w i*w j)*(missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inr i) (.inr j)+|err (.inr i) (.inr j)|) := by
    let M := missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inr i) (.inr j)
    have t : -(M-∑ a∈X,weight a*Z a (.inr i)*Z a (.inr j))≤|err (.inr i) (.inr j)| :=
      neg_le_abs _
    rw [rawEntry] at t
    change _≤(w i*w j)*(M+|err (.inr i) (.inr j)|)
    exact (div_le_iff₀ (mul_pos (wp i) (wp j))).mp (by linarith only [t]) |>.trans_eq (mul_comm ..)
  obtain ⟨D,istart,Dmass,Hmass,stable⟩ :=
    ordinary_miss_peeling (fun i : A₀=>i.val) X weight (fun a _=>wn a)
      initial (fun i=>μ i.val) dj E e (e^2) (e^2) 8 ep (sq_pos_of_pos ep) (sq_pos_of_pos ep) (by norm_num)
      mp initSum diagSmall offSmall (by
        intro i
        have t := empUpper i i
        simp only [and_self,←sq,w2] at t
        exact t.trans (mul_le_mul_of_nonneg_left (add_le_add_left (single i) _) (mp i).le)) (by
        intro i _ j ne
        apply (empUpper i j).trans
        have t := mul_le_mul_of_nonneg_left (add_le_add_left (pair i j ne) |err (.inr i) (.inr j)|)
          (mul_nonneg (wp i).le (wp j).le)
        simp only [E,if_neg ne]
        refine t.trans_eq ?_
        calc _ = 8*(w i)^2*(w j)^2+w i*(w j*|err (.inr i) (.inr j)|) := by ring
             _ = _ := by rw [w2,w2])
  refine ⟨D,Dmass,fun i h=>(stable i h).1,?_⟩
  let A := A₀ \ D.image Subtype.val
  let Y := X.filter (fun a=>a∈rel.marks ∧ ∀ i∈D,a%i.val.q≠i.val.r)
  let Z' := retainedMissColumn s A (fun i=>scale i.val) (fun k i=>(center s.degree k i.val:ℝ))
  change (∀ a,0≤weight a) ∧ (∑ a∈Y,weight a)≤1 ∧
      ∀ (v : Option (Fin (2*s.degree)) ⊕ A → ℝ), (∑ a∈X\Y,weight a*(∑ i,Z' a i*v i)^2)≤_*(∑ i,(v i)^2)
  refine ⟨wn,(sum_le_sum_of_subset_of_nonneg ((filter_subset _ X).trans (filter_subset _ S)) (fun a _ _=>wn a)).trans_eq wsum,?_⟩
  intro v
  let H := Option (Fin (2*s.degree))
  let g := fun a=>∑ i : H,Z' a (.inl i)*v (.inl i)
  let F := ∑ i,(v i)^2
  let G := fun i : Row=>if hi : i∈A then v (.inr ⟨i,hi⟩) else 0
  let U := (Fintype.card H:ℝ)*(3*(Fixed.h b:ℝ)+1)^2
  have support (a : ℕ) (ha : a∈X) : (A.filter (fun i=>a%i.q=i.r)).card≤b := by
    obtain ⟨base,sm₀,sm₁⟩ := mem_filter.mp (mem_filter.mp ha).1
    obtain ⟨_,_,hm⟩ := mem_biUnion.mp base
    have mark := (mem_filter.mp hm).2
    have l := boxed_smooth_factor_bound O false hn hd nc target absent mark ⟨x,by simp [O,PrescribedRows.unrestricted,PrescribedRows.compatible]⟩ good.1 sm₀
    have r := boxed_smooth_factor_bound O true hn hd nc target absent mark ⟨y,by simp [O,PrescribedRows.unrestricted,PrescribedRows.compatible]⟩ good.2.1 sm₁
    change value s.first a≠0 ∧ 4*(value s.first a).primeFactors.card≤b at l
    change value s.second a≠0 ∧ 4*(value s.second a).primeFactors.card≤b at r
    refine (hit_rows_count s A (fun i hi=>List.mem_toFinset.mpr (listed' ⟨i,(mem_sdiff.mp hi).1⟩)) a ?_).trans ?_
    · intro k;cases k <;> first | exact l.1 | exact r.1
    · omega
  have logBound (a : ℕ) (ha : a∈X) (i : H) : |Z' a (.inl i)|≤3*(Fixed.h b:ℝ)+1 := by
    cases i with
    | none => change |(1:ℝ)|≤_; rw [abs_one]; exact le_add_of_nonneg_left (by positivity)
    | some j =>
      obtain ⟨base,_⟩ := mem_filter.mp (mem_filter.mp ha).1
      obtain ⟨c,_,hc⟩ := mem_biUnion.mp base
      have range := mem_Ico.mp (mem_filter.mp hc).1
      change firstCellMark b c≤a ∧ a<firstCellMark b c + cellMarkCount b at range
      have eqa : firstCellMark b c+(a-firstCellMark b c)=a := Nat.add_sub_of_le range.1
      have jm : a-firstCellMark b c<cellMarkCount b := by omega
      have h := ((raw_log_profile_bounds hn hd' c).1 (gridPlace j).1 (gridPlace j).2).1 _ jm
      rw [eqa] at h
      exact h.trans (le_add_of_nonneg_right zero_le_one)
  have fPos : 0≤F := sum_nonneg (fun _ _=>sq_nonneg _)
  have headEnergy : (∑ i : H,(v (.inl i))^2)≤F := by
    simp only [F,Fintype.sum_sum_type]; exact le_add_of_nonneg_right (sum_nonneg (fun _ _=>sq_nonneg _))
  have rowEnergy : (∑ i∈A,(G i)^2)≤F := by
    rw [←sum_coe_sort A (fun i=>(G i)^2)]
    simp only [G,dif_pos (Subtype.property _),F,Fintype.sum_sum_type]
    exact le_add_of_nonneg_left (sum_nonneg (fun _ _=>sq_nonneg _))
  have gBound (a : ℕ) (ha : a∈X) : (g a)^2≤U*F := by
    apply (sum_mul_sq_le_sq_mul_sq univ (fun i : H=>Z' a (.inl i)) (fun i=>v (.inl i))).trans
    apply mul_le_mul _ headEnergy (sum_nonneg (fun _ _=>sq_nonneg _)) (by dsimp only [U];positivity)
    calc
      (∑ i : H,(Z' a (.inl i))^2) ≤ ∑ _ : H,(3*(Fixed.h b:ℝ)+1)^2 := by
        apply sum_le_sum
        intro i _
        exact sq_le_sq.mpr (by
          rw [abs_of_nonneg (by positivity : 0≤3*(Fixed.h b:ℝ)+1)]
          exact logBound a ha i)
      _ = U := by simp only [U,sum_const,card_univ,nsmul_eq_mul]
  let B' := D.image Subtype.val
  let Hr := X.filter (fun a=>∃ j∈B',a%j.q=j.r)
  let Rx := X.filter (fun a=>a∉rel.marks)
  have hitEq (a : ℕ) : (∃ j∈B',a%j.q=j.r) ↔ ∃ j∈D,a%j.val.q=j.val.r := by
    constructor
    · rintro ⟨j,hj,hit⟩; obtain ⟨i,im,rfl⟩ := mem_image.mp hj; exact ⟨i,im,hit⟩
    · rintro ⟨j,hj,hit⟩; exact ⟨j.val,mem_image.mpr ⟨j,hj,rfl⟩,hit⟩
  have rejSub : Rx⊆rejected := by
    intro a ha
    obtain ⟨hx,no⟩ := mem_filter.mp ha
    obtain ⟨base,l,r⟩ := mem_filter.mp (mem_filter.mp hx).1
    exact mem_filter.mpr ⟨base,l,r,good.1,good.2.1,by
      rintro ⟨rel',eq,hm⟩
      have same := Option.some.inj (eq.symm.trans stage)
      exact no (same ▸ hm)⟩
  have worth (a : ℕ) : 0 ≤ meshWeight n ell a := by
    have h : 0 ≤ meshWeight n ell a / Q := wn a
    simpa only [zero_mul] using (le_div_iff₀ qp).mp h
  have rejectedMass : (∑ a∈Rx,weight a)≤2*e^3 := by
    simp only [weight,←sum_div]
    refine (div_le_iff₀ qp).mpr ?_
    have h := (sum_le_sum_of_subset_of_nonneg rejSub (fun a _ _=>worth a)).trans rejMass.le
    linarith only [h,mul_le_mul_of_nonneg_right ql (show 0≤2*e^3 by positivity)]
  have peeledMass : (∑ a∈Hr,weight a)≤(8+e^2)*e := by
    simpa only [Hr,hitEq] using Hmass
  have diagonal (i : Row) (hi : i∈A) :
      (∑ a∈Rx,weight a*(z i a)^2)≤2*e ∧ (∑ a∈Hr,weight a*(z i a)^2)≤8*e+e^2/2 := by
    let t : A₀ := ⟨i,(mem_sdiff.mp hi).1⟩
    have keep : t∉D := fun hd=> (mem_sdiff.mp hi).2 (mem_image.mpr ⟨t,hd,rfl⟩)
    have notBad : i∉bad := fun hm=>keep (istart (mem_filter.mpr ⟨mem_univ _,hm⟩))
    have rawRow : i∈rawRows := mem_filter.mpr ⟨List.mem_toFinset.mpr (listed' t),(band i t.prop).2⟩
    have smallLoss : (∑ a∈rejected,meshWeight n ell a*(z i a)^2)≤e :=
      le_of_not_ge fun h=>notBad (mem_filter.mpr ⟨rawRow,h⟩)
    constructor
    · have eq : (∑ a∈Rx,weight a*(z i a)^2)=(∑ a∈Rx,meshWeight n ell a*(z i a)^2)/Q := by
        rw [sum_div]
        apply sum_congr rfl;intro a _;dsimp only [weight];ring
      rw [eq]
      apply (div_le_iff₀ qp).mpr
      have h := (sum_le_sum_of_subset_of_nonneg rejSub (fun a _ _=>mul_nonneg (worth a) (sq_nonneg _))).trans smallLoss
      linarith only [h,mul_le_mul_of_nonneg_right ql (show 0≤2*e by positivity)]
    · have eq : (∑ a∈Hr,weight a*(z i a)^2) =
          (∑ a∈X with a%i.q=i.r ∧ ∃ j∈D,a%j.val.q=j.val.r,weight a)/(w t)^2 := by
        rw [sum_div]
        simp only [Hr,sum_filter,hitEq,z]
        apply sum_congr rfl
        intro a _
        by_cases hit : a%i.q=i.r <;> by_cases hd : ∃ j∈D,a%j.val.q=j.val.r
        · simp only [hit,hd,if_true,and_self,scale,w,div_eq_mul_inv,inv_pow,t]
        all_goals simp [hit,hd]
      rw [eq,div_le_iff₀ (sq_pos_of_pos (wp t)),w2]
      exact (stable t keep).2
  have JY : X.filter (fun a=>a∈rel.marks ∧ ¬∃ j∈B',a%j.q=j.r)=Y := by
    ext a; simp only [Y,mem_filter,hitEq,not_exists,not_and]
  have score (a : ℕ) : g a+∑ i∈A,z i a*G i=∑ i,Z' a i*v i := by
    rw [Fintype.sum_sum_type,←sum_coe_sort A (fun i=>z i a*G i)]
    congr 1
    apply sum_congr rfl
    intro i _
    simp only [Z',retainedMissColumn,G,dif_pos i.property,z]
  have transfer := (retained_projected_energy s X rel stage A B' weight scale b (2*e) (8*e+e^2/2)
    (2*e^3) ((8+e^2)*e) (fun a _=>wn a) support rejectedMass peeledMass diagonal G g (U*F)
    (mul_nonneg (by dsimp only [U];positivity) fPos) gBound).1
  simp only [JY] at transfer
  change (∑ a∈X,weight a*(g a+∑ i∈A,z i a*G i)^2)≤
    (∑ a∈Y,weight a*(g a+∑ i∈A,z i a*G i)^2)+_ at transfer
  simp_rw [score] at transfer
  let energy := fun a=>weight a*(∑ i,Z' a i*v i)^2
  have add : (∑ a∈X\Y,energy a)+(∑ a∈Y,energy a)=(∑ a∈X,energy a) :=
    sum_sdiff (f:=energy) (filter_subset _ X)
  change (∑ a∈X,energy a)≤(∑ a∈Y,energy a)+_ at transfer
  change (∑ a∈X\Y,energy a)≤_*F
  have budget : 2*(2*e^3+(8+e^2)*e)*(U*F)+2*(b:ℝ)*(2*e+(8*e+e^2/2))*(∑ i∈A,(G i)^2) ≤
      exp (-(1/4)*(Fixed.z b:ℝ)^2)*F := by
    have bp' : 0≤(b:ℝ) := Nat.cast_nonneg _
    have dh : (Fixed.h b:ℝ)≤b := by
      have dpos : 1≤Fixed.d b := by omega
      have lower : Fixed.d b≤(Fixed.d b)^3 := by simpa only [pow_one] using (Nat.pow_le_pow_right dpos (by decide : 1≤3))
      exact_mod_cast (Nat.mul_le_mul_right (Fixed.z b) lower).trans (Fixed.degree_floor b).1
    have card : (Fintype.card H:ℝ)≤3*(b:ℝ) := by
      simp only [H,Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
      have h : (Fixed.d b:ℝ)≤b := by exact_mod_cast Fixed.degree_le_bits b
      change 2*(Fixed.d b:ℝ)+1≤3*(b:ℝ)
      linarith only [h,bpos]
    have size : U≤48*(b:ℝ)^3 := by
      have t : 3*(Fixed.h b:ℝ)+1≤4*(b:ℝ) := by linarith only [dh,bpos]
      have h := mul_le_mul card (pow_le_pow_left₀ (by positivity) t 2) (sq_nonneg _) (by positivity : 0≤3*(b:ℝ))
      exact h.trans_eq (by ring)
    have es : e^2≤e := by nlinarith only [mul_le_mul_of_nonneg_right e1 ep.le]
    have ec : e^3≤e := by nlinarith only [mul_le_mul_of_nonneg_right es ep.le,es]
    have massBound : 2*(2*e^3+(8+e^2)*e)≤22*e := by nlinarith only [ec]
    have rowBound : 2*(b:ℝ)*(2*e+(8*e+e^2/2))≤21*(b:ℝ)*e := by
      nlinarith only [mul_le_mul_of_nonneg_left es bp']
    have head := mul_le_mul massBound (mul_le_mul_of_nonneg_right size fPos)
      (mul_nonneg (by dsimp only [U];positivity) fPos) (by positivity : 0≤22*e)
    have tail := mul_le_mul rowBound rowEnergy (sum_nonneg (fun _ _=>sq_nonneg _)) (by positivity : 0≤21*(b:ℝ)*e)
    have b4 : (b:ℝ)^3≤(b:ℝ)^4 := pow_le_pow_right₀ bpos (by decide)
    have b1 : (b:ℝ)≤(b:ℝ)^4 := by simpa only [pow_one] using pow_le_pow_right₀ bpos (by decide : 1≤4)
    have main : 22*e*(48*(b:ℝ)^3*F)+21*(b:ℝ)*e*F≤1077*(b:ℝ)^4*e*F := by
      nlinarith only [mul_le_mul_of_nonneg_right b4 (show 0≤e*F by positivity),
        mul_le_mul_of_nonneg_right b1 (show 0≤e*F by positivity)]
    have last := saving b bs
    rw [show exp (-1*(Fixed.z b:ℝ)^2)=e by simp only [e,neg_mul,one_mul]] at last
    have final := mul_le_mul_of_nonneg_right last fPos
    linarith only [head,tail,main,final]
  linarith only [transfer,add,budget]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.miss_draw_peeling
