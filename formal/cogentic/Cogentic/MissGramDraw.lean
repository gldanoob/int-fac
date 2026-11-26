import Cogentic.OrdinaryMissCross
import Cogentic.MissGramScores
import Cogentic.RankErrorBudget
import Cogentic.TargetCellPeeling

namespace Cogentic.Construction
open Finset Real Window
open scoped Classical
noncomputable section

private theorem miss_log_cost_mean (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let H := Option (Bool×Fin (Fixed.d b)); let D := 3*(Fixed.h b:ℝ)+1
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∃ μ : ℝ, (∀ t : Ω, 0 ≤ missLogCost n ell t.1.val t.2.val) ∧
      HasSum (fun t : Ω=>twoFieldWeight O O t*missLogCost n ell t.1.val t.2.val) μ ∧
      μ≤(Fintype.card H:ℝ)^2*(C*(2*(D^2+2*D))^2*exp (-K*(Fixed.z b:ℝ)^2)) := by
  obtain ⟨C,cp,n₀,entries⟩ := miss_log_gram_second line K hk
  refine ⟨C,cp,n₀,?_⟩
  intro n large ell target comp absent b H D O Ω
  let X := univ.biUnion (constructorCellMarks n ell)
  let E := smoothMarkEvent O false; let F := smoothMarkEvent O true
  let W := missLogWeight n ell
  let count := rawMeshCount b
  have cpos : 0<count := rawMeshCount_pos b
  have entry (i j : H) : twoFieldSecond O O X (W i j) E F ≤
      C*(2*(D^2+2*D)*count)^2*exp (-K*(Fixed.z b:ℝ)^2) :=
    entries n large ell target comp absent i j
  have mean := (hasSum_sum (s:=univ) (fun i : H=>fun _=>hasSum_sum (s:=univ)
    (fun j : H=>fun _=>twoField_score_second O O target X (W i j) E F))).div_const (count^2)
  refine ⟨(∑ i : H, ∑ j : H, twoFieldSecond O O X (W i j) E F)/count^2,
    fun _=>div_nonneg (sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>sq_nonneg _))) (sq_nonneg _),?_,?_⟩
  · apply mean.congr_fun
    intro t
    simp only [missLogCost,←mul_sum,mul_div_assoc,W,X,E,F,O,count,b]
    rfl
  · apply (div_le_div_of_nonneg_right (sum_le_sum (s:=univ) (fun i _=>sum_le_sum (s:=univ)
        (fun j _=>entry i j))) (sq_nonneg count)).trans_eq
    simp only [sum_const,nsmul_eq_mul,card_univ]
    field_simp

/-- Adding the three Gram blocks on the unrestricted law leaves a budget for
the target and rejected-mark tests. The ordinary diagonal cost occurs within
the mixed block at the intercept coordinate. -/
def missGramCost (n ell : ℕ) (β : ℝ) (x y : ℤ×ℤ) : ℝ :=
  missPairCost n ell β x y + boxedMissCrossCost n ell β x y + missLogCost n ell x y

/-- The combined test costs at most three eighths. On passing, each squared
block error divided by the raw mesh count squared is below the sixth power
of the schedule error. -/
theorem miss_gram_test (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let e := exp (-(Fixed.z b:ℝ)^2)
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∀ β u : ℝ, β∈Set.Icc (0:ℝ) 1 → 0<u → u≤110*(Fixed.d b:ℝ) →
    saddleMean (primeBand b) β=log (Fixed.B b)*u →
    let test := fun t : Ω=>missGramCost n ell β t.1.val t.2.val/e^6
    ∃ μ : ℝ, (∀ t,0≤test t) ∧ HasSum (fun t=>twoFieldWeight O O t*test t) μ ∧ μ≤3/8 ∧
      ∀ t : Ω, test t<1 →
        missPairCost n ell β t.1.val t.2.val<e^6 ∧
        boxedMissCrossCost n ell β t.1.val t.2.val<e^6 ∧ missLogCost n ell t.1.val t.2.val<e^6 := by
  obtain ⟨A,ap,n₁,pairs⟩ := physical_pair_miss_entries_budget line 10 (by norm_num)
  obtain ⟨B,bp,n₂,mixed⟩ := admitted_miss_cross_budget line 10 (by norm_num)
  obtain ⟨C,cp,n₃,logs⟩ := miss_log_cost_mean line 10 (by norm_num)
  obtain ⟨b₁,sa⟩ := rank_prefactor_savings A ap.le (by norm_num : (9:ℝ)<10)
  obtain ⟨b₂,sb⟩ := rank_prefactor_savings B bp.le (by norm_num : (9:ℝ)<10)
  obtain ⟨b₃,sc⟩ := rank_prefactor_savings C cp.le (by norm_num : (9:ℝ)<10)
  refine ⟨max (max n₁ (max n₂ n₃)) (max 2 (2^(max b₁ (max b₂ b₃)))),?_⟩
  intro n lg ell target comp sieve b e O Ω β u hr up ub sd test
  obtain ⟨nn,bit⟩ := max_le_iff.mp lg
  obtain ⟨one,rem⟩ := max_le_iff.mp nn
  obtain ⟨two,three⟩ := max_le_iff.mp rem
  obtain ⟨hn,hb⟩ := max_le_iff.mp bit
  have big : max b₁ (max b₂ b₃)≤b := ((Nat.le_log2 (by omega : n≠0)).mpr hb).trans (Nat.le_succ _)
  obtain ⟨za,zz⟩ := max_le_iff.mp big
  obtain ⟨zb,zc⟩ := max_le_iff.mp zz
  obtain ⟨p,pn,pe,pv⟩ := pairs n one ell target comp sieve β hr u sd
  obtain ⟨m,mn,me,mv⟩ := mixed n two ell target comp sieve β u hr.1 hr.2 sd
  obtain ⟨l,ln,le',lv⟩ := logs n three ell target comp sieve
  let c := rawMeshCount b
  have cg : 0<c := rawMeshCount_pos b
  have e9 : exp (-9*(Fixed.z b:ℝ)^2)=e^9 := by dsimp only [e]; rw [←exp_nat_mul];congr 1;ring
  have p9 : p/c^2≤e^9 := by
    rw [div_le_iff₀ (sq_pos_of_pos cg),←e9]
    apply pv.trans
    have s := (sa b za u up.le ub).1
    change 256*u^2*(A*(3*(Fintype.card (Option (Bool×Fin (Fixed.d b))):ℝ)*(cellMarkCount b:ℝ))^2*
      exp (-10*(Fixed.z b:ℝ)^2))≤_
    calc
      _ = (256*u^2*(A*3^2*exp (-10*(Fixed.z b:ℝ)^2)))*c^2 := by
        dsimp only [c,rawMeshCount]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right s (sq_nonneg c)
  have m9 := mv.trans (sb b zb u up.le ub).2.1
  have l9 := lv.trans (sc b zc u up.le ub).2.2
  rw [e9] at m9 l9
  have eg : 0<e := exp_pos _
  have half : e≤1/2 := by
    have z : 1≤(Fixed.z b:ℝ) := by exact_mod_cast (Nat.le_add_left 1 b.log2)
    rw [show e=1/exp ((Fixed.z b:ℝ)^2) by simp [e,exp_neg,one_div]]
    apply one_div_le_one_div_of_le (by norm_num)
    exact (by linarith [Real.exp_one_gt_d9] : (2:ℝ)≤exp 1).trans (exp_le_exp.mpr (by nlinarith))
  have nonP (t : Ω) : 0 ≤ missPairCost n ell β t.1.val t.2.val := div_nonneg (pn t) (sq_nonneg c)
  let μ := ((p/c^2+m)+l)/e^6
  refine ⟨μ,fun t=>div_nonneg (add_nonneg (add_nonneg (nonP t) (mn t)) (ln t)) (pow_nonneg eg.le _),?_,?_,?_⟩
  · apply ((((pe.div_const (c^2)).add me).add le').div_const (e^6)).congr_fun
    intro t
    dsimp only [test,missGramCost,missPairCost,c,b]
    ring
  · apply (div_le_iff₀ (pow_pos eg _)).mpr
    have e3 := pow_le_pow_left₀ eg.le half 3
    have tiny := mul_le_mul_of_nonneg_right e3 (pow_nonneg eg.le 6)
    norm_num at tiny
    have eSmall : e^9≤(1/8)*e^6 := by
      calc
        e^9 = e^3*e^6 := by ring
        _ ≤ _ := tiny
    linarith only [p9,m9,l9,eSmall]
  · intro t ok
    have total := (div_lt_one (pow_pos eg 6)).mp ok
    change missPairCost n ell β t.1.val t.2.val + boxedMissCrossCost n ell β t.1.val t.2.val +
      missLogCost n ell t.1.val t.2.val < e^6 at total
    exact ⟨by linarith only [total,mn t,ln t],by linarith only [total,nonP t,ln t],
      by linarith only [total,nonP t,mn t]⟩

/-- All three target-miss Gram block tests, the rejected columns, and a
surviving mark in each target class hold on the same boxed draw. -/
theorem simultaneous_miss_gram_draw (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let d := Fixed.d b; let e := exp (-(Fixed.z b:ℝ)^2)
    ∀ β u : ℝ, β∈Set.Icc (0:ℝ) 1 → 0<u → u≤110*(d:ℝ) →
    saddleMean (primeBand b) β=log (Fixed.B b)*u →
    ∀ mix : Option (Bool×Fin d)→ℝ, (∀ c, 0 ≤ mix c) → (∑ c,mix c)=1 →
    ∀ mass scale : Marking.Row→ℝ, (∀ i,i.q.Prime → mass i*scale i^2=1) →
    ∃ x y : ℤ×ℤ, retainedDenominatorGood n ell mix x y ∧ protectedDrawRank n ell x y ∧
      RejectedRowControl n ell mix mass scale x y ∧
      (∑ i∈admittedOrdinaryRows n ell x y,(bandRowPrime i:ℝ)^(-β))<128*u ∧
      missPairCost n ell β x y<e^6 ∧ boxedMissCrossCost n ell β x y<e^6 ∧ missLogCost n ell x y<e^6 ∧
      ∃ rel, Marking.stageOne (TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat))=some rel ∧
        ∀ D⊆admittedOrdinaryRows n ell x y, (∑ i∈D,(bandRowPrime i:ℝ)^(-β))≤e →
          ∀ r∈wanted d ell (Fixed.rootBase n), ∃ a∈rel.marks, a ≡ r [MOD ell] ∧
            ∀ i∈D, ¬a ≡ i.2.2.val [MOD bandRowPrime i] := by
  obtain ⟨n₁,gram⟩ := miss_gram_test line
  obtain ⟨C,H,cp,hp,n₂,protect⟩ := target_peeling_test line
  obtain ⟨n₃,draw⟩ := protected_rank_ordinary_mass_peeling line
  obtain ⟨b₀,gap⟩ := target_peeling_gap C H cp hp
  refine ⟨max (max n₁ (max n₂ n₃)) (max 2 (2^b₀)),?_⟩
  intro n large ell target comp absent b d e β u band up ub sd mix mx norm mass scale unit
  obtain ⟨nn,bb⟩ := max_le_iff.mp large
  obtain ⟨one,rem⟩ := max_le_iff.mp nn
  obtain ⟨two,three⟩ := max_le_iff.mp rem
  obtain ⟨hn,lg⟩ := max_le_iff.mp bb
  have bit : b₀≤b := ((Nat.le_log2 (by omega : n≠0)).mpr lg).trans (Nat.le_succ _)
  let O := PrescribedRows.unrestricted n ell
  let Ω := O.CoeffPoint false × O.CoeffPoint true
  let G := fun t : Ω=>missGramCost n ell β t.1.val t.2.val/e^6
  obtain ⟨μ,gn,gm,gb,passes⟩ := gram n one ell target comp absent β u band up ub sd
  obtain ⟨f,ν,fn,fm,fb,keep⟩ := protect n two ell target comp absent β u band.1 band.2 up.le sd
  have gm' : HasSum (fun t : Ω=>twoFieldWeight O O t*G t) μ := gm
  have both : HasSum (fun t : Ω=>twoFieldWeight O O t*(G t+f t)) (μ+ν) :=
    (gm'.add fm).congr_fun (fun t=>mul_add (twoFieldWeight O O t) (G t) (f t))
  have fit : μ+ν<1/2 := by linarith only [gb,fb]
  obtain ⟨t,den,rank,pass,rows,loss⟩ := draw n three ell target comp absent β u band.1 up sd mix mx norm
    mass scale unit (fun t=>G t+f t) (μ+ν) (fun t=>add_nonneg (gn t) (fn t)) both fit.le
  obtain ⟨a,b',c⟩ := passes t ((le_add_of_nonneg_right (fn t)).trans_lt pass)
  obtain ⟨rel,stage,good⟩ := keep t den.1 den.2.1 ((le_add_of_nonneg_left (gn t)).trans_lt pass)
  exact ⟨t.1.val,t.2.val,den,rank,loss,rows,a,b',c,rel,stage,good e (exp_pos _).le (gap b bit u up.le ub)⟩

end
end Cogentic.Construction
#print axioms Cogentic.Construction.simultaneous_miss_gram_draw
