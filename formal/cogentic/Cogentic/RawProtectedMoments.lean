import Cogentic.RawLogProfiles
import Cogentic.PhysicalProfileVariance

namespace Cogentic.Construction
open Finset Real
open scoped Classical
noncomputable section

/-- The inverse-density-weighted entry in a single protected residue class
has the uniform raw-mesh mean as its center, using the same drawn denominator
over all cells. Taking modulus one gives the intercept and logarithm block. -/
theorem centered_raw_class_second (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let Cell := Option (Bool×Fin (Fixed.d b))
    let M := cellMarkCount b; let L := firstCellMark b
    let Y := constructorCellMarks n ell; let X := univ.biUnion Y
    let O := PrescribedRows.unrestricted n ell
    ∀ (q r : ℕ), 0<q → Squarefree q → q≤(Fixed.B b)^3 → q.Coprime (markModulus n ell) →
    (∀ p∈pairCorrectionPrimes b,p.Coprime q) →
    ∀ (f : Cell→ℕ→ℝ) (D : ℝ), 0≤D →
    (∀ c j,j<M → |f c (L c+j)|≤D) → (∀ c, meshVariation (L c) M (f c)≤D) →
    let count := (Fintype.card Cell:ℝ)*M
    let θ := (∑ c : Cell,∑ j∈range M,f c (L c+j))/count
    let w := pooledMarkWeight univ Y (fun c a=>(if a ≡ r [MOD q] then (q:ℝ)*f c a else 0)-θ)
    twoFieldSecond O O X (fun a=>w a/smoothMarkProbability O O a)
      (smoothMarkEvent O false) (smoothMarkEvent O true) ≤ C*(2*D*count)^2*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨B,bp,n₁,pooled⟩ := pooled_residue_score_second_uniform line K hk
  obtain ⟨C,cp,b₂,save⟩ := profileMomentBound_cancellation K B 0 hk bp.le
  refine ⟨C,cp,max n₁ (max 2 (2^b₂)),?_⟩
  intro n large ell target comp absent b Cell M L Y X O q r qp sf cap clean correction f D dp size var count θ w
  obtain ⟨old,more⟩ := max_le_iff.mp large
  obtain ⟨hn,lim⟩ := max_le_iff.mp more
  have big : b₂≤b := ((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _)
  let nc := (Fintype.card Cell:ℝ)
  have np : 0<nc := Nat.cast_pos.mpr Fintype.card_pos
  have mp : (0:ℝ)<M := by dsimp only [M,cellMarkCount];positivity
  have cnt : 0<count := mul_pos np mp
  have theta : |θ|≤D := by
    rw [abs_div,abs_of_pos cnt,div_le_iff₀ cnt]
    apply (abs_sum_le_sum_abs ..).trans
    have each (c : Cell) := (abs_sum_le_sum_abs (fun j=>f c (L c+j)) (range M)).trans
      (sum_le_sum (s:=range M) (fun j hj=>size c j (mem_range.mp hj)))
    have total := sum_le_sum (s:=univ) (fun c _=>each c)
    simpa only [count,sum_const,nsmul_eq_mul,card_range,card_univ,mul_assoc,mul_comm,mul_left_comm] using total
  let I := Cell×Bool
  let m := fun i : I=>if i.2 then q else 1
  let g := fun (i : I) a=>if i.2 then f i.1 a else -θ
  let Z := fun i : I=>(Y i.1).filter (fun a=>a ≡ r [MOD m i])
  have qr (i : I) : 0 < m i ∧ Squarefree (m i) ∧ m i≤(Fixed.B b)^3 ∧ (m i).Coprime (markModulus n ell) ∧
      ∀ p∈pairCorrectionPrimes b,p.Coprime (m i) := by
    rcases i with ⟨c,h⟩
    cases h
    · simpa only [m,Bool.false_eq_true,if_false] using And.intro (by decide : 0<1) ⟨squarefree_one, one_le_pow₀ (Nat.one_le_two_pow : 1≤Fixed.B b), Nat.coprime_one_left _, fun p _=>Nat.coprime_one_right p⟩
    · simpa [m] using And.intro qp ⟨sf,cap,clean,correction⟩
  have bd (i : I) (a : ℕ) (ha : a∈Y i.1) : |g i a|≤D := by
    have loc := mem_Ico.mp (mem_filter.mp ha).1
    change L i.1≤a ∧ a<L i.1+M at loc
    rcases i with ⟨c,h⟩
    cases h
    · simpa [g] using theta
    · change L c≤a ∧ a<L c+M at loc
      simpa [g,Nat.add_sub_of_le loc.1] using size c (a-L c) (by omega)
  let A := ∑ _i : I,D
  have aeq : A=2*nc*D := by simp only [A,nc,sum_const,nsmul_eq_mul,card_univ,I,Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat];ring
  let δ := ∑ i : I,∑ j∈range M,g i (L i.1+j)
  have zero : δ=0 := by
    simp only [δ,I,Fintype.sum_prod_type,Fintype.sum_bool,g,if_true,Bool.false_eq_true,if_false,sum_const,card_range,
      nsmul_eq_mul,mul_neg,sum_add_distrib,card_univ]
    dsimp only [θ,count];field_simp [show (Fintype.card Cell:ℝ)≠0 from np.ne',mp.ne'] <;> ring
  let V := ∑ i : I,meshVariation (L i.1) M (g i)
  have Vbd : |V|≤A := by
    rw [abs_of_nonneg (show 0≤V from sum_nonneg (fun i _=>add_nonneg (abs_nonneg _) (sum_nonneg (fun _ _=>abs_nonneg _))))]
    apply sum_le_sum; rintro ⟨c,h⟩ _
    cases h
    · simpa [g,meshVariation] using theta
    · simpa only [g,if_true] using var c
  have cover : univ.biUnion Z=X := by
    ext a
    simp only [X,Z,mem_biUnion,mem_univ,true_and,mem_filter]
    constructor
    · rintro ⟨i,ai,_⟩;exact ⟨i.1,ai⟩
    · rintro ⟨c,ac⟩;exact ⟨(c,false),ac,Nat.modEq_one⟩
  have weights : pooledMarkWeight univ Z (fun i a=>(m i:ℝ)*g i a)=w := by
    funext a
    simp only [pooledMarkWeight,I,Fintype.sum_prod_type,Fintype.sum_bool,w]
    apply sum_congr rfl;intro c _
    simp only [Z,mem_filter,m,g,if_true,Bool.false_eq_true,if_false,Nat.modEq_one,and_true,Nat.cast_one,one_mul]
    by_cases inside : a∈Y c <;> by_cases hit : a ≡ r [MOD q] <;> simp [inside,hit] <;> ring
  have law := pooled n old ell target comp absent O O (univ : Finset I) Prod.fst m (fun _=>r) g (fun _=>D)
    (fun i _=>qr i) (fun i _=>⟨dp,bd i⟩)
  change twoFieldSecond O O (univ.biUnion Z)
    (fun a=>pooledMarkWeight univ Z (fun i j=>(m i:ℝ)*g i j) a/smoothMarkProbability O O a) _ _ ≤ profileMomentBound b K B A δ V at law
  rw [cover,weights] at law
  have ap : 0≤A := sum_nonneg (fun _ _=>dp)
  have savings := save b big (Nat.succ_pos n.log2) A A δ V 0 0 ap ((abs_of_nonneg ap).le) Vbd
    (by simpa using ap) (by rw [zero,abs_zero];positivity) (by simp;positivity)
  simp only [zero_mul,zero_pow (by decide : 2≠0),mul_zero,add_zero] at savings
  have twice := mul_le_mul_of_nonneg_left law (by norm_num : (0:ℝ)≤2)
  have product : A*(M:ℝ)=2*D*count := by rw [aeq];dsimp only [nc,count];ring
  rw [product] at savings
  have nonneg : 0≤C*(2*D*count)^2*exp (-K*(Fixed.z b:ℝ)^2) := by positivity
  linarith only [nonneg,twice.trans savings]

/-- The protected Gram uses the same center for each target residue. With
`q = ell` this estimates each target/log entry separately. With `q = 1` it
estimates the full intercept/log block. -/
theorem protected_log_gram_second (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let Cell := Option (Bool×Fin (Fixed.d b))
    let M := cellMarkCount b; let L := firstCellMark b
    let Y := constructorCellMarks n ell; let X := univ.biUnion Y
    let O := PrescribedRows.unrestricted n ell; let D := 3*(Fixed.h b:ℝ)+1
    ∀ (i k : Cell) (q r : ℕ), q=1 ∨ q=ell →
    let f := fun a=>nominalLogFactor b i a*nominalLogFactor b k a
    let count := (Fintype.card Cell:ℝ)*M
    let θ := (∑ c : Cell,∑ j∈range M,f (L c+j))/count
    let w := pooledMarkWeight univ Y (fun _ a=>(if a ≡ r [MOD q] then (q:ℝ)*f a else 0)-θ)
    twoFieldSecond O O X (fun a=>w a/smoothMarkProbability O O a)
      (smoothMarkEvent O false) (smoothMarkEvent O true) ≤
      C*(2*(D^2+2*D)*count)^2*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨C,cp,n₁,core⟩ := centered_raw_class_second line K hk
  obtain ⟨b₀,degree⟩ := Fixed.degree_grows 10004
  refine ⟨C,cp,max n₁ (max 2 (2^b₀)),?_⟩
  intro n large ell target comp absent b Cell M L Y X O D i k q r mode f count θ w
  obtain ⟨old,more⟩ := max_le_iff.mp large
  obtain ⟨hn,lim⟩ := max_le_iff.mp more
  have hd := degree b (((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _))
  have valid : 0<q ∧ Squarefree q ∧ q≤(Fixed.B b)^3 ∧ q.Coprime (markModulus n ell) ∧
      ∀ p∈pairCorrectionPrimes b,p.Coprime q := by
    rcases mode with unit|hit
    · subst q
      exact ⟨by decide,squarefree_one,one_le_pow₀ Nat.one_le_two_pow,Nat.coprime_one_left _,
        fun _ _=>Nat.coprime_one_right _⟩
    · subst q
      have eb := dyadic_target_in_primeBand (Nat.succ_pos n.log2) target
      obtain ⟨prime,cap,_⟩ := mem_primeBand.mp eb
      have cap₃ : ell≤(Fixed.B b)^3 := calc
        ell ≤ Fixed.B b := cap
        _ = (Fixed.B b)^1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (Nat.pow_pos (by decide)) (by decide)
      exact ⟨prime.pos,prime.squarefree,cap₃,
        (Nat.coprime_mul_iff_right.mp (markModulus_spec hn hd comp target absent).2.2.1).2.symm,
        fun p hp=>correction_coprime_band hp eb⟩
  have bounds (c : Cell) := raw_log_entry_regular hn hd c i k
  exact core n old ell target comp absent q r valid.1 valid.2.1 valid.2.2.1 valid.2.2.2.1 valid.2.2.2.2
    (fun _=>f) (D^2+2*D) (by dsimp only [D];positivity) (fun c=>(bounds c).1) (fun c=>(bounds c).2)

end
end Cogentic.Construction
#print axioms Cogentic.Construction.centered_raw_class_second

#print axioms Cogentic.Construction.protected_log_gram_second
