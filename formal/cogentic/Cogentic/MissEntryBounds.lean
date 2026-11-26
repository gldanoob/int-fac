import Cogentic.MissGramScores
import Cogentic.OrdinaryMissCross
import Cogentic.ExecutableOrdinaryRows
import Cogentic.PhysicalMeshScore
import Cogentic.RetainedBoxRank

namespace Cogentic.Construction
open Finset Real Marking Window
open scoped Classical
noncomputable section

private theorem clean_same_prime {s : Input} {i j : Row} (hi : i∈s.clean) (hj : j∈s.clean)
    (pq : i.q=j.q) (rr : i.r=j.r) : i=j := by
  have ii := (mem_clean.mp hi).2.2
  have jj := (mem_rows.mp (mem_clean.mp hj).1).2.2
  by_cases h : i.second=j.second
  · cases i; cases j; simp_all
  · have opp : (!i.second)=j.second := by cases ei : i.second <;> cases ej : j.second <;> simp_all
    rw [opp,pq,rr] at ii
    exact (ii jj).elim

private theorem budget {p c e F cost : ℝ} (cp : 0<c) (den : c/16≤p)
    (Fn : 0≤F) (pay : p^2*F≤cost*c^2) (small : cost<e^6) :
    F≤256*e^6 := by
  have hp : 0≤p := by linarith
  have sq : c^2≤256*p^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr den) (show 0≤p+c/16 by positivity)]
  have sqF := mul_le_mul_of_nonneg_right sq Fn
  have cost' := mul_lt_mul_of_pos_right small (sq_pos_of_pos cp)
  apply le_of_lt
  by_contra! h
  have := mul_le_mul_of_nonneg_right h (sq_nonneg c)
  nlinarith only [sqF,pay,cost',this]

set_option maxHeartbeats 1200000 in
/-- Convert the boxed miss scores to normalized Gram errors on any subset of
clean ordinary rows. Repeated primes contribute only on the diagonal. -/
theorem miss_entry_bounds (line : DirichletLZerosOnLine) :
    ∃ n₀ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    n₀≤n → b₀≤b → 2≤n → 3≤Fixed.d b → ell∈dyadicTargets (Fixed.beta b) → ¬n.Prime →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (x y : ℤ×ℤ), inCoefficientBox n x → inCoefficientBox n y →
    retainedDenominatorGood n ell (meshMix n ell) x y →
    let input := TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat)
    ∀ {rel}, stageOne input=some rel → ∀ (A : Finset Row), A⊆rel.rows.toFinset →
    (∀ i∈A,i.q≠ell) → ∀ β : ℝ,
    let e := exp (-(Fixed.z b:ℝ)^2)
    missPairCost n ell β x y<e^6 → boxedMissCrossCost n ell β x y<e^6 → missLogCost n ell x y<e^6 →
    let S := smoothMesh n ell x y
    let X := S.filter (fun a=>hitsTarget n ell a false=false)
    let weight := fun a=>meshWeight n ell a/(∑ k∈S,meshWeight n ell k)
    let α := fun (z : GridPosition b)=>branchMeshSaddle n ell (firstCellMark b (z.1.map gridPlace)+z.2.val) false
    let p := fun i : A=>i.val.q; let side := fun i : A=>i.val.second
    let μ := fun i : A=>(p i:ℝ)^(-β); let w := fun i=>sqrt (μ i)
    let I := fun j k (q : ℕ)=>fullBandInsertion b q (α j k)/((q:ℝ)*(q:ℝ)^(-β))
    let m := fun j i=>w i*I j (side i) (p i); let R := fun j=>ordinaryRawEntry p side w (I j)
    let Z : ℕ→Option (Fin (2*Fixed.d b)) ⊕ ↥A→ℝ := retainedMissColumn input A (fun i=>(w i)⁻¹) (fun k i=>(center input.degree k i.val:ℝ))
    let err := fun i j=>missGridGram (1-(Fixed.d b:ℝ)/ell) m R i j-∑ a∈X,weight a*Z a i*Z a j
    (∑ i : A,μ i*(err (.inr i) (.inr i))^2)≤256*e^6 ∧
    (∑ i,∑ j,(err (.inl i) (.inl j))^2)≤256*e^6 ∧
    (∑ i,∑ j,(if i=j then 0 else err i j)^2)≤1024*e^6 := by
  obtain ⟨n₀,normalize⟩ := normalized_mesh_score line
  obtain ⟨b₀,reference⟩ := pair_miss_center_grid line
  refine ⟨n₀,b₀,?_⟩
  intro n ell b nn bb hn hd target comp sieve x y bx by' good input rel stage A listed ordinary β e pairSmall crossSmall logSmall S X weight α p side μ w I m R Z err
  have clean (i : A) : i.val∈input.clean := (rows_and_guards stage).2.2.2.1 ▸ List.mem_toFinset.mp (listed i.prop)
  let rows := executable_ordinary_rows hn hd comp target sieve x y bx by' A
    (fun i hi=>List.mem_toFinset.mpr (mem_clean.mp (clean ⟨i,hi⟩)).1) ordinary
  let O := PrescribedRows.unrestricted n ell
  let G := univ.biUnion (constructorCellMarks n ell)
  let T := (∑ c,((constructorCellMarks n ell c).card:ℝ))*(∑ a∈S,meshWeight n ell a)
  let c := rawMeshCount b
  let score := fun f=>twoFieldScore G f (smoothMarkEvent O false) (smoothMarkEvent O true) x y
  let avg := fun (f : ℕ→ℝ)=>∑ a∈S,weight a*f a
  obtain ⟨_,lower,_,_,norm⟩ := normalize n nn ell target comp sieve x y good
  have den : c/16≤T := by
    convert lower using 2
    simp [c,b,rawMeshCount,Fintype.card_prod,mul_comm]
  have cp : 0<c := rawMeshCount_pos b
  have wp (i : A) : 0<w i := by
    apply sqrt_pos.mpr (rpow_pos_of_pos ?_ _)
    change (0:ℝ)<(i.val.q:ℝ)
    rw [←rows.prime i]
    exact Nat.cast_pos.mpr (mem_primeBand.mp (rows.row i).val.2.1.prop).1.pos
  have ms (i : A) : μ i=(w i)^2 := (sq_sqrt (rpow_nonneg (Nat.cast_nonneg _) _)).symm
  have rowR (i : A) : (rows.row i).val.2.2.val=i.val.r := congrArg Row.r (rows.row_eq i)
  have rowS (i : A) : (rows.row i).val.1=side i := congrArg Row.second (rows.row_eq i)
  have residue (i : A) : i.val.r < i.val.q := (mem_rows.mp (mem_clean.mp (clean i)).1).2.1
  have logZ (a : ℕ) (h : Option (Fin (2*Fixed.d b))) :
      Z a (.inl h)=nominalLogFactor b (h.map gridPlace) a := by
    cases h <;> rfl
  have rowZ (a : ℕ) (i : A) :
      Z a (.inr i)=if a≡i.val.r [MOD i.val.q] then (w i)⁻¹ else 0 := by
    simp only [Z,retainedMissColumn,Nat.ModEq,Nat.mod_eq_of_lt (residue i)]
  have restrictAvg (f : ℕ→ℝ) :
      avg (fun a=>if hitsTarget n ell a false=false then f a else 0)=∑ a∈X,weight a*f a := by
    simp only [avg,X,sum_filter,mul_ite,mul_zero]
  have logScore (i j : Option (Fin (2*Fixed.d b))) :
      score (missLogWeight n ell (i.map gridPlace) (j.map gridPlace)) = -T*err (.inl i) (.inl j) := by
    let f := fun a=>nominalLogFactor b (i.map gridPlace) a*nominalLogFactor b (j.map gridPlace) a
    let θ := (1-(Fixed.d b:ℝ)/ell)*((∑ c,∑ j∈range (cellMarkCount b),f (firstCellMark b c+j))/rawMeshCount b)
    have ref := miss_grid_log_entry (1-(Fixed.d b:ℝ)/ell) m R i j
    change missGridGram _ m R _ _ = θ at ref
    have sc := norm (fun a=>if hitsTarget n ell a false=false then f a else 0) θ
    change score _ = T*(avg _-θ) at sc
    rw [restrictAvg] at sc
    change score (missLogWeight n ell _ _) = _
    rw [show missLogWeight n ell (i.map gridPlace) (j.map gridPlace) =
        (fun a=>pooledMarkWeight univ (constructorCellMarks n ell)
          (fun _ k=>(if hitsTarget n ell k false=false then f k else 0)-θ) a/smoothMarkProbability O O a) by
      funext a
      have eq (k : ℕ) : (if hitsTarget n ell k false then 0 else f k) =
          if hitsTarget n ell k false=false then f k else 0 := by
        cases hitsTarget n ell k false <;> rfl
      change pooledMarkWeight univ (constructorCellMarks n ell)
        (fun _ k=>(if hitsTarget n ell k false then 0 else f k)-θ) a / smoothMarkProbability O O a = _
      simp only [eq],sc]
    change _ = -T*(missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inl i) (.inl j)-_)
    rw [ref]
    simp only [logZ,f]
    rw [show (∑ a∈X,weight a*(nominalLogFactor b (i.map gridPlace) a*nominalLogFactor b (j.map gridPlace) a)) =
      ∑ a∈X,weight a*nominalLogFactor b (i.map gridPlace) a*nominalLogFactor b (j.map gridPlace) a by
      apply sum_congr rfl;intro a _;ring]
    ring
  let H := Option (Fin (2*Fixed.d b))
  let L := Option (Bool×Fin (Fixed.d b))
  let equiv : H ≃ L :=
    ((interleavePlaces (Fixed.d b)).symm.trans (Equiv.boolProdEquivSum (Fin (Fixed.d b))).symm).optionCongr
  have mapEq (h : H) : h.map gridPlace = equiv h := by cases h <;> rfl
  have boxedLog : T^2*(∑ i : H,∑ j : H,(err (.inl i) (.inl j))^2) =
      missLogCost n ell x y*c^2 := by
    have eq : (∑ i : H,∑ j : H,(score (missLogWeight n ell (i.map gridPlace) (j.map gridPlace)))^2) =
        ∑ i : L,∑ j : L,(score (missLogWeight n ell i j))^2 := by
      simp only [mapEq]
      calc
        _ = ∑ i : H,∑ j : L,(score (missLogWeight n ell (equiv i) j))^2 :=
          sum_congr rfl (fun i _=>equiv.sum_comp (fun j=>(score (missLogWeight n ell (equiv i) j))^2))
        _ = _ := equiv.sum_comp (fun i=>∑ j : L,(score (missLogWeight n ell i j))^2)
    rw [missLogCost,div_mul_cancel₀ _ (sq_pos_of_pos cp).ne']
    rw [←show _ = ∑ i : L,∑ j : L,(score (missLogWeight n ell i j))^2 from rfl,←eq]
    simp_rw [logScore,mul_pow,neg_sq,mul_sum]
  have logBound := budget cp den (sum_nonneg (fun i _=>sum_nonneg (fun j _=>sq_nonneg (err (.inl i) (.inl j))))) boxedLog.le logSmall
  let single := fun (h : L) (i : A)=>score (missCrossWeight n ell (rows.row i).val β h)
  let crossCost := fun h : L=>boxedPhysicalSingleCost (n:=n) (ell:=ell) β
      (fun i=>missCrossWeight n ell i.val β h) x y
  have singleBound (h : L) : (∑ i : A,μ i*(single h i)^2)≤crossCost h :=
    rows.single_cost bx by' β (fun i=>missCrossWeight n ell i.val β h)
  have singleScore (i : A) (h : L) :
      single h i = T*((∑ a∈X,weight a*(nominalLogFactor b h a*Z a (.inr i)/(w i)))-
        missCrossCenter n ell (rows.row i).val β h) := by
    let f := fun a=>if a≡i.val.r [MOD i.val.q] ∧ hitsTarget n ell a false=false then
      nominalLogFactor b h a / μ i else 0
    let θ := missCrossCenter n ell (rows.row i).val β h
    have sc := norm f θ
    change score _ = T*(avg f-θ) at sc
    have wf : (fun a=>pooledMarkWeight univ (constructorCellMarks n ell) (fun _ k=>f k-θ) a/
        smoothMarkProbability O O a) = missCrossWeight n ell (rows.row i).val β h := by
      funext a
      unfold missCrossWeight
      simp only [f,θ,rows.prime,rowR,μ,p]
      rfl
    rw [wf] at sc
    change single h i = _ at sc
    rw [sc]
    have same (a : ℕ) : f a = if hitsTarget n ell a false=false then
        nominalLogFactor b h a*Z a (.inr i)/(w i) else 0 := by
      rw [rowZ]
      by_cases ht : hitsTarget n ell a false=false
      · by_cases hit : a≡i.val.r [MOD i.val.q]
        · simp only [f,ht,hit,and_self,if_true,ms]
          field_simp
        · simp [f,ht,hit]
      · simp [f,ht]
    rw [show avg f=∑ a∈X,weight a*(nominalLogFactor b h a*Z a (.inr i)/w i) from
      (congrArg avg (funext same)).trans (restrictAvg _)]
  have firstEq :
      (fun (a : GridPosition b) (i : A)=>sqrt ((bandRowPrime (rows.row i).val:ℝ)^(-β))*
        (fullBandInsertion b (bandRowPrime (rows.row i).val) (α a (rows.row i).val.1)/
          ((bandRowPrime (rows.row i).val:ℝ)*(bandRowPrime (rows.row i).val:ℝ)^(-β)))) = m := by
    funext a i
    simp only [rows.prime,rowS,m,w,μ,p,I]
  have crossScore (h : H) (i : A) :
      w i*single (h.map gridPlace) i = -T*err (.inl h) (.inr i) := by
    have ref := miss_grid_cross_entry (n:=n) (ell:=ell) (fun i : A=>(rows.row i).val) β R h i
    dsimp only at ref
    rw [firstEq,rows.prime] at ref
    change missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inl h) (.inr i) =
      w i*missCrossCenter n ell (rows.row i).val β (h.map gridPlace) at ref
    rw [singleScore]
    change _ = -T*(missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inl h) (.inr i)-_)
    rw [ref]
    simp only [logZ]
    rw [mul_left_comm (w i) T,mul_sub,mul_sum]
    rw [show (∑ a∈X,w i*(weight a*(nominalLogFactor b (h.map gridPlace) a*Z a (.inr i)/w i))) =
        ∑ a∈X,weight a*nominalLogFactor b (h.map gridPlace) a*Z a (.inr i) by
      apply sum_congr rfl; intro a _
      field_simp [(wp i).ne']]
    ring
  have diagScore (i : A) : single none i = -T*err (.inr i) (.inr i) := by
    have eqR :
        (fun (a : GridPosition b)=>ordinaryRawEntry (fun i : A=>bandRowPrime (rows.row i).val)
          (fun i=>(rows.row i).val.1) (fun i=>sqrt ((bandRowPrime (rows.row i).val:ℝ)^(-β))) (I a)) = R := by
      funext a
      simp only [rows.prime,rowS,R,w,μ,p]
    have ref := miss_grid_diagonal_entry (n:=n) (ell:=ell) (fun i : A=>(rows.row i).val) β m i
    dsimp only at ref
    rw [eqR] at ref
    change missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inr i) (.inr i)=
      missCrossCenter n ell (rows.row i).val β none at ref
    rw [singleScore]
    change _ = -T*(missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inr i) (.inr i)-_)
    rw [ref]
    have eq : (∑ a∈X,weight a*(nominalLogFactor b none a*Z a (.inr i)/w i)) =
        ∑ a∈X,weight a*Z a (.inr i)*Z a (.inr i) := by
      apply sum_congr rfl; intro a _
      rw [rowZ]
      by_cases hit : a≡i.val.r [MOD i.val.q] <;> simp [hit,nominalLogFactor,div_eq_mul_inv,mul_assoc]
    rw [eq]
    ring
  have diagPay : T^2*(∑ i : A,μ i*(err (.inr i) (.inr i))^2)≤boxedMissCrossCost n ell β x y*c^2 := by
    calc
      _ = ∑ i : A,μ i*(single none i)^2 := by simp_rw [diagScore,mul_pow,neg_sq,mul_sum]; apply sum_congr rfl; intro i _;ring
      _ ≤ crossCost none := singleBound none
      _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos cp)).mp (boxedMissCross_single_le n ell β x y none)
  have diagBound := budget cp den (sum_nonneg (fun i _=>mul_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg (err (.inr i) (.inr i))))) diagPay crossSmall
  have crossPay : T^2*(∑ h : H,∑ i : A,(err (.inl h) (.inr i))^2) ≤ boxedMissCrossCost n ell β x y*c^2 := by
    have eq (h : H) (i : A) : T^2*(err (.inl h) (.inr i))^2=μ i*(single (h.map gridPlace) i)^2 := by
      rw [show μ i*(single (h.map gridPlace) i)^2=(w i*single (h.map gridPlace) i)^2 by rw [mul_pow,ms],
        crossScore]
      simp only [mul_pow,neg_sq]
    simp_rw [mul_sum,eq,mapEq]
    rw [equiv.sum_comp (fun h : L=>∑ i : A,μ i*(single h i)^2)]
    change _ ≤ (∑ h : L,crossCost h)/c^2*c^2
    rw [div_mul_cancel₀ _ (sq_pos_of_pos cp).ne']
    exact sum_le_sum (fun h _=>singleBound h)
  have crossBound := budget cp den (sum_nonneg (fun h _=>sum_nonneg (fun i _=>sq_nonneg (err (.inl h) (.inr i))))) crossPay crossSmall
  let D := distinctOrdinaryRowPairs A
  let pairScore := fun k : ↥D=>score (physicalPairMissWeight β (rows.pair k))
  have pairScoreEq (k : ↥D) :
      (w k.val.1*w k.val.2)*pairScore k=-T*err (.inr k.val.1) (.inr k.val.2) := by
    let i := k.val.1
    let j := k.val.2
    let f := fun a=>if a≡i.val.r [MOD i.val.q] ∧ a≡j.val.r [MOD j.val.q] ∧ hitsTarget n ell a false=false then
      (μ i*μ j)⁻¹ else 0
    let θ := pairMissCenter β (rows.pair k)
    have ref := reference bb hn target (rows.pair k) β p side i j
      (rows.prime i).symm (rows.prime j).symm (rowS i).symm (rowS j).symm m
    change w i*w j*θ=missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inr i) (.inr j) at ref
    have sc := norm f θ
    change score _=T*(avg f-θ) at sc
    have wf : (fun a=>pooledMarkWeight univ (constructorCellMarks n ell) (fun _ k=>f k-θ) a/
        smoothMarkProbability O O a) = physicalPairMissWeight β (rows.pair k) := by
      have fEq (a : ℕ) : f a=pairMissAmplitude β i.val.q j.val.q
          (decide (a≡i.val.r [MOD i.val.q])) (decide (a≡j.val.r [MOD j.val.q])) (hitsTarget n ell a false) := by
        dsimp only [f,pairMissAmplitude,μ,p]
        by_cases l : a≡i.val.r [MOD i.val.q] <;> by_cases r : a≡j.val.r [MOD j.val.q] <;>
          cases t : hitsTarget n ell a false <;> simp [l,r]
      funext a
      have p₁ : (rows.pair k).val.1=(rows.row i).val := rfl
      have p₂ : (rows.pair k).val.2=(rows.row j).val := rfl
      have r₁ : (rows.pair k).val.1.2.2.val=i.val.r :=
        (congrArg (fun a : BandRow b=>a.2.2.val) p₁).trans (rowR i)
      have r₂ : (rows.pair k).val.2.2.2.val=j.val.r :=
        (congrArg (fun a : BandRow b=>a.2.2.val) p₂).trans (rowR j)
      unfold physicalPairMissWeight
      simp only [p₁,p₂,rows.prime,r₁,r₂,←fEq]
      rfl
    rw [wf] at sc
    change pairScore k = _ at sc
    change w i*w j*pairScore k = -T*(missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inr i) (.inr j)-_)
    rw [sc,←ref]
    have same (a : ℕ) : f a=if hitsTarget n ell a false=false then
        Z a (.inr i)*Z a (.inr j)/(w i*w j) else 0 := by
      rw [rowZ,rowZ]
      by_cases ht : hitsTarget n ell a false=false
      · by_cases hit : a≡i.val.r [MOD i.val.q] <;> by_cases hit' : a≡j.val.r [MOD j.val.q]
        all_goals simp only [f,ht,hit,hit',and_self,and_true,and_false,if_true,if_false,
          zero_mul,mul_zero,zero_div,ms]
        field_simp
      · simp [f,ht]
    rw [show avg f=∑ a∈X,weight a*(Z a (.inr i)*Z a (.inr j)/(w i*w j)) from
      (congrArg avg (funext same)).trans (restrictAvg _)]
    rw [mul_left_comm (w i*w j) T,mul_sub,mul_sum]
    rw [show (∑ a∈X,(w i*w j)*(weight a*(Z a (.inr i)*Z a (.inr j)/(w i*w j)))) =
        ∑ a∈X,weight a*Z a (.inr i)*Z a (.inr j) by
      apply sum_congr rfl; intro a _
      field_simp [(wp i).ne',(wp j).ne']]
    dsimp only [i,j]
    ring
  have pairPay : T^2*(∑ k : ↥D,(err (.inr k.val.1) (.inr k.val.2))^2) ≤ missPairCost n ell β x y*c^2 := by
    have eq (k : ↥D) : T^2*(err (.inr k.val.1) (.inr k.val.2))^2 =
        μ k.val.1*μ k.val.2*(pairScore k)^2 := by
      rw [show μ k.val.1*μ k.val.2*(pairScore k)^2=((w k.val.1*w k.val.2)*pairScore k)^2 by
        simp only [mul_pow,ms],pairScoreEq]
      simp only [mul_pow,neg_sq]
    rw [missPairCost,div_mul_cancel₀ _ (sq_pos_of_pos cp).ne']
    simp_rw [mul_sum,eq]
    exact rows.pair_cost bx by' β (physicalPairMissWeight β)
  have pairBound := budget cp den (sum_nonneg (fun k _=>sq_nonneg (err (.inr k.val.1) (.inr k.val.2)))) pairPay pairSmall
  have samePrime (i j : A) (neq : i≠j) (pq : p i=p j) : err (.inr i) (.inr j)=0 := by
    have ref : missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inr i) (.inr j)=0 := by
      simp [missGridGram,missMomentEntry,R,ordinaryRawEntry,pq,neq]
    have zero (a : ℕ) : weight a*Z a (.inr i)*Z a (.inr j)=0 := by
      rw [rowZ,rowZ]
      by_cases hi : a≡i.val.r [MOD i.val.q] <;> by_cases hj : a≡j.val.r [MOD j.val.q]
      all_goals simp only [hi,hj,if_true,if_false,mul_zero,zero_mul]
      change i.val.q=j.val.q at pq
      have ri := hi
      rw [pq] at ri
      have rr := ri.symm.trans hj
      change i.val.r%j.val.q=j.val.r%j.val.q at rr
      rw [Nat.mod_eq_of_lt (pq ▸ residue i),Nat.mod_eq_of_lt (residue j)] at rr
      exact (neq (Subtype.ext (clean_same_prime (clean i) (clean j) pq rr))).elim
    change missGridGram (1-(Fixed.d b:ℝ)/ell) m R (.inr i) (.inr j)-_ = 0
    rw [ref,show (∑ a∈X,weight a*Z a (.inr i)*Z a (.inr j)) = 0 by
      rw [show (0:ℝ)=∑ a∈X,0 by simp]
      exact sum_congr rfl fun a _=>zero a,sub_zero]
  have ordinaryEq (i j : A) : (if i=j then 0 else err (.inr i) (.inr j))^2 =
      if i.val.q≠j.val.q then (err (.inr i) (.inr j))^2 else 0 := by
    by_cases h : i=j
    · subst j; simp
    · by_cases pq : i.val.q=j.val.q
      · simp [h,pq,samePrime i j h pq]
      · simp [h,pq]
  have crossSym (i : A) (h : H) : err (.inr i) (.inl h) = err (.inl h) (.inr i) := by
    simp only [err,missGridGram,missMomentEntry]
    congr 1
    · congr 1
      exact sum_congr rfl fun _ _=>by rw [mul_comm (m _ i)]
    · exact sum_congr rfl fun _ _=>by ring
  have logOff : (∑ i : H,∑ j : H,(if i=j then 0 else err (.inl i) (.inl j))^2)≤256*e^6 := by
    refine (sum_le_sum fun i _=>sum_le_sum fun j _=>?_).trans logBound
    split <;> simp [sq_nonneg]
  refine ⟨diagBound,logBound,?_⟩
  simp only [Fintype.sum_sum_type,sum_add_distrib,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,
    Sum.inr_ne_inl,if_false,ordinaryEq,crossSym]
  rw [distinctOrdinaryRowPairs_sum A (fun i j=>(err (.inr i) (.inr j))^2)]
  rw [sum_comm (f:=fun (i : A) (h : H)=>(err (.inl h) (.inr i))^2)]
  linarith only [logOff,crossBound,pairBound]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.miss_entry_bounds
