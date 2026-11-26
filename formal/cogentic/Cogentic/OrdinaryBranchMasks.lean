import Cogentic.DistinctPrimeGram
import Cogentic.TargetResidue

namespace Cogentic.Construction
open Finset Real Polynomial
noncomputable section

/-- The actual first field tests precisely the wanted residues at the target
prime. The second field has constant target part one. -/
theorem target_part_residues {n ell : ℕ} (hd : 3≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (a : ℕ) :
    let roots := wanted (Fixed.d (n.log2+1)) ell (Fixed.rootBase n)
    (hitsTarget n ell a false ↔ a%ell∈roots) ∧ targetPart n ell a true=1 := by
  intro roots
  let : Fact ell.Prime := ⟨(mem_dyadicTargets.mp target).1⟩
  let f (side : Bool) := (Marking.polynomial (basePolynomial n ell side)).map (Int.castRingHom (ZMod ell))
  have value (cs : List ℤ) : ((eval (a:ℤ) cs:ℤ):ZMod ell)=((Marking.polynomial cs).map (Int.castRingHom (ZMod ell))).eval (a:ZMod ell) := by
    induction cs with
    | nil => simp [Construction.eval,Marking.polynomial]
    | cons x xs ih => simp [Construction.eval,Marking.polynomial,ih]
  have hit (side : Bool) : hitsTarget n ell a side ↔ (f side).eval (a:ZMod ell)=0 := by
    rw [←value (basePolynomial n ell side)]
    simp [hitsTarget,ZMod.intCast_zmod_eq_zero_iff_dvd]
  have spec := wanted_spec (target_gt_degree target) (Fixed.rootBase n)
  have pol := (target_polynomials (show 2≤Fixed.d (n.log2+1) by omega) target 0 0 0 0).1
  have allRoots : (f false).roots=((roots.map (fun t : ℕ=>(t:ZMod ell)) : List (ZMod ell)) : Multiset (ZMod ell)) := by
    change ((Marking.polynomial (construct n ell 0 0 0 0).first).map _).roots=_
    rw [pol,roots_C_mul _ (leading_unit_at_target hd target)]
    simpa [roots,List.map_map,Function.comp_def] using
      roots_multiset_prod_X_sub_C ((roots.map (fun t : ℕ=>(t:ZMod ell)) : List (ZMod ell)) : Multiset (ZMod ell))
  have fnz : f false≠0 := by
    intro z
    have card := congrArg Multiset.card allRoots
    rw [z,roots_zero] at card
    simp [roots,spec.1] at card;omega
  have no : ¬hitsTarget n ell a true := fun h=>
    (target_roots hd target 0 0 0 0).2.2.2 (a:ZMod ell) ((hit true).mp h)
  refine ⟨?_,by simp [targetPart,no]⟩
  rw [hit,←IsRoot.def,←mem_roots fnz,allRoots]
  change (a:ZMod ell)∈roots.map (fun t : ℕ=>(t:ZMod ell)) ↔ a%ell∈roots
  constructor
  · intro hm;obtain ⟨t,tm,eq⟩ := List.mem_map.mp hm
    have val := congrArg ZMod.val eq
    rw [ZMod.val_natCast_of_lt (spec.2.2 _ tm).1,ZMod.val_natCast] at val
    exact val ▸ tm
  · intro am; exact List.mem_map.mpr ⟨a%ell,am,(ZMod.natCast_eq_natCast_iff ..).mpr (by simp [Nat.ModEq])⟩

/-- A signed indicator of one congruence class. -/
structure SignedResidueMask where
  modulus : ℕ
  residue : ℕ
  sign : ℤ

def SignedResidueMask.weight (t : SignedResidueMask) (a : ℕ) : ℝ :=
  (t.sign:ℝ)*residueEntry t.modulus t.residue a

private def unitMask : SignedResidueMask := ⟨1,0,1⟩

/-- An ordinary hit is a single class. A miss is the full class minus it. -/
def ordinaryResidueMasks (p r : ℕ) (hit : Bool) : List SignedResidueMask :=
  if hit then [⟨p,r,1⟩] else [unitMask,⟨p,r,-1⟩]

/-- All protected target roots on a hit; the full class minus these roots on a miss. -/
def targetResidueMasks (ell : ℕ) (roots : List ℕ) (hit : Bool) : List SignedResidueMask :=
  (if hit then [] else [unitMask]) ++ roots.map (fun r=>⟨ell,r,if hit then 1 else -1⟩)

private def joinMask (x y : SignedResidueMask) : SignedResidueMask :=
  ⟨x.modulus*y.modulus,crt x.modulus y.modulus x.residue y.residue,x.sign*y.sign⟩

private def joinMasks (S T : List SignedResidueMask) :=
  S.flatMap (fun x=>T.map (joinMask x))

def ordinaryTargetBranchMasks (p q ell r s : ℕ) (roots : List ℕ) (hp hq ht : Bool) :=
  joinMasks (joinMasks (ordinaryResidueMasks p r hp) (ordinaryResidueMasks q s hq)) (targetResidueMasks ell roots ht)

private theorem unit_residue (a : ℕ) : residueEntry 1 0 a=1 := by simp [residueEntry,Nat.modEq_one]

private theorem ordinary_mask_sum (p r a : ℕ) (h : Bool) :
    ((ordinaryResidueMasks p r h).map (fun t=>t.weight a)).sum =
      if decide (a ≡ r [MOD p])=h then 1 else 0 := by
  cases h <;> by_cases yes : a ≡ r [MOD p] <;> simp [ordinaryResidueMasks,SignedResidueMask.weight,unitMask,residueEntry,yes,Nat.modEq_one]

private theorem roots_entry (ell a : ℕ) (rs : List ℕ) (nodup : rs.Nodup) (small : ∀ r∈rs,r<ell) :
    (rs.map (fun r=>residueEntry ell r a)).sum=if a%ell∈rs then 1 else 0 := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have bound := small r (by simp)
    have tail := ih (List.nodup_cons.mp nodup).2 (fun r hr=>small r (by simp [hr]))
    have test : a ≡ r [MOD ell] ↔ a%ell=r := by simp [Nat.ModEq,Nat.mod_eq_of_lt bound]
    rw [List.map_cons,List.sum_cons,tail]
    simp only [List.mem_cons,residueEntry,test]
    by_cases ar : a%ell=r
    · simp [ar,(List.nodup_cons.mp nodup).1]
    · simp [ar]

private theorem target_mask_sum {n ell : ℕ} (hd : 3≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (a : ℕ) (h : Bool) :
    let roots := wanted (Fixed.d (n.log2+1)) ell (Fixed.rootBase n)
    ((targetResidueMasks ell roots h).map (fun t=>t.weight a)).sum =
      if hitsTarget n ell a false=h then 1 else 0 := by
  intro roots
  have spec := wanted_spec (target_gt_degree target) (Fixed.rootBase n)
  have hit := (target_part_residues hd target a).1
  have between := roots_entry ell a roots spec.2.1 (fun r hr=>(spec.2.2 r hr).1)
  have terms (z : ℤ) : (roots.map (fun r=>(SignedResidueMask.mk ell r z).weight a)).sum=
      (z:ℝ)*(roots.map (fun r=>residueEntry ell r a)).sum := List.sum_map_mul_left roots (fun r=>residueEntry ell r a) (z:ℝ)
  have hh : hitsTarget n ell a false=decide (a%ell∈roots) := Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hit)
  cases h
  · simp only [targetResidueMasks,Bool.false_eq_true,if_false,List.cons_append,List.nil_append,List.map_cons,List.sum_cons,
      List.map_map,Function.comp_def]
    change unitMask.weight a+(roots.map (fun r=>(SignedResidueMask.mk ell r (-1)).weight a)).sum=_
    have unit : unitMask.weight a=1 := by simp [unitMask,SignedResidueMask.weight,unit_residue]
    rw [unit,terms,between,hh]
    by_cases mem : a%ell∈roots <;> simp [mem]
  · simp only [targetResidueMasks,if_true,List.nil_append,List.map_map,Function.comp_def]
    rw [terms,between,hh]
    by_cases mem : a%ell∈roots <;> simp [mem]

private theorem join_mask_sum (S T : List SignedResidueMask) (a : ℕ)
    (cop : ∀ x∈S,∀ y∈T,x.modulus.Coprime y.modulus) :
    ((joinMasks S T).map (fun t=>t.weight a)).sum =
      (S.map (fun t=>t.weight a)).sum*(T.map (fun t=>t.weight a)).sum := by
  have entry (x y : SignedResidueMask) (xy : x.modulus.Coprime y.modulus) :
      (joinMask x y).weight a=x.weight a*y.weight a := by
    simp only [joinMask,SignedResidueMask.weight,Int.cast_mul,←residueEntry_product xy];ring
  induction S with
  | nil => simp [joinMasks]
  | cons x S ih =>
    have tail := ih (fun p pm=>cop p (by simp [pm]))
    change (((T.map (joinMask x))++(joinMasks S T)).map (fun t=>t.weight a)).sum=_
    rw [List.map_append,List.sum_append,tail,List.map_cons,List.sum_cons,add_mul]
    congr 1
    rw [List.map_map,←List.sum_map_mul_left]
    apply congrArg List.sum;apply List.map_congr_left;intro y ym
    exact entry x y (cop x (by simp) y ym)

private theorem join_length (S T : List SignedResidueMask) : (joinMasks S T).length=S.length*T.length := by
  induction S with
  | nil => simp [joinMasks]
  | cons x S ih =>
    change ((T.map (joinMask x))++joinMasks S T).length=_
    rw [List.length_append,List.length_map,ih,List.length_cons,add_mul,one_mul,add_comm]

private def maskDivides (S : List SignedResidueMask) (p : ℕ) := ∀ x∈S, x.modulus∣p

private theorem join_divides {S T : List SignedResidueMask} {p q : ℕ} (ss : maskDivides S p) (ts : maskDivides T q) :
    maskDivides (joinMasks S T) (p*q) := by
  intro z hz
  obtain ⟨x,xm,zx⟩ := List.mem_flatMap.mp hz
  obtain ⟨y,ym,zy⟩ := List.mem_map.mp zx
  subst z; exact Nat.mul_dvd_mul (ss x xm) (ts y ym)

private theorem ordinary_divides (p r : ℕ) (h : Bool) : maskDivides (ordinaryResidueMasks p r h) p := by
  intro z zm
  cases h <;> simp [ordinaryResidueMasks] at zm <;> rcases zm with rfl|rfl <;> simp [unitMask]

private theorem target_divides (ell : ℕ) (roots : List ℕ) (h : Bool) : maskDivides (targetResidueMasks ell roots h) ell := by
  intro z zm
  cases h <;> simp only [targetResidueMasks,Bool.false_eq_true,if_false,if_true,List.cons_append,List.nil_append,List.mem_cons,List.mem_map] at zm
  · rcases zm with rfl|⟨r,_,rfl⟩ <;> simp [unitMask]
  · obtain ⟨r,_,rfl⟩ := zm; rfl

/-- For two distinct ordinary primes, the exact executable target branch and
the two ordinary hit/miss tests expand into at most 4(d+1) signed CRT classes.
All classes satisfy the modulus conditions of the pooled second moment. -/
theorem ordinary_target_branch_masks {n ell p q : ℕ} (hn : 2≤n) (hd : 10004≤Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (sieve : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (pp : p∈sieveBand n ell 1) (qp : q∈sieveBand n ell 1) (pq : p≠q) (pe : p≠ell) (qe : q≠ell)
    (r s : ℕ) (hp hq ht : Bool) :
    let b := n.log2+1; let roots := wanted (Fixed.d b) ell (Fixed.rootBase n)
    let S := ordinaryTargetBranchMasks p q ell r s roots hp hq ht
    S.length≤4*(Fixed.d b+1) ∧
    (∀ t∈S, 0<t.modulus ∧ Squarefree t.modulus ∧ t.modulus≤(Fixed.B b)^3 ∧ t.modulus.Coprime (markModulus n ell) ∧
      ∀ k∈pairCorrectionPrimes b,k.Coprime t.modulus) ∧
    ∀ a, (S.map (fun t=>t.weight a)).sum=
      if decide (a ≡ r [MOD p])=hp ∧ decide (a ≡ s [MOD q])=hq ∧ hitsTarget n ell a false=ht then 1 else 0 := by
  intro b roots S
  let A := ordinaryResidueMasks p r hp; let B := ordinaryResidueMasks q s hq; let T := targetResidueMasks ell roots ht
  have l (v w : ℕ) (h : Bool) : (ordinaryResidueMasks v w h).length≤2 := by cases h <;> simp [ordinaryResidueMasks]
  have tw : T.length≤Fixed.d b+1 := by
    have len : (wanted (Fixed.d b) ell (Fixed.rootBase n)).length=Fixed.d b := (wanted_spec (target_gt_degree target) (Fixed.rootBase n)).1
    cases ht <;> simp [T,targetResidueMasks,roots,len,Nat.add_comm]
  have size : S.length≤4*(Fixed.d b+1) := by
    dsimp only [S,ordinaryTargetBranchMasks];rw [join_length,join_length]
    exact Nat.mul_le_mul (Nat.mul_le_mul (l p r hp) (l q s hq)) tw
  have ad := ordinary_divides p r hp; have bd := ordinary_divides q s hq; have td := target_divides ell roots ht
  have total : maskDivides S (p*q*ell) := join_divides (join_divides ad bd) td
  have primeE := (mem_dyadicTargets.mp target).1
  have pb := (mem_filter.mp pp).1
  have qb := (mem_filter.mp qp).1
  have eb := dyadic_target_in_primeBand (Nat.succ_pos n.log2) target
  have P := (mem_primeBand.mp pb).1; have Q := (mem_primeBand.mp qb).1
  have cop := (Nat.coprime_primes P Q).mpr pq
  have ce := Nat.coprime_mul_iff_left.mpr ⟨(Nat.coprime_primes P primeE).mpr pe,(Nat.coprime_primes Q primeE).mpr qe⟩
  have sf := (Nat.squarefree_mul ce).mpr ⟨(Nat.squarefree_mul cop).mpr ⟨P.squarefree,Q.squarefree⟩,primeE.squarefree⟩
  have fullpos := Nat.mul_pos (Nat.mul_pos P.pos Q.pos) primeE.pos
  have bound := Nat.mul_le_mul (Nat.mul_le_mul (mem_primeBand.mp pb).2.1 (mem_primeBand.mp qb).2.1) (mem_primeBand.mp eb).2.1
  have clean0 := (markModulus_spec hn hd composite target sieve).2.2.1
  have clean : (p*q*ell).Coprime (markModulus n ell) := Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr
    ⟨P.coprime_iff_not_dvd.mpr (mem_filter.mp pp).2.1,Q.coprime_iff_not_dvd.mpr (mem_filter.mp qp).2.1⟩,
    (Nat.coprime_mul_iff_right.mp clean0).2.symm⟩
  have corr (k v : ℕ) (km : k∈pairCorrectionPrimes b) (vm : v∈primeBand b) : k.Coprime v := by
    obtain ⟨kp,_,lim⟩ := mem_pairCorrectionPrimes.mp km
    obtain ⟨vp,_,hi⟩ := mem_primeBand.mp vm
    apply (Nat.coprime_primes kp vp).mpr
    rintro rfl
    apply hi.not_ge
    calc k^2 ≤ (2^(200*Fixed.h b))^2 := Nat.pow_le_pow_left lim _
         _ = 2^(200*Fixed.h b*2) := (Nat.pow_mul ..).symm
         _ ≤ Fixed.B b := Nat.pow_le_pow_right (by decide) (by dsimp [Fixed.beta];omega)
  refine ⟨size,?_,?_⟩
  · intro t tm
    have dv := total t tm
    exact ⟨Nat.pos_of_dvd_of_pos dv fullpos,sf.squarefree_of_dvd dv,(Nat.le_of_dvd fullpos dv).trans (bound.trans_eq (by ring)),
      clean.of_dvd_left dv,fun k km=>Nat.Coprime.of_dvd_right dv (Nat.coprime_mul_iff_right.mpr
        ⟨Nat.coprime_mul_iff_right.mpr ⟨corr k p km pb,corr k q km qb⟩,corr k ell km eb⟩)⟩
  · intro a
    have product := join_mask_sum (joinMasks A B) T a (fun x xm y ym=> (ce.of_dvd_left (join_divides ad bd x xm)).of_dvd_right (td y ym))
    have pair := join_mask_sum A B a (fun x xm y ym=> (cop.of_dvd_left (ad x xm)).of_dvd_right (bd y ym))
    change ((joinMasks (joinMasks A B) T).map (fun t=>t.weight a)).sum=_
    rw [product,pair]
    dsimp only [A,B,T]
    rw [ordinary_mask_sum,ordinary_mask_sum,target_mask_sum (by omega : 3≤Fixed.d (n.log2+1)) target a ht]
    split_ifs <;> simp_all

/-- The independent residue mass of a hit or its complement. -/
def residueBranchMass (density : ℝ) (hit : Bool) : ℝ :=
  if hit then density else 1-density

/-- Total variation of the signed class representation of a hit or miss. -/
def residueBranchEnvelope (density : ℝ) (hit : Bool) : ℝ :=
  if hit then density else 1+density

def maskMass (absSign : Bool) (t : SignedResidueMask) : ℝ :=
  (if absSign then |(t.sign:ℝ)| else (t.sign:ℝ)) / t.modulus

private theorem join_mass (S T : List SignedResidueMask) (z : Bool) :
    ((joinMasks S T).map (maskMass z)).sum = (S.map (maskMass z)).sum*(T.map (maskMass z)).sum := by
  have prod (x y : SignedResidueMask) : maskMass z (joinMask x y)=maskMass z x*maskMass z y := by
    cases z <;> simp only [joinMask,maskMass,Nat.cast_mul,Int.cast_mul,abs_mul,if_true,if_false,Bool.false_eq_true] <;> ring
  induction S with
  | nil => simp [joinMasks]
  | cons x S ih =>
    change (((T.map (joinMask x))++(joinMasks S T)).map (maskMass z)).sum=_
    rw [List.map_append,List.sum_append,ih,List.map_cons,List.sum_cons,add_mul]
    congr 1
    rw [List.map_map,←List.sum_map_mul_left]
    exact congrArg List.sum (List.map_congr_left (fun y _=>prod x y))

theorem branch_class_mass (p q ell r s : ℕ) (roots : List ℕ) (hp hq ht z : Bool) :
    let score := if z then residueBranchEnvelope else residueBranchMass
    let S := ordinaryTargetBranchMasks p q ell r s roots hp hq ht
    (S.map (maskMass z)).sum =
      score (p:ℝ)⁻¹ hp * score (q:ℝ)⁻¹ hq * score (roots.length/(ell:ℝ)) ht := by
  intro score S
  have one (k a) (hit : Bool) : ((ordinaryResidueMasks k a hit).map (maskMass z)).sum=score (k:ℝ)⁻¹ hit := by
    cases hit <;> cases z <;> simp [ordinaryResidueMasks,unitMask,maskMass,score,residueBranchEnvelope,residueBranchMass] <;> ring
  have t : ((targetResidueMasks ell roots ht).map (maskMass z)).sum=score (roots.length/(ell:ℝ)) ht := by
    cases ht <;> cases z <;>
      simp [targetResidueMasks,unitMask,maskMass,score,residueBranchEnvelope,residueBranchMass,
        List.map_map,Function.comp_def,List.map_const',List.sum_replicate] <;> ring
  dsimp only [S,ordinaryTargetBranchMasks]
  rw [join_mass,join_mass,one,one,t]

/-- A branch-weighted smooth profile on one cell has the mean of its full
integer mesh times the independent residue probabilities. A rare hit saves
its full class density in the discrepancy, including for two ordinary hits. -/
theorem ordinary_branch_mesh_mean (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ {p q : ℕ}, p∈sieveBand n ell 1 → q∈sieveBand n ell 1 → p≠q → p≠ell → q≠ell →
    ∀ (r s : ℕ) (hp hq ht : Bool) (cell : Option (Bool×Fin (Fixed.d (n.log2+1)))) (f : ℕ→ℝ),
    let b := n.log2+1; let L := firstCellMark b cell; let M := cellMarkCount b
    let X := (constructorCellMarks n ell cell).filter (fun a=>
      decide (a ≡ r [MOD p])=hp ∧ decide (a ≡ s [MOD q])=hq ∧ hitsTarget n ell a false=ht)
    let ρ := ∏ t∈(markModulus n ell).primeFactors,(1-(t:ℝ)⁻¹)
    let coeff := fun (g : ℝ→Bool→ℝ)=>g (p:ℝ)⁻¹ hp*g (q:ℝ)⁻¹ hq*g ((Fixed.d b:ℝ)/ell) ht
    |(∑ a∈X,f a)-coeff residueBranchMass*(ρ*∑ j∈range M,f (L+j))|≤
      coeff residueBranchEnvelope*(meshVariation L M f*(1+2*exp 6)*M*exp (-K*(Fixed.z b:ℝ)^2)) := by
  classical
  obtain ⟨n₁,counts⟩ := residue_class_contrast_drift line K hk
  obtain ⟨b₀,degrees⟩ := Fixed.degree_grows 10004
  refine ⟨max n₁ (max 2 (2^b₀)),?_⟩
  intro n old ell target comp sieve p q pp qp pq pe qe r s hp hq ht cell f b L M X ρ coeff
  obtain ⟨large,rest⟩ := max_le_iff.mp old
  obtain ⟨hn,lim⟩ := max_le_iff.mp rest
  have hd := degrees b (((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _))
  let roots := wanted (Fixed.d b) ell (Fixed.rootBase n)
  let S := ordinaryTargetBranchMasks p q ell r s roots hp hq ht
  let Y := constructorCellMarks n ell cell
  let G := ρ*∑ j∈range M,f (L+j)
  let E := meshVariation L M f*(1+2*exp 6)*M*exp (-K*(Fixed.z b:ℝ)^2)
  have prop := ordinary_target_branch_masks hn hd comp target sieve pp qp pq pe qe r s hp hq ht
  have density (z : Bool) : (S.map (maskMass z)).sum=coeff (if z then residueBranchEnvelope else residueBranchMass) := by
    have eq := branch_class_mass p q ell r s roots hp hq ht z
    dsimp only at eq
    have len : roots.length=Fixed.d b := (wanted_spec (target_gt_degree target) (Fixed.rootBase n)).1
    rwa [len] at eq
  have cls (t : SignedResidueMask) (tm : t∈S) :
      |(∑ a∈Y,t.weight a*f a)-maskMass false t*G| ≤ maskMass true t*E := by
    obtain ⟨tp,_,cap,clean,_⟩ := prop.2.1 t tm
    have tr : (0:ℝ)<t.modulus := by exact_mod_cast tp
    have law := counts n large ell target comp sieve cell 1 t.modulus 0 t.residue (by decide)
      tp (Nat.coprime_one_left _) clean (by rw [one_mul];exact cap.trans (Nat.pow_le_pow_right (Nat.pow_pos (by decide)) (by decide : 3≤4)))
      (fun v vm dvd=>(Nat.prime_of_mem_primeFactors vm).not_dvd_one dvd |>.elim) f (fun _=>0)
    dsimp only at law
    have no (v : ℕ) (hv : v∈(markModulus n ell).primeFactors) : ¬v∣1 := (Nat.prime_of_mem_primeFactors hv).not_dvd_one
    simp only [Nat.modEq_one,filter_true,Nat.cast_one,div_one,sum_const_zero,sub_zero,abs_zero,sub_self,add_zero,
      filter_true_of_mem no] at law
    let A := ∑ a∈Y with a ≡ t.residue [MOD t.modulus], f a
    change |(t.modulus:ℝ)*A-(∑ j∈range M,f (L+j))*ρ|≤E at law
    have obs : (∑ a∈Y,t.weight a*f a)=(t.sign:ℝ)*A := by
      dsimp only [A,SignedResidueMask.weight,residueEntry];rw [mul_sum,sum_filter]
      apply sum_congr rfl;intro a _;split_ifs <;> ring
    rw [obs]
    have id : (t.sign:ℝ)*A-maskMass false t*G = ((t.sign:ℝ)/t.modulus)*((t.modulus:ℝ)*A-(∑ j∈range M,f (L+j))*ρ) := by
      dsimp [maskMass,G];field_simp
    rw [id,abs_mul,abs_div,abs_of_pos tr]
    exact mul_le_mul_of_nonneg_left law (div_nonneg (abs_nonneg _) tr.le)
  have all (T : List SignedResidueMask) (sub : ∀ t∈T,t∈S) :
      |(∑ a∈Y, (T.map (fun t=>t.weight a)).sum*f a)-(T.map (maskMass false)).sum*G|≤
        (T.map (maskMass true)).sum*E := by
    induction T with
    | nil => simp
    | cons t T ih =>
      have one := cls t (sub t (by simp))
      have many := ih (fun t ht=>sub t (by simp [ht]))
      simp only [List.map_cons,List.sum_cons,add_mul,sum_add_distrib]
      rw [show _+_-(_+_)=((∑ a∈Y,t.weight a*f a)-maskMass false t*G)+
        ((∑ a∈Y,(T.map (fun t=>t.weight a)).sum*f a)-(T.map (maskMass false)).sum*G) by ring]
      exact (abs_add_le ..).trans (add_le_add one many)
  have result := all S (fun _ h=>h)
  rw [density false,density true] at result
  have actual : (∑ a∈Y,(S.map (fun t=>t.weight a)).sum*f a)=∑ a∈X,f a := by
    dsimp only [X,Y];rw [sum_filter]
    apply sum_congr rfl;intro a _
    rw [prop.2.2 a]
    split_ifs <;> simp
  rwa [actual] at result

/-- On the prescribed branch, every field has a fixed hit product. Either
or both of the two observed ordinary rows may belong to this field. -/
theorem PrescribedRows.hitProduct_on_pair_branch {n ell p q : ℕ} (R : PrescribedRows n ell)
    (pq : p≠q) (cover : R.primes⊆{p,q}) (a r s : ℕ) (hp hq : Bool)
    (pr : p∈R.primes → R.residue p ≡ r [MOD p]) (qr : q∈R.primes → R.residue q ≡ s [MOD q])
    (ph : decide (a ≡ r [MOD p])=hp) (qh : decide (a ≡ s [MOD q])=hq) :
    R.hitProduct a=(if p∈R.primes ∧ hp then p else 1)*(if q∈R.primes ∧ hq then q else 1) := by
  classical
  have hit (k v : ℕ) (bit : Bool) (res : k∈R.primes→R.residue k ≡ v [MOD k]) (mask : decide (a ≡ v [MOD k])=bit) :
      k∈R.hit a ↔ k∈R.primes ∧ bit := by
    rw [←mask]; simp only [PrescribedRows.hit,mem_filter,decide_eq_true_eq,ZMod.natCast_eq_natCast_iff]
    exact and_congr_right (fun hm=>⟨fun h=>h.symm.trans (res hm),fun h=>(res hm).trans h.symm⟩)
  have hP := hit p r hp pr ph
  have hQ := hit q s hq qr qh
  have coverHit : R.hit a⊆{p,q} := (filter_subset ..).trans cover
  have same : ({p,q} : Finset ℕ).filter (fun i=>i∈R.hit a)=R.hit a := by
    ext i;simp only [mem_filter];exact ⟨And.right,fun mem=>⟨coverHit mem,mem⟩⟩
  change (∏ k∈R.hit a,k)=_
  calc _ = ∏ k∈({p,q}:Finset ℕ),if k∈R.hit a then k else 1 := by rw [←Finset.prod_filter,same]
       _ = _ := by rw [Finset.prod_insert (by simp [pq]),Finset.prod_singleton];simp only [hP,hQ]

private def maskUnitSigns (L : List SignedResidueMask) := ∀ x∈L,x.sign.natAbs=1

/-- All signed inclusion-exclusion coefficients are one in absolute value. -/
theorem ordinaryTargetBranchMasks_unit_sign (p q ell r s : ℕ) (roots : List ℕ) (hp hq ht : Bool) :
    ∀ x∈ordinaryTargetBranchMasks p q ell r s roots hp hq ht,x.sign.natAbs=1 := by
  have ord (v w : ℕ) (b : Bool) : maskUnitSigns (ordinaryResidueMasks v w b) := by
    intro x xm
    cases b <;> simp [ordinaryResidueMasks] at xm <;> rcases xm with rfl|rfl <;> rfl
  have tgt : maskUnitSigns (targetResidueMasks ell roots ht) := by
    intro x xm
    cases ht <;> simp only [targetResidueMasks,Bool.false_eq_true,if_false,if_true,List.cons_append,List.nil_append,List.mem_cons,List.mem_map] at xm
    · rcases xm with rfl|⟨r,_,rfl⟩ <;> rfl
    · obtain ⟨r,_,rfl⟩ := xm; rfl
  have join {S T : List SignedResidueMask} (sok : maskUnitSigns S) (tok : maskUnitSigns T) : maskUnitSigns (joinMasks S T) := by
    intro z zm
    obtain ⟨x,xm,hx⟩ := List.mem_flatMap.mp zm
    obtain ⟨y,ym,rfl⟩ := List.mem_map.mp hx
    simp [joinMask,Int.natAbs_mul,sok x xm,tok y ym]
  exact join (join (ord p r hp) (ord q s hq)) tgt

/-- The hit product in a field on a chosen two-prime branch. -/
def PrescribedRows.pairBranchProduct {n ell : ℕ} (R : PrescribedRows n ell) (p q : ℕ) (hp hq : Bool) :=
  (if p∈R.primes ∧ hp then p else 1)*(if q∈R.primes ∧ hq then q else 1)

/-- An arbitrary weighted function of a distinct ordinary pair's entries,
the actual target parts and the actual field hit products is a sum over eight
branches, each supported on the signed CRT masks above. The field placement
of the two ordinary rows is arbitrary. -/
theorem prescribed_pair_branch_partition {n ell p q : ℕ} (hn : 2≤n) (hd : 10004≤Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (sieve : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (pp : p∈sieveBand n ell 1) (qp : q∈sieveBand n ell 1) (pq : p≠q) (pe : p≠ell) (qe : q≠ell)
    (r s : ℕ) (R T : PrescribedRows n ell)
    (cover : ∀ U∈[R,T], U.primes⊆{p,q} ∧
      (p∈U.primes → U.residue p ≡ r [MOD p]) ∧ (q∈U.primes → U.residue q ≡ s [MOD q]))
    (a : ℕ) (f : Bool→Bool→ℕ→ℕ→ℕ→ℕ→ℝ) :
    let bp := decide (a ≡ r [MOD p]); let bq := decide (a ≡ s [MOD q])
    let roots := wanted (Fixed.d (n.log2+1)) ell (Fixed.rootBase n)
    f bp bq (targetPart n ell a false) (targetPart n ell a true) (R.hitProduct a) (T.hitProduct a) =
      ∑ hp : Bool,∑ hq : Bool,∑ ht : Bool,
        ((ordinaryTargetBranchMasks p q ell r s roots hp hq ht).map (fun t=>t.weight a)).sum *
          f hp hq (if ht then ell else 1) 1 (R.pairBranchProduct p q hp hq) (T.pairBranchProduct p q hp hq) := by
  classical
  intro bp bq roots
  let bt := hitsTarget n ell a false
  let W (hp hq ht : Bool) := f hp hq (if ht then ell else 1) 1 (R.pairBranchProduct p q hp hq) (T.pairBranchProduct p q hp hq)
  have hits (U : PrescribedRows n ell) (um : U∈[R,T]) : U.hitProduct a=U.pairBranchProduct p q bp bq := by
    obtain ⟨sub,pr,qr⟩ := cover U um
    exact U.hitProduct_on_pair_branch pq sub a r s bp bq pr qr rfl rfl
  have sec := (target_part_residues (n:=n) (by omega) target a).2
  calc
    _ = W bp bq bt := by rw [sec,hits R (by simp),hits T (by simp)];rfl
    _ = ∑ hp : Bool,∑ hq : Bool,∑ ht : Bool,(if bp=hp ∧ bq=hq ∧ bt=ht then (1:ℝ) else 0)*W hp hq ht := by
      cases bp <;> cases bq <;> cases bt <;> simp
    _ = _ := by
      apply sum_congr rfl;intro hp _
      apply sum_congr rfl;intro hq _
      apply sum_congr rfl;intro ht _
      rw [(ordinary_target_branch_masks hn hd composite target sieve pp qp pq pe qe r s hp hq ht).2.2 a]

/-- A clean row can share its prime and residue with no distinct listed row,
including those removed by the stage-one cleanliness test. -/
theorem clean_row_eq_of_labels {s : Marking.Input} {a b : Marking.Row}
    (ha : a∈s.clean) (hb : b∈s.rows) (eqQ : a.q=b.q) (eqR : a.r=b.r) : a=b := by
  rcases a with ⟨side,p,r⟩
  rcases b with ⟨other,q,t⟩
  dsimp only at eqQ eqR
  subst q
  subst t
  have root := (Marking.mem_rows.mp hb).2.2
  have exclude := (Marking.mem_clean.mp ha).2.2
  cases side <;> cases other <;> simp_all

/-- Distinct rows at one prime already have zero raw overlap on every mark as
soon as one row survives cleaning. The other row may be in the deletion set. -/
theorem clean_same_prime_no_overlap {s : Marking.Input} {a b : Marking.Row}
    (ha : a∈s.clean) (hb : b∈s.rows) (eqQ : a.q=b.q) (ne : a≠b) (k : ℕ) :
    ¬(k%a.q=a.r ∧ k%b.q=b.r) := by
  rintro ⟨left,right⟩
  exact ne (clean_row_eq_of_labels ha hb eqQ (left.symm.trans ((congrArg (k%·) eqQ).trans right)))

/-- Distinct retained rows at the same prime have disjoint supports, even when
they come from different fields. The diagonal is exactly the retained row mass. -/
theorem retained_same_prime_gram {s : Marking.Input} {rel : Marking.Relations} (stage : Marking.stageOne s=some rel)
    (i j : Fin rel.rows.length) (prime : (rel.rows.get i).q=(rel.rows.get j).q)
    (w : Fin rel.marks.length → ℝ) :
    ∑ k, w k*((rel.matrix i.succ k:ℝ)*(rel.matrix j.succ k:ℝ)) =
      if i=j then ∑ k,w k*(rel.matrix i.succ k:ℝ) else 0 := by
  classical
  have rows := (Marking.rows_and_guards stage).2.2.2.1
  have clean (k : Fin rel.rows.length) : rel.rows.get k∈s.clean := rows ▸ rel.rows.get_mem k
  have nd : rel.rows.Nodup := by rw [rows]; exact (List.nodup_dedup _).filter _
  split
  next eq =>
    subst j
    apply sum_congr rfl
    intro k _
    simp only [Marking.Relations.matrix,Fin.cases_succ]
    split <;> simp
  next diff =>
    have distinct : (rel.rows.get i).r ≠ (rel.rows.get j).r := fun h=>
      diff (nd.get_inj_iff.mp (clean_row_eq_of_labels (clean i) (Marking.mem_clean.mp (clean j)).1 prime h))
    apply sum_eq_zero
    intro k _
    simp only [Marking.Relations.matrix,Fin.cases_succ,prime]
    split <;> split <;> simp_all

/-- Centering the same-prime block of the retained matrix needs only the
two empirical row masses, for any normalized choice of mark weights. -/
theorem retained_same_prime_covariance {s : Marking.Input} {rel : Marking.Relations} (stage : Marking.stageOne s=some rel)
    (i j : Fin rel.rows.length) (prime : (rel.rows.get i).q=(rel.rows.get j).q)
    (w : Fin rel.marks.length → ℝ) (total : ∑ k,w k=1) :
    let row := fun (a : Fin rel.rows.length) (k : Fin rel.marks.length)=>(rel.matrix a.succ k:ℝ)
    let mass := fun a=>∑ k,w k*row a k
    ∑ k,w k*((row i k-mass i)*(row j k-mass j))=(if i=j then mass i else 0)-mass i*mass j := by
  intro row mass
  have overlap := retained_same_prime_gram stage i j prime w
  change (∑ k,w k*(row i k*row j k))=(if i=j then mass i else 0) at overlap
  calc
    _ = ∑ k, (((w k*(row i k*row j k)-w k*row i k*mass j)-w k*row j k*mass i)+w k*(mass i*mass j)) := by
      apply sum_congr rfl; intro k _; ring
    _ = _ := by
      rw [sum_add_distrib,sum_sub_distrib,sum_sub_distrib,←sum_mul,←sum_mul,←sum_mul,overlap,total]
      change _ - mass i*mass j - mass j*mass i + 1*(mass i*mass j)=_
      ring

end
end Cogentic.Construction
#print axioms Cogentic.Construction.ordinary_target_branch_masks

#print axioms Cogentic.Construction.PrescribedRows.hitProduct_on_pair_branch
#print axioms Cogentic.Construction.target_part_residues

#print axioms Cogentic.Construction.prescribed_pair_branch_partition

#print axioms Cogentic.Construction.ordinary_branch_mesh_mean
