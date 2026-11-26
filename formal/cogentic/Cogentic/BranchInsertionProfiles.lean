import Cogentic.PhysicalBranchVariance
import Cogentic.SharedInsertionProfile
import Cogentic.DividedMarkTilts

namespace Cogentic.Construction
open Finset Real Window
open scoped Classical
noncomputable section

/-- The centered and unsigned pair errors both use the variation of one
two-field insertion on the raw integer mesh. -/
private theorem product_mesh_variation (a b : ℕ→ℝ) {M : ℕ} (Mp : 0<M) (D V : ℝ)
    (sup : ∀ j<M, |a j|≤D ∧ |b j|≤D)
    (dv : (∑ j∈range (M-1),|a (j+1)-a j|)≤V ∧ (∑ j∈range (M-1),|b (j+1)-b j|)≤V) :
    |a (M-1)*b (M-1)|+(∑ j∈range (M-1),|a (j+1)*b (j+1)-a j*b j|)≤D^2+2*D*V := by
  have endp := sup (M-1) (by omega)
  have dp := (abs_nonneg _).trans endp.1
  have step j (hj : j∈range (M-1)) :
      |a (j+1)*b (j+1)-a j*b j|≤D*|a (j+1)-a j|+D*|b (j+1)-b j| := by
    have size := mem_range.mp hj
    rw [show a (j+1)*b (j+1)-a j*b j=b j*(a (j+1)-a j)+a (j+1)*(b (j+1)-b j) by ring]
    apply (abs_add_le ..).trans; simp only [abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right (sup j (by omega)).2 (abs_nonneg _))
      (mul_le_mul_of_nonneg_right (sup (j+1) (by omega)).1 (abs_nonneg _))
  have v := sum_le_sum step
  rw [sum_add_distrib,←mul_sum,←mul_sum] at v
  have e := mul_le_mul endp.1 endp.2 (abs_nonneg _) dp
  rw [abs_mul]
  nlinarith only [e,v,mul_le_mul_of_nonneg_left dv.1 dp,mul_le_mul_of_nonneg_left dv.2 dp]

/-- The root of the saddle equation depends only on the point and target branch.
It is shared by every pair of ordinary prime prescriptions. -/
def branchMeshSaddle (n ell a : ℕ) (hit side : Bool) : ℝ :=
  let Y := log ((exactMean n ell a side:ℝ)/(if !side && hit then (ell:ℝ) else 1))
  if h : ∃ α∈Set.Icc (199/200:ℝ) 1, saddleMean (primeBand (n.log2+1)) α=Y then h.choose else 0

private theorem branch_mesh_saddle_eq {n ell a : ℕ} (hit side : Bool) {α : ℝ}
    (aa : α∈Set.Icc (199/200:ℝ) 1)
    (range : InMarkSaddleRange n (saddleMean (primeBand (n.log2+1)) α))
    (eq : saddleMean (primeBand (n.log2+1)) α=log ((exactMean n ell a side:ℝ)/(if !side && hit then (ell:ℝ) else 1))) :
    α=branchMeshSaddle n ell a hit side := by
  let b := n.log2+1
  let Y := log ((exactMean n ell a side:ℝ)/(if !side && hit then (ell:ℝ) else 1))
  have ex : ∃ k∈Set.Icc (199/200:ℝ) 1, saddleMean (primeBand b) k=Y := ⟨α,aa,eq⟩
  rw [branchMeshSaddle,dif_pos ex]
  have dp := Fixed.degree_pos (b:=b) (Nat.succ_pos n.log2)
  have B1 : 1<(Fixed.B b:ℝ) := by exact_mod_cast (Nat.one_lt_pow
    (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero dp.ne' (Nat.succ_ne_zero _))) (by decide) : 1<Fixed.B b)
  have J : ((Ioc ⌊sqrt (Fixed.B b:ℝ)⌋₊ ⌊(Fixed.B b:ℝ)⌋₊).filter Nat.Prime)=primeBand b := by simp [primeBand]
  have un := band_saddle_unique (α:=α) (β:=ex.choose) B1 (by linarith only [aa.1]) (by linarith only [ex.choose_spec.1.1])
  dsimp only at un;rw [J] at un
  exact un ((mul_pos (log_pos B1) (by exact_mod_cast (Nat.mul_pos (by decide : 0<90) dp) : (0:ℝ)<90*(Fixed.d b:ℝ))).trans_le range.1)
    (eq.trans ex.choose_spec.2.symm)

/-- Every common cell branch has the unique saddle in the comparison range. -/
theorem canonical_mesh_saddle_range (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ell∈dyadicTargets (Fixed.beta b) →
    ∀ (c : Option (Bool×Fin (Fixed.d b))) (hit side : Bool) (j : ℕ), j<cellMarkCount b →
    let a := firstCellMark b c+j; let γ := branchMeshSaddle n ell a hit side
    γ∈Set.Icc (199/200:ℝ) 1 ∧ InMarkSaddleRange n (saddleMean (primeBand b) γ) := by
  obtain ⟨b₁,mesh⟩ := constructor_cell_insertion_total_variation line
  obtain ⟨b₂,grow⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ b₂,?_⟩
  intro n ell b big hn target c ht side j jm a γ
  let D := if !side && ht then (ell:ℝ) else 1
  have bp : 1≤(Fixed.B b:ℝ) := by exact_mod_cast (Nat.one_le_two_pow : 1≤Fixed.B b)
  have ep : 1≤(ell:ℝ) := by exact_mod_cast (mem_dyadicTargets.mp target).1.one_le
  have eb : (ell:ℝ)≤Fixed.B b := by exact_mod_cast (mem_dyadicTargets.mp target).2.2
  have bound : 1≤D ∧ D≤Fixed.B b := by dsimp only [D];split <;> aesop
  have lim : D≤(Fixed.A b:ℝ)*(Fixed.B b:ℝ)^40 := bound.2.trans ((le_self_pow₀ bp (by decide)).trans
    (le_mul_of_one_le_left (by positivity) (by exact_mod_cast (Nat.one_le_two_pow : 1≤Fixed.A b))))
  obtain ⟨β,eq,_⟩ := mesh (max_le_iff.mp big).1 hn target c side D bound.1 lim
  have point := (fixed_grid_interval (Fixed.degree_pos (b:=b) (Nat.succ_pos n.log2)) c a
    (mem_Ico.mpr ⟨Nat.le_add_right _ _,Nat.add_lt_add_left jm _⟩)).2
  have win := grid_center_range hn (grow b (max_le_iff.mp big).2) target side point.1 point.2 D bound.1 bound.2
  have rng : InMarkSaddleRange n (saddleMean (primeBand b) (β j)) := (eq j jm).2 ▸ win
  have id := branch_mesh_saddle_eq ht side (eq j jm).1 rng (eq j jm).2
  rw [← show β j=γ from id]
  exact ⟨(eq j jm).1,rng⟩

/-- Markwise two-field insertion profiles on every raw cell and target branch.
Their actual values agree with the physical prescribed mark probabilities'
saddle insertions. Supremum and total variation have polynomial cost independent
of the two observed primes. -/
theorem two_field_branch_profiles (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ell∈dyadicTargets (Fixed.beta b) →
    ∀ {p q : ℕ}, p∈primeBand b → q∈primeBand b → p≠q → ∀ (r s : ℕ) (R T : PrescribedRows n ell),
    (∀ U∈[R,T], U.primes⊆{p,q} ∧ (p∈U.primes → U.residue p ≡ r [MOD p]) ∧ (q∈U.primes → U.residue q ≡ s [MOD q])) →
    let X := univ.biUnion (constructorCellMarks n ell)
    ∀ (α β : ℕ→ℝ), (∀ a∈X, saddleMean (primeBand b) (α a)=log ((exactMean n ell a false:ℝ)/targetPart n ell a false) ∧
      saddleMean (primeBand b) (β a)=log ((exactMean n ell a true:ℝ)/targetPart n ell a true) ∧
      α a∈Set.Icc (199/200:ℝ) 1 ∧ β a∈Set.Icc (199/200:ℝ) 1) →
    let L := firstCellMark b; let M := cellMarkCount b; let d := (Fixed.d b:ℝ)
    let A := 3*(1760*d+4)^4; let V := 40*d^2*(1760*d+4)^4*(24+32*sqrt (110*d))
    let branch := fun a=>(decide (a ≡ r [MOD p]),decide (a ≡ s [MOD q]),hitsTarget n ell a false)
    ∃ γ : Option (Bool×Fin (Fixed.d b))→Bool→Bool→ℕ→ℝ,
      (∀ c ht side j, j<M → γ c ht side j=branchMeshSaddle n ell (L c+j) ht side) ∧
      (∀ c ht side j, j<M → γ c ht side j∈Set.Icc (199/200:ℝ) 1 ∧
        InMarkSaddleRange n (saddleMean (primeBand b) (γ c ht side j))) ∧
      let F := fun c (h : Bool×Bool×Bool) j=>
        fullBandInsertion b (R.pairBranchProduct p q h.1 h.2.1) (γ c h.2.2 false j)*
        fullBandInsertion b (T.pairBranchProduct p q h.1 h.2.1) (γ c h.2.2 true j)
      (∀ c a, a∈constructorCellMarks n ell c → F c (branch a) (a-L c)=
        fullBandInsertion b (R.hitProduct a) (α a)*fullBandInsertion b (T.hitProduct a) (β a)) ∧
      (∀ c h j, j<M → |F c h j|≤A^2) ∧
      ∀ c h, meshVariation (L c) M (fun a=>F c h (a-L c)) ≤ A^2+2*A*V := by
  obtain ⟨b₁,mesh⟩ := constructor_cell_profile_extension line
  obtain ⟨b₂,degrees⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ b₂,?_⟩
  intro n ell b big hn target p q pp qp pq r s R T cover X α β law L M d A V branch
  obtain ⟨one,two⟩ := max_le_iff.mp big
  have hd := degrees b two
  have dp := Fixed.degree_pos (b:=b) (Nat.succ_pos n.log2)
  have ep := (mem_dyadicTargets.mp target).1.pos
  have ec : ell≤Fixed.B b := (mem_dyadicTargets.mp target).2.2
  have bp : 1≤Fixed.B b := Nat.pow_pos (by decide)
  have ac : 1≤Fixed.A b := Nat.pow_pos (by decide)
  let D := fun (hit side : Bool)=>if !side && hit then ell else 1
  have Dcap (hit side) : 1≤D hit side ∧ D hit side≤Fixed.B b := by
    dsimp only [D];split <;> omega
  have large : (Fixed.B b:ℝ)≤(Fixed.A b:ℝ)*(Fixed.B b:ℝ)^40 := by
    have lim := pow_le_pow_right₀ (by exact_mod_cast bp : (1:ℝ)≤Fixed.B b) (by decide : 1≤40)
    rw [pow_one] at lim
    exact lim.trans (le_mul_of_one_le_left (by positivity) (by exact_mod_cast ac))
  have chooseProfiles c ht side := mesh one hn target X α β law c side (D ht side) (by exact_mod_cast (Dcap ht side).1)
    ((by exact_mod_cast (Dcap ht side).2 : (D ht side:ℝ)≤Fixed.B b).trans large)
  choose γ hg hb using chooseProfiles
  have ranges c ht side j (jm : j<M) : γ c ht side j∈Set.Icc (199/200:ℝ) 1 ∧
      InMarkSaddleRange n (saddleMean (primeBand b) (γ c ht side j)) := by
    have cellLaw :=  hg c ht side j jm
    have point := (fixed_grid_interval dp c (L c+j) (mem_Ico.mpr ⟨Nat.le_add_right ..,Nat.add_lt_add_left jm _⟩)).2
    exact ⟨cellLaw.1,cellLaw.2.1 ▸ grid_center_range hn hd target side point.1 point.2 (D ht side)
      (by exact_mod_cast (Dcap ht side).1) (by exact_mod_cast (Dcap ht side).2)⟩
  refine ⟨γ,?_,ranges,?_⟩
  · intro c ht side j jm
    apply branch_mesh_saddle_eq ht side (ranges c ht side j jm).1 (ranges c ht side j jm).2
    simpa only [D,Nat.cast_ite,Nat.cast_one] using (hg c ht side j jm).2.1
  intro F
  let G := fun (U : PrescribedRows n ell) c (h : Bool×Bool×Bool) side j=>
    fullBandInsertion b (U.pairBranchProduct p q h.1 h.2.1) (γ c h.2.2 side j)
  have size (U : PrescribedRows n ell) (i j : Bool) : 0<U.pairBranchProduct p q i j ∧
      U.pairBranchProduct p q i j≤(Fixed.B b)^2 := by
    dsimp only [PrescribedRows.pairBranchProduct]
    have bit (k : ℕ) (kin : k∈primeBand b) (h : Bool) :
        0<(if k∈U.primes ∧ h then k else 1) ∧ (if k∈U.primes ∧ h then k else 1)≤Fixed.B b := by
      split <;> first | exact ⟨(mem_primeBand.mp kin).1.pos,(mem_primeBand.mp kin).2.1⟩ | exact ⟨by decide,bp⟩
    exact ⟨Nat.mul_pos (bit p pp i).1 (bit q qp j).1,(Nat.mul_le_mul (bit p pp i).2 (bit q qp j).2).trans_eq (sq _).symm⟩
  have single (U : PrescribedRows n ell) c (h : Bool×Bool×Bool) side :=
    hb c h.2.2 side (U.pairBranchProduct p q h.1 h.2.1) (size U _ _).1 (by
      have e := log_le_log (Nat.cast_pos.mpr (size U h.1 h.2.1).1 : (0:ℝ)<U.pairBranchProduct p q h.1 h.2.1)
        (by exact_mod_cast (size U h.1 h.2.1).2 : (U.pairBranchProduct p q h.1 h.2.1:ℝ)≤(Fixed.B b:ℝ)^2)
      simpa only [log_pow,Nat.cast_ofNat] using e)
  refine ⟨?_,?_,?_⟩
  · intro c a ha
    have am : a∈X := mem_biUnion.mpr ⟨c,mem_univ _,ha⟩
    have loc := mem_Ico.mp (mem_filter.mp ha).1
    let j := a-L c
    have eq : L c+j=a := Nat.add_sub_of_le (show L c≤a from loc.1)
    have jm : j<M := by have upper : a<L c+M := loc.2;dsimp only [j];omega
    have sidePart (side : Bool) : (targetPart n ell a side:ℝ)=D (branch a).2.2 side := by
      cases side
      · simp [targetPart,D,branch]
      · simp [D,(target_part_residues ((by decide : 3≤10004).trans hd) target a).2]
    have eqS (side : Bool) : γ c (branch a).2.2 side j=(if side then β a else α a) := by
      have src := (hg c (branch a).2.2 side j jm).2.2
      rw [eq] at src; exact src am (sidePart side)
    have eqQ (U : PrescribedRows n ell) (um : U∈[R,T]) : U.hitProduct a=U.pairBranchProduct p q (branch a).1 (branch a).2.1 :=
      U.hitProduct_on_pair_branch pq (cover U um).1 a r s _ _ (cover U um).2.1 (cover U um).2.2 rfl rfl
    dsimp only [F];rw [←eqQ R (by simp),←eqQ T (by simp),eqS false,eqS true];rfl
  · intro c h j jm
    dsimp only [F];rw [abs_mul,pow_two]
    exact mul_le_mul ((single R c h false).1 j jm) ((single T c h true).1 j jm) (abs_nonneg _) (by dsimp [A];positivity)
  · intro c h
    have pair := product_mesh_variation (G R c h false) (G T c h true) (show 0<M from Nat.pow_pos (by decide : 0<2)) A V
      (fun j jm=>⟨(single R c h false).1 j jm,(single T c h true).1 j jm⟩)
      ⟨(single R c h false).2,(single T c h true).2⟩
    simpa only [meshVariation,Nat.add_sub_cancel_left] using pair

end
end Cogentic.Construction
#print axioms Cogentic.Construction.two_field_branch_profiles
