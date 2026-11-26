import Cogentic.CommonWeightTransfer
import Cogentic.InsertionVariation

namespace Cogentic.Construction
open Finset Real Window
noncomputable section

/-- Extend any genuine markwise saddle solution to the full integer mesh on each
fixed target branch; the variation bounds hold for the same extended solution. -/
theorem constructor_cell_profile_extension (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ell∈dyadicTargets (Fixed.beta b) →
    ∀ (X : Finset ℕ) (α β : ℕ→ℝ),
    (∀ a∈X, saddleMean (primeBand b) (α a)=log ((exactMean n ell a false:ℝ)/targetPart n ell a false) ∧
      saddleMean (primeBand b) (β a)=log ((exactMean n ell a true:ℝ)/targetPart n ell a true) ∧
      α a∈Set.Icc (199/200:ℝ) 1 ∧ β a∈Set.Icc (199/200:ℝ) 1) →
      ∀ (cell : Option (Bool×Fin (Fixed.d b))) (side : Bool) (D : ℝ), 1≤D → D≤(Fixed.A b:ℝ)*(Fixed.B b:ℝ)^40 →
        let L := firstCellMark b cell; let M := cellMarkCount b
        let H := log (Fixed.B b:ℝ); let d := (Fixed.d b:ℝ)
        ∃ γ : ℕ→ℝ, (∀ j < M, γ j∈Set.Icc (199/200:ℝ) 1 ∧
          saddleMean (primeBand b) (γ j)=log ((exactMean n ell (L+j) side:ℝ)/D) ∧
          (L+j∈X → (targetPart n ell (L+j) side:ℝ)=D → γ j=(if side then β (L+j) else α (L+j)))) ∧
          ∀ Q : ℕ, 0<Q → log Q≤2*H →
          (∀ j < M, |fullBandInsertion b Q (γ j)|≤3*(1760*d+4)^4) ∧
          (∑ j∈range (M-1),|fullBandInsertion b Q (γ (j+1))-fullBandInsertion b Q (γ j)|) ≤
            40*d^2*(1760*d+4)^4*(24+32*sqrt (110*d)) := by
  obtain ⟨b₂,profiles⟩ := constructor_cell_insertion_total_variation line
  obtain ⟨b₃,degrees⟩ := Fixed.degree_grows 10004
  refine ⟨max b₂ b₃,?_⟩
  intro n ell b large hn target X α β physical
  obtain ⟨two,three⟩ := max_le_iff.mp large
  intro cell side D dl du L M H d
  obtain ⟨γ,grid,bounds⟩ := profiles two hn target cell side D dl du
  refine ⟨γ,?_,bounds⟩
  intro j jm
  have g := grid j jm
  refine ⟨g.1,g.2,?_⟩
  intro am fixed
  let a := L+j
  let x := if side then β a else α a
  have ph := physical a am
  have px : x∈Set.Icc (199/200:ℝ) 1 ∧ saddleMean (primeBand b) x=log ((exactMean n ell a side:ℝ)/D) := by
    cases side
    · exact ⟨ph.2.2.1,fixed ▸ ph.1⟩
    · exact ⟨ph.2.2.2,fixed ▸ ph.2.1⟩
  have dp : 0<Fixed.d b := Fixed.degree_pos (Nat.succ_pos n.log2)
  have B1 : (1:ℝ)<Fixed.B b := by exact_mod_cast (Nat.one_lt_pow
    (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero dp.ne' (Nat.succ_ne_zero _))) (by decide) : 1<Fixed.B b)
  have included : a∈Ico L (L+M) := mem_Ico.mpr ⟨Nat.le_add_right ..,Nat.add_lt_add_left jm L⟩
  have mesh := fixed_grid_interval dp cell a included
  have win := one_point_window hn (degrees b three) target mesh.2.1 mesh.2.2 side D ⟨dl,du⟩
  have pos : 0<log ((exactMean n ell a side:ℝ)/D) :=
    (div_pos_iff_of_pos_right (log_pos B1)).mp
      ((by exact_mod_cast (Nat.mul_pos (by decide : 0<90) dp) : (0:ℝ)<90*(Fixed.d b:ℝ)).trans_le win.2.2.1)
  have J : ((Ioc ⌊sqrt (Fixed.B b:ℝ)⌋₊ ⌊(Fixed.B b:ℝ)⌋₊).filter Nat.Prime)=primeBand b := by simp [primeBand]
  have unique := band_saddle_unique (α:=γ j) (β:=x) B1 (by linarith only [g.1.1]) (by linarith only [px.1.1])
  dsimp only at unique
  rw [J] at unique
  exact unique (g.2 ▸ pos) (g.2.trans px.2.symm)

/-- The physical second-moment comparison uses one pair of markwise saddles on
the whole eligible set, including pairs in different cells. On each fixed
target-part branch the same saddles extend to the integer mesh with uniform
supremum and variation bounds for all ordinary hit products. -/
theorem common_weight_cell_profiles (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ X : Finset ℕ, (∀ a∈X, a∈(construct n ell 0 0 0 0).marks) →
    ∃ α β : ℕ→ℝ,
      (∀ (R T : PrescribedRows n ell) (f : ℕ→ℝ),
        let O := PrescribedRows.unrestricted n ell
        let J := fun a=>fullBandInsertion b (R.hitProduct a) (α a)*fullBandInsertion b (T.hitProduct a) (β a)
        let p := smoothMarkProbability R T
        let E := smoothMarkEvent R false; let F := smoothMarkEvent T true
        twoFieldSecond R T X (fun a=>f a/smoothMarkProbability O O a-f a*(J a/p a)) E F ≤
          (C*exp (-K*(Fixed.z b:ℝ)^2))^2*twoFieldSecond R T X (fun a=>|f a| *(J a/p a)) E F) ∧
      ∀ (cell : Option (Bool×Fin (Fixed.d b))) (side : Bool) (D : ℝ), 1≤D → D≤(Fixed.A b:ℝ)*(Fixed.B b:ℝ)^40 →
        let L := firstCellMark b cell; let M := cellMarkCount b
        let H := log (Fixed.B b:ℝ); let d := (Fixed.d b:ℝ)
        ∃ γ : ℕ→ℝ, (∀ j < M, γ j∈Set.Icc (199/200:ℝ) 1 ∧
          saddleMean (primeBand b) (γ j)=log ((exactMean n ell (L+j) side:ℝ)/D) ∧
          (L+j∈X → (targetPart n ell (L+j) side:ℝ)=D → γ j=(if side then β (L+j) else α (L+j)))) ∧
          ∀ Q : ℕ, 0<Q → log Q≤2*H →
          (∀ j < M, |fullBandInsertion b Q (γ j)|≤3*(1760*d+4)^4) ∧
          (∑ j∈range (M-1),|fullBandInsertion b Q (γ (j+1))-fullBandInsertion b Q (γ j)|) ≤
            40*d^2*(1760*d+4)^4*(24+32*sqrt (110*d)) := by
  obtain ⟨C,cp,b₁,transfer⟩ := common_weight_second_transfer line K hk
  obtain ⟨b₂,profiles⟩ := constructor_cell_profile_extension line
  refine ⟨C,cp,max b₁ b₂,?_⟩
  intro n ell b large hn composite target sieve X marks
  obtain ⟨one,two⟩ := max_le_iff.mp large
  obtain ⟨α,β,physical,law⟩ := transfer one hn composite target sieve X marks
  exact ⟨α,β,law,profiles two hn target X α β physical⟩

end
end Cogentic.Construction
#print axioms Cogentic.Construction.common_weight_cell_profiles
