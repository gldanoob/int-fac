import Cogentic.RawGridModel
import Cogentic.RetainedArchRank

namespace Cogentic.Construction
open Real Finset
noncomputable section

/-- Physical position of the `j`th integer in one of the construction's
ordered raw mesh cells. -/
def rawGridPoint (b : ℕ) (c : Option (Fin (2*Fixed.d b))) (j : Fin (cellMarkCount b)) : ℝ :=
  ((firstCellMark b (c.map gridPlace)+(j:ℕ):ℕ):ℝ)/Fixed.A b

/-- The normalized uniform measure on raw positions supplies the archimedean
part of the reference Gram margin. Any eventual empirical comparison may use
the same mass on every cell. -/
theorem raw_grid_average_energy {b : ℕ} (big : 130000≤Fixed.d b) :
    let d := Fixed.d b; let M := cellMarkCount b
    let C := Option (Fin (2*d)); let Z := C×Fin M
    let cells := (2*d+1:ℝ)
    let p := (M:ℝ)⁻¹/cells
    ∀ (v₀ : ℝ) (v : Fin (2*d)→ℝ) (m Q : Z→ℝ) (F : ℝ), 0≤F →
    let g := fun a : Z=>v₀+∑ j,log |rawGridPoint b a.1 a.2-nominalCenter d j| *v j
    let arch := v₀^2+∑ j,(v j)^2
    (∀ a, (m a)^2≤120000*(d:ℝ)*F ∧ (g a+m a)^2+(13/16)*F≤Q a) →
    F+arch≤768*(10000*(d:ℝ))*cells*(∑ a,p*Q a) := by
  intro d M C Z cells p v₀ v m Q F fp g arch localBd
  let cell := fun c : C=>c.map gridPlace
  have dp : 1≤d := by change 130000≤d at big;omega
  have mp : (0:ℝ)<M := by dsimp only [M,cellMarkCount];positivity
  have cp : 1≤cells := by dsimp only [cells];linarith only [Nat.cast_nonneg (α:=ℝ) d]
  have pn : 0≤p := by dsimp only [p];positivity
  have sumP : (∑ _a : Z,p)=1 := by
    simp only [sum_const,card_univ,nsmul_eq_mul,Z,Fintype.card_prod,C,Fintype.card_option,Fintype.card_fin]
    push_cast
    dsimp only [p,cells]
    field_simp [mp.ne',show (2*(d:ℝ)+1)≠0 by positivity]
  have actual (c : C) (j : Fin M) :
      (gridCellLeft b (cell c):ℝ)≤rawGridPoint b c j ∧ rawGridPoint b c j≤(gridCellLeft b (cell c):ℝ)+(Fixed.invWidth b:ℝ)⁻¹ ∧
      firstCellMark b (cell c)+j.val≤Fixed.A b := by
    have hm := fixed_grid_interval_bounds dp (cell c) _ (mem_Ico.mpr
      ⟨Nat.le_add_right _ j.val,Nat.add_lt_add_left j.isLt _⟩)
    have lo := (Rat.cast_le (K:=ℝ)).mpr hm.1.1
    have hi := (Rat.cast_le (K:=ℝ)).mpr hm.1.2
    push_cast at lo hi
    refine ⟨?_,?_,hm.2.2.1⟩ <;> simpa only [rawGridPoint,cell,Nat.cast_add] using ‹_›
  have base (j : Fin M) : 3/4≤rawGridPoint b none j ∧ rawGridPoint b none j≤1 := by
    have loc := actual none j
    refine ⟨by simpa [cell,gridCellLeft] using loc.1,?_⟩
    apply (div_le_one (by dsimp [Fixed.A];positivity : 0<(Fixed.A b:ℝ))).mpr
    exact_mod_cast loc.2.2
  have inner (i : Fin (2*d)) (j : Fin M) :
      nominalCenter d i+(Fixed.invWidth b:ℝ)⁻¹ ≤ rawGridPoint b (some i) j ∧
      rawGridPoint b (some i) j≤nominalCenter d i+2*(Fixed.invWidth b:ℝ)⁻¹ := by
    have loc := actual (some i) j
    rw [gridPlace_center]
    rcases id : gridPlace i with ⟨side,k⟩
    simp only [cell,Option.map_some,id,gridCellLeft,Rat.cast_add,Rat.cast_inv,Rat.cast_natCast] at loc
    exact ⟨loc.1,by linarith only [loc.2.1]⟩
  let pos := fun c : C=>rawGridPoint b c
  let mass := fun (_ : C) (_ : Fin M)=>(M:ℝ)⁻¹
  have grid := fixed_nominal_grid_energy big (β:=fun _=>Fin M) pos mass base inner
    (fun _ _=>inv_nonneg.mpr mp.le) (fun _=>by simp [mass,mp.ne']) v₀ v
  have weighted : arch≤3*cells*(∑ a : Z,p*(g a)^2) := by
    have cancel : cells*p=(M:ℝ)⁻¹ := by dsimp only [p];field_simp [show cells≠0 by linarith only [cp]]
    rw [mul_assoc,mul_sum,Fintype.sum_prod_type]
    simp only [←mul_assoc,cancel,C,Fintype.sum_option]
    exact grid
  have avgMean := sum_le_sum (s:=univ) (fun (a:Z) _=>mul_le_mul_of_nonneg_left (localBd a).1 pn)
  have avgEnergy := sum_le_sum (s:=univ) (fun (a:Z) _=>mul_le_mul_of_nonneg_left (localBd a).2 pn)
  rw [←sum_mul,sumP,one_mul] at avgMean
  simp only [mul_add,sum_add_distrib,←sum_mul,sumP,one_mul] at avgEnergy
  have dr : (1:ℝ)≤d := by exact_mod_cast dp
  apply centered_model_margin (fun _ : Z=>p) g m (10000*d) cells F arch
    ((15/16)*F) (F/16) (F/16) (∑ a,p*Q a) 0 (fun _=>pn)
    (by linarith only [dr]) cp fp weighted _ (by linarith) (by linarith) (by linarith) _ _
  · linarith only [avgMean]
  · linarith only [avgEnergy]
  · dsimp only [arch];nlinarith only [sq_nonneg v₀,fp,sum_nonneg (s:=univ) (fun j _=>sq_nonneg (v j))]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.raw_grid_average_energy
