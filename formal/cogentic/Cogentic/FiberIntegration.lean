import Cogentic.PolynomialProbability

namespace Cogentic.Construction
open Real Cogentic.Window
noncomputable section

/-- Integrating lower and upper conditional probabilities on each selected
first observation gives the same bounds times the true first-event mass. -/
theorem PrescribedRows.integrate_fiber_bounds {n ell a : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (cap : a≤Fixed.A (n.log2+1))
    (side : Bool) (F : ℤ→Prop) [DecidablePred F] (E : ℤ×ℤ→Prop) [DecidablePred E]
    (lo hi : ℝ) (bounds : ∀ u v : ℤ, R.compatible side u v →
      let x := u+a*v; let m := prodPrimes (R.miss a)
      let y := fun j : ℤ => v+(m:ℤ)*j
      let key := fun j : ℤ => (x-a*y j,y j)
      let G := fun j : ℤ => coefficientWeight n (key j)
      F x → (∑' j, if E (key j) then G j else 0)/(∑' j,G j)∈Set.Icc lo hi) :
    let A := fun k : ℤ×ℤ => F (k.1+(a:ℤ)*k.2)
    let P := prescribedProbability R side A
    prescribedProbability R side (fun k => A k ∧ E k)∈Set.Icc (lo*P) (hi*P) := by
  classical
  intro A P
  let M := prodPrimes (R.miss a)
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  let Z := ∑' k : C, coefficientWeight n k.val
  obtain ⟨c,r,e,coords,ws,zp,_,events⟩ := R.coefficient_law target side cap
  let x := fun i : ℤ => c+(R.hitProduct a:ℤ)*i
  let y := fun i j : ℤ => r i+(M:ℤ)*j
  let key := fun i j : ℤ => (x i-(a:ℤ)*y i j,y i j)
  let W (k : ℤ×ℤ) := coefficientWeight n (key k.1 k.2)
  let V (Q : ℤ×ℤ→Prop) [DecidablePred Q] (k : ℤ×ℤ) := if Q (key k.1 k.2) then W k else 0
  let both := fun k : ℤ×ℤ => A k ∧ E k
  have wp (k : ℤ×ℤ) : 0<W k := mul_pos (exp_pos _) (exp_pos _)
  have summ : Summable W := ws.congr (fun _ => (coefficient_weight_projection ..).symm)
  have vs (Q : ℤ×ℤ→Prop) [DecidablePred Q] : Summable (V Q) := Summable.of_nonneg_of_le
    (fun k => by dsimp only [V]; split <;> first | exact (wp k).le | rfl)
    (fun k => by dsimp only [V]; split <;> first | exact (wp k).le | rfl) summ
  have prob (Q : ℤ×ℤ→Prop) [DecidablePred Q] : prescribedProbability R side Q=(∑' k,V Q k)/Z := by
    have h := events Q
    change prescribedProbability R side Q=(∑' k,_)/Z at h
    rw [h]
    congr 1
    apply tsum_congr
    intro k
    dsimp only [V,W]
    split <;> first | exact (coefficient_weight_projection ..).symm | rfl
  have fiber (i : ℤ) : (∑' j : ℤ,V both (i,j)) ∈
      Set.Icc (lo*(∑' j : ℤ,V A (i,j))) (hi*(∑' j : ℤ,V A (i,j))) := by
    let seed := (x i-(a:ℤ)*r i,r i)
    have ok := (e (i,0)).property
    rw [coords] at ok
    simp only [mul_zero,add_zero] at ok
    have obs (j : ℤ) : (key i j).1+(a:ℤ)*(key i j).2=x i := sub_add_cancel ..
    by_cases hit : F (x i)
    · have raw := bounds seed.1 seed.2 ok
      have atX : seed.1+(a:ℤ)*seed.2=x i := sub_add_cancel ..
      dsimp only at raw
      rw [atX] at raw
      have q := raw hit
      change (∑' j : ℤ,V E (i,j))/(∑' j : ℤ,W (i,j))∈Set.Icc lo hi at q
      have denom : 0<∑' j : ℤ,W (i,j) := (wp (i,0)).trans_le ((summ.prod_factor i).le_tsum 0 (fun j _ => (wp _).le))
      have oa (j : ℤ) : V A (i,j)=W (i,j) := if_pos (by simpa only [A,obs] using hit)
      have ob (j : ℤ) : V both (i,j)=V E (i,j) := by simp only [V,both,A,obs,hit,true_and]
      simp_rw [oa,ob]
      exact ⟨(le_div_iff₀ denom).mp q.1,(div_le_iff₀ denom).mp q.2⟩
    · have oa (j : ℤ) : V A (i,j)=0 := if_neg (by simpa only [A,obs] using hit)
      have ob (j : ℤ) : V both (i,j)=0 := if_neg (fun t => hit (by simpa only [A,obs] using t.1))
      simp [oa,ob]
  change prescribedProbability R side both∈Set.Icc (lo*prescribedProbability R side A) (hi*prescribedProbability R side A)
  rw [prob both,prob A,←mul_div_assoc,←mul_div_assoc]
  constructor
  · apply (div_le_div_iff_of_pos_right zp).mpr
    rw [(vs A).tsum_prod,(vs both).tsum_prod,←tsum_mul_left]
    exact ((vs A).prod.mul_left _).tsum_le_tsum (fun i => (fiber i).1) (vs both).prod
  · apply (div_le_div_iff_of_pos_right zp).mpr
    rw [(vs A).tsum_prod,(vs both).tsum_prod,←tsum_mul_left]
    exact (vs both).prod.tsum_le_tsum (fun i => (fiber i).2) ((vs A).prod.mul_left _)

end
end Cogentic.Construction
