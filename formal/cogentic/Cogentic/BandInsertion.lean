import Cogentic.CleanWindows
import Cogentic.WindowSaddle

namespace Cogentic.Construction
open Real Window
noncomputable section

/-- Full-band insertion at the saddle determined by a mark's unprescribed mean. -/
def fullBandInsertion (b Q : ℕ) (α : ℝ) : ℝ :=
  let M := shiftedMass (primeBand b) (primeProbability α) (fun p => log p) (log (Fixed.B b))
  (Q:ℝ)^(1-α) * (M (log Q)/M 0)

end
end Cogentic.Construction
