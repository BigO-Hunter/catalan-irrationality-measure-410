module

public import Submission.CatalanMeasure.GenD.D58.Cert590.YTab
public import Submission.CatalanMeasure.GenD.D58.Cert590.ZChain
public import Submission.CatalanMeasure.CellCert.PolyZ
public import Submission.CatalanMeasure.GenD.D58.Cert590.Data

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem D_Y_Z : D_Y.toD.Z = colZ Vc := by
  rw [PolyDataS.toD_Z, colZ, uSum_Vc]
  exact shl_eq_of_zsc _ _ 2 (by decide +kernel)
theorem hZ_Y : ∀ x : ℝ, 2 * finUR Vc x = ptZ D_Y.toD.Z 0 x := by
  intro x
  rw [D_Y_Z]
  exact colZ_spec Vc x
end CatalanMeasure.GenD.D58.Cert590
