module

public import Submission.CatalanMeasure.GenD.D58.Cert590.RTab
public import Submission.CatalanMeasure.GenD.D58.Cert590.ZChain
public import Submission.CatalanMeasure.CellCert.PolyZ
public import Submission.CatalanMeasure.GenD.D58.Cert590.Data

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem D_R_Z : D_R.toD.Z = resZ Pc := by
  rw [PolyDataS.toD_Z, resZ, uSum_Pc]
  exact shl_eq_of_zsc _ _ (-2) (by decide +kernel)
theorem hZ_R : ∀ x : ℝ, -2 * finUR Pc x = ptZ D_R.toD.Z 0 x := by
  intro x
  rw [D_R_Z]
  exact resZ_spec Pc x
end CatalanMeasure.GenD.D58.Cert590
