module

public import Submission.CatalanMeasure.GenD.D58.Cert590.ZDefs

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem uVcN_c3 : uClenN (((((Vc.reverse).drop 40).drop 40).drop 40).take 40) uVcN3 = uVcN4 := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
