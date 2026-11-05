module

public import Submission.CatalanMeasure.GenD.D58.Cert590.ZDefs

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem uPcN_c0 : uClenN ((Pc.reverse).take 40) ([], []) = uPcN1 := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
