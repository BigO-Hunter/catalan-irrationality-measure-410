module

public import Submission.CatalanMeasure.CellCert.NormClosed
public import Submission.CatalanMeasure.GenD.D58.Cert590.NormLogBounds
public import Submission.CatalanMeasure.GenD.D58.Cert590.Data

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem nlV_34 : logUpperOK (((V.drop (2 * 34)).take 2).flatMap (rowTerms V)) (logBsV.getD 34 0) = true := by decide +kernel
theorem nlV_35 : logUpperOK (((V.drop (2 * 35)).take 2).flatMap (rowTerms V)) (logBsV.getD 35 0) = true := by decide +kernel
theorem nlV_36 : logUpperOK (((V.drop (2 * 36)).take 2).flatMap (rowTerms V)) (logBsV.getD 36 0) = true := by decide +kernel
theorem nlV_37 : logUpperOK (((V.drop (2 * 37)).take 2).flatMap (rowTerms V)) (logBsV.getD 37 0) = true := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
