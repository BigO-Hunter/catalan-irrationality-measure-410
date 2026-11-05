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
theorem nlV_0 : logUpperOK (((V.drop (2 * 0)).take 2).flatMap (rowTerms V)) (logBsV.getD 0 0) = true := by decide +kernel
theorem nlV_1 : logUpperOK (((V.drop (2 * 1)).take 2).flatMap (rowTerms V)) (logBsV.getD 1 0) = true := by decide +kernel
theorem nlV_2 : logUpperOK (((V.drop (2 * 2)).take 2).flatMap (rowTerms V)) (logBsV.getD 2 0) = true := by decide +kernel
theorem nlV_3 : logUpperOK (((V.drop (2 * 3)).take 2).flatMap (rowTerms V)) (logBsV.getD 3 0) = true := by decide +kernel
theorem nlV_4 : logUpperOK (((V.drop (2 * 4)).take 2).flatMap (rowTerms V)) (logBsV.getD 4 0) = true := by decide +kernel
theorem nlV_5 : logUpperOK (((V.drop (2 * 5)).take 2).flatMap (rowTerms V)) (logBsV.getD 5 0) = true := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
