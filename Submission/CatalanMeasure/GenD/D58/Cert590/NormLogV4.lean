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
theorem nlV_24 : logUpperOK (((V.drop (2 * 24)).take 2).flatMap (rowTerms V)) (logBsV.getD 24 0) = true := by decide +kernel
theorem nlV_25 : logUpperOK (((V.drop (2 * 25)).take 2).flatMap (rowTerms V)) (logBsV.getD 25 0) = true := by decide +kernel
theorem nlV_26 : logUpperOK (((V.drop (2 * 26)).take 2).flatMap (rowTerms V)) (logBsV.getD 26 0) = true := by decide +kernel
theorem nlV_27 : logUpperOK (((V.drop (2 * 27)).take 2).flatMap (rowTerms V)) (logBsV.getD 27 0) = true := by decide +kernel
theorem nlV_28 : logUpperOK (((V.drop (2 * 28)).take 2).flatMap (rowTerms V)) (logBsV.getD 28 0) = true := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
