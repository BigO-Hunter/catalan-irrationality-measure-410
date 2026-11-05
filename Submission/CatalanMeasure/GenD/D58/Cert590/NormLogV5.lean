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
theorem nlV_29 : logUpperOK (((V.drop (2 * 29)).take 2).flatMap (rowTerms V)) (logBsV.getD 29 0) = true := by decide +kernel
theorem nlV_30 : logUpperOK (((V.drop (2 * 30)).take 2).flatMap (rowTerms V)) (logBsV.getD 30 0) = true := by decide +kernel
theorem nlV_31 : logUpperOK (((V.drop (2 * 31)).take 2).flatMap (rowTerms V)) (logBsV.getD 31 0) = true := by decide +kernel
theorem nlV_32 : logUpperOK (((V.drop (2 * 32)).take 2).flatMap (rowTerms V)) (logBsV.getD 32 0) = true := by decide +kernel
theorem nlV_33 : logUpperOK (((V.drop (2 * 33)).take 2).flatMap (rowTerms V)) (logBsV.getD 33 0) = true := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
