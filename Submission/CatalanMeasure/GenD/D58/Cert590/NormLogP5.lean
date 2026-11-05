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
theorem nlP_29 : logUpperOK (((P.drop (2 * 29)).take 2).flatMap (rowTerms P)) (logBsP.getD 29 0) = true := by decide +kernel
theorem nlP_30 : logUpperOK (((P.drop (2 * 30)).take 2).flatMap (rowTerms P)) (logBsP.getD 30 0) = true := by decide +kernel
theorem nlP_31 : logUpperOK (((P.drop (2 * 31)).take 2).flatMap (rowTerms P)) (logBsP.getD 31 0) = true := by decide +kernel
theorem nlP_32 : logUpperOK (((P.drop (2 * 32)).take 2).flatMap (rowTerms P)) (logBsP.getD 32 0) = true := by decide +kernel
theorem nlP_33 : logUpperOK (((P.drop (2 * 33)).take 2).flatMap (rowTerms P)) (logBsP.getD 33 0) = true := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
