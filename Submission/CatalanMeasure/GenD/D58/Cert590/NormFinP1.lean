module

public import Submission.CatalanMeasure.CellCert.NormClosed
public import Submission.CatalanMeasure.GenD.D58.Cert590.NormFinBounds
public import Submission.CatalanMeasure.GenD.D58.Cert590.Data

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem nfP_7 : (((P.drop (4 * 7)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 7 0 := by decide +kernel
theorem nfP_8 : (((P.drop (4 * 8)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 8 0 := by decide +kernel
theorem nfP_9 : (((P.drop (4 * 9)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 9 0 := by decide +kernel
theorem nfP_10 : (((P.drop (4 * 10)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 10 0 := by decide +kernel
theorem nfP_11 : (((P.drop (4 * 11)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 11 0 := by decide +kernel
theorem nfP_12 : (((P.drop (4 * 12)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 12 0 := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
