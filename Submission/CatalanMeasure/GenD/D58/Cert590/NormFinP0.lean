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
theorem nfP_0 : (((P.drop (4 * 0)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 0 0 := by decide +kernel
theorem nfP_1 : (((P.drop (4 * 1)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 1 0 := by decide +kernel
theorem nfP_2 : (((P.drop (4 * 2)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 2 0 := by decide +kernel
theorem nfP_3 : (((P.drop (4 * 3)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 3 0 := by decide +kernel
theorem nfP_4 : (((P.drop (4 * 4)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 4 0 := by decide +kernel
theorem nfP_5 : (((P.drop (4 * 5)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 5 0 := by decide +kernel
theorem nfP_6 : (((P.drop (4 * 6)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 6 0 := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
