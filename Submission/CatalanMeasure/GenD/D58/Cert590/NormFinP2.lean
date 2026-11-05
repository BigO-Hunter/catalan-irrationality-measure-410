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
theorem nfP_13 : (((P.drop (4 * 13)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 13 0 := by decide +kernel
theorem nfP_14 : (((P.drop (4 * 14)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 14 0 := by decide +kernel
theorem nfP_15 : (((P.drop (4 * 15)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 15 0 := by decide +kernel
theorem nfP_16 : (((P.drop (4 * 16)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 16 0 := by decide +kernel
theorem nfP_17 : (((P.drop (4 * 17)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 17 0 := by decide +kernel
theorem nfP_18 : (((P.drop (4 * 18)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD 18 0 := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
