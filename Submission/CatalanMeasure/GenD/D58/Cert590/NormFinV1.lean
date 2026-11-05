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
theorem nfV_7 : (((V.drop (4 * 7)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 7 0 := by decide +kernel
theorem nfV_8 : (((V.drop (4 * 8)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 8 0 := by decide +kernel
theorem nfV_9 : (((V.drop (4 * 9)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 9 0 := by decide +kernel
theorem nfV_10 : (((V.drop (4 * 10)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 10 0 := by decide +kernel
theorem nfV_11 : (((V.drop (4 * 11)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 11 0 := by decide +kernel
theorem nfV_12 : (((V.drop (4 * 12)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 12 0 := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
