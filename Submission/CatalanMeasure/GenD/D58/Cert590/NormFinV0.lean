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
theorem nfV_0 : (((V.drop (4 * 0)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 0 0 := by decide +kernel
theorem nfV_1 : (((V.drop (4 * 1)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 1 0 := by decide +kernel
theorem nfV_2 : (((V.drop (4 * 2)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 2 0 := by decide +kernel
theorem nfV_3 : (((V.drop (4 * 3)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 3 0 := by decide +kernel
theorem nfV_4 : (((V.drop (4 * 4)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 4 0 := by decide +kernel
theorem nfV_5 : (((V.drop (4 * 5)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 5 0 := by decide +kernel
theorem nfV_6 : (((V.drop (4 * 6)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 6 0 := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
