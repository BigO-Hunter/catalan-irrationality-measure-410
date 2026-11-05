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
theorem nfV_13 : (((V.drop (4 * 13)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 13 0 := by decide +kernel
theorem nfV_14 : (((V.drop (4 * 14)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 14 0 := by decide +kernel
theorem nfV_15 : (((V.drop (4 * 15)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 15 0 := by decide +kernel
theorem nfV_16 : (((V.drop (4 * 16)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 16 0 := by decide +kernel
theorem nfV_17 : (((V.drop (4 * 17)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 17 0 := by decide +kernel
theorem nfV_18 : (((V.drop (4 * 18)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD 18 0 := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
