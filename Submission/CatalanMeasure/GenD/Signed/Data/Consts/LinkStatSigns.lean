module

public import Submission.CatalanMeasure.CellCert.RawInts
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.PolyPos
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkSigns
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkStatP

@[expose] public section

namespace CatalanMeasure.Signed.Consts
open CatalanMeasure.CellCert CatalanMeasure.Cert

set_option maxRecDepth 1000000
set_option Elab.async false

open CatalanMeasure.Signed

theorem Cp_stat : Hq gCp (1 / 2 ^ 20) * (3 / 1000) ≤ ((58331170863990251 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem Cm_stat : Hq gCm (1 / 2 ^ 20) * (3 / 1000) ≤ ((58331170863990251 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
end CatalanMeasure.Signed.Consts
