module

public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Blocks
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1BlockR
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Fields.P4

/-! Trial 1: the cell fields (`FieldQ` literals) of the seven field classes and the identifications `hid`. -/

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Trial.T1
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
open CatalanMeasure.Cert (TailQ)

set_option maxRecDepth 1000000
set_option Elab.async false


theorem spmFq_eq : spmFq = spmFQ trial (sqFQ (53 / 58)) pT aS rS bS rr (10 / 29) (11 / 8) ((1 : ℚ) / 200) := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Trial.T1
