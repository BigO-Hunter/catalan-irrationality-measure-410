module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Fields

@[expose] public section

/-! Shared-path identification of the SP cell data with the Trial literals: Laurent terms, plogs and poles by `decide +kernel`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1spTs_eq : q1spTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qTn := by decide +kernel
theorem q1spFq_plogs : q1spFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T1.spFq.plogs := by decide +kernel
theorem q1spFq_poles : q1spFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.spFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
