module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T2Fields

@[expose] public section

/-! Shared-path identification of the SP cell data with the Trial literals: Laurent terms, plogs and poles by `decide +kernel`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q2spTs_eq : q2spTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qTn := by decide +kernel
theorem q2spFq_plogs : q2spFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T2.spFq.plogs := by decide +kernel
theorem q2spFq_poles : q2spFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.spFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
