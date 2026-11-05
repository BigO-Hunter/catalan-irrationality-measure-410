module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T0Fields

@[expose] public section

/-! Shared-path identification of the SP cell data with the Trial literals: Laurent terms, plogs and poles by `decide +kernel`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q0spTs_eq : q0spTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qTn := by decide +kernel
theorem q0spFq_plogs : q0spFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq.plogs := by decide +kernel
theorem q0spFq_poles : q0spFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
