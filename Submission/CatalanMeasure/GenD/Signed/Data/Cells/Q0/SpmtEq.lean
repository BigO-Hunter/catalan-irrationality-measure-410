module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmtFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T0Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the SPM_TOP data (trial 0) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q0spmtTs_eq : q0spmtTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qTn := by decide +kernel
theorem q0spmtTsM_eq : q0spmtTsM = mergeL q0spmtTs := by decide +kernel
theorem q0spmtFq_poles : q0spmtFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T0.spmFq.poles := by decide +kernel
theorem q0spmtFq_plogs : q0spmtFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T0.spmFq.plogs.take 38 := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
