module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmtFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T2Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the SPM_TOP data (trial 2) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q2spmtTs_eq : q2spmtTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qTn := by decide +kernel
theorem q2spmtTsM_eq : q2spmtTsM = mergeL q2spmtTs := by decide +kernel
theorem q2spmtFq_poles : q2spmtFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.spmFq.poles := by decide +kernel
theorem q2spmtFq_plogs : q2spmtFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T2.spmFq.plogs.take 36 := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
