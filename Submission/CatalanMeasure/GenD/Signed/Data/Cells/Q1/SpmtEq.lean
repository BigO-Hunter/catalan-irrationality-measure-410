module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmtFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the SPM_TOP data (trial 1) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1spmtTs_eq : q1spmtTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qTn := by decide +kernel
theorem q1spmtTsM_eq : q1spmtTsM = mergeL q1spmtTs := by decide +kernel
theorem q1spmtFq_poles : q1spmtFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.spmFq.poles := by decide +kernel
theorem q1spmtFq_plogs : q1spmtFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T1.spmFq.plogs.take 36 := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
