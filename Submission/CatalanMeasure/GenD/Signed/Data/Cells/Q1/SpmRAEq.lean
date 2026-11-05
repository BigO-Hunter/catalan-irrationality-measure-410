module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAGFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the SPM_R data (trial 1, corner a) with the trial literals; merge lemma. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1spmraTs_eq : q1spmraTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qTn := by decide +kernel
theorem q1spmraTsM_eq : q1spmraTsM = mergeL q1spmraTs := by decide +kernel
theorem q1spmraFq_poles : q1spmraFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.spmFq.poles := by decide +kernel
theorem q1spmraFq_plogs : q1spmraFq.plogs.take 36 = CatalanMeasure.GenD.Signed.Data.Trial.T1.spmFq.plogs.take 36 := by decide +kernel
theorem q1spmraFq_plogs_full : q1spmraFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T1.spmFq.plogs := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
