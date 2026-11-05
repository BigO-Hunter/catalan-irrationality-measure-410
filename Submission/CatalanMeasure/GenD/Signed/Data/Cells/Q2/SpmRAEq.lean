module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAGFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T2Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the SPM_R data (trial 2, corner a) with the trial literals; merge lemma. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q2spmraTs_eq : q2spmraTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qTn := by decide +kernel
theorem q2spmraTsM_eq : q2spmraTsM = mergeL q2spmraTs := by decide +kernel
theorem q2spmraFq_poles : q2spmraFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.spmFq.poles := by decide +kernel
theorem q2spmraFq_plogs : q2spmraFq.plogs.take 36 = CatalanMeasure.GenD.Signed.Data.Trial.T2.spmFq.plogs.take 36 := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
