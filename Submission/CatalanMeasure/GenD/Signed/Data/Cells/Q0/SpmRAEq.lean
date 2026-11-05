module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAGFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T0Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the SPM_R data (trial 0, corner a) with the trial literals; merge lemma. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q0spmraTs_eq : q0spmraTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qTn := by decide +kernel
theorem q0spmraTsM_eq : q0spmraTsM = mergeL q0spmraTs := by decide +kernel
theorem q0spmraFq_poles : q0spmraFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T0.spmFq.poles := by decide +kernel
theorem q0spmraFq_plogs : q0spmraFq.plogs.take 38 = CatalanMeasure.GenD.Signed.Data.Trial.T0.spmFq.plogs.take 38 := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
