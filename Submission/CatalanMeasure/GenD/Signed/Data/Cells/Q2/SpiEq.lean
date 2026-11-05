module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpiFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T2Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the SP data (trial 2) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q2spiTs_eq : q2spiTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qTn := by decide +kernel
theorem q2spiTsM_eq : q2spiTsM = mergeL q2spiTs := by decide +kernel
theorem q2spiFq_poles : q2spiFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.spFq.poles := by decide +kernel
theorem q2spiFq_plogs : q2spiFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T2.spFq.plogs := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
