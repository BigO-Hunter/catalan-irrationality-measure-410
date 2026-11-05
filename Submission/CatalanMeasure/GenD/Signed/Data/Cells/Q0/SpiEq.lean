module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T0Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the SP data (trial 0) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q0spiTs_eq : q0spiTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qTn := by decide +kernel
theorem q0spiTsM_eq : q0spiTsM = mergeL q0spiTs := by decide +kernel
theorem q0spiFq_poles : q0spiFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq.poles := by decide +kernel
theorem q0spiFq_plogs : q0spiFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq.plogs := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
