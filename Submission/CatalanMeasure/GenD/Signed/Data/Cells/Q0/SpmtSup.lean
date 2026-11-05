module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmtEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmtB000

@[expose] public section

/-! **SPM_TOP, trial 0: sup statements.** -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q0spmtSupM : ∀ x ∈ Icc ((q0spmtBd.getD 0 0 : ℚ) : ℝ) ((q0spmtBd.getD 1 0 : ℚ) : ℝ), fieldTower q0spmtFq (poleF q0spmtFq.poles) 0 x + lfieldTower q0spmtTsM 0 x ≤ (q0spmtT : ℝ) :=
  q0spmtB000Bound
theorem q0spmtSup : ∀ x ∈ Icc ((q0spmtBd.getD 0 0 : ℚ) : ℝ) ((q0spmtBd.getD 1 0 : ℚ) : ℝ), fieldTower q0spmtFq (poleF q0spmtFq.poles) 0 x + lfieldTower q0spmtTs 0 x ≤ (q0spmtT : ℝ) := by
  intro x hx
  have h := q0spmtSupM x hx
  rw [q0spmtTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
