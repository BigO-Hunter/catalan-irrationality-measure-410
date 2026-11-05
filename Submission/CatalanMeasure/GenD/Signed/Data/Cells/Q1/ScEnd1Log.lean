module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScE041

@[expose] public section

/-! **SC trial 1: log-form end data at e = 1** (for `fNeg_cell_zero` / `fPosS_cell_zero` / `fCol_cell_one`): the window gives `field <= TR + U + c log|x - e|` with `c = endC > 0`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q1scE041Log : ∀ x ∈ Icc ((q1scE041Blo : ℚ) : ℝ) ((q1scE041Bhi : ℚ) : ℝ), x ≠ ((q1scE041E : ℚ) : ℝ) →
    fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ ((q1scE041TR : ℚ) : ℝ) + ((q1scE041U : ℚ) : ℝ) + ((endC q1scFq [] q1scE041E : ℚ) : ℝ) * Real.log |x - ((q1scE041E : ℚ) : ℝ)| := by
  intro x hx _
  exact endOK_sound0 _ _ _ _ _ _ _ (endOK_of_endUOK q1scE041End) q1scE041Bound x hx
theorem q1scE041Cpos : 0 < endC q1scFq [] q1scE041E := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
