module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScE046

@[expose] public section

/-! **SC trial 2: log-form end data at e = 1** (for `fNeg_cell_zero` / `fPosS_cell_zero` / `fCol_cell_one`): the window gives `field <= TR + U + c log|x - e|` with `c = endC > 0`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q2scE046Log : ∀ x ∈ Icc ((q2scE046Blo : ℚ) : ℝ) ((q2scE046Bhi : ℚ) : ℝ), x ≠ ((q2scE046E : ℚ) : ℝ) →
    fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ ((q2scE046TR : ℚ) : ℝ) + ((q2scE046U : ℚ) : ℝ) + ((endC q2scFq [] q2scE046E : ℚ) : ℝ) * Real.log |x - ((q2scE046E : ℚ) : ℝ)| := by
  intro x hx _
  exact endOK_sound0 _ _ _ _ _ _ _ (endOK_of_endUOK q2scE046End) q2scE046Bound x hx
theorem q2scE046Cpos : 0 < endC q2scFq [] q2scE046E := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
