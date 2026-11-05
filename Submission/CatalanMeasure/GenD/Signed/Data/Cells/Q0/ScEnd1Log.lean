module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScE040

@[expose] public section

/-! **SC trial 0: log-form end data at e = 1** (for `fNeg_cell_zero` / `fPosS_cell_zero` / `fCol_cell_one`): the window gives `field <= TR + U + c log|x - e|` with `c = endC > 0`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q0scE040Log : ∀ x ∈ Icc ((q0scE040Blo : ℚ) : ℝ) ((q0scE040Bhi : ℚ) : ℝ), x ≠ ((q0scE040E : ℚ) : ℝ) →
    fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ ((q0scE040TR : ℚ) : ℝ) + ((q0scE040U : ℚ) : ℝ) + ((endC q0scFq [] q0scE040E : ℚ) : ℝ) * Real.log |x - ((q0scE040E : ℚ) : ℝ)| := by
  intro x hx _
  exact endOK_sound0 _ _ _ _ _ _ _ (endOK_of_endUOK q0scE040End) q0scE040Bound x hx
theorem q0scE040Cpos : 0 < endC q0scFq [] q0scE040E := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
