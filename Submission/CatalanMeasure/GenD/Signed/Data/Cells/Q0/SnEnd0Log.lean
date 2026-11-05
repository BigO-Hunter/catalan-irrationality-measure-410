module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnE096

@[expose] public section

/-! **SN trial 0: log-form end data at e = 0** (for `fNeg_cell_zero` / `fPosS_cell_zero` / `fCol_cell_one`): the window gives `field <= TR + U + c log|x - e|` with `c = endC > 0`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q0snE096Log : ∀ x ∈ Icc ((q0snE096Blo : ℚ) : ℝ) ((q0snE096Bhi : ℚ) : ℝ), x ≠ ((q0snE096E : ℚ) : ℝ) →
    fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ ((q0snE096TR : ℚ) : ℝ) + ((q0snE096U : ℚ) : ℝ) + ((endC q0snFq [] q0snE096E : ℚ) : ℝ) * Real.log |x - ((q0snE096E : ℚ) : ℝ)| := by
  intro x hx _
  exact endOK_sound0 _ _ _ _ _ _ _ (endOK_of_endUOK q0snE096End) q0snE096Bound x hx
theorem q0snE096Cpos : 0 < endC q0snFq [] q0snE096E := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
