module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnE117

@[expose] public section

/-! **SN trial 1: log-form end data at e = 0** (for `fNeg_cell_zero` / `fPosS_cell_zero` / `fCol_cell_one`): the window gives `field <= TR + U + c log|x - e|` with `c = endC > 0`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q1snE117Log : ∀ x ∈ Icc ((q1snE117Blo : ℚ) : ℝ) ((q1snE117Bhi : ℚ) : ℝ), x ≠ ((q1snE117E : ℚ) : ℝ) →
    fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ ((q1snE117TR : ℚ) : ℝ) + ((q1snE117U : ℚ) : ℝ) + ((endC q1snFq [] q1snE117E : ℚ) : ℝ) * Real.log |x - ((q1snE117E : ℚ) : ℝ)| := by
  intro x hx _
  exact endOK_sound0 _ _ _ _ _ _ _ (endOK_of_endUOK q1snE117End) q1snE117Bound x hx
theorem q1snE117Cpos : 0 < endC q1snFq [] q1snE117E := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
