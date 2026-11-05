module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnE120

@[expose] public section

/-! **SN trial 2: log-form end data at e = 0** (for `fNeg_cell_zero` / `fPosS_cell_zero` / `fCol_cell_one`): the window gives `field <= TR + U + c log|x - e|` with `c = endC > 0`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q2snE120Log : ∀ x ∈ Icc ((q2snE120Blo : ℚ) : ℝ) ((q2snE120Bhi : ℚ) : ℝ), x ≠ ((q2snE120E : ℚ) : ℝ) →
    fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ ((q2snE120TR : ℚ) : ℝ) + ((q2snE120U : ℚ) : ℝ) + ((endC q2snFq [] q2snE120E : ℚ) : ℝ) * Real.log |x - ((q2snE120E : ℚ) : ℝ)| := by
  intro x hx _
  exact endOK_sound0 _ _ _ _ _ _ _ (endOK_of_endUOK q2snE120End) q2snE120Bound x hx
theorem q2snE120Cpos : 0 < endC q2snFq [] q2snE120E := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
