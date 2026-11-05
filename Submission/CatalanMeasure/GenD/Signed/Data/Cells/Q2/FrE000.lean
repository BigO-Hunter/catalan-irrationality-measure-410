module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! FR, alpha = 0.0625: box cell [-1, -1] (`boxOK`). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

def q2frE000Lo : ℚ := q2frBd.getD 0 0
def q2frE000Hi : ℚ := q2frBd.getD 1 0
theorem q2frE000Box : boxOK q2frFq 56 q2frE000Lo q2frE000Hi [] q2frT = true := by decide +kernel
theorem q2frE000Bound : ∀ x ∈ Icc ((q2frE000Lo : ℚ) : ℝ) ((q2frE000Hi : ℚ) : ℝ), fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  boxOK_sound _ _ _ _ _ _ q2frE000Box

end CatalanMeasure.GenD.Signed.Data.Cells
