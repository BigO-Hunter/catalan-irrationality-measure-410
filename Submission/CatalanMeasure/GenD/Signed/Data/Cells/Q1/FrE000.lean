module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! FR, alpha = 0.005: box cell [-1, -1] (`boxOK`). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

def q1frE000Lo : ℚ := q1frBd.getD 0 0
def q1frE000Hi : ℚ := q1frBd.getD 1 0
theorem q1frE000Box : boxOK q1frFq 56 q1frE000Lo q1frE000Hi [] q1frT = true := by decide +kernel
theorem q1frE000Bound : ∀ x ∈ Icc ((q1frE000Lo : ℚ) : ℝ) ((q1frE000Hi : ℚ) : ℝ), fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  boxOK_sound _ _ _ _ _ _ q1frE000Box

end CatalanMeasure.GenD.Signed.Data.Cells
