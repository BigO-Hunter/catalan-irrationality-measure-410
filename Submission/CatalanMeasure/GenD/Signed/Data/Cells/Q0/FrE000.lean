module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! FR, alpha = 0.0: box cell [-1, -1] (`boxOK`). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

def q0frE000Lo : ℚ := q0frBd.getD 0 0
def q0frE000Hi : ℚ := q0frBd.getD 1 0
theorem q0frE000Box : boxOK q0frFq 56 q0frE000Lo q0frE000Hi [] q0frT = true := by decide +kernel
theorem q0frE000Bound : ∀ x ∈ Icc ((q0frE000Lo : ℚ) : ℝ) ((q0frE000Hi : ℚ) : ℝ), fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  boxOK_sound _ _ _ _ _ _ q0frE000Box

end CatalanMeasure.GenD.Signed.Data.Cells
