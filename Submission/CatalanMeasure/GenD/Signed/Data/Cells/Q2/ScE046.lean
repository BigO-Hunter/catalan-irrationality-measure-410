module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! SC, alpha = 0.0625: window around e = 1, [1, 1] (`endUOK`). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

def q2scE046E : ℚ := qmk (1) 1 0 0
def q2scE046TR : ℚ := dy3 (-16446746495729) 0 40
def q2scE046U : ℚ := 0
def q2scE046Blo : ℚ := q2scBd.getD 46 0
def q2scE046Bhi : ℚ := q2scBd.getD 47 0
theorem q2scE046RegBox : boxOK (regQ q2scFq q2scE046E) 56 q2scE046Blo q2scE046Bhi [1] q2scE046TR = true := by decide +kernel
theorem q2scE046Bound : ∀ x ∈ Icc ((q2scE046Blo : ℚ) : ℝ) ((q2scE046Bhi : ℚ) : ℝ), fieldTower (regQ q2scFq q2scE046E) (poleF (regQ q2scFq q2scE046E).poles) 0 x ≤ (q2scE046TR : ℝ) :=
  boxOK_sound _ _ _ _ _ _ q2scE046RegBox

theorem q2scE046End : endUOK q2scFq [] q2scE046E q2scE046Blo q2scE046Bhi 40 40 q2scE046U q2scE046TR q2scT = true := by decide +kernel
theorem q2scE046Unif : ∀ x ∈ Icc ((q2scE046Blo : ℚ) : ℝ) ((q2scE046Bhi : ℚ) : ℝ), x ≠ ((q2scE046E : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  endUOK_sound0 _ _ _ _ _ _ _ _ _ q2scE046End q2scE046Bound
theorem q2scE046Eq : q2scE046E = q2scBd.getD 47 0 := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
