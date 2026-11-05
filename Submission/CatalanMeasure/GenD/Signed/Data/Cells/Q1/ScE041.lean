module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! SC, alpha = 0.005: window around e = 1, [1, 1] (`endUOK`). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

def q1scE041E : ℚ := qmk (1) 1 0 0
def q1scE041TR : ℚ := dy3 (-8265209862821) 0 39
def q1scE041U : ℚ := 0
def q1scE041Blo : ℚ := q1scBd.getD 41 0
def q1scE041Bhi : ℚ := q1scBd.getD 42 0
theorem q1scE041RegBox : boxOK (regQ q1scFq q1scE041E) 56 q1scE041Blo q1scE041Bhi [1] q1scE041TR = true := by decide +kernel
theorem q1scE041Bound : ∀ x ∈ Icc ((q1scE041Blo : ℚ) : ℝ) ((q1scE041Bhi : ℚ) : ℝ), fieldTower (regQ q1scFq q1scE041E) (poleF (regQ q1scFq q1scE041E).poles) 0 x ≤ (q1scE041TR : ℝ) :=
  boxOK_sound _ _ _ _ _ _ q1scE041RegBox

theorem q1scE041End : endUOK q1scFq [] q1scE041E q1scE041Blo q1scE041Bhi 40 40 q1scE041U q1scE041TR q1scT = true := by decide +kernel
theorem q1scE041Unif : ∀ x ∈ Icc ((q1scE041Blo : ℚ) : ℝ) ((q1scE041Bhi : ℚ) : ℝ), x ≠ ((q1scE041E : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  endUOK_sound0 _ _ _ _ _ _ _ _ _ q1scE041End q1scE041Bound
theorem q1scE041Eq : q1scE041E = q1scBd.getD 42 0 := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
