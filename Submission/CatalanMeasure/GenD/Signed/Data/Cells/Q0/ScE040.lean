module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! SC, alpha = 0.0: window around e = 1, [1, 1] (`endUOK`). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

def q0scE040E : ℚ := qmk (1) 1 0 0
def q0scE040TR : ℚ := dy3 (-2067199023269) 0 37
def q0scE040U : ℚ := 0
def q0scE040Blo : ℚ := q0scBd.getD 40 0
def q0scE040Bhi : ℚ := q0scBd.getD 41 0
theorem q0scE040RegBox : boxOK (regQ q0scFq q0scE040E) 56 q0scE040Blo q0scE040Bhi [1] q0scE040TR = true := by decide +kernel
theorem q0scE040Bound : ∀ x ∈ Icc ((q0scE040Blo : ℚ) : ℝ) ((q0scE040Bhi : ℚ) : ℝ), fieldTower (regQ q0scFq q0scE040E) (poleF (regQ q0scFq q0scE040E).poles) 0 x ≤ (q0scE040TR : ℝ) :=
  boxOK_sound _ _ _ _ _ _ q0scE040RegBox

theorem q0scE040End : endUOK q0scFq [] q0scE040E q0scE040Blo q0scE040Bhi 40 40 q0scE040U q0scE040TR q0scT = true := by decide +kernel
theorem q0scE040Unif : ∀ x ∈ Icc ((q0scE040Blo : ℚ) : ℝ) ((q0scE040Bhi : ℚ) : ℝ), x ≠ ((q0scE040E : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  endUOK_sound0 _ _ _ _ _ _ _ _ _ q0scE040End q0scE040Bound
theorem q0scE040Eq : q0scE040E = q0scBd.getD 41 0 := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
