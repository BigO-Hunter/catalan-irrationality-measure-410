module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmtL1E
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! SP, trial 0: the jump region [1 - 2^-10, 1): field + Laurent part is at most `q0spmtTJ`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q0spmtL1Ladder : ∀ x ∈ Icc ((q0spmtL1B00Blo : ℚ) : ℝ) ((q0spmtL1B13Bhi : ℚ) : ℝ),
    fieldTower q0spmtFq (poleF q0spmtFq.poles) 0 x + lfieldTower q0spmtTs 0 x ≤ (q0spmtTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0spmtL1B00Orig) q0spmtL1B01Orig) q0spmtL1B02Orig) q0spmtL1B03Orig) q0spmtL1B04Orig) q0spmtL1B05Orig) q0spmtL1B06Orig) q0spmtL1B07Orig) q0spmtL1B08Orig) q0spmtL1B09Orig) q0spmtL1B10Orig) q0spmtL1B11Orig) q0spmtL1B12Orig) q0spmtL1B13Orig
theorem q0spmtL1Sup : ∀ x ∈ Ico ((q0spmtL1B00Blo : ℚ) : ℝ) ((1 : ℚ) : ℝ),
    fieldTower q0spmtFq (poleF q0spmtFq.poles) 0 x + lfieldTower q0spmtTs 0 x ≤ (q0spmtTJ : ℝ) := by
  intro x hx
  by_cases h : x ≤ ((q0spmtL1B13Bhi : ℚ) : ℝ)
  · exact q0spmtL1Ladder x ⟨hx.1, h⟩
  · have hB : ((q0spmtL1EBhi : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      rw [show q0spmtL1EBhi = (1 : ℚ) by decide +kernel]
    exact q0spmtL1EOrig x ⟨le_of_lt (not_le.mp h), hB ▸ hx.2.le⟩ hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
