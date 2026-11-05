module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmtL1E
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! SP, trial 1: the jump region [1 - 2^-10, 1): field + Laurent part is at most `q1spmtTJ`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1spmtL1Ladder : ∀ x ∈ Icc ((q1spmtL1B00Blo : ℚ) : ℝ) ((q1spmtL1B13Bhi : ℚ) : ℝ),
    fieldTower q1spmtFq (poleF q1spmtFq.poles) 0 x + lfieldTower q1spmtTs 0 x ≤ (q1spmtTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1spmtL1B00Orig) q1spmtL1B01Orig) q1spmtL1B02Orig) q1spmtL1B03Orig) q1spmtL1B04Orig) q1spmtL1B05Orig) q1spmtL1B06Orig) q1spmtL1B07Orig) q1spmtL1B08Orig) q1spmtL1B09Orig) q1spmtL1B10Orig) q1spmtL1B11Orig) q1spmtL1B12Orig) q1spmtL1B13Orig
theorem q1spmtL1Sup : ∀ x ∈ Ico ((q1spmtL1B00Blo : ℚ) : ℝ) ((1 : ℚ) : ℝ),
    fieldTower q1spmtFq (poleF q1spmtFq.poles) 0 x + lfieldTower q1spmtTs 0 x ≤ (q1spmtTJ : ℝ) := by
  intro x hx
  by_cases h : x ≤ ((q1spmtL1B13Bhi : ℚ) : ℝ)
  · exact q1spmtL1Ladder x ⟨hx.1, h⟩
  · have hB : ((q1spmtL1EBhi : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      rw [show q1spmtL1EBhi = (1 : ℚ) by decide +kernel]
    exact q1spmtL1EOrig x ⟨le_of_lt (not_le.mp h), hB ▸ hx.2.le⟩ hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
