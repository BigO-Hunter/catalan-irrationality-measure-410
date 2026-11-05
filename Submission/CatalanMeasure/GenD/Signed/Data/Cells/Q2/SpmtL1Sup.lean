module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmtL1E
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! SP, trial 2: the jump region [1 - 2^-10, 1): field + Laurent part is at most `q2spmtTJ`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q2spmtL1Ladder : ∀ x ∈ Icc ((q2spmtL1B00Blo : ℚ) : ℝ) ((q2spmtL1B13Bhi : ℚ) : ℝ),
    fieldTower q2spmtFq (poleF q2spmtFq.poles) 0 x + lfieldTower q2spmtTs 0 x ≤ (q2spmtTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2spmtL1B00Orig) q2spmtL1B01Orig) q2spmtL1B02Orig) q2spmtL1B03Orig) q2spmtL1B04Orig) q2spmtL1B05Orig) q2spmtL1B06Orig) q2spmtL1B07Orig) q2spmtL1B08Orig) q2spmtL1B09Orig) q2spmtL1B10Orig) q2spmtL1B11Orig) q2spmtL1B12Orig) q2spmtL1B13Orig
theorem q2spmtL1Sup : ∀ x ∈ Ico ((q2spmtL1B00Blo : ℚ) : ℝ) ((1 : ℚ) : ℝ),
    fieldTower q2spmtFq (poleF q2spmtFq.poles) 0 x + lfieldTower q2spmtTs 0 x ≤ (q2spmtTJ : ℝ) := by
  intro x hx
  by_cases h : x ≤ ((q2spmtL1B13Bhi : ℚ) : ℝ)
  · exact q2spmtL1Ladder x ⟨hx.1, h⟩
  · have hB : ((q2spmtL1EBhi : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      rw [show q2spmtL1EBhi = (1 : ℚ) by decide +kernel]
    exact q2spmtL1EOrig x ⟨le_of_lt (not_le.mp h), hB ▸ hx.2.le⟩ hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
