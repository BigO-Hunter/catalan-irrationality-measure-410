module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpL1E
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! SP, trial 1: the jump region [1 - 2^-10, 1): field + Laurent part is at most `q1spTJ`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1spL1Ladder : ∀ x ∈ Icc ((q1spL1B00Blo : ℚ) : ℝ) ((q1spL1B15Bhi : ℚ) : ℝ),
    fieldTower q1spFq (poleF q1spFq.poles) 0 x + lfieldTower q1spTs 0 x ≤ (q1spTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1spL1B00Orig) q1spL1B01Orig) q1spL1B02Orig) q1spL1B03Orig) q1spL1B04Orig) q1spL1B05Orig) q1spL1B06Orig) q1spL1B07Orig) q1spL1B08Orig) q1spL1B09Orig) q1spL1B10Orig) q1spL1B11Orig) q1spL1B12Orig) q1spL1B13Orig) q1spL1B14Orig) q1spL1B15Orig
theorem q1spL1Sup : ∀ x ∈ Ico ((q1spL1B00Blo : ℚ) : ℝ) ((1 : ℚ) : ℝ),
    fieldTower q1spFq (poleF q1spFq.poles) 0 x + lfieldTower q1spTs 0 x ≤ (q1spTJ : ℝ) := by
  intro x hx
  by_cases h : x ≤ ((q1spL1B15Bhi : ℚ) : ℝ)
  · exact q1spL1Ladder x ⟨hx.1, h⟩
  · have hB : ((q1spL1EBhi : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      rw [show q1spL1EBhi = (1 : ℚ) by decide +kernel]
    exact q1spL1EOrig x ⟨le_of_lt (not_le.mp h), hB ▸ hx.2.le⟩ hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
