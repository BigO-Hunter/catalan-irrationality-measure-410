module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpL1E
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! SP, trial 2: the jump region [1 - 2^-10, 1): field + Laurent part is at most `q2spTJ`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q2spL1Ladder : ∀ x ∈ Icc ((q2spL1B00Blo : ℚ) : ℝ) ((q2spL1B15Bhi : ℚ) : ℝ),
    fieldTower q2spFq (poleF q2spFq.poles) 0 x + lfieldTower q2spTs 0 x ≤ (q2spTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2spL1B00Orig) q2spL1B01Orig) q2spL1B02Orig) q2spL1B03Orig) q2spL1B04Orig) q2spL1B05Orig) q2spL1B06Orig) q2spL1B07Orig) q2spL1B08Orig) q2spL1B09Orig) q2spL1B10Orig) q2spL1B11Orig) q2spL1B12Orig) q2spL1B13Orig) q2spL1B14Orig) q2spL1B15Orig
theorem q2spL1Sup : ∀ x ∈ Ico ((q2spL1B00Blo : ℚ) : ℝ) ((1 : ℚ) : ℝ),
    fieldTower q2spFq (poleF q2spFq.poles) 0 x + lfieldTower q2spTs 0 x ≤ (q2spTJ : ℝ) := by
  intro x hx
  by_cases h : x ≤ ((q2spL1B15Bhi : ℚ) : ℝ)
  · exact q2spL1Ladder x ⟨hx.1, h⟩
  · have hB : ((q2spL1EBhi : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      rw [show q2spL1EBhi = (1 : ℚ) by decide +kernel]
    exact q2spL1EOrig x ⟨le_of_lt (not_le.mp h), hB ▸ hx.2.le⟩ hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
