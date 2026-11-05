module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpL1E
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! SP, trial 0: the jump region [1 - 2^-10, 1): field + Laurent part is at most `q0spTJ`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q0spL1Ladder : ∀ x ∈ Icc ((q0spL1B00Blo : ℚ) : ℝ) ((q0spL1B15Bhi : ℚ) : ℝ),
    fieldTower q0spFq (poleF q0spFq.poles) 0 x + lfieldTower q0spTs 0 x ≤ (q0spTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0spL1B00Orig) q0spL1B01Orig) q0spL1B02Orig) q0spL1B03Orig) q0spL1B04Orig) q0spL1B05Orig) q0spL1B06Orig) q0spL1B07Orig) q0spL1B08Orig) q0spL1B09Orig) q0spL1B10Orig) q0spL1B11Orig) q0spL1B12Orig) q0spL1B13Orig) q0spL1B14Orig) q0spL1B15Orig
theorem q0spL1Sup : ∀ x ∈ Ico ((q0spL1B00Blo : ℚ) : ℝ) ((1 : ℚ) : ℝ),
    fieldTower q0spFq (poleF q0spFq.poles) 0 x + lfieldTower q0spTs 0 x ≤ (q0spTJ : ℝ) := by
  intro x hx
  by_cases h : x ≤ ((q0spL1B15Bhi : ℚ) : ℝ)
  · exact q0spL1Ladder x ⟨hx.1, h⟩
  · have hB : ((q0spL1EBhi : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      rw [show q0spL1EBhi = (1 : ℚ) by decide +kernel]
    exact q0spL1EOrig x ⟨le_of_lt (not_le.mp h), hB ▸ hx.2.le⟩ hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
