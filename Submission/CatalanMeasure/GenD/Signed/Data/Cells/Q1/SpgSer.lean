module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpgSup
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpGE0
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! SP gap (0, 3/10), trial 1: the series window `l0_series_sound` turns the Laurent-free cover `q1spgSup` of fq' into the bound for the true SP field plus the merged Laurent terms. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

def q1spgN : ℕ := 72
def q1spgHi : ℚ := qmk (3) 5 0 1
def q1spgDelta : ℚ := dy3 (1) 0 69
theorem q1spg_laurent : l0OK q1spiTsM q1spgHi q1spgN = true := by decide +kernel
theorem q1spg_cL : l0C q1spiTsM = 0 := by decide +kernel
theorem q1spg_plogs : q1spgFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T1.spFq.plogs := by decide +kernel
theorem q1spg_poles : q1spgFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.spFq.poles := by decide +kernel
theorem q1spg_hD : polyAB (vecAdd (vecAdd CatalanMeasure.GenD.Signed.Data.Trial.T1.spFq.poly (l0P q1spiTsM q1spgN)) (q1spgPoly.map (fun t => (-1 : ℚ) * t))) 0 q1spgHi ≤ q1spgDelta := by decide +kernel
theorem q1spg_tot : q1spgT + q1spgDelta + l0Err q1spgHi q1spgN q1spiTsM ≤ q1spiT := by decide +kernel
theorem q1spg_b0 : 0 < q1spgBd.getD 0 0 := by decide +kernel
theorem q1spg_b0E : q1spgBd.getD 0 0 = q1spe0Hi := by decide +kernel
theorem q1spg_bN : q1spgBd.getD 74 0 ≤ q1spgHi := by decide +kernel
theorem q1spg_bNeq : q1spgBd.getD 74 0 = 3 / 10 := by decide +kernel
theorem q1spgGapM : ∀ x ∈ Ioo ((q1spgBd.getD 0 0 : ℚ) : ℝ) ((q1spgBd.getD 74 0 : ℚ) : ℝ), fieldTower CatalanMeasure.GenD.Signed.Data.Trial.T1.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial.T1.spFq.poles) 0 x + lfieldTower q1spiTsM 0 x ≤ (q1spiT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q1spgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q1spg_b0
  have hN : ((q1spgBd.getD 74 0 : ℚ) : ℝ) ≤ (q1spgHi : ℝ) := by exact_mod_cast q1spg_bN
  have h := l0_series_sound CatalanMeasure.GenD.Signed.Data.Trial.T1.spFq q1spgFq q1spiTsM q1spgHi q1spgN q1spgDelta q1spgT q1spg_laurent q1spg_cL q1spg_plogs q1spg_poles q1spg_hD
    (Set.Ioo ((q1spgBd.getD 0 0 : ℚ) : ℝ) ((q1spgBd.getD 74 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q1spgSup y hy) x hx
  have hq : ((q1spgT + q1spgDelta + l0Err q1spgHi q1spgN q1spiTsM : ℚ) : ℝ) ≤ (q1spiT : ℝ) := by exact_mod_cast q1spg_tot
  exact h.trans hq

/-- **SP gap (0, 3/10)**, trial 1: the true SP field plus the exact Laurent terms. -/
theorem q1spiGapSup : ∀ x ∈ Ioo ((q1spgBd.getD 0 0 : ℚ) : ℝ) ((q1spgBd.getD 74 0 : ℚ) : ℝ), fieldTower CatalanMeasure.GenD.Signed.Data.Trial.T1.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial.T1.spFq.poles) 0 x + lfieldTower q1spiTs 0 x ≤ (q1spiT : ℝ) := by
  intro x hx
  have h := q1spgGapM x hx
  rw [q1spiTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
