module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAB006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAB007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAB008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRAGB000

@[expose] public section

/-! **SPM_R, trial 2, corner 1/200: sup statement** (series window on [gs, 3/10], merged Laurent cells on [3/10, xc)). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


def q2spmragN : ℕ := 72
def q2spmragHi : ℚ := qmk (3) 5 0 1
def q2spmragDelta : ℚ := dy3 (1) 0 69
theorem q2spmrag_laurent : l0OK q2spmraTsM q2spmragHi q2spmragN = true := by decide +kernel
theorem q2spmrag_cL : l0C q2spmraTsM = 0 := by decide +kernel
theorem q2spmrag_plogs : q2spmragFq.plogs = q2spmraFq.plogs := by decide +kernel
theorem q2spmrag_poles : q2spmragFq.poles = q2spmraFq.poles := by decide +kernel
theorem q2spmrag_hD : polyAB (vecAdd (vecAdd q2spmraFq.poly (l0P q2spmraTsM q2spmragN)) (q2spmragPoly.map (fun t => (-1 : ℚ) * t))) 0 q2spmragHi ≤ q2spmragDelta := by decide +kernel
theorem q2spmrag_tot : q2spmragT + q2spmragDelta + l0Err q2spmragHi q2spmragN q2spmraTsM ≤ q2spmraT := by decide +kernel
theorem q2spmrag_b0 : 0 < q2spmragBd.getD 0 0 := by decide +kernel
theorem q2spmrag_bN : q2spmragBd.getD 4 0 ≤ q2spmragHi := by decide +kernel
theorem q2spmrag_bmid : q2spmragBd.getD 4 0 = q2spmraBd.getD 0 0 := by decide +kernel
theorem q2spmrag_dom0 : q2spmragBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q2spmra_domN : q2spmraBd.getD 12 0 = 999 / 1000 := by decide +kernel
theorem q2spmragCells : ∀ x ∈ Icc ((q2spmragBd.getD 0 0 : ℚ) : ℝ) ((q2spmragBd.getD 4 0 : ℚ) : ℝ), fieldTower q2spmragFq (poleF q2spmragFq.poles) 0 x ≤ (q2spmragT : ℝ) :=
  cover_union (cover_union (cover_union (q2spmragB000Bound) q2spmragB001Bound) q2spmragB002Bound) q2spmragB003Bound
theorem q2spmragSer : ∀ x ∈ Icc ((q2spmragBd.getD 0 0 : ℚ) : ℝ) ((q2spmragBd.getD 4 0 : ℚ) : ℝ), fieldTower q2spmraFq (poleF q2spmraFq.poles) 0 x + lfieldTower q2spmraTsM 0 x ≤ (q2spmraT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q2spmragBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q2spmrag_b0
  have hN : ((q2spmragBd.getD 4 0 : ℚ) : ℝ) ≤ (q2spmragHi : ℝ) := by exact_mod_cast q2spmrag_bN
  have h := l0_series_sound q2spmraFq q2spmragFq q2spmraTsM q2spmragHi q2spmragN q2spmragDelta q2spmragT q2spmrag_laurent q2spmrag_cL q2spmrag_plogs q2spmrag_poles q2spmrag_hD
    (Set.Icc ((q2spmragBd.getD 0 0 : ℚ) : ℝ) ((q2spmragBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q2spmragCells y hy) x hx
  have hq : ((q2spmragT + q2spmragDelta + l0Err q2spmragHi q2spmragN q2spmraTsM : ℚ) : ℝ) ≤ (q2spmraT : ℝ) := by exact_mod_cast q2spmrag_tot
  exact h.trans hq

theorem q2spmraLaurentM : ∀ x ∈ Icc ((q2spmraBd.getD 0 0 : ℚ) : ℝ) ((q2spmraBd.getD 12 0 : ℚ) : ℝ), fieldTower q2spmraFq (poleF q2spmraFq.poles) 0 x + lfieldTower q2spmraTsM 0 x ≤ (q2spmraT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2spmraB000Bound) q2spmraB001Bound) q2spmraB002Bound) q2spmraB003Bound) q2spmraB004Bound) q2spmraB005Bound) q2spmraB006Bound) q2spmraB007Bound) q2spmraB008Bound) q2spmraB009Bound) q2spmraB010Bound) q2spmraB011Bound
/-- **SPM_R**, trial 2, corner 1/200: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q2spmraSup : ∀ x ∈ Icc ((q2spmragBd.getD 0 0 : ℚ) : ℝ) ((q2spmraBd.getD 12 0 : ℚ) : ℝ), fieldTower q2spmraFq (poleF q2spmraFq.poles) 0 x + lfieldTower q2spmraTs 0 x ≤ (q2spmraT : ℝ) := by
  intro x hx
  have hb : ((q2spmragBd.getD 4 0 : ℚ) : ℝ) = ((q2spmraBd.getD 0 0 : ℚ) : ℝ) := by rw [q2spmrag_bmid]
  have h1 := q2spmragSer
  rw [hb] at h1
  have h := cover_union h1 q2spmraLaurentM x hx
  rw [q2spmraTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
