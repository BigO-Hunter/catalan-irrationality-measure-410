module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.CellsCap
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZCellInst
@[expose] public section
set_option Elab.async false

/-!
# Law_L(4) cells: exact rational checks (G2h)

Rank-one structure of the window-`s` responses (`v_0 = -6 w`, `v_1 = -3 w`, `v_3 = -(3/2) w`,
`w = v_2 - v_1`) and of the window-`s+1` differences `z_J` (`z_1 = 2 z_2`, `3 z_3 = 2 z_2`,
`2 z_4 = z_2`), for the `K = 5` cells `uL, u2L, y1L, y2L`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ.Q
open OAI.InternalCatalan

theorem L_v0_rank1 : ∀ c ∈ [0, 1, 2, 3],
    (vResp 5 uL u2L y1L y2L 0).getD c 0 =
      (-6 : ℚ) * ((vResp 5 uL u2L y1L y2L 2).getD c 0 - (vResp 5 uL u2L y1L y2L 1).getD c 0) := by
  decide +kernel

theorem L_v1_rank1 : ∀ c ∈ [0, 1, 2, 3],
    (vResp 5 uL u2L y1L y2L 1).getD c 0 =
      (-3 : ℚ) * ((vResp 5 uL u2L y1L y2L 2).getD c 0 - (vResp 5 uL u2L y1L y2L 1).getD c 0) := by
  decide +kernel

theorem L_v3_rank1 : ∀ c ∈ [0, 1, 2, 3],
    (vResp 5 uL u2L y1L y2L 3).getD c 0 =
      (-3 / 2 : ℚ) * ((vResp 5 uL u2L y1L y2L 2).getD c 0 - (vResp 5 uL u2L y1L y2L 1).getD c 0) := by
  decide +kernel

theorem L_z1_rank : ∀ c ∈ [0, 1, 2, 3],
    (1 : ℚ) * (zq 5 uL u2L y1L y2L 1).getD c 0 = 2 * (zq 5 uL u2L y1L y2L 2).getD c 0 := by
  decide +kernel

theorem L_z3_rank : ∀ c ∈ [0, 1, 2, 3],
    (3 : ℚ) * (zq 5 uL u2L y1L y2L 3).getD c 0 = 2 * (zq 5 uL u2L y1L y2L 2).getD c 0 := by
  decide +kernel

theorem L_z4_rank : ∀ c ∈ [0, 1, 2, 3],
    (2 : ℚ) * (zq 5 uL u2L y1L y2L 4).getD c 0 = (zq 5 uL u2L y1L y2L 2).getD c 0 := by
  decide +kernel

end CatalanMeasure.GenD.Uniform.W.ZoneZ.Q

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
/-- Independence determinants of the Law_L cells (blocks 3, 4). -/
def DqUL : ℚ := Q.uL 3 * Q.u2L 4 - Q.uL 4 * Q.u2L 3
def DqYL : ℚ := Q.y1L 3 * Q.y2L 4 - Q.y1L 4 * Q.y2L 3
theorem DqUL_num_ne : DqUL.num ≠ 0 := by unfold DqUL; decide +kernel
theorem DqYL_num_ne : DqYL.num ≠ 0 := by unfold DqYL; decide +kernel
end CatalanMeasure.GenD.Uniform.W.ZoneZ
