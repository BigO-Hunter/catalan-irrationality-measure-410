module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.CellsL
@[expose] public section
set_option Elab.async false

/-!
# Lemma-S shapes of the cells at `s = 4` (exact, over `ℚ`)

These are the consequences of the Shift Lemma and the cell definitions (zone/ REPORT sec. 2):
`Φ+(J,s-1;u*) = A* - ψ/(J+1)`, `Φ+(J,s+1;u*) = A* + ψ'/J`, `Φ-(J,s;y2) = -ψ/(J+1)`,
`Φ-(J,s+1;y1) = ψ/J`, `Φ+(J,s;u2) - Φ+(J,s+1;u2) = c/J`; and the rank-one collapse of the
main conditions `v_J - v_1 ∈ ℚ·ψvec` (one condition per position).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ.Q
open OAI.InternalCatalan

/-- `f J * (J+1)` is constant on the listed `J`. -/
def ConstTimes (f : ℕ → ℚ) (sh : ℕ) (Js : List ℕ) : Prop :=
  ∀ J ∈ Js, ∀ J' ∈ Js, f J * ((J : ℚ) + sh) = f J' * ((J' : ℚ) + sh)

instance (f : ℕ → ℚ) (sh : ℕ) (Js : List ℕ) : Decidable (ConstTimes f sh Js) := by
  unfold ConstTimes; infer_instance

-- Law_H, s = 4
theorem H_uStar_below : ConstTimes (fun J => 1 - fTp 4 uH J 3) 1 [0, 1, 2, 3] := by decide +kernel
theorem H_uStar_above : ConstTimes (fun J => fTp 4 uH J 5 - 1) 0 [2, 3, 4, 5] := by decide +kernel
theorem H_y2_s : ConstTimes (fun J => - fTm 4 y2H J 4) 1 [1, 2, 3] := by decide +kernel
theorem H_y1_s1 : ConstTimes (fun J => fTm 4 y1H J 5) 0 [2, 3, 4] := by decide +kernel
theorem H_u2_diff : ConstTimes (fun J => fTd 4 u2H J 5) 0 [2, 3, 4] := by decide +kernel

-- Law_L, s = 4
theorem L_uStar_below : ConstTimes (fun J => 1 - fTp 5 uL J 3) 1 [0, 1, 2, 3] := by decide +kernel
theorem L_uStar_above : ConstTimes (fun J => fTp 5 uL J 5 - 1) 0 [1, 2, 3, 4, 5] := by
  decide +kernel

/-- Rank-one collapse of the main conditions: `v_J - v_1 = (1/(J+1) - 1/2) · w`, `J = 2, 3`. -/
theorem H_main_rank_one : ∀ c ∈ [0, 1, 2, 3],
    ((vResp 4 uH u2H y1H y2H 2).getD c 0 - (vResp 4 uH u2H y1H y2H 1).getD c 0) * (1/4 - 1/2) =
    ((vResp 4 uH u2H y1H y2H 3).getD c 0 - (vResp 4 uH u2H y1H y2H 1).getD c 0) * (1/3 - 1/2) := by
  decide +kernel

theorem L_main_rank_one : ∀ c ∈ [0, 1, 2, 3],
    ((vResp 5 uL u2L y1L y2L 2).getD c 0 - (vResp 5 uL u2L y1L y2L 1).getD c 0) * (1/4 - 1/2) =
    ((vResp 5 uL u2L y1L y2L 3).getD c 0 - (vResp 5 uL u2L y1L y2L 1).getD c 0) * (1/3 - 1/2) := by
  decide +kernel

end CatalanMeasure.GenD.Uniform.W.ZoneZ.Q
