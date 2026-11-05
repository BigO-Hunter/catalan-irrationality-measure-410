module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.CellsZmod
@[expose] public section
set_option Elab.async false

/-!
# Rank-one structure of the main conditions, in `ZMod p`

`v_1 = -3 (v_2 - v_1)` and `v_3 = -(3/2) (v_2 - v_1)` (so `v_J = -w/(J+1)`, `w = 6 (v_2 - v_1)`),
exact over `ℚ` for Law_H (`s = 4`), then reduced mod `p`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Polynomial Module OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem H_v1_rank1 : ∀ c ∈ [0, 1, 2, 3],
    (Q.vResp 4 Q.uH Q.u2H Q.y1H Q.y2H 1).getD c 0 =
      (-3 : ℚ) * ((Q.vResp 4 Q.uH Q.u2H Q.y1H Q.y2H 2).getD c 0 -
        (Q.vResp 4 Q.uH Q.u2H Q.y1H Q.y2H 1).getD c 0) := by decide +kernel

theorem H_v3_rank1 : ∀ c ∈ [0, 1, 2, 3],
    (Q.vResp 4 Q.uH Q.u2H Q.y1H Q.y2H 3).getD c 0 =
      (-3 / 2 : ℚ) * ((Q.vResp 4 Q.uH Q.u2H Q.y1H Q.y2H 2).getD c 0 -
        (Q.vResp 4 Q.uH Q.u2H Q.y1H Q.y2H 1).getD c 0) := by decide +kernel

/-- Generic reduction of `V_J = m (V_2 - V_1)`. -/
theorem rank1_zmod (hm : MomUnits p) {K H J : ℕ} (hH : 7 ≤ H) (hJ : J < 7) (u u2 y1 y2 : ℕ → ℚ)
    (hu : ∀ k < K, u k ∈ unitSub p) (hu2 : ∀ k < K, u2 k ∈ unitSub p)
    (hy1 : ∀ k < K, y1 k ∈ unitSub p) (hy2 : ∀ k < K, y2 k ∈ unitSub p) (m : ℚ)
    (hmm : m ∈ unitSub p)
    (hQ : ∀ c ∈ [0, 1, 2, 3], (Q.vResp K u u2 y1 y2 J).getD c 0 =
      m * ((Q.vResp K u u2 y1 y2 2).getD c 0 - (Q.vResp K u u2 y1 y2 1).getD c 0))
    (c : ℕ) (hc : c < 4) :
    (vRespP p K H J u u2 y1 y2).getD c 0 = palindromicRatResidue p m *
      ((vRespP p K H 2 u u2 y1 y2).getD c 0 - (vRespP p K H 1 u u2 y1 y2).getD c 0) := by
  have mem := fun J' (hJ' : J' < 7) => vResp_getD_mem hm u u2 y1 y2 hu hu2 hy1 hy2 hJ' c hc
  have key := congrArg (resHom p) (Subtype.ext (hQ c (by interval_cases c <;> simp)) :
    (⟨(Q.vResp K u u2 y1 y2 J).getD c 0, mem J hJ⟩ : unitSub p) =
      ⟨m, hmm⟩ * (⟨(Q.vResp K u u2 y1 y2 2).getD c 0, mem 2 (by omega)⟩ -
        ⟨(Q.vResp K u u2 y1 y2 1).getD c 0, mem 1 (by omega)⟩))
  simp only [map_mul, map_sub, resHom_apply] at key
  rw [vRespP_eq hm u u2 y1 y2 hu hu2 hy1 hy2 hJ hH c hc,
    vRespP_eq hm u u2 y1 y2 hu hu2 hy1 hy2 (by omega) hH c hc,
    vRespP_eq hm u u2 y1 y2 hu hu2 hy1 hy2 (by omega) hH c hc]
  exact key

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
