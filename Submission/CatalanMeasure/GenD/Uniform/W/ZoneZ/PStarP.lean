module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.CellFactsP
@[expose] public section
set_option Elab.async false

/-!
# (P*) at `s = 4` in `ZMod p` (Law_H and Law_L)

The exact rational identity of `CellsL` (`pstar_H`, `pstar_L`), reduced mod `p`, for every
prime `p ∤ ZcH` (resp. `ZcL`), `p ≠ 2`.  Statement: for the four coordinates `c`,

    v_4[c] - v_1[c] = μ₂ (v_2[c] - v_1[c]) + μ₃ (v_3[c] - v_1[c]) + ν t[c] + ρ b0[c],

with `v_J = (ψ+(J,3)-ψ+(J,4) on u*, same on u2, ψ-(J,4) on y1, on y2)`, `t` the top-block
values and `b0 = (u*_0, u2_0, -y1_0, -y2_0)`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Polynomial Module OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem vResp_getD_mem (hm : MomUnits p) {K : ℕ} (u u2 y1 y2 : ℕ → ℚ)
    (hu : ∀ k < K, u k ∈ unitSub p) (hu2 : ∀ k < K, u2 k ∈ unitSub p)
    (hy1 : ∀ k < K, y1 k ∈ unitSub p) (hy2 : ∀ k < K, y2 k ∈ unitSub p)
    {J : ℕ} (hJ : J < 7) (c : ℕ) (hc : c < 4) :
    (Q.vResp K u u2 y1 y2 J).getD c 0 ∈ unitSub p := by
  have d4 : ∀ z : ℕ → ℚ, (∀ k < K, z k ∈ unitSub p) → Q.fTd K z J 4 ∈ unitSub p := by
    intro z hz
    rw [show (4 : ℕ) = 3 + 1 from rfl, fTd_succ]
    exact Subring.sub_mem _ (fTp_mem hm z hz hJ (by omega)) (fTp_mem hm z hz hJ (by omega))
  interval_cases c
  · simpa [Q.vResp] using d4 u hu
  · simpa [Q.vResp] using d4 u2 hu2
  · simpa [Q.vResp] using fTm_mem hm y1 hy1 hJ (σ := 4) (by omega)
  · simpa [Q.vResp] using fTm_mem hm y2 hy2 hJ (σ := 4) (by omega)

theorem topVec_getD_mem {K : ℕ} (u u2 y1 y2 : ℕ → ℚ)
    (hu : ∀ k < K, u k ∈ unitSub p) (hu2 : ∀ k < K, u2 k ∈ unitSub p)
    (hy1 : ∀ k < K, y1 k ∈ unitSub p) (hy2 : ∀ k < K, y2 k ∈ unitSub p) (hK : 0 < K)
    (c : ℕ) (hc : c < 4) : (Q.topVec K u u2 y1 y2).getD c 0 ∈ unitSub p := by
  interval_cases c
  · simpa [Q.topVec] using hu (K - 1) (by omega)
  · simpa [Q.topVec] using hu2 (K - 1) (by omega)
  · simpa [Q.topVec] using hy1 (K - 1) (by omega)
  · simpa [Q.topVec] using hy2 (K - 1) (by omega)

theorem zeroVec_getD_mem {K : ℕ} (u u2 y1 y2 : ℕ → ℚ)
    (hu : ∀ k < K, u k ∈ unitSub p) (hu2 : ∀ k < K, u2 k ∈ unitSub p)
    (hy1 : ∀ k < K, y1 k ∈ unitSub p) (hy2 : ∀ k < K, y2 k ∈ unitSub p) (hK : 0 < K)
    (c : ℕ) (hc : c < 4) : (Q.zeroVec u u2 y1 y2).getD c 0 ∈ unitSub p := by
  interval_cases c
  · simpa [Q.zeroVec] using hu 0 hK
  · simpa [Q.zeroVec] using hu2 0 hK
  · simpa [Q.zeroVec] using Subring.neg_mem _ (hy1 0 hK)
  · simpa [Q.zeroVec] using Subring.neg_mem _ (hy2 0 hK)

/-- Generic transfer of (P*). -/
theorem pstar_zmod (hm : MomUnits p) {K H : ℕ} (hK : 0 < K) (hH : 7 ≤ H)
    (u u2 y1 y2 : ℕ → ℚ)
    (hu : ∀ k < K, u k ∈ unitSub p) (hu2 : ∀ k < K, u2 k ∈ unitSub p)
    (hy1 : ∀ k < K, y1 k ∈ unitSub p) (hy2 : ∀ k < K, y2 k ∈ unitSub p)
    (μ2 μ3 ν ρ : ℚ) (h2 : μ2 ∈ unitSub p) (h3 : μ3 ∈ unitSub p) (hn : ν ∈ unitSub p)
    (hr : ρ ∈ unitSub p) (hP : Q.PStar K u u2 y1 y2 μ2 μ3 ν ρ) (c : ℕ) (hc : c < 4) :
    (vRespP p K H 4 u u2 y1 y2).getD c 0 - (vRespP p K H 1 u u2 y1 y2).getD c 0 =
      palindromicRatResidue p μ2 *
        ((vRespP p K H 2 u u2 y1 y2).getD c 0 - (vRespP p K H 1 u u2 y1 y2).getD c 0) +
      palindromicRatResidue p μ3 *
        ((vRespP p K H 3 u u2 y1 y2).getD c 0 - (vRespP p K H 1 u u2 y1 y2).getD c 0) +
      palindromicRatResidue p ν * palindromicRatResidue p ((Q.topVec K u u2 y1 y2).getD c 0) +
      palindromicRatResidue p ρ * palindromicRatResidue p ((Q.zeroVec u u2 y1 y2).getD c 0) := by
  have key := res_pstar_form (p := p)
    (vResp_getD_mem hm u u2 y1 y2 hu hu2 hy1 hy2 (J := 1) (by omega) c hc)
    (vResp_getD_mem hm u u2 y1 y2 hu hu2 hy1 hy2 (J := 2) (by omega) c hc)
    (vResp_getD_mem hm u u2 y1 y2 hu hu2 hy1 hy2 (J := 3) (by omega) c hc)
    (vResp_getD_mem hm u u2 y1 y2 hu hu2 hy1 hy2 (J := 4) (by omega) c hc)
    h2 h3 hn hr (topVec_getD_mem u u2 y1 y2 hu hu2 hy1 hy2 hK c hc)
    (zeroVec_getD_mem u u2 y1 y2 hu hu2 hy1 hy2 hK c hc)
    (hP c (by interval_cases c <;> simp))
  rw [vRespP_eq hm u u2 y1 y2 hu hu2 hy1 hy2 (by omega) hH c hc,
    vRespP_eq hm u u2 y1 y2 hu hu2 hy1 hy2 (by omega) hH c hc,
    vRespP_eq hm u u2 y1 y2 hu hu2 hy1 hy2 (by omega) hH c hc,
    vRespP_eq hm u u2 y1 y2 hu hu2 hy1 hy2 (by omega) hH c hc]
  exact key

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
