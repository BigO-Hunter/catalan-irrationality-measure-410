module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.PStarP
@[expose] public section
set_option Elab.async false

/-!
# The cell facts of Theorem Z at `s = 4`, in `ZMod p`

Everything the zone count uses about the cells, for `p ≠ 2`, `p ∤ ZcH` (Law_H) or `p ∤ ZcL`
(Law_L):  cell properties (fold / raw), (P*), reduced from the exact rational checks of
`CellsH`/`CellsL`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Polynomial Module OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- (P*) for Law_H at `s = 4`. -/
theorem pstar_H_zmod (hp2 : p ≠ 2) (hc : ¬ p ∣ ZcH) {H : ℕ} (hH : 7 ≤ H) (c : ℕ) (hc4 : c < 4) :
    (vRespP p 4 H 4 Q.uH Q.u2H Q.y1H Q.y2H).getD c 0 -
      (vRespP p 4 H 1 Q.uH Q.u2H Q.y1H Q.y2H).getD c 0 =
    palindromicRatResidue p (18795091 / 2065026 : ℚ) *
      ((vRespP p 4 H 2 Q.uH Q.u2H Q.y1H Q.y2H).getD c 0 -
        (vRespP p 4 H 1 Q.uH Q.u2H Q.y1H Q.y2H).getD c 0) +
    palindromicRatResidue p (0 : ℚ) *
      ((vRespP p 4 H 3 Q.uH Q.u2H Q.y1H Q.y2H).getD c 0 -
        (vRespP p 4 H 1 Q.uH Q.u2H Q.y1H Q.y2H).getD c 0) +
    palindromicRatResidue p (105927881 / 6195078 : ℚ) *
      palindromicRatResidue p ((Q.topVec 4 Q.uH Q.u2H Q.y1H Q.y2H).getD c 0) +
    palindromicRatResidue p (-594979 / 688342 : ℚ) *
      palindromicRatResidue p ((Q.zeroVec Q.uH Q.u2H Q.y1H Q.y2H).getD c 0) :=
  pstar_zmod (momUnits_H hp2 hc) (by omega) hH Q.uH Q.u2H Q.y1H Q.y2H
    (fun k hk => uH_mem hp2 hc hk) (fun k hk => u2H_mem hp2 hc hk)
    (fun k hk => y1H_mem hp2 hc hk) (fun k hk => y2H_mem hp2 hc hk)
    _ _ _ _ (mem_unitSub_of_dvd coefH_den.1 hc) (Subring.zero_mem _)
    (mem_unitSub_of_dvd coefH_den.2.1 hc) (mem_unitSub_of_dvd coefH_den.2.2 hc)
    Q.pstar_H c hc4

section L
variable (hp2 : p ≠ 2) (hc : ¬ p ∣ ZcL)
include hp2 hc

theorem momUnits_L : MomUnits p := ⟨hp2, fun h => hc (h.trans Zmom_dvd_ZcL)⟩

theorem uL_mem {k : ℕ} (hk : k < 5) : Q.uL k ∈ unitSub p := mem_unitSub_of_dvd (uL_den k hk).1 hc
theorem u2L_mem {k : ℕ} (hk : k < 5) : Q.u2L k ∈ unitSub p :=
  mem_unitSub_of_dvd (uL_den k hk).2.1 hc
theorem y1L_mem {k : ℕ} (hk : k < 5) : Q.y1L k ∈ unitSub p :=
  mem_unitSub_of_dvd (uL_den k hk).2.2.1 hc
theorem y2L_mem {k : ℕ} (hk : k < 5) : Q.y2L k ∈ unitSub p :=
  mem_unitSub_of_dvd (uL_den k hk).2.2.2 hc

/-- ψ+ of `u*` at `σ = 4` is `1` for `J = 0..4` (Law_L). -/
theorem L_uStar_fold {H J : ℕ} (hJ : J ∈ [0, 1, 2, 3, 4]) (hH : 7 ≤ H) :
    (profTp p 5).psi H J (4 : ℕ) (zvec p 5 Q.uL) = 1 := by
  have hJ7 : J < 7 := by simp at hJ; omega
  rw [psiTp_zvec (momUnits_L hp2 hc) Q.uL (fun k hk => uL_mem hp2 hc hk) hJ7 (by omega) hH,
    Q.uL_fold J hJ, res_one]

theorem L_u2_raw {H J : ℕ} (hJ : J ∈ [0, 1, 2, 3]) (hH : 7 ≤ H) :
    (profTp p 5).psi H J (3 : ℕ) (zvec p 5 Q.u2L) = (profTp p 5).psi H J (4 : ℕ) (zvec p 5 Q.u2L) := by
  have hJ7 : J < 7 := by simp at hJ; omega
  have hm := momUnits_L hp2 hc
  rw [psiTp_zvec hm Q.u2L (fun k hk => u2L_mem hp2 hc hk) hJ7 (by omega) (by omega),
    psiTp_zvec hm Q.u2L (fun k hk => u2L_mem hp2 hc hk) hJ7 (by omega) hH]
  have := Q.u2L_raw J hJ
  rw [fTd_succ] at this
  congr 1
  linarith

theorem L_y1_raw {H J : ℕ} (hJ : J ∈ [0, 1, 2, 3]) (hH : 7 ≤ H) :
    (profTm p 5).psi H J (4 : ℕ) (zvec p 5 Q.y1L) = 0 := by
  have hJ7 : J < 7 := by simp at hJ; omega
  rw [psiTm_zvec (momUnits_L hp2 hc) Q.y1L (fun k hk => y1L_mem hp2 hc hk) hJ7 (by omega) hH,
    Q.y1L_raw J hJ, res_zero]

theorem L_y2_raw {H J : ℕ} (hJ : J ∈ [1, 2, 3, 4]) (hH : 8 ≤ H) :
    (profTm p 5).psi H J (5 : ℕ) (zvec p 5 Q.y2L) = 0 := by
  have hJ7 : J < 7 := by simp at hJ; omega
  rw [psiTm_zvec (momUnits_L hp2 hc) Q.y2L (fun k hk => y2L_mem hp2 hc hk) hJ7 (by omega) hH,
    Q.y2L_raw J hJ, res_zero]

/-- (P*) for Law_L at `s = 4`. -/
theorem pstar_L_zmod {H : ℕ} (hH : 7 ≤ H) (c : ℕ) (hc4 : c < 4) :
    (vRespP p 5 H 4 Q.uL Q.u2L Q.y1L Q.y2L).getD c 0 -
      (vRespP p 5 H 1 Q.uL Q.u2L Q.y1L Q.y2L).getD c 0 =
    palindromicRatResidue p (75682715747 / 5165255043 : ℚ) *
      ((vRespP p 5 H 2 Q.uL Q.u2L Q.y1L Q.y2L).getD c 0 -
        (vRespP p 5 H 1 Q.uL Q.u2L Q.y1L Q.y2L).getD c 0) +
    palindromicRatResidue p (0 : ℚ) *
      ((vRespP p 5 H 3 Q.uL Q.u2L Q.y1L Q.y2L).getD c 0 -
        (vRespP p 5 H 1 Q.uL Q.u2L Q.y1L Q.y2L).getD c 0) +
    palindromicRatResidue p (-488670298849 / 61983060516 : ℚ) *
      palindromicRatResidue p ((Q.topVec 5 Q.uL Q.u2L Q.y1L Q.y2L).getD c 0) +
    palindromicRatResidue p (-946593725 / 3443503362 : ℚ) *
      palindromicRatResidue p ((Q.zeroVec Q.uL Q.u2L Q.y1L Q.y2L).getD c 0) :=
  pstar_zmod (momUnits_L hp2 hc) (by omega) hH Q.uL Q.u2L Q.y1L Q.y2L
    (fun k hk => uL_mem hp2 hc hk) (fun k hk => u2L_mem hp2 hc hk)
    (fun k hk => y1L_mem hp2 hc hk) (fun k hk => y2L_mem hp2 hc hk)
    _ _ _ _ (mem_unitSub_of_dvd coefL_den.1 hc) (Subring.zero_mem _)
    (mem_unitSub_of_dvd coefL_den.2.1 hc) (mem_unitSub_of_dvd coefL_den.2.2 hc)
    Q.pstar_L c hc4

end L

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
