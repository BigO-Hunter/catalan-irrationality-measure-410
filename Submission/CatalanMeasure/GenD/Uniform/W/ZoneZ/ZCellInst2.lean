module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZCellInst
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem vv_eq_vRespP (K H J : ℕ) (u u2 y1 y2 : ℕ → ℚ) (c : ℕ) (hc : c < 4) :
    vv p K H (zvec p K u) (zvec p K u2) (zvec p K y1) (zvec p K y2) J c =
      (vRespP p K H J u u2 y1 y2).getD c 0 := by
  interval_cases c <;> rfl

theorem res_neg_of_mem (q : ℚ) (hq : q ∈ unitSub p) :
    palindromicRatResidue p (-q) = - palindromicRatResidue p q := by
  have := map_neg (resHom p) ⟨q, hq⟩
  simpa [resHom_apply] using this

theorem res_neg3 : palindromicRatResidue p (-3 : ℚ) = -3 := by
  have := palindromicRatResidue_intCast p (-3)
  simpa using this

theorem res_neg32 (hp2 : p ≠ 2) : palindromicRatResidue p (-3 / 2 : ℚ) = -3 / 2 := by
  have h32 := res_half3 hp2
  have hm := half3_mem (p := p) hp2
  have : (-3 / 2 : ℚ) = -(3 / 2 : ℚ) := by norm_num
  rw [this, res_neg_of_mem _ hm, h32]; ring

theorem neg3_mem : (-3 : ℚ) ∈ unitSub p := by
  show (((-3 : ℚ).den : ℕ) : ZMod p) ≠ 0
  have : (-3 : ℚ).den = 1 := by decide +kernel
  rw [this]; simp

theorem neg32_mem (hp2 : p ≠ 2) : (-3 / 2 : ℚ) ∈ unitSub p := by
  have : (-3 / 2 : ℚ) = -(3 / 2 : ℚ) := by norm_num
  rw [this]; exact Subring.neg_mem _ (half3_mem hp2)

section H
variable (hp2 : p ≠ 2) (hc : ¬ p ∣ ZcH)
include hp2 hc

theorem cellHyp_H {H : ℕ} (hH : 7 ≤ H) :
    CellHyp p 4 H (zvec p 4 Q.uH) (zvec p 4 Q.u2H) (zvec p 4 Q.y1H) (zvec p 4 Q.y2H)
      (palindromicRatResidue p (18795091 / 2065026 : ℚ)) (palindromicRatResidue p (0 : ℚ))
      (palindromicRatResidue p (105927881 / 6195078 : ℚ))
      (palindromicRatResidue p (-594979 / 688342 : ℚ)) ⟨3, by omega⟩ ⟨0, by omega⟩ where
  fold J hJ := H_uStar_fold hp2 hc hJ hH
  r1 c hc4 := by
    have := rank1_zmod (momUnits_H hp2 hc) (K := 4) (H := H) (J := 1) hH (by omega) Q.uH Q.u2H Q.y1H
      Q.y2H (fun k hk => uH_mem hp2 hc hk) (fun k hk => u2H_mem hp2 hc hk)
      (fun k hk => y1H_mem hp2 hc hk) (fun k hk => y2H_mem hp2 hc hk) (-3) neg3_mem
      H_v1_rank1 c hc4
    rw [vv_eq_vRespP 4 H 1 _ _ _ _ c hc4, vv_eq_vRespP 4 H 2 _ _ _ _ c hc4]
    rw [res_neg3] at this
    exact this
  r3 c hc4 := by
    have := rank1_zmod (momUnits_H hp2 hc) (K := 4) (H := H) (J := 3) hH (by omega) Q.uH Q.u2H Q.y1H
      Q.y2H (fun k hk => uH_mem hp2 hc hk) (fun k hk => u2H_mem hp2 hc hk)
      (fun k hk => y1H_mem hp2 hc hk) (fun k hk => y2H_mem hp2 hc hk) (-3 / 2) (neg32_mem hp2)
      H_v3_rank1 c hc4
    rw [vv_eq_vRespP 4 H 3 _ _ _ _ c hc4, vv_eq_vRespP 4 H 2 _ _ _ _ c hc4,
      vv_eq_vRespP 4 H 1 _ _ _ _ c hc4]
    rw [res_neg32 hp2] at this
    exact this
  ps c hc4 := by
    have := pstar_H_zmod hp2 hc hH c hc4
    have htop : topv (zvec p 4 Q.uH) (zvec p 4 Q.u2H) (zvec p 4 Q.y1H) (zvec p 4 Q.y2H)
        ⟨3, by omega⟩ c = palindromicRatResidue p ((Q.topVec 4 Q.uH Q.u2H Q.y1H Q.y2H).getD c 0) := by
      interval_cases c <;> rfl
    have hzero : zerov (zvec p 4 Q.uH) (zvec p 4 Q.u2H) (zvec p 4 Q.y1H) (zvec p 4 Q.y2H)
        ⟨0, by omega⟩ c = palindromicRatResidue p ((Q.zeroVec Q.uH Q.u2H Q.y1H Q.y2H).getD c 0) := by
      interval_cases c
      · rfl
      · rfl
      · show -palindromicRatResidue p (Q.y1H 0) = palindromicRatResidue p (-(Q.y1H 0))
        rw [res_neg_of_mem _ (y1H_mem hp2 hc (by omega))]
      · show -palindromicRatResidue p (Q.y2H 0) = palindromicRatResidue p (-(Q.y2H 0))
        rw [res_neg_of_mem _ (y2H_mem hp2 hc (by omega))]
    rw [vv_eq_vRespP 4 H 4 _ _ _ _ c hc4, vv_eq_vRespP 4 H 1 _ _ _ _ c hc4,
      vv_eq_vRespP 4 H 2 _ _ _ _ c hc4, vv_eq_vRespP 4 H 3 _ _ _ _ c hc4, htop, hzero]
    exact this

end H

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
