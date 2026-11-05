module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ2.CellsL1
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZCap1
@[expose] public section
set_option Elab.async false

/-!
# Law_L(4) cells in `ZMod p` (G2h)

`cellHyp_L : CellHyp p 5 H …` (same shape as Law_H, with `μ_3 = 0`, top block `4`, block `0`), the
extra digit-`0` facts (`fold0`, `r0`) and the cap fact `z_1 = 2 z_2`; the Law_L independence hypotheses.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- Digit-`0` facts of the Law_L cell: `ψ+(0,4)(u*) = 1` and `v_0 = -6 (v_2 - v_1)`. -/
structure CellHyp0 (p K H : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) : Prop where
  fold0 : fuV p K H u 0 ((4 : ℕ) : ℤ) = 1
  r0 : ∀ c < 4, vv p K H u u2 y1 y2 0 c = -6 * (vv p K H u u2 y1 y2 2 c - vv p K H u u2 y1 y2 1 c)

/-- Cap fact for `J = 1`: `z_1 = 2 z_2`. -/
structure CellHypCap1 (p K H : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) : Prop where
  zr1 : ∀ c < 4, zz p K H u u2 y1 y2 1 c = 2 * zz p K H u u2 y1 y2 2 c

section L
variable (hp2 : p ≠ 2) (hc : ¬ p ∣ ZcL)
include hp2 hc

theorem neg6_mem : (-6 : ℚ) ∈ unitSub p := by
  show (((-6 : ℚ).den : ℕ) : ZMod p) ≠ 0
  have : (-6 : ℚ).den = 1 := by decide +kernel
  rw [this]; simp

theorem res_neg6 : palindromicRatResidue p (-6 : ℚ) = -6 := by
  have := palindromicRatResidue_intCast p (-6)
  simpa using this

theorem cellHyp_L {H : ℕ} (hH : 7 ≤ H) :
    CellHyp p 5 H (zvec p 5 Q.uL) (zvec p 5 Q.u2L) (zvec p 5 Q.y1L) (zvec p 5 Q.y2L)
      (palindromicRatResidue p (75682715747 / 5165255043 : ℚ)) (palindromicRatResidue p (0 : ℚ))
      (palindromicRatResidue p (-488670298849 / 61983060516 : ℚ))
      (palindromicRatResidue p (-946593725 / 3443503362 : ℚ)) ⟨4, by omega⟩ ⟨0, by omega⟩ where
  fold J hJ := L_uStar_fold hp2 hc (by simp at hJ ⊢; omega) hH
  r1 c hc4 := by
    have := rank1_zmod (momUnits_L hp2 hc) (K := 5) (H := H) (J := 1) hH (by omega) Q.uL Q.u2L Q.y1L
      Q.y2L (fun k hk => uL_mem hp2 hc hk) (fun k hk => u2L_mem hp2 hc hk)
      (fun k hk => y1L_mem hp2 hc hk) (fun k hk => y2L_mem hp2 hc hk) (-3) neg3_mem
      Q.L_v1_rank1 c hc4
    rw [vv_eq_vRespP 5 H 1 _ _ _ _ c hc4, vv_eq_vRespP 5 H 2 _ _ _ _ c hc4]
    rw [res_neg3] at this
    exact this
  r3 c hc4 := by
    have := rank1_zmod (momUnits_L hp2 hc) (K := 5) (H := H) (J := 3) hH (by omega) Q.uL Q.u2L Q.y1L
      Q.y2L (fun k hk => uL_mem hp2 hc hk) (fun k hk => u2L_mem hp2 hc hk)
      (fun k hk => y1L_mem hp2 hc hk) (fun k hk => y2L_mem hp2 hc hk) (-3 / 2) (neg32_mem hp2)
      Q.L_v3_rank1 c hc4
    rw [vv_eq_vRespP 5 H 3 _ _ _ _ c hc4, vv_eq_vRespP 5 H 2 _ _ _ _ c hc4,
      vv_eq_vRespP 5 H 1 _ _ _ _ c hc4]
    rw [res_neg32 hp2] at this
    exact this
  ps c hc4 := by
    have := pstar_L_zmod hp2 hc hH c hc4
    have htop : topv (zvec p 5 Q.uL) (zvec p 5 Q.u2L) (zvec p 5 Q.y1L) (zvec p 5 Q.y2L)
        ⟨4, by omega⟩ c = palindromicRatResidue p ((Q.topVec 5 Q.uL Q.u2L Q.y1L Q.y2L).getD c 0) := by
      interval_cases c <;> rfl
    have hzero : zerov (zvec p 5 Q.uL) (zvec p 5 Q.u2L) (zvec p 5 Q.y1L) (zvec p 5 Q.y2L)
        ⟨0, by omega⟩ c = palindromicRatResidue p ((Q.zeroVec Q.uL Q.u2L Q.y1L Q.y2L).getD c 0) := by
      interval_cases c
      · rfl
      · rfl
      · show -palindromicRatResidue p (Q.y1L 0) = palindromicRatResidue p (-(Q.y1L 0))
        rw [res_neg_of_mem _ (y1L_mem hp2 hc (by omega))]
      · show -palindromicRatResidue p (Q.y2L 0) = palindromicRatResidue p (-(Q.y2L 0))
        rw [res_neg_of_mem _ (y2L_mem hp2 hc (by omega))]
    rw [vv_eq_vRespP 5 H 4 _ _ _ _ c hc4, vv_eq_vRespP 5 H 1 _ _ _ _ c hc4,
      vv_eq_vRespP 5 H 2 _ _ _ _ c hc4, vv_eq_vRespP 5 H 3 _ _ _ _ c hc4, htop, hzero]
    exact this

theorem cellHyp0_L {H : ℕ} (hH : 7 ≤ H) :
    CellHyp0 p 5 H (zvec p 5 Q.uL) (zvec p 5 Q.u2L) (zvec p 5 Q.y1L) (zvec p 5 Q.y2L) where
  fold0 := L_uStar_fold hp2 hc (by simp) hH
  r0 c hc4 := by
    have := rank1_zmod (momUnits_L hp2 hc) (K := 5) (H := H) (J := 0) hH (by omega) Q.uL Q.u2L Q.y1L
      Q.y2L (fun k hk => uL_mem hp2 hc hk) (fun k hk => u2L_mem hp2 hc hk)
      (fun k hk => y1L_mem hp2 hc hk) (fun k hk => y2L_mem hp2 hc hk) (-6) (neg6_mem hp2 hc)
      Q.L_v0_rank1 c hc4
    rw [vv_eq_vRespP 5 H 0 _ _ _ _ c hc4, vv_eq_vRespP 5 H 2 _ _ _ _ c hc4,
      vv_eq_vRespP 5 H 1 _ _ _ _ c hc4]
    rw [res_neg6 hp2 hc] at this
    exact this

theorem cellHypCap_L {H : ℕ} (hH : 8 ≤ H) :
    CellHypCap p 5 H (zvec p 5 Q.uL) (zvec p 5 Q.u2L) (zvec p 5 Q.y1L) (zvec p 5 Q.y2L) := by
  have hm := momUnits_L hp2 hc
  have mu : ∀ k < 5, Q.uL k ∈ unitSub p := fun k hk => uL_mem hp2 hc hk
  have mu2 : ∀ k < 5, Q.u2L k ∈ unitSub p := fun k hk => u2L_mem hp2 hc hk
  have my1 : ∀ k < 5, Q.y1L k ∈ unitSub p := fun k hk => y1L_mem hp2 hc hk
  have my2 : ∀ k < 5, Q.y2L k ∈ unitSub p := fun k hk => y2L_mem hp2 hc hk
  constructor
  · intro c hc4
    have := zrank_int hm hH Q.uL Q.u2L Q.y1L Q.y2L mu mu2 my1 my2
      3 2 (by omega) (by omega) 3 2 (by simpa using Q.L_z3_rank) c hc4
    simpa using this
  · intro c hc4
    have := zrank_int hm hH Q.uL Q.u2L Q.y1L Q.y2L mu mu2 my1 my2
      4 2 (by omega) (by omega) 2 1 (by simpa using Q.L_z4_rank) c hc4
    simpa using this

theorem cellHypCap1_L {H : ℕ} (hH : 8 ≤ H) :
    CellHypCap1 p 5 H (zvec p 5 Q.uL) (zvec p 5 Q.u2L) (zvec p 5 Q.y1L) (zvec p 5 Q.y2L) := by
  have hm := momUnits_L hp2 hc
  constructor
  · intro c hc4
    have := zrank_int hm hH Q.uL Q.u2L Q.y1L Q.y2L (fun k hk => uL_mem hp2 hc hk)
      (fun k hk => u2L_mem hp2 hc hk) (fun k hk => y1L_mem hp2 hc hk) (fun k hk => y2L_mem hp2 hc hk)
      1 2 (by omega) (by omega) 1 2 (by simpa using Q.L_z1_rank) c hc4
    simpa using this

end L

/-- Final bad-prime integer for Law_L (with the independence numerators). -/
def ZcL' : ℕ := Nat.lcm ZcL (Nat.lcm DqUL.num.natAbs DqYL.num.natAbs)

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
