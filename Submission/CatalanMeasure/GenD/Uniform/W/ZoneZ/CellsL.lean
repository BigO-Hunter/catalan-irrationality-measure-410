module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.CellsH
@[expose] public section
set_option Elab.async false

/-!
# (P*) at `s = 4`: Law_H (blocks `0..3`) and Law_L (blocks `0..4`)
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ.Q
open OAI.InternalCatalan

/-- The four window-`s` response vectors `v_J = (Td(u*), Td(u2), T-(y1), T-(y2))` at `s = 4`. -/
def vResp (K : ℕ) (u u2 y1 y2 : ℕ → ℚ) (J : ℕ) : List ℚ :=
  [fTd K u J 4, fTd K u2 J 4, fTm K y1 J 4, fTm K y2 J 4]

/-- Top-block and block-0 vectors. -/
def topVec (K : ℕ) (u u2 y1 y2 : ℕ → ℚ) : List ℚ := [u (K - 1), u2 (K - 1), y1 (K - 1), y2 (K - 1)]
def zeroVec (u u2 y1 y2 : ℕ → ℚ) : List ℚ := [u 0, u2 0, - y1 0, - y2 0]

/-- (P*): `v_4 - v_1 = μ_2 (v_2 - v_1) + μ_3 (v_3 - v_1) + ν t + ρ b0`, coordinatewise. -/
def PStar (K : ℕ) (u u2 y1 y2 : ℕ → ℚ) (μ2 μ3 ν ρ : ℚ) : Prop :=
  ∀ c ∈ [0, 1, 2, 3],
    (vResp K u u2 y1 y2 4).getD c 0 - (vResp K u u2 y1 y2 1).getD c 0 =
      μ2 * ((vResp K u u2 y1 y2 2).getD c 0 - (vResp K u u2 y1 y2 1).getD c 0) +
      μ3 * ((vResp K u u2 y1 y2 3).getD c 0 - (vResp K u u2 y1 y2 1).getD c 0) +
      ν * (topVec K u u2 y1 y2).getD c 0 + ρ * (zeroVec u u2 y1 y2).getD c 0

instance (K : ℕ) (u u2 y1 y2 : ℕ → ℚ) (μ2 μ3 ν ρ : ℚ) :
    Decidable (PStar K u u2 y1 y2 μ2 μ3 ν ρ) := by unfold PStar; infer_instance

theorem pstar_H : PStar 4 uH u2H y1H y2H (18795091/2065026) 0 (105927881/6195078)
    (-594979/688342) := by decide +kernel

def uL : ℕ → ℚ := vecOf [(16335250408/4836845981), (15991309929/4836845981),
  (8279432410/4836845981), (178863075/439713271), (1254820503/4836845981)]
def u2L : ℕ → ℚ := vecOf [(427077419/50393059), (418094758/50393059), (296992046/50393059),
  (195129298/151179177), 1]
def y1L : ℕ → ℚ := vecOf [(8664930857/152048223), (-1821296080/50682741), (65977256/16894247),
  (-50110016/16894247), 1]
def y2L : ℕ → ℚ := vecOf [(419275949383/5438040633), (-16403904265/604226737),
  (2560320080/604226737), (-3450530161/1812680211), 1]

theorem uL_fold : ∀ J ∈ [0, 1, 2, 3, 4], fTp 5 uL J 4 = 1 := by decide +kernel
theorem u2L_raw : ∀ J ∈ [0, 1, 2, 3], fTd 5 u2L J 4 = 0 := by decide +kernel
theorem y1L_raw : ∀ J ∈ [0, 1, 2, 3], fTm 5 y1L J 4 = 0 := by decide +kernel
theorem y2L_raw : ∀ J ∈ [1, 2, 3, 4], fTm 5 y2L J 5 = 0 := by decide +kernel

theorem pstar_L : PStar 5 uL u2L y1L y2L (75682715747/5165255043) 0 (-488670298849/61983060516)
    (-946593725/3443503362) := by decide +kernel

end CatalanMeasure.GenD.Uniform.W.ZoneZ.Q
