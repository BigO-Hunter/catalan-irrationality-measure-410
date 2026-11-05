module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.CellFacts
@[expose] public section
set_option Elab.async false

/-!
# Law_H / Law_L cells at `s = 4`, in `ZMod p`

`ZcH`, `ZcL` are the explicit bad-prime integers (Lemma B: only `¬ p ∣ Zc` is used).  For
`p ∤ Zc` the covectors `ψ(J,σ)` of the slot systems on the residue cells satisfy:

* cell properties: `ψ+(J,4)(u*) = 1`, raw `Td` of `u2`, raw `T-` of `y1`, `y2`;
* (P*): `v_4 - v_1 = μ₂ (v_2 - v_1) + μ₃ (v_3 - v_1) + ν t + ρ b0`;
* rank one: `(v_2 - v_1)(1/4 - 1/2) = (v_3 - v_1)(1/3 - 1/2)`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Polynomial Module OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- Bad-prime integer of the Law_H cells at `s = 4`. -/
def ZcH : ℕ :=
  (((List.range 4).flatMap fun k => [(Q.uH k).den, (Q.u2H k).den, (Q.y1H k).den, (Q.y2H k).den]) ++
    [(18795091 / 2065026 : ℚ).den, (105927881 / 6195078 : ℚ).den, (-594979 / 688342 : ℚ).den]
  ).foldl Nat.lcm Zmom

/-- Bad-prime integer of the Law_L cells at `s = 4`. -/
def ZcL : ℕ :=
  (((List.range 5).flatMap fun k => [(Q.uL k).den, (Q.u2L k).den, (Q.y1L k).den, (Q.y2L k).den]) ++
    [(75682715747 / 5165255043 : ℚ).den, (-488670298849 / 61983060516 : ℚ).den,
      (-946593725 / 3443503362 : ℚ).den]).foldl Nat.lcm Zmom

theorem foldl_lcm_start (l : List ℕ) (a : ℕ) : a ∣ l.foldl Nat.lcm a := by
  induction l generalizing a with
  | nil => exact dvd_rfl
  | cons y l ih => exact (Nat.dvd_lcm_left a y).trans (ih _)

theorem fTd_succ (K : ℕ) (z : ℕ → ℚ) (J S : ℕ) :
    Q.fTd K z J (S + 1) = Q.fTp K z J S - Q.fTp K z J (S + 1) := by
  unfold Q.fTd Q.fTp Q.comb Q.PhiTd
  simp only [Nat.add_sub_cancel, mul_sub, Finset.sum_sub_distrib]

theorem res_one : palindromicRatResidue p (1 : ℚ) = 1 := by simp [palindromicRatResidue]
theorem res_zero : palindromicRatResidue p (0 : ℚ) = 0 := by simp [palindromicRatResidue]

theorem Zmom_dvd_ZcH : Zmom ∣ ZcH := by
  unfold ZcH
  exact foldl_lcm_start _ _

theorem Zmom_dvd_ZcL : Zmom ∣ ZcL := by
  unfold ZcL
  exact foldl_lcm_start _ _

theorem uH_den : ∀ k < 4, (Q.uH k).den ∣ ZcH ∧ (Q.u2H k).den ∣ ZcH ∧ (Q.y1H k).den ∣ ZcH ∧
    (Q.y2H k).den ∣ ZcH := by decide +kernel
theorem uL_den : ∀ k < 5, (Q.uL k).den ∣ ZcL ∧ (Q.u2L k).den ∣ ZcL ∧ (Q.y1L k).den ∣ ZcL ∧
    (Q.y2L k).den ∣ ZcL := by decide +kernel
theorem coefH_den : (18795091 / 2065026 : ℚ).den ∣ ZcH ∧ (105927881 / 6195078 : ℚ).den ∣ ZcH ∧
    (-594979 / 688342 : ℚ).den ∣ ZcH := by decide +kernel
theorem coefL_den : (75682715747 / 5165255043 : ℚ).den ∣ ZcL ∧
    (-488670298849 / 61983060516 : ℚ).den ∣ ZcL ∧ (-946593725 / 3443503362 : ℚ).den ∣ ZcL := by
  decide +kernel

section H
variable (hp2 : p ≠ 2) (hc : ¬ p ∣ ZcH)
include hp2 hc

theorem momUnits_H : MomUnits p :=
  ⟨hp2, fun h => hc (h.trans Zmom_dvd_ZcH)⟩

theorem uH_mem {k : ℕ} (hk : k < 4) : Q.uH k ∈ unitSub p := mem_unitSub_of_dvd (uH_den k hk).1 hc
theorem u2H_mem {k : ℕ} (hk : k < 4) : Q.u2H k ∈ unitSub p :=
  mem_unitSub_of_dvd (uH_den k hk).2.1 hc
theorem y1H_mem {k : ℕ} (hk : k < 4) : Q.y1H k ∈ unitSub p :=
  mem_unitSub_of_dvd (uH_den k hk).2.2.1 hc
theorem y2H_mem {k : ℕ} (hk : k < 4) : Q.y2H k ∈ unitSub p :=
  mem_unitSub_of_dvd (uH_den k hk).2.2.2 hc

/-- ψ+ of `u*` at `σ = 4` is `1` for `J = 1..4`. -/
theorem H_uStar_fold {H J : ℕ} (hJ : J ∈ [1, 2, 3, 4]) (hH : 7 ≤ H) :
    (profTp p 4).psi H J (4 : ℕ) (zvec p 4 Q.uH) = 1 := by
  have hJ7 : J < 7 := by simp at hJ; omega
  rw [psiTp_zvec (momUnits_H hp2 hc) Q.uH (fun k hk => uH_mem hp2 hc hk) hJ7 (by omega) hH,
    Q.uH_fold J hJ, res_one]

/-- raw `Td` of `u2`: `ψ+(J,3) = ψ+(J,4)`, `J = 1..3`. -/
theorem H_u2_raw {H J : ℕ} (hJ : J ∈ [1, 2, 3]) (hH : 7 ≤ H) :
    (profTp p 4).psi H J (3 : ℕ) (zvec p 4 Q.u2H) = (profTp p 4).psi H J (4 : ℕ) (zvec p 4 Q.u2H) := by
  have hJ7 : J < 7 := by simp at hJ; omega
  have hm := momUnits_H hp2 hc
  rw [psiTp_zvec hm Q.u2H (fun k hk => u2H_mem hp2 hc hk) hJ7 (by omega) (by omega),
    psiTp_zvec hm Q.u2H (fun k hk => u2H_mem hp2 hc hk) hJ7 (by omega) hH]
  have := Q.u2H_raw J hJ
  rw [fTd_succ] at this
  congr 1
  linarith

/-- raw `T-` of `y1`: `ψ-(J,4) = 0`, `J = 1..3`. -/
theorem H_y1_raw {H J : ℕ} (hJ : J ∈ [1, 2, 3]) (hH : 7 ≤ H) :
    (profTm p 4).psi H J (4 : ℕ) (zvec p 4 Q.y1H) = 0 := by
  have hJ7 : J < 7 := by simp at hJ; omega
  rw [psiTm_zvec (momUnits_H hp2 hc) Q.y1H (fun k hk => y1H_mem hp2 hc hk) hJ7 (by omega) hH,
    Q.y1H_raw J hJ, res_zero]

/-- raw `T-` of `y2` at `σ = 5`: `ψ-(J,5) = 0`, `J = 2..4`. -/
theorem H_y2_raw {H J : ℕ} (hJ : J ∈ [2, 3, 4]) (hH : 8 ≤ H) :
    (profTm p 4).psi H J (5 : ℕ) (zvec p 4 Q.y2H) = 0 := by
  have hJ7 : J < 7 := by simp at hJ; omega
  rw [psiTm_zvec (momUnits_H hp2 hc) Q.y2H (fun k hk => y2H_mem hp2 hc hk) hJ7 (by omega) hH,
    Q.y2H_raw J hJ, res_zero]

end H

/-! ### (P*) in `ZMod p` -/

theorem fTp_mem (hm : MomUnits p) {K : ℕ} (z : ℕ → ℚ) (hz : ∀ k < K, z k ∈ unitSub p) {J σ : ℕ}
    (hJ : J < 7) (hσ : σ + 3 ≤ 9) : Q.fTp K z J σ ∈ unitSub p := by
  unfold Q.fTp Q.comb
  exact Subring.sum_mem _ fun k hk => Subring.mul_mem _ (hz k (Finset.mem_range.mp hk))
    (PhiTp_mem hm k hJ hσ)

theorem fTm_mem (hm : MomUnits p) {K : ℕ} (z : ℕ → ℚ) (hz : ∀ k < K, z k ∈ unitSub p) {J σ : ℕ}
    (hJ : J < 7) (hσ : σ + 3 ≤ 9) : Q.fTm K z J σ ∈ unitSub p := by
  unfold Q.fTm Q.comb
  exact Subring.sum_mem _ fun k hk => Subring.mul_mem _ (hz k (Finset.mem_range.mp hk))
    (PhiTm_mem hm k hJ hσ)

theorem res_fTd4 (hm : MomUnits p) {K : ℕ} (z : ℕ → ℚ) (hz : ∀ k < K, z k ∈ unitSub p) {J : ℕ}
    (hJ : J < 7) : palindromicRatResidue p (Q.fTd K z J 4) =
      palindromicRatResidue p (Q.fTp K z J 3) - palindromicRatResidue p (Q.fTp K z J 4) := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, fTd_succ]
  exact (res_sub (fTp_mem hm z hz hJ (by omega)) (fTp_mem hm z hz hJ (by omega))).2

/-- The window-`s` response vector `v_J` of the four cells, in `ZMod p` (`s = 4`). -/
def vRespP (p : ℕ) [Fact p.Prime] (K H J : ℕ) (u u2 y1 y2 : ℕ → ℚ) : List (ZMod p) :=
  [(profTp p K).psi H J (3 : ℕ) (zvec p K u) - (profTp p K).psi H J (4 : ℕ) (zvec p K u),
   (profTp p K).psi H J (3 : ℕ) (zvec p K u2) - (profTp p K).psi H J (4 : ℕ) (zvec p K u2),
   (profTm p K).psi H J (4 : ℕ) (zvec p K y1), (profTm p K).psi H J (4 : ℕ) (zvec p K y2)]

theorem vRespP_eq (hm : MomUnits p) {K H J : ℕ} (u u2 y1 y2 : ℕ → ℚ)
    (hu : ∀ k < K, u k ∈ unitSub p) (hu2 : ∀ k < K, u2 k ∈ unitSub p)
    (hy1 : ∀ k < K, y1 k ∈ unitSub p) (hy2 : ∀ k < K, y2 k ∈ unitSub p)
    (hJ : J < 7) (hH : 7 ≤ H) (c : ℕ) (hc : c < 4) :
    (vRespP p K H J u u2 y1 y2).getD c 0 =
      palindromicRatResidue p ((Q.vResp K u u2 y1 y2 J).getD c 0) := by
  have e3 := fun z hz => psiTp_zvec hm (K := K) (J := J) (H := H) z hz hJ (σ := 3) (by omega) (by omega)
  have e4 := fun z hz => psiTp_zvec hm (K := K) (J := J) (H := H) z hz hJ (σ := 4) (by omega) hH
  have m4 := fun z hz => psiTm_zvec hm (K := K) (J := J) (H := H) z hz hJ (σ := 4) (by omega) hH
  interval_cases c
  · simp only [vRespP, Q.vResp, List.getD_cons_zero]
    rw [e3 u hu, e4 u hu, ← res_fTd4 hm u hu hJ]
  · simp only [vRespP, Q.vResp, List.getD_cons_succ, List.getD_cons_zero]
    rw [e3 u2 hu2, e4 u2 hu2, ← res_fTd4 hm u2 hu2 hJ]
  · simp only [vRespP, Q.vResp, List.getD_cons_succ, List.getD_cons_zero]
    rw [m4 y1 hy1]
  · simp only [vRespP, Q.vResp, List.getD_cons_succ, List.getD_cons_zero]
    rw [m4 y2 hy2]

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
