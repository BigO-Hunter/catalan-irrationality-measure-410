module

public import Submission.CatalanMeasure.GenD.D58.Cert590.Data
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.MeanEval
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkSigns
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkSlope

/-!
# D2 constants: `certMean` rows of `LinkCert` (`hκlo`, `hκhi`, `hq2g`, `hspq`, `hmarg`) at `e = 2^-30`

For `D0.p = trialSeqS Pc P` (K590), the exact means `mCp, mCm, mS0 … mS23` (`MeanEval.meanGo`) and
the affine rows at the interval endpoints.  `certMean (Cp i).K (Cp i).G D0.p` unfolds to the sum in
the statements (`G = gcertG e gCp`, so `hG := fun _ => rfl`).

* `q_ge_I{0,1}`: `25/58 ≤ (1-α) c0 + mean - sP` on `[0, 1/200]`, `[1/200, 1/16]`
  (gives `hq2g`, since `2 g0/n0 = 5/29 < 25/58`, and `hspq` via `sp_le_q`).
* `kappaLo_I{0,1}`: `κlo ≤ (1-α) c0 + mean - sM` with `κlo = 3/10`, `27/100` (`hκlo`; `hk0` is trivial).
* `kappaHi_I{0,1}`: `(1-α) - q ≤ κhi` with `κhi = 223/500`, `4431/10000` (`hκhi`).
* `marg_S{j}`: `5/29 + 1/20 ≤ (1-α) c0 + mean - sT` on `[0, 1/16]`, `j < 24` (`hmarg`, `ηT = 1/20`).
* The constants `κlo`, `κhi` are free parameters of the contract (certified windows
  `[0.30207, 0.44582]`, `[0.27600, 0.44308]`); the endpoint checks are the only place they enter.
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert CatalanMeasure.CellCert
open CatalanMeasure.GenD.D58.Cert590 (Pc P)

set_option maxRecDepth 1000000
set_option Elab.async false

/-- Exact `e` of the means: `LinkCert` at `e = 2^-30` (`hec`, `Dtop`). -/
def eMean : ℚ := 1 / 2 ^ 30

/-- The table `pp_1 … pp_60` of `D0.p = trialSeqS Pc P`; every `g` has length at most `60`. -/
def tab60 : List ℚ := ppTab Pc P 60

def sCp : ℚ := (58331170863990251 / 1152921504606846976 : ℚ)
def mCp : ℚ := meanGo eMean 0 gCp (tab60)
def sCm : ℚ := (58331170863990251 / 1152921504606846976 : ℚ)
def mCm : ℚ := meanGo eMean 0 gCm (tab60)
def sS0 : ℚ := (44262364356690289 / 1152921504606846976 : ℚ)
def mS0 : ℚ := meanGo eMean 0 gS0 (tab60)
def sS1 : ℚ := (44085058945642727 / 1152921504606846976 : ℚ)
def mS1 : ℚ := meanGo eMean 0 gS1 (tab60)
def sS2 : ℚ := (43924903296079385 / 1152921504606846976 : ℚ)
def mS2 : ℚ := meanGo eMean 0 gS2 (tab60)
def sS3 : ℚ := (2737192102190911 / 72057594037927936 : ℚ)
def mS3 : ℚ := meanGo eMean 0 gS3 (tab60)
def sS4 : ℚ := (1365705215671109 / 36028797018963968 : ℚ)
def mS4 : ℚ := meanGo eMean 0 gS4 (tab60)
def sS5 : ℚ := (43649544539328125 / 1152921504606846976 : ℚ)
def mS5 : ℚ := meanGo eMean 0 gS5 (tab60)
def sS6 : ℚ := (43634517020379795 / 1152921504606846976 : ℚ)
def mS6 : ℚ := meanGo eMean 0 gS6 (tab60)
def sS7 : ℚ := (43653451785908229 / 1152921504606846976 : ℚ)
def mS7 : ℚ := meanGo eMean 0 gS7 (tab60)
def sS8 : ℚ := (5462594465280421 / 144115188075855872 : ℚ)
def mS8 : ℚ := meanGo eMean 0 gS8 (tab60)
def sS9 : ℚ := (43770095140288341 / 1152921504606846976 : ℚ)
def mS9 : ℚ := meanGo eMean 0 gS9 (tab60)
def sS10 : ℚ := (43855035824395397 / 1152921504606846976 : ℚ)
def mS10 : ℚ := meanGo eMean 0 gS10 (tab60)
def sS11 : ℚ := (43949505039869305 / 1152921504606846976 : ℚ)
def mS11 : ℚ := meanGo eMean 0 gS11 (tab60)
def sS12 : ℚ := (44048092415460849 / 1152921504606846976 : ℚ)
def mS12 : ℚ := meanGo eMean 0 gS12 (tab60)
def sS13 : ℚ := (44146215800592473 / 1152921504606846976 : ℚ)
def mS13 : ℚ := meanGo eMean 0 gS13 (tab60)
def sS14 : ℚ := (22120090910996035 / 576460752303423488 : ℚ)
def mS14 : ℚ := meanGo eMean 0 gS14 (tab60)
def sS15 : ℚ := (44327170212707003 / 1152921504606846976 : ℚ)
def mS15 : ℚ := meanGo eMean 0 gS15 (tab60)
def sS16 : ℚ := (2775322976326637 / 72057594037927936 : ℚ)
def mS16 : ℚ := meanGo eMean 0 gS16 (tab60)
def sS17 : ℚ := (44472871925198423 / 1152921504606846976 : ℚ)
def mS17 : ℚ := meanGo eMean 0 gS17 (tab60)
def sS18 : ℚ := (44529583117655019 / 1152921504606846976 : ℚ)
def mS18 : ℚ := meanGo eMean 0 gS18 (tab60)
def sS19 : ℚ := (11143773061287733 / 288230376151711744 : ℚ)
def mS19 : ℚ := meanGo eMean 0 gS19 (tab60)
def sS20 : ℚ := (44609576004829639 / 1152921504606846976 : ℚ)
def mS20 : ℚ := meanGo eMean 0 gS20 (tab60)
def sS21 : ℚ := (11158375385669819 / 288230376151711744 : ℚ)
def mS21 : ℚ := meanGo eMean 0 gS21 (tab60)
def sS22 : ℚ := (1395235741153435 / 36028797018963968 : ℚ)
def mS22 : ℚ := meanGo eMean 0 gS22 (tab60)
def sS23 : ℚ := (44652515488083947 / 1152921504606846976 : ℚ)
def mS23 : ℚ := meanGo eMean 0 gS23 (tab60)
/-- **All endpoint checks in one kernel declaration** (they share the table `tab60`: about 20 s,
against 12-19 s for each check alone). -/
theorem all_ends :
  ((25 / 58 ≤ (1 - 0) * c0Cp + mCp - sCp ∧ 25 / 58 ≤ (1 - 1 / 200) * c0Cp + mCp - sCp ∧
      25 / 58 ≤ (1 - 1 / 16) * c0Cp + mCp - sCp) ∧
    ((1 - 0) - ((1 - 0) * c0Cp + mCp - sCp) ≤ 223 / 500 ∧
      (1 - 1 / 200) - ((1 - 1 / 200) * c0Cp + mCp - sCp) ≤ 223 / 500) ∧
    ((1 - 1 / 200) - ((1 - 1 / 200) * c0Cp + mCp - sCp) ≤ 4431 / 10000 ∧
      (1 - 1 / 16) - ((1 - 1 / 16) * c0Cp + mCp - sCp) ≤ 4431 / 10000)) ∧
  ((3 / 10 ≤ (1 - 0) * c0Cm + mCm - sCm ∧ 3 / 10 ≤ (1 - 1 / 200) * c0Cm + mCm - sCm) ∧
    (27 / 100 ≤ (1 - 1 / 200) * c0Cm + mCm - sCm ∧ 27 / 100 ≤ (1 - 1 / 16) * c0Cm + mCm - sCm)) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S0 + mS0 - sS0 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S0 + mS0 - sS0) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S1 + mS1 - sS1 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S1 + mS1 - sS1) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S2 + mS2 - sS2 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S2 + mS2 - sS2) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S3 + mS3 - sS3 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S3 + mS3 - sS3) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S4 + mS4 - sS4 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S4 + mS4 - sS4) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S5 + mS5 - sS5 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S5 + mS5 - sS5) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S6 + mS6 - sS6 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S6 + mS6 - sS6) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S7 + mS7 - sS7 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S7 + mS7 - sS7) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S8 + mS8 - sS8 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S8 + mS8 - sS8) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S9 + mS9 - sS9 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S9 + mS9 - sS9) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S10 + mS10 - sS10 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S10 + mS10 - sS10) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S11 + mS11 - sS11 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S11 + mS11 - sS11) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S12 + mS12 - sS12 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S12 + mS12 - sS12) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S13 + mS13 - sS13 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S13 + mS13 - sS13) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S14 + mS14 - sS14 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S14 + mS14 - sS14) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S15 + mS15 - sS15 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S15 + mS15 - sS15) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S16 + mS16 - sS16 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S16 + mS16 - sS16) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S17 + mS17 - sS17 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S17 + mS17 - sS17) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S18 + mS18 - sS18 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S18 + mS18 - sS18) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S19 + mS19 - sS19 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S19 + mS19 - sS19) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S20 + mS20 - sS20 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S20 + mS20 - sS20) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S21 + mS21 - sS21 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S21 + mS21 - sS21) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S22 + mS22 - sS22 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S22 + mS22 - sS22) ∧
  (5 / 29 + 1 / 20 ≤ (1 - 0) * c0S23 + mS23 - sS23 ∧
    5 / 29 + 1 / 20 ≤ (1 - 1 / 16) * c0S23 + mS23 - sS23) := by
  decide +kernel

abbrev Cp_ends := all_ends.1
abbrev Cm_ends := all_ends.2.1
abbrev S0_ends := all_ends.2.2.1
abbrev S1_ends := all_ends.2.2.2.1
abbrev S2_ends := all_ends.2.2.2.2.1
abbrev S3_ends := all_ends.2.2.2.2.2.1
abbrev S4_ends := all_ends.2.2.2.2.2.2.1
abbrev S5_ends := all_ends.2.2.2.2.2.2.2.1
abbrev S6_ends := all_ends.2.2.2.2.2.2.2.2.1
abbrev S7_ends := all_ends.2.2.2.2.2.2.2.2.2.1
abbrev S8_ends := all_ends.2.2.2.2.2.2.2.2.2.2.1
abbrev S9_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S10_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S11_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S12_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S13_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S14_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S15_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S16_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S17_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S18_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S19_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S20_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S21_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S22_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev S23_ends := all_ends.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ### Rows of `LinkCert` (real form; `certMean K G pp` is the sum, `G = gcertG e g`: `hG := fun _ => rfl`) -/

theorem q_ge_I0 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gCp.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 200 : ℝ)) :
    (25 / 58 : ℝ) ≤ (1 - α) * (c0Cp : ℝ) + ∑ k ∈ Finset.range gCp.length, G k * pp (k + 1) - (sCp : ℝ) := by
  have h := row_ge eMean gCp Pc P c0Cp sCp (25 / 58 : ℚ) (0 : ℚ) (1 / 200 : ℚ) mCp (n := 60) (by decide +kernel) rfl ⟨Cp_ends.1.1, Cp_ends.1.2.1⟩
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem q_ge_I1 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gCp.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (1 / 200 : ℝ) (1 / 16 : ℝ)) :
    (25 / 58 : ℝ) ≤ (1 - α) * (c0Cp : ℝ) + ∑ k ∈ Finset.range gCp.length, G k * pp (k + 1) - (sCp : ℝ) := by
  have h := row_ge eMean gCp Pc P c0Cp sCp (25 / 58 : ℚ) (1 / 200 : ℚ) (1 / 16 : ℚ) mCp (n := 60) (by decide +kernel) rfl ⟨Cp_ends.1.2.1, Cp_ends.1.2.2⟩
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem kappaHi_I0 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gCp.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 200 : ℝ)) :
    (1 - α) - ((1 - α) * (c0Cp : ℝ) + ∑ k ∈ Finset.range gCp.length, G k * pp (k + 1) - (sCp : ℝ)) ≤ (223 / 500 : ℝ) := by
  have h := row_le eMean gCp Pc P c0Cp sCp (223 / 500 : ℚ) (0 : ℚ) (1 / 200 : ℚ) mCp (n := 60) (by decide +kernel) rfl ⟨Cp_ends.2.1.1, Cp_ends.2.1.2⟩
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem kappaHi_I1 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gCp.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (1 / 200 : ℝ) (1 / 16 : ℝ)) :
    (1 - α) - ((1 - α) * (c0Cp : ℝ) + ∑ k ∈ Finset.range gCp.length, G k * pp (k + 1) - (sCp : ℝ)) ≤ (4431 / 10000 : ℝ) := by
  have h := row_le eMean gCp Pc P c0Cp sCp (4431 / 10000 : ℚ) (1 / 200 : ℚ) (1 / 16 : ℚ) mCp (n := 60) (by decide +kernel) rfl ⟨Cp_ends.2.2.1, Cp_ends.2.2.2⟩
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem kappaLo_I0 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gCm.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 200 : ℝ)) :
    (3 / 10 : ℝ) ≤ (1 - α) * (c0Cm : ℝ) + ∑ k ∈ Finset.range gCm.length, G k * pp (k + 1) - (sCm : ℝ) := by
  have h := row_ge eMean gCm Pc P c0Cm sCm (3 / 10 : ℚ) (0 : ℚ) (1 / 200 : ℚ) mCm (n := 60) (by decide +kernel) rfl Cm_ends.1
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem kappaLo_I1 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gCm.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (1 / 200 : ℝ) (1 / 16 : ℝ)) :
    (27 / 100 : ℝ) ≤ (1 - α) * (c0Cm : ℝ) + ∑ k ∈ Finset.range gCm.length, G k * pp (k + 1) - (sCm : ℝ) := by
  have h := row_ge eMean gCm Pc P c0Cm sCm (27 / 100 : ℚ) (1 / 200 : ℚ) (1 / 16 : ℚ) mCm (n := 60) (by decide +kernel) rfl Cm_ends.2
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S0 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS0.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S0 : ℝ) + ∑ k ∈ Finset.range gS0.length, G k * pp (k + 1) - (sS0 : ℝ) := by
  have h := row_ge eMean gS0 Pc P c0S0 sS0 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS0 (n := 60) (by decide +kernel) rfl S0_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S1 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS1.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S1 : ℝ) + ∑ k ∈ Finset.range gS1.length, G k * pp (k + 1) - (sS1 : ℝ) := by
  have h := row_ge eMean gS1 Pc P c0S1 sS1 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS1 (n := 60) (by decide +kernel) rfl S1_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S2 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS2.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S2 : ℝ) + ∑ k ∈ Finset.range gS2.length, G k * pp (k + 1) - (sS2 : ℝ) := by
  have h := row_ge eMean gS2 Pc P c0S2 sS2 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS2 (n := 60) (by decide +kernel) rfl S2_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S3 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS3.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S3 : ℝ) + ∑ k ∈ Finset.range gS3.length, G k * pp (k + 1) - (sS3 : ℝ) := by
  have h := row_ge eMean gS3 Pc P c0S3 sS3 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS3 (n := 60) (by decide +kernel) rfl S3_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S4 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS4.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S4 : ℝ) + ∑ k ∈ Finset.range gS4.length, G k * pp (k + 1) - (sS4 : ℝ) := by
  have h := row_ge eMean gS4 Pc P c0S4 sS4 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS4 (n := 60) (by decide +kernel) rfl S4_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S5 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS5.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S5 : ℝ) + ∑ k ∈ Finset.range gS5.length, G k * pp (k + 1) - (sS5 : ℝ) := by
  have h := row_ge eMean gS5 Pc P c0S5 sS5 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS5 (n := 60) (by decide +kernel) rfl S5_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S6 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS6.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S6 : ℝ) + ∑ k ∈ Finset.range gS6.length, G k * pp (k + 1) - (sS6 : ℝ) := by
  have h := row_ge eMean gS6 Pc P c0S6 sS6 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS6 (n := 60) (by decide +kernel) rfl S6_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S7 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS7.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S7 : ℝ) + ∑ k ∈ Finset.range gS7.length, G k * pp (k + 1) - (sS7 : ℝ) := by
  have h := row_ge eMean gS7 Pc P c0S7 sS7 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS7 (n := 60) (by decide +kernel) rfl S7_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S8 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS8.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S8 : ℝ) + ∑ k ∈ Finset.range gS8.length, G k * pp (k + 1) - (sS8 : ℝ) := by
  have h := row_ge eMean gS8 Pc P c0S8 sS8 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS8 (n := 60) (by decide +kernel) rfl S8_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S9 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS9.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S9 : ℝ) + ∑ k ∈ Finset.range gS9.length, G k * pp (k + 1) - (sS9 : ℝ) := by
  have h := row_ge eMean gS9 Pc P c0S9 sS9 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS9 (n := 60) (by decide +kernel) rfl S9_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S10 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS10.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S10 : ℝ) + ∑ k ∈ Finset.range gS10.length, G k * pp (k + 1) - (sS10 : ℝ) := by
  have h := row_ge eMean gS10 Pc P c0S10 sS10 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS10 (n := 60) (by decide +kernel) rfl S10_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S11 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS11.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S11 : ℝ) + ∑ k ∈ Finset.range gS11.length, G k * pp (k + 1) - (sS11 : ℝ) := by
  have h := row_ge eMean gS11 Pc P c0S11 sS11 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS11 (n := 60) (by decide +kernel) rfl S11_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S12 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS12.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S12 : ℝ) + ∑ k ∈ Finset.range gS12.length, G k * pp (k + 1) - (sS12 : ℝ) := by
  have h := row_ge eMean gS12 Pc P c0S12 sS12 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS12 (n := 60) (by decide +kernel) rfl S12_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S13 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS13.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S13 : ℝ) + ∑ k ∈ Finset.range gS13.length, G k * pp (k + 1) - (sS13 : ℝ) := by
  have h := row_ge eMean gS13 Pc P c0S13 sS13 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS13 (n := 60) (by decide +kernel) rfl S13_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S14 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS14.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S14 : ℝ) + ∑ k ∈ Finset.range gS14.length, G k * pp (k + 1) - (sS14 : ℝ) := by
  have h := row_ge eMean gS14 Pc P c0S14 sS14 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS14 (n := 60) (by decide +kernel) rfl S14_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S15 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS15.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S15 : ℝ) + ∑ k ∈ Finset.range gS15.length, G k * pp (k + 1) - (sS15 : ℝ) := by
  have h := row_ge eMean gS15 Pc P c0S15 sS15 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS15 (n := 60) (by decide +kernel) rfl S15_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S16 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS16.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S16 : ℝ) + ∑ k ∈ Finset.range gS16.length, G k * pp (k + 1) - (sS16 : ℝ) := by
  have h := row_ge eMean gS16 Pc P c0S16 sS16 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS16 (n := 60) (by decide +kernel) rfl S16_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S17 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS17.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S17 : ℝ) + ∑ k ∈ Finset.range gS17.length, G k * pp (k + 1) - (sS17 : ℝ) := by
  have h := row_ge eMean gS17 Pc P c0S17 sS17 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS17 (n := 60) (by decide +kernel) rfl S17_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S18 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS18.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S18 : ℝ) + ∑ k ∈ Finset.range gS18.length, G k * pp (k + 1) - (sS18 : ℝ) := by
  have h := row_ge eMean gS18 Pc P c0S18 sS18 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS18 (n := 60) (by decide +kernel) rfl S18_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S19 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS19.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S19 : ℝ) + ∑ k ∈ Finset.range gS19.length, G k * pp (k + 1) - (sS19 : ℝ) := by
  have h := row_ge eMean gS19 Pc P c0S19 sS19 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS19 (n := 60) (by decide +kernel) rfl S19_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S20 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS20.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S20 : ℝ) + ∑ k ∈ Finset.range gS20.length, G k * pp (k + 1) - (sS20 : ℝ) := by
  have h := row_ge eMean gS20 Pc P c0S20 sS20 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS20 (n := 60) (by decide +kernel) rfl S20_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S21 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS21.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S21 : ℝ) + ∑ k ∈ Finset.range gS21.length, G k * pp (k + 1) - (sS21 : ℝ) := by
  have h := row_ge eMean gS21 Pc P c0S21 sS21 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS21 (n := 60) (by decide +kernel) rfl S21_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S22 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS22.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S22 : ℝ) + ∑ k ∈ Finset.range gS22.length, G k * pp (k + 1) - (sS22 : ℝ) := by
  have h := row_ge eMean gS22 Pc P c0S22 sS22 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS22 (n := 60) (by decide +kernel) rfl S22_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

theorem marg_S23 {e : ℝ} (he : e = 1 / 2 ^ 30) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((gS23.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS Pc P k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16 : ℝ)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0S23 : ℝ) + ∑ k ∈ Finset.range gS23.length, G k * pp (k + 1) - (sS23 : ℝ) := by
  have h := row_ge eMean gS23 Pc P c0S23 sS23 (5 / 29 + 1 / 20 : ℚ) (0 : ℚ) (1 / 16 : ℚ) mS23 (n := 60) (by decide +kernel) rfl S23_ends
    (by rw [he]; norm_num [eMean]) hG hpp (α := α) (by push_cast; exact hα)
  push_cast at h
  first | exact h | linarith

/-- `hsmall` of `LinkCert` with `Dtop = 13/5000`, `dgap = 1/25`, `a0 = 7/100`, `ts = 13/128`,
`ηT = 1/20`, `2 g0 / n0 = 5/29`. -/
theorem hsmall_410 {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16)) :
    (5 : ℝ) / 29 + 1 / 20 <
      ((1 - α) - (13 / 5000) / (1 / 25)) * ((7 / 100) ^ 2 / ((13 / 128) ^ 2 + (7 / 100) ^ 2)) := by
  obtain ⟨h0, h1⟩ := hα
  norm_num
  first | linarith | nlinarith

/-- `hspq` (L7) from a lower bound `25/58` of the free count `q` (`sp = 20 N`, `g = 5 N`,
`n = 58 N`). -/
theorem sp_le_q {q sp g n : ℝ} {N : ℕ} (hq : (25 : ℝ) / 58 ≤ q) (hsp : sp = 20 * N)
    (hg : g = 5 * N) (hn : n = 58 * N) : sp + g ≤ q * n := by
  subst hsp hg hn
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

end CatalanMeasure.Signed.Consts
