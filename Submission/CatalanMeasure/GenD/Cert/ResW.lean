module

public import Submission.CatalanMeasure.CellCert.EvalS
public import Submission.CatalanMeasure.CellCert.FieldsSLink

@[expose] public section

/-!
# The residual field with a weight parameter

`CellCert.resFieldG`, `CellCert.resPoles` and `CellCert.resTermsS` hard-code the residual weight `9/10`
(the 728 design).  Here the weight `ρ` (`= d0/n0`; `53/58` for the design (58,9,3,5,3)) is a
parameter: `resFieldW ρ u = -ρ log(1+x²) - 2 T(u)` (the same function as `Analytic.resFieldGen ρ u`),
its log terms `resTermsW ρ`, its derivative poles `resPolesW ρ`, and the derivative link.
-/

open OAI.InternalCatalan Polynomial Set

namespace CatalanMeasure.CellCert
open CatalanMeasure.Cert
noncomputable section

/-- the residual field with weight `ρ` -/
def resFieldW (ρ : ℝ) (u : ℕ → ℝ) (x : ℝ) : ℝ :=
  -ρ * Real.log (1 + x ^ 2) - 2 * barrierTrialT u x

def resTermsW (ρ : ℚ) (P : List TailQ) (x : ℚ) : List LogTerm :=
  [⟨-ρ, 0, 1 + x * x, 0⟩] ++
    P.map (fun t => ⟨t.rr, t.ri, (quadArg x t).1, (quadArg x t).2⟩)

def resPolesW (ρ : ℚ) (P : List TailQ) : List PoleR := ⟨-2 * ρ, 0, 0, 1⟩ :: P.map poleOfTail

theorem resFieldW_continuousOn (ρ : ℝ) {u : ℕ → ℝ} (hu : Summable (fun k => |u k|)) :
    ContinuousOn (resFieldW ρ u) (Icc (-1 : ℝ) 1) :=
  ((log_one_add_sq_continuous.continuousOn.const_mul _)).sub
    ((barrierTrialT_continuousOn u hu).const_mul _)

theorem resFieldW_eq (ρ : ℚ) {Pc : List ℤ} {P : List TailQ} (hP : tailsInDisk P = true) {x : ℚ}
    (hx : |(x : ℝ)| ≤ 1) :
    resFieldW (ρ : ℝ) (trialSeqS Pc P) x =
      ((resTermsW ρ P x).map LogTerm.val).sum + (-2 * finTR Pc x) := by
  unfold resFieldW finTR
  rw [trialSeqS_T_eq_finite_log Pc hP hx]
  simp only [resTermsW, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, tailLog_T1, log_term_sq]
  push_cast
  ring

theorem resFieldW_hasDerivAt (ρ : ℚ) {Pc : List ℤ} {P : List TailQ}
    (hP : tailsInDisk P = true) (hPz : ∀ t ∈ P, t.zr ≠ 0 ∨ t.zi ≠ 0)
    (Z : List ℤ) (hZ : ∀ x : ℝ, -2 * finUR Pc x = ptZ Z 0 x)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (resFieldW (ρ : ℝ) (trialSeqS Pc P)) (ftZ Z (resPolesW ρ P) 0 x) x := by
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  obtain ⟨sP1, sP2⟩ := trialSeqS_summable (cs := Pc) hP
  have hT := barrierTrialT_hasDerivAt_series (trialSeqS Pc P) sP1 sP2 hx
  rw [(trialSeqS_U_hasSum Pc hP hxa).tsum_eq] at hT
  have hg := (hasDerivAt_log_one_add_sq x).const_mul (-(ρ : ℝ))
  have hall := hg.sub (hT.const_mul 2)
  unfold resFieldW
  refine hall.congr_deriv ?_
  unfold ftZ
  rw [← hZ x]
  simp only [resPolesW, List.map_cons, List.sum_cons, sum_qt_poleOfTail P hP hPz hxa]
  rw [qt_i]
  unfold finUR
  have hd : (x ^ 2 + 1) ≠ 0 := by positivity
  have hd' : (1 + x ^ 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end
end CatalanMeasure.CellCert
