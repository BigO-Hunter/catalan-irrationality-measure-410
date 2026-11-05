module
public import Submission.CatalanMeasure.GenD.Uniform.Bank.Budget532
public import Submission.CatalanMeasure.GenD.D58.FirstTrialCert
public import Submission.CatalanMeasure.GenD.D58.Circle
public import Submission.CatalanMeasure.GenD.Analytic.DeltaChain
public import Submission.CatalanMeasure.GenD.D58.Cert590.XCover
public import Submission.CatalanMeasure.GenD.D58.Cert590.YCover
public import Submission.CatalanMeasure.GenD.D58.Cert590.RCover
public import Submission.CatalanMeasure.GenD.D58.Cert590.Norm
public import Submission.CatalanMeasure.GenD.D58.Cert590.Near
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Uniform.Bank532
open D58 Analytic Set Filter CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.CellCert
noncomputable section
/-- the K590 second-population trial. -/
def secondU590 : ℕ → ℝ := trialSeqS Cert590.Pc Cert590.P
def secondV590 : ℕ → ℝ := trialSeqS Cert590.Vc Cert590.V

theorem second_hu590 : Summable (fun k => |secondU590 k|) := (trialSeqS_summable Cert590.tailsP).1
theorem second_hv590 : Summable (fun k => |secondV590 k|) := (trialSeqS_summable Cert590.tailsV).1

theorem second_field_sum590 :
    ((Cert590.MX : ℚ) : ℝ) + ((Cert590.MY : ℚ) : ℝ) = K590.fieldCap := by
  norm_num [Cert590.MX, Cert590.MY, K590.fieldCap]

theorem second_norm_le590 :
    2 * barrierTrialNormSq secondU590 + barrierTrialNormSq secondV590 / 2 ≤ K590.normCap := by
  have h := Cert590.weighted_norm_le
  have h2 : (((2 * Cert590.NP + Cert590.NV / 2 : ℚ)) : ℝ) ≤ K590.normCap := by
    norm_num [Cert590.NP, Cert590.NV, K590.normCap]
  unfold secondU590 secondV590
  linarith

theorem second_row_sup590 : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    rowFieldG (11 / 29) (3 / 29) (39 / 29) secondU590 secondV590 x ≤ ((Cert590.MX : ℚ) : ℝ) := by
  intro x hx
  have h := Cert590.row_sup_S x hx
  have e : rowFieldS Cert590.R Cert590.Pc Cert590.Vc Cert590.P Cert590.V =
      rowFieldG (11 / 29) (3 / 29) (39 / 29) secondU590 secondV590 := by
    unfold rowFieldS secondU590 secondV590
    norm_num [Cert590.R]
  rw [e] at h
  exact h

theorem second_column_sup590 : ∀ s ∈ Ioo (0 : ℝ) 1,
    colFieldG (9 / 58) (3 / 58) secondV590 s ≤ ((Cert590.MY : ℚ) : ℝ) := by
  intro s hs
  have h := Cert590.column_sup_S s hs
  have e : colFieldS Cert590.C Cert590.Vc Cert590.V = colFieldG (9 / 58) (3 / 58) secondV590 := by
    unfold colFieldS secondV590
    norm_num [Cert590.C]
  rw [e] at h
  exact h

theorem second_residual_sup590 : ∀ x ∈ Icc (-1 : ℝ) 1, (401 / 2500 : ℝ) ≤ |x| →
    Analytic.resFieldGen (53 / 58) secondU590 x ≤ K590.residualCap := by
  intro x hx hg
  have h := Cert590.residual_sup_S x hx hg
  have e : Analytic.resFieldGen (53 / 58) secondU590 x =
      resFieldW (((53 / 58 : ℚ)) : ℝ) (trialSeqS Cert590.Pc Cert590.P) x := by
    unfold Analytic.resFieldGen resFieldW secondU590
    norm_num
  rw [e]
  have e2 : ((Cert590.MR : ℚ) : ℝ) = K590.residualCap := by norm_num [Cert590.MR, K590.residualCap]
  linarith

theorem second_near_sup_d58_590 : ∀ y ∈ Ioo (0 : ℝ) 1,
    -(53 / 58 : ℝ) * Real.log (1 + y ^ 2) + (47 / 58 : ℝ) * Real.log y - secondU590 1 * y ≤ -(77 / 100 : ℝ) :=
  fun y hy => Cert.near_residual_field_le_d58 Cert590.first_lower hy.1 hy.2.le


theorem second_budget {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-gC0 Odd.design + gC1 Odd.design * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      K590.normCap + (1 - a) * K590.fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * K590.residualCap + t * nearCap ≤
        -K590.target + Real.log 2 / 2 + K590.secondCost * a := by
  rw [Instances.d58_gC0, Instances.d58_gC1]
  have h := K590.second_budget_log2 ha ht
  norm_num [c07, c26] at h
  linarith

end
end CatalanMeasure.GenD.Uniform.Bank532
