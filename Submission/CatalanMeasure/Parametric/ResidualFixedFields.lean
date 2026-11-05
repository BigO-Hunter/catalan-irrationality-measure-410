module
public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
@[expose] public section
namespace CatalanMeasure.Parametric
noncomputable section

/-- The first-case fixed field after subtracting the proposed shared-factor weight.
Its connection to the determinant majorant is a separate remaining theorem. -/
def proposedResidualFieldOne (lambda x : ℝ) : ℝ :=
  -(3/8:ℝ)*Real.log 2 -(41/96:ℝ)*Real.log (1+x^2) +
    lambda*((7/48:ℝ)-2*x^2/(1+x^2))

theorem proposedResidualFieldOne_le {lambda : ℝ} (hlambda : 0≤lambda) (x : ℝ) :
    proposedResidualFieldOne lambda x ≤ -(3/8:ℝ)*Real.log 2+(7/48:ℝ)*lambda := by
  have hlog : 0≤Real.log (1+x^2) := Real.log_nonneg (by nlinarith [sq_nonneg x])
  have hratio : 0≤2*x^2/(1+x^2) := div_nonneg (by positivity) (by positivity)
  have hh := mul_nonneg hlambda hratio
  unfold proposedResidualFieldOne
  nlinarith

def proposedCaseOneLambda : ℚ := 230703773/100000000

/-- A loose uniform cap with ample room; valid for all real x, not a grid. -/
theorem proposedResidualFieldOne_scaled_le_eight (x : ℝ) :
    96*proposedResidualFieldOne (proposedCaseOneLambda:ℝ) x ≤ 8 := by
  have hh := mul_le_mul_of_nonneg_left (proposedResidualFieldOne_le
    (lambda := (proposedCaseOneLambda:ℝ)) (by norm_num [proposedCaseOneLambda]) x)
    (by norm_num : (0:ℝ)≤96)
  have hl := OAI.InternalCatalan.barrier_log_two_lower
  norm_num [proposedCaseOneLambda] at hh ⊢
  linarith

end
end CatalanMeasure.Parametric
