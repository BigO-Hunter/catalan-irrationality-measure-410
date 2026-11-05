module
public import Submission.CatalanMeasure.Parametric.RestrictedWeights
public import Submission.CatalanMeasure.Parametric.ResidualFixedFields
public import Submission.OAI.NumberTheory.Catalan.Estimates.RealEnergyDiagonal
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Polynomial
noncomputable section

theorem commonFactor_coordinate_log (P : Parameters) (N : ℕ) {x : ℝ} (hx : x<0) :
    Real.log |(rowCommonFactor P N).eval (realCoordinateInv x)| =
      (P.A N:ℝ)*(Real.log 2+Real.log |x|-Real.log (1+x^2)) +
      (P.h N:ℝ)*(2*Real.log (1-x)-Real.log (1+x^2)) := by
  have hd : 0<1+x^2 := by positivity
  have hx0 : x≠0 := hx.ne
  have hm : 0<1-x := by linarith
  have ht : realCoordinateInv x<0 := by
    unfold realCoordinateInv
    exact div_neg_of_neg_of_pos (by linarith) hd
  have h1t : 0<1-realCoordinateInv x := by linarith
  have hlogt : Real.log |realCoordinateInv x| =
      Real.log 2+Real.log |x|-Real.log (1+x^2) := by
    rw [realCoordinateInv,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos hd,
      Real.log_div (mul_ne_zero (by norm_num) (abs_ne_zero.mpr hx0)) hd.ne',
      Real.log_mul (by norm_num) (abs_ne_zero.mpr hx0)]
  have he : 1-realCoordinateInv x=(1-x)^2/(1+x^2) := by
    unfold realCoordinateInv
    field_simp
    ring
  have hlogone : Real.log (1-realCoordinateInv x)=
      2*Real.log (1-x)-Real.log (1+x^2) := by
    rw [he,Real.log_div (pow_ne_zero _ hm.ne') hd.ne',Real.log_pow]
    norm_num
  simp only [rowCommonFactor,eval_mul,eval_pow,eval_X,eval_sub,eval_one,abs_mul,abs_pow]
  rw [abs_of_pos h1t,Real.log_mul (pow_ne_zero _ (abs_ne_zero.mpr ht.ne))
      (pow_ne_zero _ h1t.ne'),Real.log_pow,Real.log_pow,hlogt,hlogone]

def proposedFixedFieldOne (lambda x : ℝ) : ℝ :=
  (3/8:ℝ)*Real.log |x| +(5/48:ℝ)*Real.log (1-x) -(41/48:ℝ)*Real.log (1+x^2) +
    lambda*((7/48:ℝ)-2*x^2/(1+x^2))

def proposedFixedFieldTwo (T : ℝ → ℝ) (x : ℝ) : ℝ :=
  (3/8:ℝ)*Real.log |x| +(5/48:ℝ)*Real.log (1-x) -(65/48:ℝ)*Real.log (1+x^2) -2*T x

theorem proposedFixedFieldOne_sub_common {x : ℝ} (hx : x<0) (lambda : ℝ) :
    proposedFixedFieldOne lambda x -
      Real.log |(rowCommonFactor proposed 1).eval (realCoordinateInv x)| /96 =
      proposedResidualFieldOne lambda x := by
  rw [commonFactor_coordinate_log proposed 1 hx]
  norm_num [Parameters.A,Parameters.b,Parameters.q,Parameters.g,Parameters.h,proposed,
    proposedFixedFieldOne,proposedResidualFieldOne]
  ring

theorem proposedFixedFieldTwo_sub_common {x : ℝ} (hx : x<0) (T : ℝ → ℝ) :
    proposedFixedFieldTwo T x -
      Real.log |(rowCommonFactor proposed 1).eval (realCoordinateInv x)| /96 =
      -(3/8:ℝ)*Real.log 2 -(89/96:ℝ)*Real.log (1+x^2) -2*T x := by
  rw [commonFactor_coordinate_log proposed 1 hx]
  norm_num [Parameters.A,Parameters.b,Parameters.q,Parameters.g,Parameters.h,proposed,
    proposedFixedFieldTwo]
  ring

theorem proposedFixedFieldOne_after_common_le_eight {x : ℝ} (hx : x<0) :
    96*(proposedFixedFieldOne (proposedCaseOneLambda:ℝ) x -
      Real.log |(rowCommonFactor proposed 1).eval (realCoordinateInv x)| /96) ≤ 8 := by
  rw [proposedFixedFieldOne_sub_common hx]
  exact proposedResidualFieldOne_scaled_le_eight x

end
end CatalanMeasure.Parametric
