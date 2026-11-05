module
public import Submission.CatalanMeasure.Parametric.CommonFactorCoordinate
public import Submission.CatalanMeasure.Parametric.PopulationCase
@[expose] public section
namespace CatalanMeasure.Parametric
open Set Finset Real OAI.InternalCatalan Polynomial
noncomputable section

def paramPopulationRowField (P : Parameters) (N : ℕ) (k x : ℝ) : ℝ :=
  (P.A N:ℝ)/(P.n N:ℝ)*Real.log |x|+2*(P.h N:ℝ)/(P.n N:ℝ)*Real.log (1-x)-
    ((P.H N:ℝ)/(P.n N:ℝ)+(k-2)/2)*Real.log (1+x^2)

/-- Exact cancellation of the actual common factor in a fixed-column field. -/
theorem paramPopulationRowField_sub_common {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0<N) (k : ℝ) {x : ℝ} (hx : x<0) :
    paramPopulationRowField P N k x-
      Real.log |(rowCommonFactor P N).eval (realCoordinateInv x)|/(P.n N:ℝ)=
      -(P.A N:ℝ)/(P.n N:ℝ)*Real.log 2-
        (k/2-(P.g N:ℝ)/(P.n N:ℝ))*Real.log (1+x^2) :=by
  have hn : (P.n N:ℝ)≠0 :=by exact_mod_cast (n_pos hP hN).ne'
  have hg : P.g N ≤ P.n N :=by have :=two_g_lt_n hP hN;omega
  have hC :=C_eq_A_add_residual hP hN
  have hH : (P.H N:ℝ)=(P.A N:ℝ)+(P.n N:ℝ)-(P.g N:ℝ)+(P.h N:ℝ) :=by
    change ((P.C N+P.h N:ℕ):ℝ)=_
    rw [hC,Nat.cast_add,Nat.cast_add,Nat.cast_sub hg]
    ring
  rw [commonFactor_coordinate_log P N hx]
  unfold paramPopulationRowField
  rw [hH]
  field_simp
  ring

def paramResidualFixedOne (P : Parameters) (N : ℕ) (lambda x : ℝ) : ℝ :=
  -(P.A N:ℝ)/(P.n N:ℝ)*Real.log 2-
    ((1/2:ℝ)-(P.g N:ℝ)/(P.n N:ℝ))*Real.log (1+x^2)+lambda*paramCaseField P N x

theorem paramFixedOne_sub_common {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0<N) (lambda : ℝ) {x : ℝ} (hx : x<0) :
    paramPopulationRowField P N 1 x+lambda*paramCaseField P N x-
      Real.log |(rowCommonFactor P N).eval (realCoordinateInv x)|/(P.n N:ℝ)=
      paramResidualFixedOne P N lambda x :=by
  have hh :=paramPopulationRowField_sub_common hP hN 1 hx
  unfold paramResidualFixedOne
  norm_num only at hh ⊢
  linarith

/-- A uniform cap, valid on all real x; no sampling assumption is used. -/
theorem paramResidualFixedOne_le {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0<N) {lambda : ℝ} (hlambda : 0 ≤ lambda) (x : ℝ) :
    paramResidualFixedOne P N lambda x ≤
      -(P.A N:ℝ)/(P.n N:ℝ)*Real.log 2+lambda*2*(P.g N:ℝ)/(P.n N:ℝ) :=by
  have hn : (0:ℝ)<P.n N :=by exact_mod_cast n_pos hP hN
  have hg :=two_g_lt_n hP hN
  have hgr : 2*(P.g N:ℝ)<(P.n N:ℝ) :=by exact_mod_cast hg
  have hcoef : 0 ≤ (1/2:ℝ)-(P.g N:ℝ)/(P.n N:ℝ) :=by
    have hh : (P.g N:ℝ)/(P.n N:ℝ) ≤ 1/2 :=by
      rw [div_le_iff₀ hn]
      linarith
    linarith
  have hlog : 0 ≤ Real.log (1+x^2) :=Real.log_nonneg (by nlinarith [sq_nonneg x])
  have hr : 0 ≤ 2*x^2/(1+x^2) :=div_nonneg (by positivity) (by positivity)
  have ha :=mul_nonneg hcoef hlog
  have hb :=mul_nonneg hlambda hr
  unfold paramResidualFixedOne paramCaseField
  ring_nf at ha hb ⊢
  linarith only [ha,hb]

end
end CatalanMeasure.Parametric
