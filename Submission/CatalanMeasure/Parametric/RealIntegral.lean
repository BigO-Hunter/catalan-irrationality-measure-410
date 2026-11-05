module
public import Submission.CatalanMeasure.Parametric.RealEvaluation
public import Submission.OAI.NumberTheory.Catalan.Analysis.RealPairedIntegral
public import Submission.OAI.NumberTheory.Catalan.Estimates.MomentFilter
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset Set MeasureTheory OAI.InternalCatalan
noncomputable section

def filteredColumn (P : Parameters) (N k : ℕ) : ℝ[X] :=
  X^(P.b N+k)*(1-X)^(P.q N)

theorem filteredColumn_expansion (P : Parameters) (N k : ℕ) :
    filteredColumn P N k = ∑ v ∈ range (P.q N+1),
      C (filterCoeffRat P N v:ℝ)*X^(P.b N+k+v) := by
  have hh := congrArg (Polynomial.map (Int.castRingHom ℝ))
    (one_sub_X_pow_expansion (P.q N))
  simp only [Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_one,Polynomial.map_X,
    Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C] at hh
  rw [filteredColumn,hh,mul_sum]
  apply sum_congr rfl
  intro v _
  rw [pow_add]
  simp only [filterCoeffRat,Int.castRingHom, RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk]
  push_cast
  ring

theorem map_filteredColumn (F : ℝ[X] →ₗ[ℝ] ℝ) (P : Parameters) (N k : ℕ) :
    F (filteredColumn P N k)=∑ v ∈ range (P.q N+1),
      (filterCoeffRat P N v:ℝ)*F (X^(P.b N+k+v)) := by
  rw [filteredColumn_expansion,map_sum]
  apply sum_congr rfl
  intro v _
  simpa only [Polynomial.smul_eq_C_mul,smul_eq_mul] using
    F.map_smul (filterCoeffRat P N v:ℝ) (X^(P.b N+k+v))

theorem realEntry_eq_filtered_moments (P : Parameters) (N r k : ℕ) :
    realEntry P N r k =
      mixedMoment (realPoly (rowP P N r)) (filteredColumn P N k) -
      (3/2:ℝ)*zetaMoment (realPoly (rowD P N r)) (filteredColumn P N k) := by
  rw [← mixedMomentRightLinear_apply,← zetaMomentRightLinear_apply,
    map_filteredColumn,map_filteredColumn]
  simp_rw [mixedMomentRightLinear_apply,zetaMomentRightLinear_apply]
  unfold realEntry
  rw [mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro v _
  ring

def realRowAmplitude (P : Parameters) (N r : ℕ) (t : ℝ) : ℝ :=
  (realPoly (rowP P N r)).eval t - (3/2:ℝ)*
    (if 0<t then Real.sqrt (1-t^2)/t*(realPoly (rowD P N r)).eval t else 0)

theorem realRowAmplitude_of_nonpos (P : Parameters) (N r : ℕ) {t : ℝ} (ht : t≤0) :
    realRowAmplitude P N r t=(realPoly (rowP P N r)).eval t := by
  simp [realRowAmplitude,not_lt.mpr ht]

theorem realRowAmplitude_weighted_eq (P : Parameters) (N r : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (-1:ℝ) 1) :
    (|t|/Real.sqrt (1-t^2))*realRowAmplitude P N r t =
      (|t|/Real.sqrt (1-t^2))*(realPoly (rowP P N r)).eval t -
        (3/2:ℝ)*(if 0<t then (realPoly (rowD P N r)).eval t else 0) := by
  by_cases hp : 0<t
  · simp only [realRowAmplitude,ite_eq_left hp]
    have ht0 : t≠0 := hp.ne'
    have hrad : 0<1-t^2 := by
      have hh :=mul_pos (sub_pos.mpr ht.2) (show (0:ℝ)<1+t by linarith [ht.1])
      nlinarith
    have hs0 : Real.sqrt (1-t^2)≠0 :=(Real.sqrt_pos.mpr hrad).ne'
    rw [abs_of_pos hp]
    field_simp [ht0,hs0]
    <;> ring
  · simp [realRowAmplitude,hp]

theorem realRowAmplitude_kernel_eq (P : Parameters) (N r : ℕ) (Q : ℝ[X]) {t : ℝ}
    (ht : t ∈ Ioo (-1:ℝ) 1) (s : ℝ) :
    (|t|/Real.sqrt (1-t^2))*(realRowAmplitude P N r t*Q.eval s)/(1-t*s) =
      (|t|/Real.sqrt (1-t^2))*((realPoly (rowP P N r)).eval t*Q.eval s)/(1-t*s) -
        (3/2:ℝ)*(if 0<t then
          (realPoly (rowD P N r)).eval t*Q.eval s/(1-t*s) else 0) := by
  calc
    _ = ((|t|/Real.sqrt (1-t^2))*realRowAmplitude P N r t)*Q.eval s/(1-t*s) := by ring
    _ = _ := by
      rw [realRowAmplitude_weighted_eq P N r ht]
      by_cases hp : 0<t <;> simp only [hp,ite_true,ite_false] <;> ring

theorem integrable_realRowAmplitude (P : Parameters) (N r : ℕ) (Q : ℝ[X]) :
    Integrable (fun p : ℝ×ℝ => (|p.1|/Real.sqrt (1-p.1^2))*
      (realRowAmplitude P N r p.1*Q.eval p.2)/(1-p.1*p.2))
      ((volume.restrict (Ioo (-1:ℝ) 1)).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
  have hi :=(integrable_mixedPolynomial (realPoly (rowP P N r)) Q).sub
    ((integrable_positive_zetaPolynomial (realPoly (rowD P N r)) Q).const_mul (3/2:ℝ))
  apply hi.congr
  filter_upwards [ae_mem_mixed_rectangle] with p hp
  exact (realRowAmplitude_kernel_eq P N r Q hp.1 p.2).symm

theorem integral_prod_realRowAmplitude (P : Parameters) (N r : ℕ) (Q : ℝ[X]) :
    (∫ p : ℝ×ℝ, (|p.1|/Real.sqrt (1-p.1^2))*
      (realRowAmplitude P N r p.1*Q.eval p.2)/(1-p.1*p.2)
      ∂(volume.restrict (Ioo (-1:ℝ) 1)).prod (volume.restrict (Ioo (0:ℝ) 1))) =
      mixedMoment (realPoly (rowP P N r)) Q -
        (3/2:ℝ)*zetaMoment (realPoly (rowD P N r)) Q := by
  calc
    _ = ∫ p : ℝ×ℝ,
      ((|p.1|/Real.sqrt (1-p.1^2))*((realPoly (rowP P N r)).eval p.1*Q.eval p.2)/(1-p.1*p.2) -
        (3/2:ℝ)*(if 0<p.1 then
          (realPoly (rowD P N r)).eval p.1*Q.eval p.2/(1-p.1*p.2) else 0))
      ∂(volume.restrict (Ioo (-1:ℝ) 1)).prod (volume.restrict (Ioo (0:ℝ) 1)) := by
        apply integral_congr_ae
        filter_upwards [ae_mem_mixed_rectangle] with p hp
        exact realRowAmplitude_kernel_eq P N r Q hp.1 p.2
    _ = _ := by
      rw [integral_sub (integrable_mixedPolynomial (realPoly (rowP P N r)) Q)
        ((integrable_positive_zetaPolynomial (realPoly (rowD P N r)) Q).const_mul (3/2:ℝ)),
        integral_const_mul,integral_positive_zetaPolynomial]
      rw [integral_prod_mixedPolynomial,← mixedMoment_eq_sum]

theorem integrable_realPlaceRow (P : Parameters) (N r : ℕ) (Q : ℝ[X]) :
    Integrable (fun p : ℝ×ℝ =>
      realRowAmplitude P N r p.1*Q.eval p.2/(1-p.1*p.2))
      (realPlaceMeasure.prod (volume.restrict (Ioo (0:ℝ) 1))) := by
  apply (integrable_realPlaceMeasure_prod_iff _).mpr
  simpa only [mul_div_assoc] using integrable_realRowAmplitude P N r Q

theorem realEntry_eq_realPlace_product (P : Parameters) (N r k : ℕ) :
    realEntry P N r k = ∫ p : ℝ×ℝ,
      realRowAmplitude P N r p.1*(filteredColumn P N k).eval p.2/(1-p.1*p.2)
      ∂realPlaceMeasure.prod (volume.restrict (Ioo (0:ℝ) 1)) := by
  rw [integral_realPlaceMeasure_prod]
  simpa only [realEntry_eq_filtered_moments,mul_div_assoc] using
    (integral_prod_realRowAmplitude P N r (filteredColumn P N k)).symm

theorem realEntry_eq_realPlace_integral (P : Parameters) (N r k : ℕ) :
    realEntry P N r k = ∫ t, (∫ s in (0:ℝ)..1,
      realRowAmplitude P N r t*(filteredColumn P N k).eval s/(1-t*s)) ∂realPlaceMeasure := by
  rw [realEntry_eq_realPlace_product]
  have hh :=integral_prod (fun p : ℝ×ℝ =>
    realRowAmplitude P N r p.1*(filteredColumn P N k).eval p.2/(1-p.1*p.2))
    (integrable_realPlaceRow P N r (filteredColumn P N k))
  simpa only [intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using hh

end
end CatalanMeasure.Parametric
