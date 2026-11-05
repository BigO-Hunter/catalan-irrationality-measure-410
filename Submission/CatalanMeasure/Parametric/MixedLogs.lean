module
public import Submission.CatalanMeasure.Parametric.MixedCoordinates
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset Set OAI.InternalCatalan Real
open scoped BigOperators
noncomputable section

theorem param_s_weight_product_pos (P : Parameters) (N : ℕ) {p : ℕ} (s : Fin p → ℝ)
    (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1) :
    0<∏ i,s i^(P.b N)*(1-s i)^(P.q N) :=
  prod_pos fun i _ =>mul_pos (pow_pos (hs i).1 _) (pow_pos (sub_pos.mpr (hs i).2) _)

theorem log_param_s_weight_product (P : Parameters) (N : ℕ) {p : ℕ} (s : Fin p → ℝ)
    (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1) :
    Real.log (∏ i,s i^(P.b N)*(1-s i)^(P.q N))=
      ∑ i,((P.b N:ℝ)*Real.log (s i)+(P.q N:ℝ)*Real.log (1-s i)) :=by
  rw [Real.log_prod (fun i _ =>mul_ne_zero (pow_ne_zero _ (hs i).1.ne')
    (pow_ne_zero _ (sub_pos.mpr (hs i).2).ne'))]
  apply sum_congr rfl
  intro i _
  rw [Real.log_mul (pow_ne_zero _ (hs i).1.ne')
    (pow_ne_zero _ (sub_pos.mpr (hs i).2).ne'),Real.log_pow,Real.log_pow]

theorem log_positive_node_product (a b : ℕ) {p : ℕ} (x : Fin p → ℝ)
    (hx : ∀ i,x i<1) (hx0 : ∀ i,x i≠0) :
    Real.log (∏ i,|x i|^a*(1-x i)^b)=
      ∑ i,((a:ℝ)*Real.log |x i|+(b:ℝ)*Real.log (1-x i)) :=by
  rw [Real.log_prod (fun i _ =>mul_ne_zero (pow_ne_zero _ (abs_ne_zero.mpr (hx0 i)))
    (pow_ne_zero _ (sub_pos.mpr (hx i)).ne'))]
  apply sum_congr rfl
  intro i _
  rw [Real.log_mul (pow_ne_zero _ (abs_ne_zero.mpr (hx0 i)))
    (pow_ne_zero _ (sub_pos.mpr (hx i)).ne'),Real.log_pow,Real.log_pow]

theorem log_positive_quadratic_product (a : ℕ) {p : ℕ} (x : Fin p → ℝ) :
    Real.log (∏ i,(1+x i^2)^a)=∑ i,(a:ℝ)*Real.log (1+x i^2) :=by
  rw [Real.log_prod (fun i _ =>pow_ne_zero _ (realCoordinateInv_denominator_pos (x i)).ne')]
  simp only [Real.log_pow]

/-- Exact logarithm of the actual generalized principal product. -/
theorem log_paramPinPrincipal {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0<N)
    {p : ℕ} (x s : Fin p → ℝ)
    (hx : ∀ i,x i ∈ Ioo (-1:ℝ) 1) (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1)
    (hx0 : ∀ i,x i≠0) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (paramPinPrincipal P N x s)=
      ((p*(P.C N-1)+p.choose 2:ℕ):ℝ)*Real.log 2+
      (∑ i,∑ j ∈ Ioi i,Real.log |x j-x i|)+
      2*(∑ i,∑ j ∈ Ioi i,Real.log |s j-s i|)+
      (∑ i,∑ j ∈ Ioi i,Real.log (1-x i*x j))+
      (∑ j,((P.b N:ℝ)*Real.log (s j)+(P.q N:ℝ)*Real.log (1-s j)))+
      (∑ i,(((P.C N-1:ℕ):ℝ)*Real.log |x i|+((2*P.h N:ℕ):ℝ)*Real.log (1-x i)))-
      (∑ i,∑ j,Real.log (1-2*x i*s j+x i^2))-
      (∑ i,((P.H N-2:ℕ):ℝ)*Real.log (1+x i^2)) :=by
  have hX :=energy_abs_vandermonde_pos x hxi
  have hS :=energy_abs_vandermonde_pos s hsi
  have hPair :=energy_pair_product_pos x hx
  have hK :=energy_mixed_product_pos x s hs
  have hSW :=param_s_weight_product_pos P N s hs
  have hW : 0<∏ i,|x i|^(P.C N-1)*(1-x i)^(2*P.h N) :=
    prod_pos fun i _ =>mul_pos (pow_pos (abs_pos.mpr (hx0 i)) _)
      (pow_pos (sub_pos.mpr (hx i).2) _)
  have hD : 0<∏ i,(1+x i^2)^(P.H N-2) :=
    prod_pos fun i _ =>pow_pos (realCoordinateInv_denominator_pos (x i)) _
  rw [paramPinPrincipal_coordinate hP hN x s hx]
  rw [Real.log_div (by positivity) (mul_pos hK hD).ne',
    Real.log_mul (by positivity) hW.ne',Real.log_mul (by positivity) hSW.ne',
    Real.log_mul (by positivity) hPair.ne',Real.log_mul (by positivity) (pow_ne_zero _ hS.ne'),
    Real.log_mul (by positivity) hX.ne',Real.log_mul hK.ne' hD.ne']
  rw [Real.log_pow,Real.log_pow,log_abs_vandermonde x hxi,
    log_abs_vandermonde s hsi,log_energy_pair_product x hx,
    log_param_s_weight_product P N s hs,
    log_positive_node_product _ _ x (fun i =>(hx i).2) hx0,
    log_energy_mixed_product x s hs,log_positive_quadratic_product]
  ring

theorem paramRowNodeWeight_pos (P : Parameters) (N : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) (hx0 : x≠0) : 0<paramRowNodeWeight P N x :=by
  have ht0 : realCoordinateInv x≠0 :=by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hx0) (by positivity)
  exact mul_pos (pow_pos (abs_pos.mpr ht0) _)
    (pow_pos (one_sub_realCoordinateInv_pos hx) _)

theorem log_paramRowNodeWeight (P : Parameters) (N : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) (hx0 : x≠0) :
    Real.log (paramRowNodeWeight P N x)=
      ((P.C N-1:ℕ):ℝ)*Real.log 2+((P.C N-1:ℕ):ℝ)*Real.log |x|+
      ((2*P.h N:ℕ):ℝ)*Real.log (1-x)-
      ((P.C N-1+P.h N:ℕ):ℝ)*Real.log (1+x^2) :=by
  have hA : |x|^(P.C N-1)≠0 :=pow_ne_zero _ (abs_ne_zero.mpr hx0)
  have hB : (1-x)^(2*P.h N)≠0 :=pow_ne_zero _ (sub_pos.mpr hx.2).ne'
  have hD : (1+x^2)^(P.C N-1+P.h N)≠0 :=
    pow_ne_zero _ (realCoordinateInv_denominator_pos x).ne'
  have hTwo : (2:ℝ)^(P.C N-1)≠0 :=by positivity
  rw [paramRowNodeWeight_coordinate,
    Real.log_div (mul_ne_zero hTwo (mul_ne_zero hA hB)) hD,
    Real.log_mul hTwo (mul_ne_zero hA hB),Real.log_mul hA hB]
  simp only [Real.log_pow]
  ring

theorem paramPinPrincipal_pos {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0<N)
    {p : ℕ} (x s : Fin p → ℝ)
    (hx : ∀ i,x i ∈ Ioo (-1:ℝ) 1) (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1)
    (hx0 : ∀ i,x i≠0) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    0<paramPinPrincipal P N x s :=by
  have hX :=energy_abs_vandermonde_pos x hxi
  have hS :=energy_abs_vandermonde_pos s hsi
  have hPair :=energy_pair_product_pos x hx
  have hK :=energy_mixed_product_pos x s hs
  have hSW :=param_s_weight_product_pos P N s hs
  have hW : 0<∏ i,|x i|^(P.C N-1)*(1-x i)^(2*P.h N) :=
    prod_pos fun i _ =>mul_pos (pow_pos (abs_pos.mpr (hx0 i)) _)
      (pow_pos (sub_pos.mpr (hx i).2) _)
  have hD : 0<∏ i,(1+x i^2)^(P.H N-2) :=
    prod_pos fun i _ =>pow_pos (realCoordinateInv_denominator_pos (x i)) _
  rw [paramPinPrincipal_coordinate hP hN x s hx]
  positivity

end
end CatalanMeasure.Parametric
