module

public import Submission.CatalanMeasure.Parametric.GroupedGramBound
public import Submission.OAI.NumberTheory.Catalan.Energy.RealTwoSheetIntegralBound
public import Submission.OAI.NumberTheory.Catalan.Determinants.RealCauchyDeterminant

/-!
# Exact Gram factors of real Hardy-space evaluation kernels

The Cauchy determinant formula supplies the within-group Vandermonde factors
needed in the grouped determinant bound.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Polynomial Set Finset
open scoped BigOperators

noncomputable section

theorem one_sub_node_mul_pos {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) :
    0 < 1 - x * y := by
  have hm : |x * y| < 1 := by
    rw [abs_mul]
    calc
      |x| * |y| ≤ 1 * |y| := mul_le_mul_of_nonneg_right hx.le (abs_nonneg y)
      _ < 1 := by simpa only [one_mul] using hy
  exact sub_pos.mpr ((le_abs_self (x * y)).trans_lt hm)

theorem firstSheetKernel_analytic_closedDisk {x : ℝ} (hx : |x| < 1) :
    AnalyticOnNhd ℂ (firstSheetKernel x) (Metric.closedBall (0 : ℂ) 1) := by
  unfold firstSheetKernel
  apply AnalyticOnNhd.inv
  · fun_prop
  · intro z hz
    apply firstSheetKernel_denominator_ne_zero hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz

theorem firstSheetKernelVector_gram {p : ℕ} (x : Fin p → ℝ)
    (hx : ∀ i, |x i| < 1) :
    Matrix.gram ℂ (fun i => firstSheetKernelVector (x i) (hx i)) =
      (Matrix.of (fun i j => (1 : ℝ) / (1 - x i * x j))).map Complex.ofReal := by
  ext i j
  rw [Matrix.gram_apply]
  change inner ℂ (firstSheetKernelVector (x i) (hx i))
    (firstSheetBoundaryVector (firstSheetKernel (x j)) _) = _
  rw [firstSheetBoundary_inner_kernel (firstSheetKernel_analytic_closedDisk (hx j)) (hx i)]
  simp only [firstSheetKernel, Matrix.map_apply, Matrix.of_apply, one_div,
    Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul]
  rw [mul_comm]

theorem norm_firstSheetKernelVector_gram_det {p : ℕ} (x : Fin p → ℝ)
    (hx : ∀ i, |x i| < 1) :
    ‖(Matrix.gram ℂ (fun i => firstSheetKernelVector (x i) (hx i))).det‖ =
      (∏ i : Fin p, ∏ j ∈ Ioi i, (x j - x i)) ^ 2 /
        (∏ i : Fin p, ∏ j : Fin p, (1 - x i * x j)) := by
  have hden : 0 < ∏ i : Fin p, ∏ j : Fin p, (1 - x i * x j) :=
    prod_pos fun i _ => prod_pos fun j _ => one_sub_node_mul_pos (hx i) (hx j)
  rw [firstSheetKernelVector_gram, firstSheet_norm_ofReal_det,
    cauchy_det_eq_prod x x (fun i j => (one_sub_node_mul_pos (hx i) (hx j)).ne'),
    ← pow_two, abs_of_nonneg (div_nonneg (sq_nonneg _) hden.le)]

theorem sqrt_norm_firstSheetKernelVector_gram_det {p : ℕ} (x : Fin p → ℝ)
    (hx : ∀ i, |x i| < 1) :
    Real.sqrt ‖(Matrix.gram ℂ (fun i => firstSheetKernelVector (x i) (hx i))).det‖ =
      |∏ i : Fin p, ∏ j ∈ Ioi i, (x j - x i)| /
        Real.sqrt (∏ i : Fin p, ∏ j : Fin p, (1 - x i * x j)) := by
  rw [norm_firstSheetKernelVector_gram_det, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem firstSheetKernelVector_linearIndependent {p : ℕ} (x : Fin p → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) :
    LinearIndependent ℂ (fun i => firstSheetKernelVector (x i) (hx i)) := by
  have hV : (∏ i : Fin p, ∏ j ∈ Ioi i, (x j - x i)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro i _
    apply prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro h
    exact (ne_of_lt (mem_Ioi.mp hj)) (hxi h).symm
  have hden : 0 < ∏ i : Fin p, ∏ j : Fin p, (1 - x i * x j) :=
    prod_pos fun i _ => prod_pos fun j _ => one_sub_node_mul_pos (hx i) (hx j)
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  apply norm_ne_zero_iff.mp
  rw [norm_firstSheetKernelVector_gram_det]
  exact (div_pos (sq_pos_of_ne_zero hV) hden).ne'

end

end CatalanMeasure.Parametric
