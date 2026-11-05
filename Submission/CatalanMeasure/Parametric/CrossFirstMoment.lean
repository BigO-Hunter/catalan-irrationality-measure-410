module

public import Submission.CatalanMeasure.Parametric.CauchyGroupProducts
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A coupled first-moment majorant for the regular cross product

The scalar log(1-xy) <= -xy retains the interaction of the two first moments.
Its quadratic coupling admits an elementary square-completion certificate.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open Finset
open scoped BigOperators

noncomputable section

theorem crossCauchyProduct_log_le_first_moment
    {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι → ℝ) (y : κ → ℝ)
    (hx : ∀ i, |x i| < 1) (hy : ∀ j, |y j| < 1) :
    Real.log (crossCauchyProduct x y) ≤ -(∑ i, x i) * (∑ j, y j) := by
  unfold crossCauchyProduct
  rw [Real.log_prod (fun i _ =>
    (prod_pos fun j _ => one_sub_node_mul_pos (hx i) (hy j)).ne')]
  calc
    _ = ∑ i, ∑ j, Real.log (1 - x i * y j) := by
      apply sum_congr rfl
      intro i _
      exact Real.log_prod (fun j _ => (one_sub_node_mul_pos (hx i) (hy j)).ne')
    _ ≤ ∑ i, ∑ j, -(x i * y j) := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      have h := Real.log_le_sub_one_of_pos (one_sub_node_mul_pos (hx i) (hy j))
      linarith only [h]
    _ = _ := by simp [sum_neg_distrib, ← mul_sum, ← sum_mul, neg_mul]

theorem crossCauchyProduct_le_exp_first_moment
    {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι → ℝ) (y : κ → ℝ)
    (hx : ∀ i, |x i| < 1) (hy : ∀ j, |y j| < 1) :
    crossCauchyProduct x y ≤ Real.exp (-(∑ i, x i) * (∑ j, y j)) := by
  have h := Real.exp_le_exp.mpr (crossCauchyProduct_log_le_first_moment x y hx hy)
  rwa [Real.exp_log (crossCauchyProduct_pos x y hx hy)] at h

theorem first_moment_coupled_dual (a b c d : ℝ) :
    -(a ^ 2) - b ^ 2 - a * b ≤
      c ^ 2 + d ^ 2 + c * d - (2 * c + d) * a - (2 * d + c) * b := by
  nlinarith only [sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a - c + (b - d))]

end

end CatalanMeasure.Parametric
