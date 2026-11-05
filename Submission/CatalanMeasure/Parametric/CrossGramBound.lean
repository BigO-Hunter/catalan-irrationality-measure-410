module

public import Submission.CatalanMeasure.Parametric.GroupedGramBound

@[expose] public section

namespace CatalanMeasure.Parametric

open scoped BigOperators

noncomputable section

theorem innerMatrix_eq_basis_product
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ E) (f g : ι → E) :
    Matrix.of (fun i j => inner ℂ (f i) (g j)) =
      (b.toBasis.toMatrix f).conjTranspose * b.toBasis.toMatrix g := by
  ext i j
  simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, b.coe_toBasis_repr_apply,
    b.repr_apply_apply, b.sum_inner_mul_inner]

theorem norm_innerMatrix_det
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ E) (f g : ι → E) :
    ‖(Matrix.of (fun i j => inner ℂ (f i) (g j))).det‖ =
      ‖b.toBasis.det f‖ * ‖b.toBasis.det g‖ := by
  rw [innerMatrix_eq_basis_product b f g, Matrix.det_mul, Matrix.det_conjTranspose,
    norm_mul, norm_star, Module.Basis.det_apply, Module.Basis.det_apply]

theorem norm_innerMatrix_det_gram
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ E) (f g : ι → E) :
    ‖(Matrix.of (fun i j => inner ℂ (f i) (g j))).det‖ =
      Real.sqrt ‖(Matrix.gram ℂ f).det‖ * Real.sqrt ‖(Matrix.gram ℂ g).det‖ := by
  rw [norm_innerMatrix_det b f g, norm_gram_det_eq_norm_basis_det_sq b f,
    norm_gram_det_eq_norm_basis_det_sq b g,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem grouped_innerMatrix_det_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {p q : ℕ}
    (b : OrthonormalBasis (Fin p ⊕ Fin q) ℂ E)
    (f : Fin p → E) (g : Fin q → E) (w : Fin p ⊕ Fin q → E)
    (hf : LinearIndependent ℂ f) (hg : LinearIndependent ℂ g)
    (L : E →ₗ[ℂ] E) {K : ℝ} (hK : 0 ≤ K)
    (hL : ∀ u, ‖L u‖ ≤ K * ‖u‖) :
    ‖(Matrix.of (fun i j => inner ℂ (Sum.elim (fun i => L (f i)) g i) (w j))).det‖ ≤
      K ^ p * Real.sqrt ‖(Matrix.gram ℂ f).det‖ * Real.sqrt ‖(Matrix.gram ℂ g).det‖ *
        Real.sqrt ‖(Matrix.gram ℂ w).det‖ := by
  rw [norm_innerMatrix_det b, norm_gram_det_eq_norm_basis_det_sq b w,
    Real.sqrt_sq (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (grouped_operator_det_gram_bound b f g hf hg L hK hL)
    (norm_nonneg _)

end

end CatalanMeasure.Parametric
