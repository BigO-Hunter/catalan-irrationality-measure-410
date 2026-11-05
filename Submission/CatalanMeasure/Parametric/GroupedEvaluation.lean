module

public import Submission.CatalanMeasure.Parametric.CrossGramBound
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Grouped evaluation determinants and adjoints

Transfer the group volume bound to a matrix where only the first row group
evaluates a bounded operator applied to the coefficient vectors.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

noncomputable section

theorem adjoint_norm_le_of_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) {K : ℝ} (hK : 0 ≤ K)
    (hT : ∀ u, ‖T u‖ ≤ K * ‖u‖) (u : E) : ‖T.adjoint u‖ ≤ K * ‖u‖ := by
  letI := FiniteDimensional.complete ℂ E
  change ‖T.toContinuousLinearMap.adjoint u‖ ≤ _
  calc
    _ ≤ ‖T.toContinuousLinearMap.adjoint‖ * ‖u‖ :=
      T.toContinuousLinearMap.adjoint.le_opNorm u
    _ = ‖T.toContinuousLinearMap‖ * ‖u‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ K * ‖u‖ := mul_le_mul_of_nonneg_right
      (T.toContinuousLinearMap.opNorm_le_bound hK hT) (norm_nonneg u)

theorem grouped_evaluation_det_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {p q : ℕ}
    (b : OrthonormalBasis (Fin p ⊕ Fin q) ℂ E)
    (f : Fin p → E) (g : Fin q → E) (w : Fin p ⊕ Fin q → E)
    (hf : LinearIndependent ℂ f) (hg : LinearIndependent ℂ g)
    (T : E →ₗ[ℂ] E) {K : ℝ} (hK : 0 ≤ K)
    (hT : ∀ u, ‖T u‖ ≤ K * ‖u‖) :
    ‖(Matrix.of (fun i j => Sum.elim (fun a => inner ℂ (f a) (T (w j)))
      (fun a => inner ℂ (g a) (w j)) i)).det‖ ≤
      K ^ p * Real.sqrt ‖(Matrix.gram ℂ f).det‖ * Real.sqrt ‖(Matrix.gram ℂ g).det‖ *
        Real.sqrt ‖(Matrix.gram ℂ w).det‖ := by
  have h := grouped_innerMatrix_det_bound b f g w hf hg T.adjoint hK
    (adjoint_norm_le_of_bound T hK hT)
  have hm : Matrix.of (fun i j => Sum.elim (fun a => inner ℂ (f a) (T (w j)))
      (fun a => inner ℂ (g a) (w j)) i) =
      Matrix.of (fun i j => inner ℂ (Sum.elim (fun a => T.adjoint (f a)) g i) (w j)) := by
    ext i j
    rcases i with i | i
    · exact (T.adjoint_inner_left (w j) (f i)).symm
    · rfl
  rw [hm]
  exact h

end

end CatalanMeasure.Parametric
