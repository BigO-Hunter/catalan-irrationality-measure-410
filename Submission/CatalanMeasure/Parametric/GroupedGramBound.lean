module

public import Submission.CatalanMeasure.Parametric.GroupedDeterminant
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# The Gram volumes retained by a grouped operator determinant

The first group passes through one bounded operator; the second does not.
This preserves both within-group volume factors, without a row-hole loss.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open scoped BigOperators

noncomputable section

theorem norm_gram_det_eq_norm_basis_det_sq
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ E) (f : ι → E) :
    ‖(Matrix.gram ℂ f).det‖ = ‖b.toBasis.det f‖ ^ 2 := by
  rw [Matrix.gram_eq_conjTranspose_mul b f, Matrix.det_mul, Matrix.det_conjTranspose,
    norm_mul, norm_star, Module.Basis.det_apply]
  rw [pow_two]
  have he : (Matrix.of fun i j => (b.repr (f j)).ofLp i) = b.toBasis.toMatrix f := by
    ext i j
    exact (b.coe_toBasis_repr_apply (f j) i).symm
  rw [he]

theorem grouped_operator_det_gram_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {p q : ℕ}
    (b : OrthonormalBasis (Fin p ⊕ Fin q) ℂ E)
    (f : Fin p → E) (g : Fin q → E)
    (hf : LinearIndependent ℂ f) (hg : LinearIndependent ℂ g)
    (L : E →ₗ[ℂ] E) {K : ℝ} (hK : 0 ≤ K)
    (hL : ∀ u, ‖L u‖ ≤ K * ‖u‖) :
    ‖b.toBasis.det (Sum.elim (fun i => L (f i)) g)‖ ≤
      K ^ p * Real.sqrt ‖(Matrix.gram ℂ f).det‖ *
        Real.sqrt ‖(Matrix.gram ℂ g).det‖ := by
  classical
  let Sf := Submodule.span ℂ (Set.range f)
  let Sg := Submodule.span ℂ (Set.range g)
  let ff : Fin p → Sf := fun i => ⟨f i, Submodule.subset_span ⟨i, rfl⟩⟩
  let gg : Fin q → Sg := fun i => ⟨g i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hdf : Module.finrank ℂ Sf = Fintype.card (Fin p) := finrank_span_eq_card hf
  have hdg : Module.finrank ℂ Sg = Fintype.card (Fin q) := finrank_span_eq_card hg
  let a := InnerProductSpace.gramSchmidtOrthonormalBasis hdf ff
  let c := InnerProductSpace.gramSchmidtOrthonormalBasis hdg gg
  let U : Fin p → E := fun i => (a i : E)
  let V : Fin q → E := fun i => (c i : E)
  let A : Matrix (Fin p) (Fin p) ℂ := a.toBasis.toMatrix ff
  let B : Matrix (Fin q) (Fin q) ℂ := c.toBasis.toMatrix gg
  have hU : ∀ i, ‖U i‖ ≤ 1 := fun i => (a.norm_eq_one i).le
  have hV : ∀ i, ‖V i‖ ≤ 1 := fun i => (c.norm_eq_one i).le
  have hsumf (i : Fin p) : (∑ j, A j i • U j) = f i := by
    have h := congrArg (fun z : Sf => (z : E)) (a.toBasis.sum_toMatrix_smul_self ff i)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, OrthonormalBasis.coe_toBasis] using h
  have hsumg (i : Fin q) : (∑ j, B j i • V j) = g i := by
    have h := congrArg (fun z : Sg => (z : E)) (c.toBasis.sum_toMatrix_smul_self gg i)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, OrthonormalBasis.coe_toBasis] using h
  have hAf : Real.sqrt ‖(Matrix.gram ℂ f).det‖ = ‖A.det‖ := by
    have he : Matrix.gram ℂ f = Matrix.gram ℂ ff := rfl
    rw [he, norm_gram_det_eq_norm_basis_det_sq a ff, Real.sqrt_sq (norm_nonneg _)]
    rfl
  have hBg : Real.sqrt ‖(Matrix.gram ℂ g).det‖ = ‖B.det‖ := by
    have he : Matrix.gram ℂ g = Matrix.gram ℂ gg := rfl
    rw [he, norm_gram_det_eq_norm_basis_det_sq c gg, Real.sqrt_sq (norm_nonneg _)]
    rfl
  have h := grouped_operator_det_bound b U V hU hV L hK hL A B
  simp_rw [hsumf, hsumg] at h
  rw [hAf, hBg]
  exact h

end

end CatalanMeasure.Parametric
