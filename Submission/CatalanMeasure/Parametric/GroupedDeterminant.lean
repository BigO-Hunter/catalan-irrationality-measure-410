module

public import Submission.OAI.NumberTheory.Catalan.Energy.FirstSheetHilbertDeterminant

/-!
# Determinants with one operator applied to only one column group

The coordinate determinants of each group are retained separately. This is
the algebraic Hilbert-space step for a block-Gram estimate; its application
to the actual Catalan matrix still requires the evaluation-kernel factors.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open scoped BigOperators

noncomputable section

theorem orthonormalBasis_det_norm_le_prod_norm_fin
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ E)
    (f : Fin n → E) : ‖b.toBasis.det f‖ ≤ ∏ i, ‖f i‖ := by
  classical
  have hd : Module.finrank ℂ E = Fintype.card (Fin n) :=
    Module.finrank_eq_card_basis b.toBasis
  let c := InnerProductSpace.gramSchmidtOrthonormalBasis hd f
  have hdet : ‖b.toBasis.det f‖ = ‖c.toBasis.det f‖ := by
    have h : b.toBasis.det f = b.toBasis.det c * c.toBasis.det f := by
      simpa only [AlternatingMap.smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis] using
        DFunLike.congr_fun (b.toBasis.det.eq_smul_basis_det c.toBasis) f
    rw [h, norm_mul, OrthonormalBasis.det_to_matrix_orthonormalBasis, one_mul]
  rw [hdet]
  have hp := InnerProductSpace.gramSchmidtOrthonormalBasis_det hd f
  rw [hp, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  exact (norm_inner_le_norm (c i) (f i)).trans_eq (by rw [c.norm_eq_one, one_mul])

theorem orthonormalBasis_det_norm_le_prod_norm
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (f : ι → E) :
    ‖b.toBasis.det f‖ ≤ ∏ i, ‖f i‖ := by
  classical
  let e := Fintype.equivFin ι
  have h := orthonormalBasis_det_norm_le_prod_norm_fin (b.reindex e) (f ∘ e.symm)
  change ‖(b.toBasis.reindex e).det (f ∘ e.symm)‖ ≤ _ at h
  rw [Module.Basis.det_reindex] at h
  have h' : ‖b.toBasis.det f‖ ≤ ∏ i : Fin (Fintype.card ι), ‖f (e.symm i)‖ := by
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id,
      Function.comp_apply] using h
  exact h'.trans_eq (e.symm.prod_comp (fun i => ‖f i‖))

theorem basis_det_sum_smul
    {E ι : Type*} [AddCommGroup E] [Module ℂ E] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ E) (v : ι → E) (C : Matrix ι ι ℂ) :
    b.det (fun i => ∑ j, C j i • v j) = b.det v * C.det := by
  have hmatrix : b.toMatrix (fun i => ∑ j, C j i • v j) = b.toMatrix v * C := by
    ext i j
    simp only [Module.Basis.toMatrix_apply, map_sum, map_smul, Finsupp.smul_apply,
      Finsupp.finsetSum_apply, smul_eq_mul, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  rw [Module.Basis.det_apply, hmatrix, Matrix.det_mul, Module.Basis.det_apply]

theorem grouped_operator_det_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {p q : ℕ}
    (b : OrthonormalBasis (Fin p ⊕ Fin q) ℂ E)
    (U : Fin p → E) (V : Fin q → E)
    (hU : ∀ i, ‖U i‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1)
    (L : E →ₗ[ℂ] E) {K : ℝ} (hK : 0 ≤ K)
    (hL : ∀ u, ‖L u‖ ≤ K * ‖u‖)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) :
    ‖b.toBasis.det (Sum.elim (fun i => L (∑ j, A j i • U j))
      (fun i => ∑ j, B j i • V j))‖ ≤ K ^ p * ‖A.det‖ * ‖B.det‖ := by
  classical
  let v : Fin p ⊕ Fin q → E := Sum.elim (fun i => L (U i)) V
  let C : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks A 0 0 B
  have hfamily : Sum.elim (fun i => L (∑ j, A j i • U j))
      (fun i => ∑ j, B j i • V j) = fun i => ∑ j, C j i • v j := by
    funext i
    rcases i with i | i <;>
      simp [C, v, Fintype.sum_sum_type, map_sum, map_smul]
  have hv : ‖b.toBasis.det v‖ ≤ K ^ p := by
    apply (orthonormalBasis_det_norm_le_prod_norm b v).trans
    calc
      (∏ i, ‖v i‖) = (∏ i : Fin p, ‖L (U i)‖) * ∏ j : Fin q, ‖V j‖ := by
        simp [v, Fintype.prod_sum_type]
      _ ≤ (∏ _i : Fin p, K) * ∏ _j : Fin q, (1 : ℝ) := by
        apply mul_le_mul
        · apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro i _
          exact (hL (U i)).trans (by simpa using mul_le_mul_of_nonneg_left (hU i) hK)
        · exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hV j)
        · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
        · exact Finset.prod_nonneg (fun _ _ => hK)
      _ = K ^ p := by simp
  rw [hfamily, basis_det_sum_smul, norm_mul]
  have hC : C.det = A.det * B.det := Matrix.det_fromBlocks_zero₂₁ A 0 B
  rw [hC, norm_mul]
  exact (mul_le_mul_of_nonneg_right hv
    (mul_nonneg (norm_nonneg A.det) (norm_nonneg B.det))).trans_eq (by ring)

end

end CatalanMeasure.Parametric
