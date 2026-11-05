module

public import Submission.CatalanMeasure.Parametric.SheetMixedOperator
public import Submission.CatalanMeasure.Parametric.CauchyGroupProducts

/-!
# Grouped bound for actual and monomial sheet evaluations

Only the first group uses the actual reversal-plus-multiplier operator.
The second group retains its unmodified kernel volume.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Finset
open scoped BigOperators

noncomputable section

theorem sqrt_gram_det_comp_equiv
    {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : ι → E) (e : κ ≃ ι) :
    Real.sqrt ‖(Matrix.gram ℂ (v ∘ e)).det‖ = Real.sqrt ‖(Matrix.gram ℂ v).det‖ := by
  have hm : Matrix.gram ℂ (v ∘ e) = (Matrix.gram ℂ v).submatrix e e := rfl
  rw [hm, Matrix.det_submatrix_equiv_self]

theorem sheetKernelFamily_linearIndependent {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) :
    LinearIndependent ℂ (sheetKernelFamily x hx) := by
  exact (firstSheetKernelVector_linearIndependent x hx hxi).of_comp
    (firstSheetSpace x hx).subtype

theorem sheet_grouped_normalized_det_bound {p q : ℕ} (x : Fin (p + q) → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (Metric.closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖h z‖ ≤ K) :
    ‖(Matrix.of (fun (i r : Fin p ⊕ Fin q) =>
      Sum.elim
        (fun a => ((x (Fin.castAdd q a) : ℂ) ^ ((finSumFinEquiv r).rev : ℕ) +
          h (x (Fin.castAdd q a) : ℂ) * (x (Fin.castAdd q a) : ℂ) ^ (finSumFinEquiv r : ℕ)) /
          firstSheetDenominator univ x (x (Fin.castAdd q a) : ℂ))
        (fun a => (x (Fin.natAdd p a) : ℂ) ^ (finSumFinEquiv r : ℕ) /
          firstSheetDenominator univ x (x (Fin.natAdd p a) : ℂ)) i)).det‖ ≤
      (1 + K) ^ p *
        (|∏ i : Fin p, ∏ j ∈ Ioi i, (x (Fin.castAdd q j) - x (Fin.castAdd q i))| /
          Real.sqrt (cauchyNodeProduct (fun i => x (Fin.castAdd q i)))) *
        (|∏ i : Fin q, ∏ j ∈ Ioi i, (x (Fin.natAdd p j) - x (Fin.natAdd p i))| /
          Real.sqrt (cauchyNodeProduct (fun i => x (Fin.natAdd p i)))) *
        (1 / Real.sqrt (cauchyNodeProduct x)) := by
  let b : OrthonormalBasis (Fin p ⊕ Fin q) ℂ (firstSheetSpace x hx) :=
    ((stdOrthonormalBasis ℂ (firstSheetSpace x hx)).reindex
      (finCongr (firstSheetSpace_finrank x hx hxi))).reindex finSumFinEquiv.symm
  let f := fun i : Fin p => sheetKernelFamily x hx (Fin.castAdd q i)
  let g := fun i : Fin q => sheetKernelFamily x hx (Fin.natAdd p i)
  let w := sheetCoefficientFamily x hx ∘ finSumFinEquiv
  have hf : LinearIndependent ℂ f :=
    (sheetKernelFamily_linearIndependent x hx hxi).comp _ (Fin.castAdd_injective p q)
  have hg : LinearIndependent ℂ g :=
    (sheetKernelFamily_linearIndependent x hx hxi).comp _ (Fin.natAdd_injective q p)
  have hb := grouped_evaluation_det_bound b f g w hf hg
    (sheetSpaceMixedOperator x hx hxi h) (by positivity : 0 ≤ 1 + K)
    (sheetSpaceMixedOperator_norm_le x hx hxi h hh hK hbound)
  simp only [f, g, w, Function.comp_apply, sheetSpaceMixedOperator_inner_coefficient,
    sheetCoefficientFamily_inner] at hb
  have hgf : Matrix.gram ℂ f = Matrix.gram ℂ
      (fun i => firstSheetKernelVector (x (Fin.castAdd q i)) (hx (Fin.castAdd q i))) := rfl
  have hgg : Matrix.gram ℂ g = Matrix.gram ℂ
      (fun i => firstSheetKernelVector (x (Fin.natAdd p i)) (hx (Fin.natAdd p i))) := rfl
  rw [hgf, hgg, sqrt_norm_firstSheetKernelVector_gram_det,
    sqrt_norm_firstSheetKernelVector_gram_det] at hb
  rw [sqrt_gram_det_comp_equiv, sqrt_norm_sheetCoefficientFamily_gram_det x hx hxi] at hb
  exact hb

end

end CatalanMeasure.Parametric
