module

public import Submission.CatalanMeasure.MixedAndreief

@[expose] public section

/-!
# The single-measure Andreief (Heine) identity with fixed columns

For a finite measure `μ` on `ℝ`, functions `F : Fin (p + m) → ℝ → ℝ`, `G : Fin p → ℝ → ℝ` and
fixed nodes `τ' : Fin m → ℝ`,

  `∫ rowDet F τ' t · det [G_i(t_j)] dμ^p(t) = p! · det M`,

where `M r c = ∫ F_r G_c dμ` for `c < p` and `M r (p + j) = F_r(τ'_j)`.  This is the first half of
`CatalanMeasure.MixedAndreief` (one antisymmetrisation instead of two); the permutation layer
(`permExt`, `append_comp_perm`, `sign_permExt`, `rowDet`, `rowDet_comp_perm`) is imported
unchanged.
-/

open MeasureTheory Finset

namespace CatalanMeasure

section Algebra

variable {p m : ℕ} (F : Fin (p + m) → ℝ → ℝ) (τ' : Fin m → ℝ) (G : Fin p → ℝ → ℝ)

/-- The integrand after integrating the columns. -/
noncomputable def heineRaw (t : Fin p → ℝ) : ℝ :=
  rowDet F τ' t * ∏ i, G i (t i)

/-- The antisymmetrised integrand `rowDet F τ' t · det [G_i(t_j)]`. -/
noncomputable def heineDet (t : Fin p → ℝ) : ℝ :=
  rowDet F τ' t * (Matrix.of fun j i : Fin p => G i (t j)).det

theorem sum_heineRaw_perm (t : Fin p → ℝ) :
    ∑ σ : Equiv.Perm (Fin p), heineRaw F τ' G (t ∘ σ) = heineDet F τ' G t := by
  unfold heineRaw heineDet
  rw [Matrix.det_apply' (Matrix.of fun j i : Fin p => G i (t j))]
  simp only [rowDet_comp_perm, Function.comp_apply, Matrix.of_apply, mul_sum]
  apply sum_congr rfl
  intro σ _
  ring

theorem heineRaw_expand (t : Fin p → ℝ) :
    heineRaw F τ' G t = ∑ σ : Equiv.Perm (Fin (p + m)),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ j, F (σ (Fin.natAdd p j)) (τ' j)) *
        ∏ i, (F (σ (Fin.castAdd m i)) (t i) * G i (t i)) := by
  unfold heineRaw rowDet
  rw [Matrix.det_apply', sum_mul]
  apply sum_congr rfl
  intro σ _
  simp only [Matrix.of_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    prod_mul_distrib]
  ring

end Algebra

section Integral

variable {p m : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ]
variable (F : Fin (p + m) → ℝ → ℝ) (τ' : Fin m → ℝ) (G : Fin p → ℝ → ℝ)

/-- The Heine moment matrix. -/
noncomputable def heineMatrix : Matrix (Fin (p + m)) (Fin (p + m)) ℝ :=
  Matrix.of fun r c => Fin.addCases
    (fun i : Fin p => ∫ z, F r z * G i z ∂μ)
    (fun j : Fin m => F r (τ' j)) c

variable {μ F G}

theorem integrable_heineRaw
    (hint : ∀ r i, Integrable (fun z : ℝ => F r z * G i z) μ) :
    Integrable (fun t : Fin p → ℝ => heineRaw F τ' G t) (Measure.pi fun _ : Fin p => μ) := by
  have hsum := integrable_finsetSum (μ := Measure.pi fun _ : Fin p => μ)
    (univ : Finset (Equiv.Perm (Fin (p + m))))
    (f := fun σ (t : Fin p → ℝ) =>
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ j, F (σ (Fin.natAdd p j)) (τ' j)) *
        ∏ i, (F (σ (Fin.castAdd m i)) (t i) * G i (t i)))
    (fun σ _ => (Integrable.fintype_prod (μ := fun _ : Fin p => μ)
      (f := fun i (z : ℝ) => F (σ (Fin.castAdd m i)) z * G i z)
      (fun i => hint _ i)).const_mul _)
  refine hsum.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [heineRaw_expand]

theorem integral_heineRaw
    (hint : ∀ r i, Integrable (fun z : ℝ => F r z * G i z) μ) :
    ∫ t, heineRaw F τ' G t ∂(Measure.pi fun _ : Fin p => μ) = (heineMatrix μ F τ' G).det := by
  simp_rw [heineRaw_expand]
  rw [integral_finsetSum _ (fun σ _ => (Integrable.fintype_prod
      (μ := fun _ : Fin p => μ)
      (f := fun i (z : ℝ) => F (σ (Fin.castAdd m i)) z * G i z)
      (fun i => hint _ i)).const_mul _)]
  rw [Matrix.det_apply']
  apply sum_congr rfl
  intro σ _
  rw [integral_const_mul, integral_fintype_prod_eq_prod
    (fun i (z : ℝ) => F (σ (Fin.castAdd m i)) z * G i z)]
  simp only [heineMatrix, Matrix.of_apply, Fin.prod_univ_add, Fin.addCases_left,
    Fin.addCases_right]
  ring

theorem integral_perm (σ : Equiv.Perm (Fin p)) (H : (Fin p → ℝ) → ℝ) :
    (∫ t, H (t ∘ σ) ∂(Measure.pi fun _ : Fin p => μ)) =
      ∫ t, H t ∂(Measure.pi fun _ : Fin p => μ) :=
  (measurePreserving_piCongrLeft (fun _ : Fin p => μ) σ).symm.integral_comp' H

theorem integrable_perm (σ : Equiv.Perm (Fin p)) {H : (Fin p → ℝ) → ℝ}
    (hH : Integrable H (Measure.pi fun _ : Fin p => μ)) :
    Integrable (fun t => H (t ∘ σ)) (Measure.pi fun _ : Fin p => μ) :=
  (measurePreserving_piCongrLeft (fun _ : Fin p => μ) σ).symm.integrable_comp_of_integrable hH

theorem integrable_heineDet
    (hint : ∀ r i, Integrable (fun z : ℝ => F r z * G i z) μ) :
    Integrable (fun t : Fin p → ℝ => heineDet F τ' G t) (Measure.pi fun _ : Fin p => μ) := by
  have hi := integrable_finsetSum (univ : Finset (Equiv.Perm (Fin p)))
    (fun σ _ => integrable_perm σ (integrable_heineRaw τ' hint))
  refine hi.congr (Filter.Eventually.of_forall fun t => ?_)
  exact sum_heineRaw_perm F τ' G t

/-- **Heine–Andreief identity with fixed columns.** -/
theorem integral_rowDet_mul_det
    (hint : ∀ r i, Integrable (fun z : ℝ => F r z * G i z) μ) :
    ∫ t, rowDet F τ' t * (Matrix.of fun j i : Fin p => G i (t j)).det
        ∂(Measure.pi fun _ : Fin p => μ) =
      (p.factorial : ℝ) * (heineMatrix μ F τ' G).det := by
  calc ∫ t, rowDet F τ' t * (Matrix.of fun j i : Fin p => G i (t j)).det
        ∂(Measure.pi fun _ : Fin p => μ)
      = ∫ t, ∑ σ : Equiv.Perm (Fin p), heineRaw F τ' G (t ∘ σ)
          ∂(Measure.pi fun _ : Fin p => μ) := by
        apply integral_congr_ae
        filter_upwards with t
        exact (sum_heineRaw_perm F τ' G t).symm
    _ = ∑ σ : Equiv.Perm (Fin p), ∫ t, heineRaw F τ' G (t ∘ σ)
          ∂(Measure.pi fun _ : Fin p => μ) :=
        integral_finsetSum _ (fun σ _ => integrable_perm σ (integrable_heineRaw τ' hint))
    _ = _ := by
        simp only [integral_perm _ (fun t => heineRaw F τ' G t),
          integral_heineRaw τ' hint, sum_const, card_univ, Fintype.card_perm,
          Fintype.card_fin, nsmul_eq_mul]

end Integral

end CatalanMeasure

#print axioms CatalanMeasure.integral_rowDet_mul_det
