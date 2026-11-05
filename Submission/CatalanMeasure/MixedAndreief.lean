module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# A mixed Andreief identity

Let `B` be the `(p + m) × (p + m)` matrix whose first `p` columns are moments
`B r i = ∫∫ F_r(t) G_i(s) K(t, s) dμ(t) dν(s)` and whose last `m` columns are point values
`B r (p + j) = F_r(τ'_j)`.  Integrating the columns one at a time and antisymmetrizing in the
`t`- and then the `s`-variables gives

  `(p!)² det B = ∫∫ det [F_r(t ⧺ τ')] · det [K(t_i, s_j)] · det [G_i(s_j)] dμ^p(t) dν^p(s)`,

the identity of OpenAI's `determinant_eq_productRealIntegral` (the case `m = 0`) with fixed
columns added.  Consequently `|det B|` is at most the supremum of the right-hand integrand times
the mass of `μ^p ⊗ ν^p`.
-/

open MeasureTheory Finset

namespace CatalanMeasure

section Algebra

variable {p m : ℕ}

/-- A permutation of the first `p` indices, extended by the identity. -/
def permExt (σ : Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p + m)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr σ (Equiv.refl (Fin m)))

theorem append_comp_perm (t : Fin p → ℝ) (τ' : Fin m → ℝ) (σ : Equiv.Perm (Fin p)) :
    Fin.append (t ∘ σ) τ' = Fin.append t τ' ∘ permExt σ := by
  funext c
  refine Fin.addCases (fun i => ?_) (fun j => ?_) c
  · simp [permExt, Equiv.permCongr_apply]
  · simp [permExt, Equiv.permCongr_apply]

theorem sign_permExt (σ : Equiv.Perm (Fin p)) :
    Equiv.Perm.sign (permExt (m := m) σ) = Equiv.Perm.sign σ := by
  simp [permExt, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

variable (F : Fin (p + m) → ℝ → ℝ) (τ' : Fin m → ℝ) (G : Fin p → ℝ → ℝ) (K : ℝ → ℝ → ℝ)

/-- The row determinant with `p` free and `m` fixed nodes. -/
noncomputable def rowDet (t : Fin p → ℝ) : ℝ :=
  (Matrix.of fun r c => F r (Fin.append t τ' c)).det

theorem rowDet_comp_perm (t : Fin p → ℝ) (σ : Equiv.Perm (Fin p)) :
    rowDet F τ' (t ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * rowDet F τ' t := by
  unfold rowDet
  rw [append_comp_perm]
  have h := Matrix.det_permute' (permExt (m := m) σ)
    (Matrix.of fun r c => F r (Fin.append t τ' c))
  rw [sign_permExt] at h
  exact h

/-- The integrand after integrating the columns. -/
noncomputable def mixedRaw (t s : Fin p → ℝ) : ℝ :=
  rowDet F τ' t * ∏ i, (G i (s i) * K (t i) (s i))

/-- The integrand after antisymmetrizing in `t`. -/
noncomputable def mixedLeft (t s : Fin p → ℝ) : ℝ :=
  rowDet F τ' t * (Matrix.of fun i j : Fin p => K (t i) (s j)).det * ∏ i, G i (s i)

/-- The fully antisymmetrized integrand. -/
noncomputable def mixedDouble (t s : Fin p → ℝ) : ℝ :=
  rowDet F τ' t * (Matrix.of fun i j : Fin p => K (t i) (s j)).det *
    (Matrix.of fun j i : Fin p => G i (s j)).det

theorem sum_mixedRaw_perm (t s : Fin p → ℝ) :
    ∑ σ : Equiv.Perm (Fin p), mixedRaw F τ' G K (t ∘ σ) s = mixedLeft F τ' G K t s := by
  unfold mixedRaw mixedLeft
  rw [Matrix.det_apply' (Matrix.of fun i j : Fin p => K (t i) (s j))]
  simp only [rowDet_comp_perm, Function.comp_apply, Matrix.of_apply, prod_mul_distrib,
    mul_sum, sum_mul]
  apply sum_congr rfl
  intro σ _
  ring

theorem sum_mixedLeft_perm (t s : Fin p → ℝ) :
    ∑ π : Equiv.Perm (Fin p), mixedLeft F τ' G K t (s ∘ π) = mixedDouble F τ' G K t s := by
  unfold mixedLeft mixedDouble
  rw [Matrix.det_apply' (Matrix.of fun j i : Fin p => G i (s j))]
  have hK : ∀ π : Equiv.Perm (Fin p),
      (Matrix.of fun i j : Fin p => K (t i) (s (π j))).det =
        ((Equiv.Perm.sign π : ℤ) : ℝ) * (Matrix.of fun i j : Fin p => K (t i) (s j)).det :=
    fun π => Matrix.det_permute' π (Matrix.of fun i j : Fin p => K (t i) (s j))
  simp only [Function.comp_apply, hK, Matrix.of_apply, mul_sum]
  apply sum_congr rfl
  intro π _
  ring

/-- Expansion of the raw integrand into products over the free pairs. -/
theorem mixedRaw_expand (t s : Fin p → ℝ) :
    mixedRaw F τ' G K t s = ∑ σ : Equiv.Perm (Fin (p + m)),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ j, F (σ (Fin.natAdd p j)) (τ' j)) *
        ∏ i, (F (σ (Fin.castAdd m i)) (t i) * (G i (s i) * K (t i) (s i))) := by
  unfold mixedRaw rowDet
  rw [Matrix.det_apply', sum_mul]
  apply sum_congr rfl
  intro σ _
  simp only [Matrix.of_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    prod_mul_distrib]
  ring

end Algebra

section Integral

variable {p m : ℕ} (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable (F : Fin (p + m) → ℝ → ℝ) (τ' : Fin m → ℝ) (G : Fin p → ℝ → ℝ) (K : ℝ → ℝ → ℝ)

/-- The mixed moment matrix. -/
noncomputable def mixedMatrix : Matrix (Fin (p + m)) (Fin (p + m)) ℝ :=
  Matrix.of fun r c => Fin.addCases
    (fun i : Fin p => ∫ z, F r z.1 * (G i z.2 * K z.1 z.2) ∂(μ.prod ν))
    (fun j : Fin m => F r (τ' j)) c

/-- The product measure on pairs of lists. -/
noncomputable def pairMeasure (p : ℕ) : Measure ((Fin p → ℝ) × (Fin p → ℝ)) :=
  (Measure.pi fun _ : Fin p => μ).prod (Measure.pi fun _ : Fin p => ν)

instance (p : ℕ) : IsFiniteMeasure (pairMeasure μ ν p) := by
  unfold pairMeasure
  infer_instance

variable {μ ν F G K}

theorem integrable_mixedRaw
    (hint : ∀ r i, Integrable (fun z : ℝ × ℝ => F r z.1 * (G i z.2 * K z.1 z.2)) (μ.prod ν)) :
    Integrable (fun w : (Fin p → ℝ) × (Fin p → ℝ) => mixedRaw F τ' G K w.1 w.2)
      (pairMeasure μ ν p) := by
  have hmap := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin p)
    (fun _ => μ) (fun _ => ν)
  apply (hmap.integrable_comp_emb
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin p)).measurableEmbedding).mp
  have hsum := integrable_finsetSum (μ := Measure.pi fun _ : Fin p => μ.prod ν)
    (univ : Finset (Equiv.Perm (Fin (p + m))))
    (f := fun σ (z : Fin p → ℝ × ℝ) =>
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ j, F (σ (Fin.natAdd p j)) (τ' j)) *
        ∏ i, (F (σ (Fin.castAdd m i)) (z i).1 * (G i (z i).2 * K (z i).1 (z i).2)))
    (fun σ _ => (Integrable.fintype_prod (μ := fun _ : Fin p => μ.prod ν)
      (f := fun i (z : ℝ × ℝ) => F (σ (Fin.castAdd m i)) z.1 * (G i z.2 * K z.1 z.2))
      (fun i => hint _ i)).const_mul _)
  refine hsum.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply]
  rw [mixedRaw_expand]
  rfl

theorem integral_mixedRaw
    (hint : ∀ r i, Integrable (fun z : ℝ × ℝ => F r z.1 * (G i z.2 * K z.1 z.2)) (μ.prod ν)) :
    ∫ w, mixedRaw F τ' G K w.1 w.2 ∂(pairMeasure μ ν p) = (mixedMatrix μ ν F τ' G K).det := by
  have hmap := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin p)
    (fun _ => μ) (fun _ => ν)
  unfold pairMeasure
  rw [← hmap.integral_comp' (fun w => mixedRaw F τ' G K w.1 w.2)]
  have hexp : ∀ z : Fin p → ℝ × ℝ,
      mixedRaw F τ' G K ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin p)) z).1
        ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin p)) z).2 =
      ∑ σ : Equiv.Perm (Fin (p + m)),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ j, F (σ (Fin.natAdd p j)) (τ' j)) *
          ∏ i, (F (σ (Fin.castAdd m i)) (z i).1 * (G i (z i).2 * K (z i).1 (z i).2)) := by
    intro z
    rw [mixedRaw_expand]
    rfl
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun σ _ => (Integrable.fintype_prod
      (μ := fun _ : Fin p => μ.prod ν)
      (f := fun i (z : ℝ × ℝ) => F (σ (Fin.castAdd m i)) z.1 * (G i z.2 * K z.1 z.2))
      (fun i => hint _ i)).const_mul _)]
  rw [Matrix.det_apply']
  apply sum_congr rfl
  intro σ _
  rw [integral_const_mul, integral_fintype_prod_eq_prod
    (fun i (z : ℝ × ℝ) => F (σ (Fin.castAdd m i)) z.1 * (G i z.2 * K z.1 z.2))]
  simp only [mixedMatrix, Matrix.of_apply, Fin.prod_univ_add, Fin.addCases_left,
    Fin.addCases_right]
  ring

theorem pair_permute_left_preserving (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin p => ℝ) σ).symm.prodCongr
        (MeasurableEquiv.refl (Fin p → ℝ)))
      (pairMeasure μ ν p) (pairMeasure μ ν p) :=
  (measurePreserving_piCongrLeft (fun _ : Fin p => μ) σ).symm.prod (MeasurePreserving.id _)

theorem pair_permute_right_preserving (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving
      ((MeasurableEquiv.refl (Fin p → ℝ)).prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ : Fin p => ℝ) σ).symm)
      (pairMeasure μ ν p) (pairMeasure μ ν p) :=
  (MeasurePreserving.id _).prod (measurePreserving_piCongrLeft (fun _ : Fin p => ν) σ).symm

theorem integral_pair_permute_left (σ : Equiv.Perm (Fin p))
    (H : (Fin p → ℝ) × (Fin p → ℝ) → ℝ) :
    (∫ w, H (w.1 ∘ σ, w.2) ∂pairMeasure μ ν p) = ∫ w, H w ∂pairMeasure μ ν p :=
  (pair_permute_left_preserving σ).integral_comp' H

theorem integral_pair_permute_right (σ : Equiv.Perm (Fin p))
    (H : (Fin p → ℝ) × (Fin p → ℝ) → ℝ) :
    (∫ w, H (w.1, w.2 ∘ σ) ∂pairMeasure μ ν p) = ∫ w, H w ∂pairMeasure μ ν p :=
  (pair_permute_right_preserving σ).integral_comp' H

theorem integrable_pair_permute_left (σ : Equiv.Perm (Fin p))
    {H : (Fin p → ℝ) × (Fin p → ℝ) → ℝ} (hH : Integrable H (pairMeasure μ ν p)) :
    Integrable (fun w => H (w.1 ∘ σ, w.2)) (pairMeasure μ ν p) :=
  (pair_permute_left_preserving σ).integrable_comp_of_integrable hH

theorem integrable_pair_permute_right (σ : Equiv.Perm (Fin p))
    {H : (Fin p → ℝ) × (Fin p → ℝ) → ℝ} (hH : Integrable H (pairMeasure μ ν p)) :
    Integrable (fun w => H (w.1, w.2 ∘ σ)) (pairMeasure μ ν p) :=
  (pair_permute_right_preserving σ).integrable_comp_of_integrable hH

theorem integrable_mixedLeft
    (hint : ∀ r i, Integrable (fun z : ℝ × ℝ => F r z.1 * (G i z.2 * K z.1 z.2)) (μ.prod ν)) :
    Integrable (fun w : (Fin p → ℝ) × (Fin p → ℝ) => mixedLeft F τ' G K w.1 w.2)
      (pairMeasure μ ν p) := by
  have hi := integrable_finsetSum (univ : Finset (Equiv.Perm (Fin p)))
    (fun σ _ => integrable_pair_permute_left σ (integrable_mixedRaw τ' hint))
  refine hi.congr (Filter.Eventually.of_forall fun w => ?_)
  exact sum_mixedRaw_perm F τ' G K w.1 w.2

theorem integral_mixedLeft
    (hint : ∀ r i, Integrable (fun z : ℝ × ℝ => F r z.1 * (G i z.2 * K z.1 z.2)) (μ.prod ν)) :
    ∫ w, mixedLeft F τ' G K w.1 w.2 ∂(pairMeasure μ ν p) =
      (p.factorial : ℝ) * (mixedMatrix μ ν F τ' G K).det := by
  calc ∫ w, mixedLeft F τ' G K w.1 w.2 ∂(pairMeasure μ ν p)
      = ∫ w, ∑ σ : Equiv.Perm (Fin p), mixedRaw F τ' G K (w.1 ∘ σ) w.2
          ∂(pairMeasure μ ν p) := by
        apply integral_congr_ae
        filter_upwards with w
        exact (sum_mixedRaw_perm F τ' G K w.1 w.2).symm
    _ = ∑ σ : Equiv.Perm (Fin p), ∫ w, mixedRaw F τ' G K (w.1 ∘ σ) w.2
          ∂(pairMeasure μ ν p) :=
        integral_finsetSum _ (fun σ _ =>
          integrable_pair_permute_left σ (integrable_mixedRaw τ' hint))
    _ = _ := by
        simp only [integral_pair_permute_left _ (fun w => mixedRaw F τ' G K w.1 w.2),
          integral_mixedRaw τ' hint, sum_const, card_univ, Fintype.card_perm,
          Fintype.card_fin, nsmul_eq_mul]

theorem integral_mixedDouble
    (hint : ∀ r i, Integrable (fun z : ℝ × ℝ => F r z.1 * (G i z.2 * K z.1 z.2)) (μ.prod ν)) :
    ∫ w, mixedDouble F τ' G K w.1 w.2 ∂(pairMeasure μ ν p) =
      (p.factorial : ℝ) ^ 2 * (mixedMatrix μ ν F τ' G K).det := by
  calc ∫ w, mixedDouble F τ' G K w.1 w.2 ∂(pairMeasure μ ν p)
      = ∫ w, ∑ π : Equiv.Perm (Fin p), mixedLeft F τ' G K w.1 (w.2 ∘ π)
          ∂(pairMeasure μ ν p) := by
        apply integral_congr_ae
        filter_upwards with w
        exact (sum_mixedLeft_perm F τ' G K w.1 w.2).symm
    _ = ∑ π : Equiv.Perm (Fin p), ∫ w, mixedLeft F τ' G K w.1 (w.2 ∘ π)
          ∂(pairMeasure μ ν p) :=
        integral_finsetSum _ (fun π _ =>
          integrable_pair_permute_right π (integrable_mixedLeft τ' hint))
    _ = _ := by
        simp only [integral_pair_permute_right _ (fun w => mixedLeft F τ' G K w.1 w.2),
          integral_mixedLeft τ' hint, sum_const, card_univ, Fintype.card_perm,
          Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Mixed Andreief bound.** -/
theorem abs_det_mixedMatrix_le
    (hint : ∀ r i, Integrable (fun z : ℝ × ℝ => F r z.1 * (G i z.2 * K z.1 z.2)) (μ.prod ν))
    {Bd : ℝ} (hBd : ∀ᵐ w ∂(pairMeasure μ ν p), |mixedDouble F τ' G K w.1 w.2| ≤ Bd) :
    |(mixedMatrix μ ν F τ' G K).det| ≤ Bd * (pairMeasure μ ν p).real Set.univ := by
  have h := integral_mixedDouble τ' hint
  have hf : (1 : ℝ) ≤ (p.factorial : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ p.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr p.factorial_ne_zero
    nlinarith
  have hb := norm_integral_le_of_norm_le_const (μ := pairMeasure μ ν p)
    (f := fun w => mixedDouble F τ' G K w.1 w.2) (C := Bd) (by simpa only [Real.norm_eq_abs] using hBd)
  rw [h, Real.norm_eq_abs, abs_mul] at hb
  have h0 : 0 ≤ |(mixedMatrix μ ν F τ' G K).det| := abs_nonneg _
  have hpos : |((p.factorial : ℝ) ^ 2)| = (p.factorial : ℝ) ^ 2 := abs_of_nonneg (by positivity)
  rw [hpos] at hb
  nlinarith

end Integral

end CatalanMeasure
