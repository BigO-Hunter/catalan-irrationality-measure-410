module

public import Submission.CatalanMeasure.Parametric.SheetGroupedInterpolation
public import Submission.CatalanMeasure.Parametric.PositiveResidual

/-!
# Actual and near Laurent sheets

Extract the common far monomial from an actual/near population before applying
the grouped interpolation determinant estimate. No cross-population Vandermonde
is asserted.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Finset
open scoped BigOperators

noncomputable section

def actualLaurentEntry (g r : ℕ) (x : ℝ) : ℝ :=
  if x < 0 then
    (1 / 2 : ℝ) * x ^ ((g : ℤ) - r) + (1 / 2 : ℝ) * x ^ ((r : ℤ) - g)
  else
    -(1 / 4 : ℝ) * x ^ ((g : ℤ) - r) + (5 / 4 : ℝ) * x ^ ((r : ℤ) - g)

theorem far_laurent_factor {n g : ℕ} (r : Fin n) {x : ℝ} (hx : x ≠ 0) :
    x ^ ((g : ℤ) - (n - 1 : ℕ)) * x ^ (r.rev : ℕ) = x ^ ((g : ℤ) - r) := by
  rw [← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  have hr := r.isLt
  simp only [Fin.val_rev]
  omega

theorem actual_laurent_factor {n g : ℕ} (hng : 2 * g < n) (r : Fin n)
    {x : ℝ} (hx : x ≠ 0) :
    actualLaurentEntry g r x =
      (if x < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
        x ^ ((g : ℤ) - (n - 1 : ℕ)) *
          (x ^ (r.rev : ℕ) +
            (if x < 0 then x ^ (n - 1 - 2 * g) else -5 * x ^ (n - 1 - 2 * g)) *
              x ^ (r : ℕ)) := by
  have hnear : x ^ ((g : ℤ) - (n - 1 : ℕ)) *
      (x ^ (n - 1 - 2 * g) * x ^ (r : ℕ)) = x ^ ((r : ℤ) - g) := by
    rw [← pow_add]
    exact (near_sheet_factorization hng hx).symm
  by_cases hneg : x < 0
  · simp only [actualLaurentEntry, if_pos hneg]
    rw [← far_laurent_factor r hx, ← hnear]
    ring
  · simp only [actualLaurentEntry, if_neg hneg]
    rw [← far_laurent_factor r hx, ← hnear]
    ring

def groupedLaurentMatrix {p q : ℕ} (x : Fin (p + q) → ℝ) (g : ℕ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  Matrix.of fun i r => Sum.elim
    (fun a => actualLaurentEntry g (finSumFinEquiv r) (x (Fin.castAdd q a)))
    (fun a => x (Fin.natAdd p a) ^ (((finSumFinEquiv r : Fin (p + q)) : ℤ) - g)) i

def groupedLaurentWeight {p q : ℕ} (x : Fin (p + q) → ℝ) (g : ℕ) :
    Fin p ⊕ Fin q → ℝ :=
  Sum.elim
    (fun a => (if x (Fin.castAdd q a) < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
      x (Fin.castAdd q a) ^ ((g : ℤ) - (p + q - 1 : ℕ)))
    (fun a => x (Fin.natAdd p a) ^ ((g : ℤ) - (p + q - 1 : ℕ)))

theorem grouped_laurent_matrix_factor {p q g : ℕ} (x : Fin (p + q) → ℝ)
    (hng : 2 * g < p + q) (hx0 : ∀ i, x i ≠ 0) :
    (groupedLaurentMatrix (p := p) (q := q) x g).map Complex.ofReal =
      Matrix.of (fun i r => (groupedLaurentWeight x g i : ℂ) *
        groupedNearSheetMatrix (p := p) (q := q) x (p + q - 1 - 2 * g) i r) := by
  ext i r
  rcases i with i | i
  · simp only [Matrix.map_apply, groupedLaurentMatrix, Matrix.of_apply, Sum.elim_inl]
    rw [actual_laurent_factor hng (finSumFinEquiv r) (hx0 _)]
    simp only [groupedLaurentWeight, Sum.elim_inl, groupedNearSheetMatrix,
      groupedActualSheetMatrix, Matrix.of_apply, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_pow]
    split_ifs <;> push_cast <;> ring
  · simp only [Matrix.map_apply, groupedLaurentMatrix, Matrix.of_apply, Sum.elim_inr]
    rw [near_sheet_factorization hng (hx0 _), pow_add]
    simp only [groupedLaurentWeight, Sum.elim_inr, groupedNearSheetMatrix,
      groupedActualSheetMatrix, Matrix.of_apply, Complex.ofReal_mul,
      Complex.ofReal_pow]

theorem grouped_laurent_weight_bound {p q g : ℕ} (x : Fin (p + q) → ℝ) :
    ∏ i, |groupedLaurentWeight (p := p) (q := q) x g i| ≤
      ∏ i : Fin (p + q), |x i| ^ ((g : ℤ) - (p + q - 1 : ℕ)) := by
  have he : ∏ i : Fin p ⊕ Fin q,
      |x (finSumFinEquiv i)| ^ ((g : ℤ) - (p + q - 1 : ℕ)) =
        ∏ i : Fin (p + q), |x i| ^ ((g : ℤ) - (p + q - 1 : ℕ)) :=
    Fintype.prod_equiv finSumFinEquiv _ _ fun _ => rfl
  rw [← he]
  apply prod_le_prod₀
  · intro i _
    exact abs_nonneg _
  · intro i _
    rcases i with i | i
    · simp only [groupedLaurentWeight, Sum.elim_inl, abs_mul, abs_zpow]
      exact (mul_le_mul_of_nonneg_right (realFirstSheet_far_coefficient_abs_le _)
        (zpow_nonneg (abs_nonneg _) _)).trans_eq (one_mul _)
    · simp only [groupedLaurentWeight, Sum.elim_inr, abs_zpow]
      exact le_rfl

theorem grouped_laurent_det_bound {p q g : ℕ} (x : Fin (p + q) → ℝ)
    (hn : 48 ≤ p + q) (hng : 2 * g + 1 < p + q)
    (hx0 : ∀ i, x i ≠ 0) (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x)
    (hweight : (∑ i : Fin p, blaschkeWeight (x (Fin.castAdd q i))) ≤
      ((p + q - 1 - 2 * g : ℕ) : ℝ)) :
    |(groupedLaurentMatrix (p := p) (q := q) x g).det| ≤
      (∏ i : Fin (p + q), |x i| ^ ((g : ℤ) - (p + q - 1 : ℕ))) *
      ((∏ i : Fin q, |x (Fin.natAdd p i)| ^ (p + q - 1 - 2 * g)) *
        ((1 + 10 * Real.exp 12 * ((p + q : ℕ) : ℝ)) ^ p *
          |∏ i : Fin p, ∏ j ∈ Ioi i, (x (Fin.castAdd q j) - x (Fin.castAdd q i))| *
          |∏ i : Fin q, ∏ j ∈ Ioi i, (x (Fin.natAdd p j) - x (Fin.natAdd p i))| *
          crossCauchyProduct (fun i => x (Fin.castAdd q i))
            (fun i => x (Fin.natAdd p i)))) := by
  have hfactor : ‖((groupedLaurentMatrix (p := p) (q := q) x g).map Complex.ofReal).det‖ =
      (∏ i, |groupedLaurentWeight (p := p) (q := q) x g i|) *
        ‖(groupedNearSheetMatrix (p := p) (q := q) x (p + q - 1 - 2 * g)).det‖ := by
    rw [grouped_laurent_matrix_factor x (by omega) hx0, Matrix.det_mul_column,
      norm_mul, norm_prod]
    simp only [Complex.norm_real, Real.norm_eq_abs]
  have hreal : ‖((groupedLaurentMatrix (p := p) (q := q) x g).map Complex.ofReal).det‖ =
      |(groupedLaurentMatrix (p := p) (q := q) x g).det| := by
    calc
      _ = ‖((groupedLaurentMatrix (p := p) (q := q) x g).det : ℂ)‖ :=
        congrArg norm (Complex.ofRealHom.map_det _).symm
      _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hreal] at hfactor
  rw [hfactor]
  exact mul_le_mul (grouped_laurent_weight_bound x)
    (grouped_near_sheet_det_bound x hn (by omega) (by omega)
      (fun i => hx0 _) hx hxi hweight) (norm_nonneg _)
      (prod_nonneg fun i _ => zpow_nonneg (abs_nonneg _) _)

end

end CatalanMeasure.Parametric
