module

public import Submission.CatalanMeasure.Parametric.SheetGroupedDeterminant

/-!
# Uniform interpolation on the actual population only

The monomial population does not enter the Blaschke weight condition.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Finset
open scoped BigOperators

noncomputable section

def groupedActualSheetMatrix {p q : ℕ} (x : Fin (p + q) → ℝ) (D : ℕ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.of fun i r => Sum.elim
    (fun a => (x (Fin.castAdd q a) : ℂ) ^ ((finSumFinEquiv r).rev : ℕ) +
      (if x (Fin.castAdd q a) < 0 then (x (Fin.castAdd q a) : ℂ) ^ D
        else -5 * (x (Fin.castAdd q a) : ℂ) ^ D) *
      (x (Fin.castAdd q a) : ℂ) ^ (finSumFinEquiv r : ℕ))
    (fun a => (x (Fin.natAdd p a) : ℂ) ^ (finSumFinEquiv r : ℕ)) i

theorem grouped_actual_sheet_det_bound {p q D : ℕ} (x : Fin (p + q) → ℝ)
    (hn : 48 ≤ p + q) (hDpos : 0 < D) (hDn : D ≤ p + q)
    (hx0 : ∀ i : Fin p, x (Fin.castAdd q i) ≠ 0)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x)
    (hweight : (∑ i : Fin p, blaschkeWeight (x (Fin.castAdd q i))) ≤ (D : ℝ)) :
    ‖(groupedActualSheetMatrix (p := p) (q := q) x D).det‖ ≤
      (1 + 10 * Real.exp 12 * ((p + q : ℕ) : ℝ)) ^ p *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (x (Fin.castAdd q j) - x (Fin.castAdd q i))| *
        |∏ i : Fin q, ∏ j ∈ Ioi i, (x (Fin.natAdd p j) - x (Fin.natAdd p i))| *
        crossCauchyProduct (fun i => x (Fin.castAdd q i)) (fun i => x (Fin.natAdd p i)) := by
  obtain ⟨h, hh, heval, hbound⟩ := real_uniform_interpolation_actual univ
    (fun i : Fin p => x (Fin.castAdd q i)) D (p + q) hn hDpos hDn
    (by simp) (fun i _ => hx0 i) (fun i _ => hx _) hweight
  have hm : groupedActualSheetMatrix x D = groupedSheetMatrix (p := p) (q := q) x h := by
    ext i r
    rcases i with i | i
    · simp only [groupedActualSheetMatrix, groupedSheetMatrix, Matrix.of_apply,
        Sum.elim_inl, heval i (mem_univ i)]
    · rfl
  rw [hm]
  exact grouped_sheet_det_bound x hx hxi h hh (by positivity) hbound

def groupedNearSheetMatrix {p q : ℕ} (x : Fin (p + q) → ℝ) (D : ℕ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.of fun i r => Sum.elim
    (fun a => groupedActualSheetMatrix (p := p) (q := q) x D (Sum.inl a) r)
    (fun a => (x (Fin.natAdd p a) : ℂ) ^ D *
      groupedActualSheetMatrix (p := p) (q := q) x D (Sum.inr a) r) i

theorem grouped_near_sheet_det_bound {p q D : ℕ} (x : Fin (p + q) → ℝ)
    (hn : 48 ≤ p + q) (hDpos : 0 < D) (hDn : D ≤ p + q)
    (hx0 : ∀ i : Fin p, x (Fin.castAdd q i) ≠ 0)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x)
    (hweight : (∑ i : Fin p, blaschkeWeight (x (Fin.castAdd q i))) ≤ (D : ℝ)) :
    ‖(groupedNearSheetMatrix (p := p) (q := q) x D).det‖ ≤
      (∏ i : Fin q, |x (Fin.natAdd p i)| ^ D) *
      ((1 + 10 * Real.exp 12 * ((p + q : ℕ) : ℝ)) ^ p *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (x (Fin.castAdd q j) - x (Fin.castAdd q i))| *
        |∏ i : Fin q, ∏ j ∈ Ioi i, (x (Fin.natAdd p j) - x (Fin.natAdd p i))| *
        crossCauchyProduct (fun i => x (Fin.castAdd q i)) (fun i => x (Fin.natAdd p i))) := by
  let w : Fin p ⊕ Fin q → ℂ := Sum.elim (fun _ => 1)
    (fun i => (x (Fin.natAdd p i) : ℂ) ^ D)
  have hm : groupedNearSheetMatrix (p := p) (q := q) x D =
      Matrix.of (fun i r => w i * groupedActualSheetMatrix (p := p) (q := q) x D i r) := by
    ext i r
    rcases i with i | i <;> simp [groupedNearSheetMatrix, w]
  rw [hm, Matrix.det_mul_column, norm_mul, norm_prod]
  have hw : ∏ i, ‖w i‖ = ∏ i : Fin q, |x (Fin.natAdd p i)| ^ D := by
    simp [w, Fintype.prod_sum_type, Complex.norm_real, Real.norm_eq_abs]
  rw [hw]
  exact mul_le_mul_of_nonneg_left (grouped_actual_sheet_det_bound x hn hDpos hDn hx0 hx hxi hweight)
    (prod_nonneg fun i _ => pow_nonneg (abs_nonneg _) _)

end

end CatalanMeasure.Parametric
