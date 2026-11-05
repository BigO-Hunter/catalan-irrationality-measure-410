module

public import Submission.CatalanMeasure.Parametric.SheetGroupedBound

/-!
# A mixed-sheet determinant with regular cross-group factors

The first population uses the actual sheet operator, the second monomials.
The determinant retains the Vandermonde in each population separately.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Finset
open scoped BigOperators

noncomputable section

def groupedSheetMatrix {p q : ℕ} (x : Fin (p + q) → ℝ) (h : ℂ → ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.of fun i r => Sum.elim
    (fun a => (x (Fin.castAdd q a) : ℂ) ^ ((finSumFinEquiv r).rev : ℕ) +
      h (x (Fin.castAdd q a) : ℂ) * (x (Fin.castAdd q a) : ℂ) ^ (finSumFinEquiv r : ℕ))
    (fun a => (x (Fin.natAdd p a) : ℂ) ^ (finSumFinEquiv r : ℕ)) i

theorem cauchyNodeProduct_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (e : κ ≃ ι) : cauchyNodeProduct (x ∘ e) = cauchyNodeProduct x := by
  unfold cauchyNodeProduct
  apply Fintype.prod_equiv e
  intro i
  exact Fintype.prod_equiv e _ _ fun j => rfl

theorem grouped_sheet_normalization {p q : ℕ} (x : Fin (p + q) → ℝ)
    (hx : ∀ i, |x i| < 1) (h : ℂ → ℂ) :
    ‖(Matrix.of (fun (i r : Fin p ⊕ Fin q) => groupedSheetMatrix x h i r /
      firstSheetDenominator univ x (x (finSumFinEquiv i) : ℂ))).det‖ =
      ‖(groupedSheetMatrix x h).det‖ / cauchyNodeProduct x := by
  let d := fun i : Fin p ⊕ Fin q => ∏ j : Fin (p + q), (1 - x j * x (finSumFinEquiv i))
  have hd : ∀ i, 0 < d i := fun i => prod_pos fun j _ =>
    one_sub_node_mul_pos (hx j) (hx (finSumFinEquiv i))
  have hden : ∀ i, firstSheetDenominator univ x (x (finSumFinEquiv i) : ℂ) = (d i : ℂ) := by
    intro i
    simp only [firstSheetDenominator, d, Complex.ofReal_prod, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_mul]
  have hm : Matrix.of (fun (i r : Fin p ⊕ Fin q) => groupedSheetMatrix x h i r /
      firstSheetDenominator univ x (x (finSumFinEquiv i) : ℂ)) =
      Matrix.of (fun i r => ((d i : ℂ)⁻¹) * groupedSheetMatrix x h i r) := by
    ext i r
    simp only [Matrix.of_apply, hden, div_eq_mul_inv, mul_comm]
  have hp : ∏ i, d i = cauchyNodeProduct x := by
    dsimp only [d]
    calc
      _ = ∏ i : Fin (p + q), ∏ j : Fin (p + q), (1 - x j * x i) :=
        Fintype.prod_equiv finSumFinEquiv _ _ fun i => rfl
      _ = _ := Finset.prod_comm
  rw [hm, Matrix.det_mul_column, norm_mul, norm_prod]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hd _)]
  rw [prod_inv_distrib, hp]
  ring

theorem grouped_sheet_det_bound {p q : ℕ} (x : Fin (p + q) → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (Metric.closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖h z‖ ≤ K) :
    ‖(groupedSheetMatrix (p := p) (q := q) x h).det‖ ≤
      (1 + K) ^ p *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (x (Fin.castAdd q j) - x (Fin.castAdd q i))| *
        |∏ i : Fin q, ∏ j ∈ Ioi i, (x (Fin.natAdd p j) - x (Fin.natAdd p i))| *
        crossCauchyProduct (fun i => x (Fin.castAdd q i)) (fun i => x (Fin.natAdd p i)) := by
  let a := fun i : Fin p => x (Fin.castAdd q i)
  let b := fun i : Fin q => x (Fin.natAdd p i)
  have ha : ∀ i, |a i| < 1 := fun i => hx _
  have hb : ∀ i, |b i| < 1 := fun i => hx _
  have hc : cauchyNodeProduct (Sum.elim a b) = cauchyNodeProduct x := by
    have he : Sum.elim a b = x ∘ finSumFinEquiv := by
      funext i
      rcases i with i | i <;> rfl
    rw [he, cauchyNodeProduct_comp_equiv]
  have hv := cauchy_group_volume_identity a b ha hb
  rw [hc] at hv
  have ht := sheet_grouped_normalized_det_bound (p := p) (q := q) x hx hxi h hh hK hbound
  have hm : Matrix.of (fun (i r : Fin p ⊕ Fin q) =>
      Sum.elim
        (fun a => ((x (Fin.castAdd q a) : ℂ) ^ ((finSumFinEquiv r).rev : ℕ) +
          h (x (Fin.castAdd q a) : ℂ) * (x (Fin.castAdd q a) : ℂ) ^ (finSumFinEquiv r : ℕ)) /
          firstSheetDenominator univ x (x (Fin.castAdd q a) : ℂ))
        (fun a => (x (Fin.natAdd p a) : ℂ) ^ (finSumFinEquiv r : ℕ) /
          firstSheetDenominator univ x (x (Fin.natAdd p a) : ℂ)) i) =
      Matrix.of (fun (i r : Fin p ⊕ Fin q) => groupedSheetMatrix x h i r /
        firstSheetDenominator univ x (x (finSumFinEquiv i) : ℂ)) := by
    ext i r
    rcases i with i | i <;> rfl
  rw [hm, grouped_sheet_normalization x hx h] at ht
  have ht' := (div_le_iff₀ (cauchyNodeProduct_pos x hx)).mp ht
  calc
    _ ≤ _ := ht'
    _ = _ := by
      change (1 + K) ^ p * (_ / Real.sqrt (cauchyNodeProduct a)) *
        (_ / Real.sqrt (cauchyNodeProduct b)) * (1 / Real.sqrt (cauchyNodeProduct x)) *
        cauchyNodeProduct x = _
      rw [← hv]
      ring

end

end CatalanMeasure.Parametric
