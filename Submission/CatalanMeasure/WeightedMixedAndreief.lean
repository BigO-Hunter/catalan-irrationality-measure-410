module
public import Submission.CatalanMeasure.MixedAndreief
@[expose] public section
namespace CatalanMeasure
open MeasureTheory Finset
open scoped BigOperators
noncomputable section

theorem abs_det_mixedMatrix_mul_weight_le {p m : ℕ}
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (F : Fin (p+m) → ℝ → ℝ) (τ : Fin m → ℝ)
    (G : Fin p → ℝ → ℝ) (K : ℝ → ℝ → ℝ) {W Bd : ℝ} (hW : 0 ≤ W)
    (hint : ∀ r i,Integrable (fun z : ℝ×ℝ =>F r z.1*(G i z.2*K z.1 z.2)) (μ.prod ν))
    (hBd : ∀ᵐ w ∂pairMeasure μ ν p,|mixedDouble F τ G K w.1 w.2| * W ≤ Bd) :
    |(mixedMatrix μ ν F τ G K).det| * W ≤ Bd*(pairMeasure μ ν p).real Set.univ :=by
  have hh :=integral_mixedDouble τ hint
  have hf : (1:ℝ) ≤ (p.factorial:ℝ)^2 :=by
    have hp : (1:ℝ) ≤ p.factorial :=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr p.factorial_ne_zero
    nlinarith only [hp]
  have hb :=norm_integral_le_of_norm_le_const (μ :=pairMeasure μ ν p)
    (f :=fun w =>mixedDouble F τ G K w.1 w.2*W) (C :=Bd) (by
      filter_upwards [hBd] with w hw
      simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hW] using hw)
  rw [integral_mul_const,hh,Real.norm_eq_abs,abs_mul,abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (p.factorial:ℝ)^2),abs_of_nonneg hW] at hb
  have hp :=mul_nonneg (abs_nonneg ((mixedMatrix μ ν F τ G K).det)) hW
  nlinarith only [hb,mul_le_mul_of_nonneg_right hf hp]

end
end CatalanMeasure
