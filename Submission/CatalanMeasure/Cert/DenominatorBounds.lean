module

public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierFinitePotentialDerivatives
public import Submission.OAI.NumberTheory.Catalan.Analysis.RealEnergyLogMajorants
public import Submission.OAI.NumberTheory.Catalan.Estimates.RealEnergyChebyshev

@[expose] public section

/-! OpenAI's two generic denominator bounds, isolated from the case-two
certificate. The proof bodies are copied unchanged from `Case2Height`. -/

open OAI.InternalCatalan Set
open scoped ComplexConjugate

namespace CatalanMeasure.Cert

theorem linear_den_norm_lower {x : ℝ} {z : ℂ} (hx : |x| ≤ 1) :
    1 - ‖z‖ ≤ ‖barrierTailLinearDen z x‖ := by
  have hm : ‖(x : ℂ) * z‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg z)
  change 1 - ‖z‖ ≤ ‖(1 : ℂ) - (x : ℂ) * z‖
  exact (sub_le_sub_left hm 1).trans
    (by simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) ((x : ℂ) * z))

theorem quadratic_den_norm_lower {x : ℝ} {z : ℂ} (hx : |x| ≤ 1)
    (hz : ‖z‖ ≤ 1) : (1 - ‖z‖) ^ 2 ≤ ‖barrierTailQuadraticDen z x‖ := by
  have hx' : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
  have hA : 1 - ‖z‖ ≤ ‖(1 : ℂ) - z * realEnergyCirclePoint x‖ := by
    simpa only [norm_one, norm_mul, realEnergyCirclePoint_norm hx', mul_one] using
      norm_sub_norm_le (1 : ℂ) (z * realEnergyCirclePoint x)
  have hB : 1 - ‖z‖ ≤ ‖(1 : ℂ) - z * conj (realEnergyCirclePoint x)‖ := by
    simpa only [norm_one, norm_mul, Complex.norm_conj,
      realEnergyCirclePoint_norm hx', mul_one] using
      norm_sub_norm_le (1 : ℂ) (z * conj (realEnergyCirclePoint x))
  have hfactor :
      ((1 : ℂ) - z * realEnergyCirclePoint x) *
        (1 - z * conj (realEnergyCirclePoint x)) = barrierTailQuadraticDen z x := by
    calc
      _ = 1 - z * (realEnergyCirclePoint x + conj (realEnergyCirclePoint x)) +
          z ^ 2 * (realEnergyCirclePoint x * conj (realEnergyCirclePoint x)) := by ring
      _ = _ := by
        rw [realEnergyCirclePoint_add_conj, realEnergyCirclePoint_mul_conj hx']
        unfold barrierTailQuadraticDen
        ring
  calc
    _ ≤ ‖(1 : ℂ) - z * realEnergyCirclePoint x‖ *
        ‖(1 : ℂ) - z * conj (realEnergyCirclePoint x)‖ := by
      simpa only [pow_two] using mul_le_mul hA hB (sub_nonneg.mpr hz) (norm_nonneg _)
    _ = _ := by rw [← norm_mul, hfactor]


end CatalanMeasure.Cert
