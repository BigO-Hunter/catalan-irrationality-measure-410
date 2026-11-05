module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# D2 constants: a rational upper bound for `log` below `1`

`log y <= 2 (y - 1) / (y + 1)` for `0 < y <= 1` (monotonicity of `log y - 2 (y-1)/(y+1)`).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set

theorem hasDerivAt_pade {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.log t - 2 * (t - 1) / (t + 1)) (1 / x - 4 / (x + 1) ^ 2) x := by
  have h1 : HasDerivAt (fun t : ℝ => Real.log t) (x⁻¹) x := Real.hasDerivAt_log hx.ne'
  have h2 : HasDerivAt (fun t : ℝ => 2 * (t - 1)) 2 x := by
    simpa using ((hasDerivAt_id x).sub_const 1).const_mul 2
  have h3 : HasDerivAt (fun t : ℝ => t + 1) 1 x := (hasDerivAt_id x).add_const 1
  have hne : x + 1 ≠ 0 := by positivity
  have h4 := h2.div h3 hne
  have h5 := h1.sub h4
  convert h5 using 1
  field_simp
  ring

theorem log_le_pade {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    Real.log y ≤ 2 * (y - 1) / (y + 1) := by
  set f : ℝ → ℝ := fun t => Real.log t - 2 * (t - 1) / (t + 1) with hf
  have hderiv : ∀ x ∈ interior (Ioi (0 : ℝ)), HasDerivAt f (1 / x - 4 / (x + 1) ^ 2) x := by
    intro x hx
    rw [interior_Ioi] at hx
    exact hasDerivAt_pade hx
  have hmono : MonotoneOn f (Ioi (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · intro x hx; exact (hasDerivAt_pade hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hderiv x hx).deriv]
      rw [interior_Ioi] at hx
      have hx0 : 0 < x := hx
      have : 1 / x - 4 / (x + 1) ^ 2 = (x - 1) ^ 2 / (x * (x + 1) ^ 2) := by
        field_simp; ring
      rw [this]; positivity
  have h := hmono (show (y : ℝ) ∈ Ioi 0 from hy) (show (1 : ℝ) ∈ Ioi 0 from one_pos) hy1
  simp only [hf, Real.log_one] at h
  norm_num at h
  linarith

end CatalanMeasure.Signed.Consts
