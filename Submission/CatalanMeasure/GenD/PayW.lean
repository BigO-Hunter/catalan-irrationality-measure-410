module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Payment hypotheses of the window criterion (module 5, `Pay` with the window parameter `w`)

`PayW w d0 ρ η κ δ B` are the hypotheses of
`irrationality_measure_of_recycled_polynomials_window` (lower window end `V = (κ - w) L`):
`w = 1` is the original criterion (`κ > 2`), `w = 3/4` is used for the displaced design (`κ > 3/2`).
Here `η` is the total decay rate (the old `η + χ`).
-/

namespace CatalanMeasure.GenD

def PayW (w d0 ρ η κ δ B : ℝ) : Prop :=
  ρ * κ = B ∧ 0 < η ∧ 0 < ρ ∧ 0 < w ∧ 2 * w < κ ∧ 0 < δ ∧
    1 < 2 * (w - δ * (2 * κ - w)) ∧ η < 2 * d0 ∧ d0 + 4 * d0 * δ * κ < η * κ

end CatalanMeasure.GenD
