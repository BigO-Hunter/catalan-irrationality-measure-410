module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZLB
@[expose] public section
set_option Elab.async false

/-!
# Window `s+1` (cap) cell facts for Law_H, exact over `ℚ`

`zq J c` is the `c`-th component of `z_J = (Φ+(J,5;u*) - Φ+(J,4;u*), Φ+(J,5;u2) - Φ+(J,4;u2),
Φ-(J,5;y1), Φ-(J,5;y2))`.  In the window-`s+1` zone the response is
`ψ+(J,4)(u*) fold(π1)[r'] + z_J . (π1, π2, λ1, λ2)[r']`, and `z_3 = (2/3) z_2`, `z_4 = (1/2) z_2`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ.Q
open OAI.InternalCatalan

/-- Components of `z_J` (`s = 4`, window `5` minus window `4`). -/
def zq (K : ℕ) (u u2 y1 y2 : ℕ → ℚ) (J : ℕ) : List ℚ :=
  [fTp K u J 5 - fTp K u J 4, fTp K u2 J 5 - fTp K u2 J 4, fTm K y1 J 5, fTm K y2 J 5]

theorem H_z3_rank : ∀ c ∈ [0, 1, 2, 3],
    (3 : ℚ) * (zq 4 uH u2H y1H y2H 3).getD c 0 = 2 * (zq 4 uH u2H y1H y2H 2).getD c 0 := by
  decide +kernel

theorem H_z4_rank : ∀ c ∈ [0, 1, 2, 3],
    (2 : ℚ) * (zq 4 uH u2H y1H y2H 4).getD c 0 = (zq 4 uH u2H y1H y2H 2).getD c 0 := by
  decide +kernel

end CatalanMeasure.GenD.Uniform.W.ZoneZ.Q
