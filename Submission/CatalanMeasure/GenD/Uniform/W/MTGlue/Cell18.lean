module
public import Submission.CatalanMeasure.GenD.Uniform.W.MTGlue.Transfer
public import Submission.CatalanMeasure.GenD.Uniform.W.MTGlue.Data18
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# MT (b) joint cell at `s = 18`: the equations over `ℚ`

Blocks `k0 = -1`, `K = 15`; main window `S = 18` on the digits `J ∈ [2, 16]`, overflow window `S = 19` on
`J ∈ [3, 17]`.  One declaration per window.
-/

namespace CatalanMeasure.GenD.Uniform.W.MTGlue
open CatalanMeasure.GenD.Uniform.W.ZoneZ

def y18 (k : ℕ) : ℤ := yz18.getD k 0
def u18 (k : ℕ) : ℤ := uz18.getD k 0
def A18 : ℤ := ab18.getD 0 0
def B18 : ℤ := ab18.getD 1 0

/-- Main window: `Φ-(J,18;y) = A` and `Φ+'(J,18;u) = B` for `J = 2..16`. -/
theorem cell18_main : ∀ J ∈ List.range' 2 15,
    Q.PhiQ (cmb y18 (-1) 15 y2uI) (cmb y18 (-1) 15 tI) J 18 = (A18 : ℚ) ∧
    Q.PhiQ (cmb u18 (-1) 15 xtI) (cmb u18 (-1) 15 xuI) J 18 = (B18 : ℚ) := by
  decide +kernel

/-- Overflow window: `Φ-(J,19;y) + Φ+'(J,19;u) = A + B` for `J = 3..17`. -/
theorem cell18_over : ∀ J ∈ List.range' 3 15,
    Q.PhiQ (cmb y18 (-1) 15 y2uI) (cmb y18 (-1) 15 tI) J 19 +
      Q.PhiQ (cmb u18 (-1) 15 xtI) (cmb u18 (-1) 15 xuI) J 19 = (A18 : ℚ) + (B18 : ℚ) := by
  decide +kernel

end CatalanMeasure.GenD.Uniform.W.MTGlue
end
