module
public import Submission.CatalanMeasure.GenD.Uniform.W.MTGlue.Transfer
public import Submission.CatalanMeasure.GenD.Uniform.W.MTGlue.Data17
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# MT (b) joint cell at `s = 17`: the equations over `ℚ`

Blocks `k0 = -1`, `K = 14`; main window `S = 17` on the digits `J ∈ [2, 15]`, overflow window `S = 18` on
`J ∈ [3, 16]`.  One declaration per window.
-/

namespace CatalanMeasure.GenD.Uniform.W.MTGlue
open CatalanMeasure.GenD.Uniform.W.ZoneZ

def y17 (k : ℕ) : ℤ := yz17.getD k 0
def u17 (k : ℕ) : ℤ := uz17.getD k 0
def A17 : ℤ := ab17.getD 0 0
def B17 : ℤ := ab17.getD 1 0

/-- Main window: `Φ-(J,17;y) = A` and `Φ+'(J,17;u) = B` for `J = 2..15`. -/
theorem cell17_main : ∀ J ∈ List.range' 2 14,
    Q.PhiQ (cmb y17 (-1) 14 y2uI) (cmb y17 (-1) 14 tI) J 17 = (A17 : ℚ) ∧
    Q.PhiQ (cmb u17 (-1) 14 xtI) (cmb u17 (-1) 14 xuI) J 17 = (B17 : ℚ) := by
  decide +kernel

/-- Overflow window: `Φ-(J,18;y) + Φ+'(J,18;u) = A + B` for `J = 3..16`. -/
theorem cell17_over : ∀ J ∈ List.range' 3 14,
    Q.PhiQ (cmb y17 (-1) 14 y2uI) (cmb y17 (-1) 14 tI) J 18 +
      Q.PhiQ (cmb u17 (-1) 14 xtI) (cmb u17 (-1) 14 xuI) J 18 = (A17 : ℚ) + (B17 : ℚ) := by
  decide +kernel

end CatalanMeasure.GenD.Uniform.W.MTGlue
end
