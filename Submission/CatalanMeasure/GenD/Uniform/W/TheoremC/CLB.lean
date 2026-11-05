module
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.LB
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.Cell1
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.Cell2
@[expose] public section
set_option Elab.async false

/-!
# Theorem C: the nullity lower bound `cLB`

The pointwise maximum of the bounds of the two rational cells (windows `S = 22` and `S = 21`).
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open CatalanMeasure.GenD CatalanMeasure.Parametric
noncomputable section

theorem y1_ne : cell1.y cell1.ky ≠ 0 := by
  show y1 0 ≠ 0
  decide +kernel

theorem y2_ne : cell2.y cell2.ky ≠ 0 := by
  show y2 0 ≠ 0
  decide +kernel

/-- **Theorem C** as a nullity lower bound (design-generic). -/
def cLB (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.sup (cCellLB cell1 P hP) (cCellLB cell2 P hP)

theorem cLB_kap (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (cLB P hP).kap N p = max ((cCellLB cell1 P hP).kap N p) ((cCellLB cell2 P hP).kap N p) := rfl

end
end CatalanMeasure.GenD.Uniform.W.TheoremC
