module
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.LBP
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.CellP1
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.CellP2
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.CellP3
@[expose] public section
set_option Elab.async false

/-!
# Theorem C': the nullity lower bound `cPrimeLB`

The pointwise maximum of the bounds of the three rational cells (windows `S = 31, 32, 33`).
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open CatalanMeasure.GenD CatalanMeasure.Parametric
noncomputable section

theorem yp1_ne : cellp1.y cellp1.ky ≠ 0 := by
  show yp1 0 ≠ 0
  decide +kernel

theorem yp2_ne : cellp2.y cellp2.ky ≠ 0 := by
  show yp2 0 ≠ 0
  decide +kernel

theorem yp3_ne : cellp3.y cellp3.ky ≠ 0 := by
  show yp3 0 ≠ 0
  decide +kernel

/-- **Theorem C'** as a nullity lower bound (design-generic). -/
def cPrimeLB (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.sup (cCellLBP cellp1 P hP) (NullityLB.sup (cCellLBP cellp2 P hP) (cCellLBP cellp3 P hP))

end
end CatalanMeasure.GenD.Uniform.W.TheoremC
