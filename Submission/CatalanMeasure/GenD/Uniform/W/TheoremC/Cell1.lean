module
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.Cell
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.Data1
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Theorem C cell 1: the equations over `ℚ`

Window `S = 22`, digits `J ∈ [3, 19]`, blocks `k0 = -1`, `K = 17`.
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.MTGlue

def y1 (k : ℕ) : ℤ := yz1.getD k 0
def A1 : ℚ := (ab1.getD 0 0 : ℚ) / (ab1.getD 1 1 : ℚ)

theorem cell1_eq : ∀ J ∈ List.range' 3 17,
    Q.PhiQ (cmb y1 (-1) 17 y2uI) (cmb y1 (-1) 17 tI) J 21 -
      Q.PhiQ (cmb y1 (-1) 17 y2uI) (cmb y1 (-1) 17 tI) J 22 = A1 := by
  decide +kernel

def cell1 : CCell where
  S := 22
  Jlo := 3
  Jhi := 19
  K := 17
  k0 := -1
  y := y1
  A := A1
  ky := 0
  hS := by norm_num
  hJ := by norm_num
  hky := by norm_num
  heq := cell1_eq

end CatalanMeasure.GenD.Uniform.W.TheoremC
end
