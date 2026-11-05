module
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.Cell
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.Data2
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Theorem C cell 2: the equations over `ℚ`

Window `S = 21`, digits `J ∈ [3, 18]`, blocks `k0 = -1`, `K = 16`.
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.MTGlue

def y2 (k : ℕ) : ℤ := yz2.getD k 0
def A2 : ℚ := (ab2.getD 0 0 : ℚ) / (ab2.getD 1 1 : ℚ)

theorem cell2_eq : ∀ J ∈ List.range' 3 16,
    Q.PhiQ (cmb y2 (-1) 16 y2uI) (cmb y2 (-1) 16 tI) J 20 -
      Q.PhiQ (cmb y2 (-1) 16 y2uI) (cmb y2 (-1) 16 tI) J 21 = A2 := by
  decide +kernel

def cell2 : CCell where
  S := 21
  Jlo := 3
  Jhi := 18
  K := 16
  k0 := -1
  y := y2
  A := A2
  ky := 0
  hS := by norm_num
  hJ := by norm_num
  hky := by norm_num
  heq := cell2_eq

end CatalanMeasure.GenD.Uniform.W.TheoremC
end
