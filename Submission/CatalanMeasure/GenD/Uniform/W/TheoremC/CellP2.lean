module
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.CellP
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.DataP2
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Theorem C' cell P2: the equations over `ℚ`

Window `S = 32`, digits `J ∈ [4, 28]`, blocks `k0 = -2`, `K = 25`.
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.MTGlue

def yp2 (k : ℕ) : ℤ := yzp2.getD k 0
def Ap2 : ℚ := (abp2.getD 0 0 : ℚ) / (abp2.getD 1 1 : ℚ)

theorem cellp2_eq : ∀ J ∈ List.range' 4 25,
    Q.PhiQ (cmb yp2 (-2) 25 y2uI) (cmb yp2 (-2) 25 tI) J 31 -
      Q.PhiQ (cmb yp2 (-2) 25 y2uI) (cmb yp2 (-2) 25 tI) J 32 = Ap2 := by
  decide +kernel

def cellp2 : CCell2 where
  S := 32
  Jlo := 4
  Jhi := 28
  K := 25
  k0 := -2
  y := yp2
  A := Ap2
  ky := 0
  hS := by norm_num
  hJ := by norm_num
  hky := by norm_num
  heq := cellp2_eq

end CatalanMeasure.GenD.Uniform.W.TheoremC
end
