module
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.CellP
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.DataP3
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Theorem C' cell P3: the equations over `ℚ`

Window `S = 33`, digits `J ∈ [4, 29]`, blocks `k0 = -2`, `K = 26`.
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.MTGlue

def yp3 (k : ℕ) : ℤ := yzp3.getD k 0
def Ap3 : ℚ := (abp3.getD 0 0 : ℚ) / (abp3.getD 1 1 : ℚ)

theorem cellp3_eq : ∀ J ∈ List.range' 4 26,
    Q.PhiQ (cmb yp3 (-2) 26 y2uI) (cmb yp3 (-2) 26 tI) J 32 -
      Q.PhiQ (cmb yp3 (-2) 26 y2uI) (cmb yp3 (-2) 26 tI) J 33 = Ap3 := by
  decide +kernel

def cellp3 : CCell2 where
  S := 33
  Jlo := 4
  Jhi := 29
  K := 26
  k0 := -2
  y := yp3
  A := Ap3
  ky := 0
  hS := by norm_num
  hJ := by norm_num
  hky := by norm_num
  heq := cellp3_eq

end CatalanMeasure.GenD.Uniform.W.TheoremC
end
