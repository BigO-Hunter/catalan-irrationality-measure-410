module
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.CellP
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.DataP1
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Theorem C' cell P1: the equations over `ℚ`

Window `S = 31`, digits `J ∈ [4, 27]`, blocks `k0 = -2`, `K = 24`.
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.MTGlue

def yp1 (k : ℕ) : ℤ := yzp1.getD k 0
def Ap1 : ℚ := (abp1.getD 0 0 : ℚ) / (abp1.getD 1 1 : ℚ)

theorem cellp1_eq : ∀ J ∈ List.range' 4 24,
    Q.PhiQ (cmb yp1 (-2) 24 y2uI) (cmb yp1 (-2) 24 tI) J 30 -
      Q.PhiQ (cmb yp1 (-2) 24 y2uI) (cmb yp1 (-2) 24 tI) J 31 = Ap1 := by
  decide +kernel

def cellp1 : CCell2 where
  S := 31
  Jlo := 4
  Jhi := 27
  K := 24
  k0 := -2
  y := yp1
  A := Ap1
  ky := 0
  hS := by norm_num
  hJ := by norm_num
  hky := by norm_num
  heq := cellp1_eq

end CatalanMeasure.GenD.Uniform.W.TheoremC
end
