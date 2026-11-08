module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB012H1
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB009
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB010
@[expose] public section

/-! Block 12 of FR, alpha = 0.0: 1 cells. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

set_option maxRecDepth 100000
theorem q0frB012CrOK : absLeL (shiftLK 1 401 (q0frFq.poly.map qabs')) q0frB012Cr = true := by decide +kernel
theorem q0frB012PolyX : absLeL (shiftLKs q0frB012Cen 35 q0frFq.poly) q0frB012CbP = true := by decide +kernel
theorem q0frB012Poly : absLeL (shiftLK q0frB012Cen q0frB012CbP.length q0frFq.poly) q0frB012CbP = true :=
  polySplit_ok q0frB012Cen 35 401 q0frFq.poly q0frB012Cr q0frB012CbP (by decide +kernel) (by decide +kernel) (by decide) q0frB012CrOK (by decide +kernel) q0frB012PolyX (by decide +kernel)
theorem q0frB012Pls : plogBlkOK2 q0frB012Cen q0frB012Blo q0frB012Bhi q0frFq.plogs q0frB012Pb = true := plogBlkOK2_nil _ _ _
theorem q0frB012Block : blockOK4 q0frFq q0frB012Cen q0frB012Blo q0frB012Bhi 16 q0frB012CbP q0frB012Pb q0frB012Ks q0frB012BM = true := blockOK4_of_parts q0frB012Rest q0frB012Poly q0frB012Pls
theorem q0frB012Facts : BlockFacts q0frFq q0frB012Blo q0frB012Bhi 16 q0frB012BM := blockFacts_of_ok4 _ _ _ _ _ _ _ _ _ q0frB012Block

def q0frB012P0 : ℚ := q0frB012Blo
def q0frB012P1 : ℚ := q0frB012Bhi

def q0frB012Cc0 : ℚ := (Rat.mk' (-4722366377316260511747) 4722366482869645213696 : ℚ)
def q0frB012Ls0 : List ℚ := []
def q0frB012Es0 : List ℚ := []
def q0frB012A0_0 : ℚ := dy3 (-108272484582525879) 0 60
def q0frB012L1_0 : ℚ := dy3 (-12323947508473147) 0 47
def q0frB012U1_0 : ℚ := dy3 (-98591580067785175) 0 50
def q0frB012A2_0 : ℚ := dy3 (33954101879570604686274895) 0 50
def q0frB012Bl0 : List ℚ := [dy3 (8747065) 37 0, dy3 (4264167) 62 0, dy3 (14661005) 85 0, dy3 (13305377) 112 0, dy3 (740709) 142 0, dy3 (2144757) 166 0, dy3 (5594573) 190 0, dy3 (213409) 220 0, dy3 (7931237) 240 0, dy3 (2204019) 267 0, dy3 (9365213) 290 0, dy3 (4707411) 316 0, dy3 (8740785) 340 0]
theorem q0frB012C0 : cellW q0frFq 12 56 200 71891400098113236461629301009104090374057222401299051988491643427832 45915570820240004198797561829811544521249392461174062186496 2 467592103484435012864784871182523138767639716266458113361221406 116426194196013340132069552692147602407348072620924929572864 q0frB012Cc0 q0frB012Blo q0frB012Bhi q0frB012P0 q0frB012P1 q0frB012Ls0 q0frB012Es0 q0frB012A0_0 q0frB012L1_0 q0frB012U1_0 q0frB012A2_0 q0frB012Bl0 q0frB012BM q0frT = true := by decide +kernel
theorem q0frB012R0 : ∀ x ∈ Icc ((q0frB012P0 : ℚ) : ℝ) ((q0frB012P1 : ℚ) : ℝ), fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  cellW_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q0frB012C0 q0frB012Facts

theorem q0frB012Bound : ∀ x ∈ Icc ((q0frB012Blo : ℚ) : ℝ) ((q0frB012Bhi : ℚ) : ℝ), fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  q0frB012R0

end CatalanMeasure.GenD.Signed.Data.Cells
