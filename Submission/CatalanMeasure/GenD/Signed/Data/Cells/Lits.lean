module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Core

/-! Literal readers of the cell lane.  `qlistC` and `mkPolesC` have the bodies of `Data.Trial.qlist` / `mkPolesQ`, so that the
`plogs` and `poles` text of a cell field is verbatim the text of the hid-side field literal (`Data/Trial/T{t}Fields.lean`). -/

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

def qlistC : List ℤ → List ℚ
  | n :: d :: r => ((n : ℚ) / (d : ℚ)) :: qlistC r
  | _ => []

def mkPolesC : List ℚ → List PoleR
  | a :: b :: c :: d :: r => ⟨a, b, c, d⟩ :: mkPolesC r
  | _ => []

end CatalanMeasure.GenD.Signed.Data.Cells
