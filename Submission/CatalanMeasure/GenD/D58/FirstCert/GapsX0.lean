module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_0 : ipNoRootCheck AZX (-50000000:ℤ) (-49999441:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_0 : PieceNoRoot AX ((-1 : ℚ),(-49999441 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -50000000) (b := -49999441) (d := 50000000)
    (by norm_num) (by norm_num) checkX_0
end CatalanMeasure.GenD.D58.FirstCert
