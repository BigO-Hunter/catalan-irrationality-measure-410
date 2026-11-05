module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_4 : ipNoRootCheck AZX (-9862:ℤ) (-9725:ℤ) (10000:ℤ)=true := by
  certify_hom_gap
theorem gapX_4 : PieceNoRoot AX ((-4931 / 5000 : ℚ),(-389 / 400 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -9862) (b := -9725) (d := 10000)
    (by norm_num) (by norm_num) checkX_4
end CatalanMeasure.GenD.D58.FirstCert
