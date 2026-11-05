module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_5 : ipNoRootCheck AZX (-389:ℤ) (-378:ℤ) (400:ℤ)=true := by
  certify_hom_gap
theorem gapX_5 : PieceNoRoot AX ((-389 / 400 : ℚ),(-189 / 200 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -389) (b := -378) (d := 400)
    (by norm_num) (by norm_num) checkX_5
end CatalanMeasure.GenD.D58.FirstCert
