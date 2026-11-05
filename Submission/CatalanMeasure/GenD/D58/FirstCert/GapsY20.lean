module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_20 : ipNoRootCheck AZY (60419121:ℤ) (67505542:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_20 : PieceNoRoot AY ((60419121 / 100000000 : ℚ),(33752771 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 60419121) (b := 67505542) (d := 100000000)
    (by norm_num) (by norm_num) checkY_20
end CatalanMeasure.GenD.D58.FirstCert
