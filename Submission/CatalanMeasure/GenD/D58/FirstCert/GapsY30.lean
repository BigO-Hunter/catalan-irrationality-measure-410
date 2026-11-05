module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_30 : ipNoRootCheck AZY (10588237:ℤ) (11550000:ℤ) (12500000:ℤ)=true := by
  certify_hom_gap
theorem gapY_30 : PieceNoRoot AY ((10588237 / 12500000 : ℚ),(231 / 250 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 10588237) (b := 11550000) (d := 12500000)
    (by norm_num) (by norm_num) checkY_30
end CatalanMeasure.GenD.D58.FirstCert
