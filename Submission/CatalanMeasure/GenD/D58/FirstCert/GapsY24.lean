module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_24 : ipNoRootCheck AZY (71949269:ℤ) (77039359:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_24 : PieceNoRoot AY ((71949269 / 100000000 : ℚ),(77039359 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 71949269) (b := 77039359) (d := 100000000)
    (by norm_num) (by norm_num) checkY_24
end CatalanMeasure.GenD.D58.FirstCert
