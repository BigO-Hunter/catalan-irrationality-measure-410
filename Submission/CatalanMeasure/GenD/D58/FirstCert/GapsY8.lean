module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_8 : ipNoRootCheck AZY (10361309:ℤ) (15035283:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_8 : PieceNoRoot AY ((10361309 / 50000000 : ℚ),(15035283 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 10361309) (b := 15035283) (d := 50000000)
    (by norm_num) (by norm_num) checkY_8
end CatalanMeasure.GenD.D58.FirstCert
