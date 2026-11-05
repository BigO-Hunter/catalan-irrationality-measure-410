module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_31 : ipNoRootCheck AZY (462:ℤ) (481:ℤ) (500:ℤ)=true := by
  certify_hom_gap
theorem gapY_31 : PieceNoRoot AY ((231 / 250 : ℚ),(481 / 500 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 462) (b := 481) (d := 500)
    (by norm_num) (by norm_num) checkY_31
end CatalanMeasure.GenD.D58.FirstCert
