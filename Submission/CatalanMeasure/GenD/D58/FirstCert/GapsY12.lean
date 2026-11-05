module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_12 : ipNoRootCheck AZY (6895836:ℤ) (8739773:ℤ) (20000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_12 : PieceNoRoot AY ((1723959 / 5000000 : ℚ),(8739773 / 20000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 6895836) (b := 8739773) (d := 20000000)
    (by norm_num) (by norm_num) checkY_12
end CatalanMeasure.GenD.D58.FirstCert
