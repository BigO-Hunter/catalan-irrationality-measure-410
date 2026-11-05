module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_18 : ipNoRootCheck AZY (28156261:ℤ) (30209559:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_18 : PieceNoRoot AY ((28156261 / 50000000 : ℚ),(30209559 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 28156261) (b := 30209559) (d := 50000000)
    (by norm_num) (by norm_num) checkY_18
end CatalanMeasure.GenD.D58.FirstCert
