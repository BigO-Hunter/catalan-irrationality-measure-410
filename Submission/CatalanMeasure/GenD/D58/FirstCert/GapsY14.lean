module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_14 : ipNoRootCheck AZY (43698868:ℤ) (47822999:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_14 : PieceNoRoot AY ((10924717 / 25000000 : ℚ),(47822999 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 43698868) (b := 47822999) (d := 100000000)
    (by norm_num) (by norm_num) checkY_14
end CatalanMeasure.GenD.D58.FirstCert
