module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_4 : ipNoRootCheck AZY (7260205:ℤ) (16065963:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_4 : PieceNoRoot AY ((1452041 / 20000000 : ℚ),(16065963 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 7260205) (b := 16065963) (d := 100000000)
    (by norm_num) (by norm_num) checkY_4
end CatalanMeasure.GenD.D58.FirstCert
