module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_22 : ipNoRootCheck AZY (67505545:ℤ) (71949266:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_22 : PieceNoRoot AY ((13501109 / 20000000 : ℚ),(35974633 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 67505545) (b := 71949266) (d := 100000000)
    (by norm_num) (by norm_num) checkY_22
end CatalanMeasure.GenD.D58.FirstCert
