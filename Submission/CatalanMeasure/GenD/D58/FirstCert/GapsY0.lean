module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_0 : ipNoRootCheck AZY (0:ℤ) (1761943:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_0 : PieceNoRoot AY ((0 : ℚ),(1761943 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 0) (b := 1761943) (d := 50000000)
    (by norm_num) (by norm_num) checkY_0
end CatalanMeasure.GenD.D58.FirstCert
