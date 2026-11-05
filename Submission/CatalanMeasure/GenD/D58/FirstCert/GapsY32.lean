module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_32 : ipNoRootCheck AZY (962:ℤ) (981:ℤ) (1000:ℤ)=true := by
  certify_hom_gap
theorem gapY_32 : PieceNoRoot AY ((481 / 500 : ℚ),(981 / 1000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 962) (b := 981) (d := 1000)
    (by norm_num) (by norm_num) checkY_32
end CatalanMeasure.GenD.D58.FirstCert
