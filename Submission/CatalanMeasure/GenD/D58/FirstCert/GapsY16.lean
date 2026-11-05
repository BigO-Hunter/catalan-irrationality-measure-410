module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_16 : ipNoRootCheck AZY (47823002:ℤ) (56312519:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_16 : PieceNoRoot AY ((23911501 / 50000000 : ℚ),(56312519 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 47823002) (b := 56312519) (d := 100000000)
    (by norm_num) (by norm_num) checkY_16
end CatalanMeasure.GenD.D58.FirstCert
