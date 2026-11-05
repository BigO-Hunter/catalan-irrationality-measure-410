module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_2 : ipNoRootCheck AZY (3523889:ℤ) (7260202:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_2 : PieceNoRoot AY ((3523889 / 100000000 : ℚ),(3630101 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 3523889) (b := 7260202) (d := 100000000)
    (by norm_num) (by norm_num) checkY_2
end CatalanMeasure.GenD.D58.FirstCert
