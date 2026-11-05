module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_13 : ipNoRootCheck AZX (0:ℤ) (3273197:ℤ) (25000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_13 : PieceNoRoot AX ((0 : ℚ),(3273197 / 25000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 0) (b := 3273197) (d := 25000000)
    (by norm_num) (by norm_num) checkX_13
end CatalanMeasure.GenD.D58.FirstCert
