module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_17 : ipNoRootCheck AZX (391:ℤ) (500:ℤ) (500:ℤ)=true := by
  certify_hom_gap
theorem gapX_17 : PieceNoRoot AX ((391 / 500 : ℚ),(1 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 391) (b := 500) (d := 500)
    (by norm_num) (by norm_num) checkX_17
end CatalanMeasure.GenD.D58.FirstCert
