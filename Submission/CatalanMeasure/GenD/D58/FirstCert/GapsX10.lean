module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_10 : ipNoRootCheck AZX (-17450000:ℤ) (-6605091:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_10 : PieceNoRoot AX ((-349 / 1000 : ℚ),(-6605091 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -17450000) (b := -6605091) (d := 50000000)
    (by norm_num) (by norm_num) checkX_10
end CatalanMeasure.GenD.D58.FirstCert
