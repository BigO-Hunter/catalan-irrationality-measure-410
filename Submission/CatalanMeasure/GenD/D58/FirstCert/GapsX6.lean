module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_6 : ipNoRootCheck AZX (-945:ℤ) (-891:ℤ) (1000:ℤ)=true := by
  certify_hom_gap
theorem gapX_6 : PieceNoRoot AX ((-189 / 200 : ℚ),(-891 / 1000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -945) (b := -891) (d := 1000)
    (by norm_num) (by norm_num) checkX_6
end CatalanMeasure.GenD.D58.FirstCert
