module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Foundations
public meta import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
public import Submission.CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_15 : ipNoRootCheck AZX (13092791:ℤ) (56500000:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_15 : PieceNoRoot AX ((13092791 / 100000000 : ℚ),(113 / 200 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 13092791) (b := 56500000) (d := 100000000)
    (by norm_num) (by norm_num) checkX_15
end CatalanMeasure.GenD.D58.FirstCert
