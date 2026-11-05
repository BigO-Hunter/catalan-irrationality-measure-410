module

public import Submission.CatalanMeasure.GenD.D58.FirstTrial
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Data

@[expose] public section

/-!
# D58 first trial: the certificate fields are the generic scale-free fields

`FirstCert.R` / `FirstCert.C` fields (`shiftedRowField`, `shiftedColumnField`) coincide with
`firstRowFieldG (11/29) (3/29) (49/58) lamFirst (5/29) firstP firstV` and `colFieldG (9/58) (3/58) firstV`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Set OAI.InternalCatalan CatalanMeasure.Cert CatalanMeasure.CellCert
open CatalanMeasure.GenD.Analytic
noncomputable section

theorem barrierTrialT_two_mul (u : ℕ → ℝ) (x : ℝ) :
    barrierTrialT (fun j => 2 * u j) x = 2 * barrierTrialT u x := by
  unfold barrierTrialT
  rw [← tsum_mul_left]
  congr 1
  funext j
  ring

theorem firstRowFieldG_D58_eq (x : ℝ) :
    firstRowFieldG (11 / 29) (3 / 29) (49 / 58) lamFirst (5 / 29) firstP firstV x =
      shiftedRowField FirstCert.R FirstCert.Pc FirstCert.Vc FirstCert.P FirstCert.V x := by
  have hT : barrierTrialT firstP x = 2 * barrierTrialT (trialSeq FirstCert.Pc FirstCert.P) x :=
    barrierTrialT_two_mul _ x
  unfold firstRowFieldG firstRowReg shiftedRowField realEnergyRowTrialField realEnergyField
    realEnergyCaseField
  rw [hT]
  have e : (((168493357 / 100000000 : ℚ)) : ℝ) = lamFirst := by norm_num [lamFirst]
  simp only [FirstCert.R, FirstCert.Vc, FirstCert.Pc, FirstCert.P, FirstCert.V, firstV, e]
  push_cast
  ring

theorem colFieldG_D58_eq (s : ℝ) :
    colFieldG (9 / 58) (3 / 58) firstV s =
      shiftedColumnField FirstCert.C FirstCert.Vc FirstCert.V s := by
  unfold colFieldG colRegG shiftedColumnField realEnergyColumnTrialField realEnergyColumnField
  simp only [FirstCert.C, FirstCert.Vc, FirstCert.V, firstV]
  push_cast
  ring

end
end D58
end CatalanMeasure.GenD
