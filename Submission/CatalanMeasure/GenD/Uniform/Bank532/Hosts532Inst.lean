module
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Final532
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts5.Phys
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0072_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0076_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0077_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0079_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0080_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0084_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0085_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0086_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0099_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0100_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0108_right
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0110_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0111_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0112_k268_65
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0113_k262_61
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0117_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0133_right
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0134_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0135_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0136_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0139_k89_16
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0140_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0145_k280_47
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0154_right
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0156_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0157_k71_10
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0162_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0163_k134_17
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0174_right
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0179_k89_8
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0180_left
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0192_k118_7
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Host_L0192_left
@[expose] public section
set_option Elab.async false

/-! The 34 packet hosts, from the verified checker `checkHost` (33 packets) and the pilot host (L0146):
    `Hosts532` and the unconditional `μ(G) ≤ 532`. -/

namespace CatalanMeasure.GenD.Uniform.Bank532
noncomputable section

theorem hosts532 : Hosts532 where
  h_L0072_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0072_left.phys
  h_L0076_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0076_left.phys
  h_L0077_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0077_left.phys
  h_L0079_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0079_left.phys
  h_L0080_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0080_left.phys
  h_L0084_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0084_left.phys
  h_L0085_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0085_left.phys
  h_L0086_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0086_left.phys
  h_L0099_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0099_left.phys
  h_L0100_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0100_left.phys
  h_L0108_right := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0108_right.phys
  h_L0110_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0110_left.phys
  h_L0111_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0111_left.phys
  h_L0112_k268_65 := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0112_k268_65.phys
  h_L0113_k262_61 := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0113_k262_61.phys
  h_L0117_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0117_left.phys
  h_L0133_right := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0133_right.phys
  h_L0134_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0134_left.phys
  h_L0135_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.phys
  h_L0136_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0136_left.phys
  h_L0139_k89_16 := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0139_k89_16.phys
  h_L0140_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0140_left.phys
  h_L0145_k280_47 := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0145_k280_47.phys
  h_L0146_k152_25 := CatalanMeasure.GenD.Uniform.W.Charts5.physHost_pilot
  h_L0154_right := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0154_right.phys
  h_L0156_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0156_left.phys
  h_L0157_k71_10 := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0157_k71_10.phys
  h_L0162_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0162_left.phys
  h_L0163_k134_17 := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0163_k134_17.phys
  h_L0174_right := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0174_right.phys
  h_L0179_k89_8 := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.phys
  h_L0180_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0180_left.phys
  h_L0192_k118_7 := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0192_k118_7.phys
  h_L0192_left := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0192_left.phys

/-- **`μ(G) ≤ 532`.** -/
theorem catalan_irrationalityMeasure_532 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(532 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  catalan_irrationalityMeasure_532_of_hosts hosts532

end
end CatalanMeasure.GenD.Uniform.Bank532

#print axioms CatalanMeasure.GenD.Uniform.Bank532.catalan_irrationalityMeasure_532
