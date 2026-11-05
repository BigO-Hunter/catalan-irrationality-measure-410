module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Gate

@[expose] public section
set_option Elab.async false

/-!
# Gates for `B = 534, 533, 532` (lane G10)

Same pattern as `Bank535/Gate`: `measure_of_design` needs `PayW` and `eta < tDelta - gDg g`.
The payment threshold is `eta > d0 rho / B + 4 d0 delta`; `eta` is a fixed rational just above it
and the gain needed is `eta - 7.98775`:

* `B = 534`: `eta = 29.93`, gain `>= 21.94225`;
* `B = 533`: `eta = 29.99`, gain `>= 22.00225`;
* `B = 532`: `eta = 30.041`, gain `>= 22.05325`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank532
open CatalanMeasure.GenD D58 Uniform.Bank540.Ledger Uniform.Bank535
noncomputable section

theorem pay534 : payB 534 (2993 / 100) :=
  payB_of _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem pay533 : payB 533 (2999 / 100) :=
  payB_of _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem pay532 : payB 532 (30041 / 1000) :=
  payB_of _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem gain_ok534 (g : ℝ) (h : 2194225 / 100000 ≤ g) : (2993 / 100 : ℝ) < Bank540.tDelta - gDg g :=
  eta_lt_of_gain _ _ (by norm_num; linarith)
theorem gain_ok533 (g : ℝ) (h : 2200225 / 100000 ≤ g) : (2999 / 100 : ℝ) < Bank540.tDelta - gDg g :=
  eta_lt_of_gain _ _ (by norm_num; linarith)
theorem gain_ok532 (g : ℝ) (h : 2205325 / 100000 ≤ g) : (30041 / 1000 : ℝ) < Bank540.tDelta - gDg g :=
  eta_lt_of_gain _ _ (by norm_num; linarith)

end
end CatalanMeasure.GenD.Uniform.Bank532
#print axioms CatalanMeasure.GenD.Uniform.Bank532.pay532
#print axioms CatalanMeasure.GenD.Uniform.Bank532.gain_ok532
#print axioms CatalanMeasure.GenD.Uniform.Bank532.pay533
#print axioms CatalanMeasure.GenD.Uniform.Bank532.gain_ok533
#print axioms CatalanMeasure.GenD.Uniform.Bank532.pay534
#print axioms CatalanMeasure.GenD.Uniform.Bank532.gain_ok534
