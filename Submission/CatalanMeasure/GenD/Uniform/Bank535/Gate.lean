module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger5.Merge5

@[expose] public section
set_option Elab.async false

/-!
# Gates for `B = 539, 538, 537, 536, 535` (lane G6)

`measure_of_design` needs only `PayW` and `eta < tDelta - gDg g`.  For a target `B` the payment
threshold is `eta > d0 rho / B + 4 d0 delta`; here `eta` is a fixed rational just above it, and the
gain needed is `eta - 7.9877648`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535
open CatalanMeasure.GenD D58 Uniform.Bank540.Ledger
noncomputable section

/-- Decay budget: `eta <= g + 7.9877648` suffices. -/
theorem eta_lt_of_gain (eta g : ℝ) (h : eta ≤ g + 798775 / 100000) :
    eta < Bank540.tDelta - gDg g := by
  obtain ⟨hl, hh⟩ := D58.log2_bounds
  unfold Bank540.tDelta gDg
  norm_num [K590.target, D58.lo, D58.hi] at hl hh ⊢
  linarith

/-- Payment clauses at target `B` and decay rate `eta`. -/
def payB (B eta : ℝ) : Prop :=
  PayW (3 / 4) D58.d0 Bank540.rho eta (B / Bank540.rho) D58.delta B

theorem payB_of (B eta : ℝ) (hB : 460 ≤ B) (hB' : B ≤ 600) (he : 0 < eta) (he2 : eta < 106)
    (hmin : 53 * (301.54258 : ℝ) + 4 * 53 * (29 / 100000000 : ℝ) * B < eta * B) : payB B eta := by
  have hr : Bank540.rho = 301.54258 := by
    norm_num [Bank540.rho, K590.rho, K590.secondCost, D58.wcap, D58.t]
  have hd : D58.delta = 29 / 100000000 := by norm_num [D58.delta, D58.t, D58.deltaRef]
  have h0 : D58.d0 = 53 := rfl
  have hpos : (0 : ℝ) < 301.54258 := by norm_num
  unfold payB PayW
  rw [h0, hd]
  rw [hr]
  refine ⟨by field_simp, he, hpos, by norm_num, ?_, by norm_num, ?_, by linarith, ?_⟩
  · rw [lt_div_iff₀ hpos]; nlinarith
  · have : B / 301.54258 ≤ 600 / 301.54258 := by gcongr
    nlinarith
  · have hk : 0 < B / 301.54258 := by positivity
    have e : B / 301.54258 * 301.54258 = B := by field_simp
    nlinarith

theorem pay539 : payB 539 (2966 / 100) := payB_of _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem pay538 : payB 538 (2972 / 100) := payB_of _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem pay537 : payB 537 (2978 / 100) := payB_of _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem pay536 : payB 536 (2983 / 100) := payB_of _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem pay535 : payB 535 (2988 / 100) := payB_of _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Gains needed: `eta - 7.98775`: 539: 21.67225, 538: 21.73225, 537: 21.79225, 536: 21.84225, 535: 21.89225. -/
theorem gain_ok539 (g : ℝ) (h : 216723 / 10000 ≤ g) : (2966 / 100 : ℝ) < Bank540.tDelta - gDg g :=
  eta_lt_of_gain _ _ (by norm_num; linarith)

end
end CatalanMeasure.GenD.Uniform.Bank535
#print axioms CatalanMeasure.GenD.Uniform.Bank535.pay535
#print axioms CatalanMeasure.GenD.Uniform.Bank535.gain_ok539
