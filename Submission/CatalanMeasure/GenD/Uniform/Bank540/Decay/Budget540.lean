module
public import Submission.CatalanMeasure.GenD.D58.Budget590
public import Submission.CatalanMeasure.GenD.PayW
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

/-! Scalar bank for the tier-1 target `B = 540` at D58. The trial pair, circle and
analytic rates are the certified K590 envelopes (the gi witness, requalified at the
corrected constraints `u₁ ≥ 9/50`, gap `401/2500`; gate `x = 538.699 < 540 - 1/3`).
Only the payment side changes: the denominator ledger must deliver content
`gain540 = 21.68168` (own units) and then `η = 29.66` fits under `tΔ - gD`. -/
namespace CatalanMeasure.GenD.Uniform.Bank540
open D58
noncomputable section

/-- Denominator-ledger content (saving, own units) required of the tier-1 ledger. -/
def gain : ℝ := 2168168 / 100000
def gD : ℝ := 24733 / 4 + (2673 / 8) * Real.log 2 - gain
def tDelta : ℝ := (K590.target - Real.log 2 / 2) * 58 ^ 2
def eta : ℝ := 1483 / 50
def rho : ℝ := K590.rho
def B : ℝ := 540
def kappa : ℝ := B / rho

theorem eta_lt : eta < tDelta - gD := by
  obtain ⟨hl, hh⟩ := D58.log2_bounds
  unfold eta tDelta gD gain
  norm_num [K590.target, D58.lo, D58.hi] at hl hh ⊢
  linarith

theorem pay : PayW (3 / 4) D58.d0 rho eta kappa D58.delta B := by
  unfold PayW kappa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [B, rho, eta, D58.d0, D58.delta, D58.t, D58.deltaRef,
      K590.rho, K590.secondCost, D58.wcap]

/-- The payment margin stays strictly positive. -/
theorem payment_margin :
    (1 / 20 : ℝ) < eta * kappa - D58.d0 - 4 * D58.d0 * D58.delta * kappa := by
  norm_num [B, rho, eta, kappa, D58.d0, D58.delta, D58.t, D58.deltaRef,
    K590.rho, K590.secondCost, D58.wcap]

end
end CatalanMeasure.GenD.Uniform.Bank540
#print axioms CatalanMeasure.GenD.Uniform.Bank540.pay
#print axioms CatalanMeasure.GenD.Uniform.Bank540.eta_lt
#print axioms CatalanMeasure.GenD.Uniform.Bank540.payment_margin
