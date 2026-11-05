module
public import Submission.CatalanMeasure.GenD.D58.Budget590
public import Submission.CatalanMeasure.GenD.PayW
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

/-! A scalar bank qualification. The denominator rate below is an explicit
candidate ledger; its growth theorem is supplied by the separate rank/prefix lane.
The trial target and costs are unchanged certified K590 analytic envelopes. -/
namespace CatalanMeasure.GenD.Uniform.Bank532
open D58
noncomputable section

def gain : ℝ := 534121468871212736197 / 24183176360959455840
def gD : ℝ := 24733 / 4 + (2673 / 8) * Real.log 2 - gain
def tDelta : ℝ := (K590.target - Real.log 2 / 2) * 58 ^ 2
def eta : ℝ := 3007 / 100
def rho : ℝ := K590.rho
def B : ℝ := 532
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

/-- Rounded bank margin remains strictly positive. -/
theorem payment_margin :
    (1 / 20 : ℝ) < eta * kappa - D58.d0 - 4 * D58.d0 * D58.delta * kappa := by
  norm_num [B, rho, eta, kappa, D58.d0, D58.delta, D58.t, D58.deltaRef,
    K590.rho, K590.secondCost, D58.wcap]

end
end CatalanMeasure.GenD.Uniform.Bank532
#print axioms CatalanMeasure.GenD.Uniform.Bank532.pay
#print axioms CatalanMeasure.GenD.Uniform.Bank532.eta_lt
