module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Decay.Budget540
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger.Instance

@[expose] public section
set_option Elab.async false

/-!
# The B = 540 gate, symbolic in the ledger gain (lane G5c)

`Decay.Budget540` fixes `gain = 21.68168`.  Here the gain is a parameter `g`:

* `gDg g = 24733/4 + (2673/8) log 2 - g` is the exponent produced by `Ledger.ledger_growth`
  (and by `partial_growth` for `g = partialGain`);
* `gate_ineq`  : `g >= 21.6083` implies `eta = 29.596 < tDelta - gDg g`;
* `gate_pay`   : the payment hypotheses `PayW` hold at `eta = 29.596` (independent of `g`);
* `gate`       : both, as an existential over `eta`;
* `gate_of_remaining` : with the partial ledger, any further families of total area
  `>= 1.5565` complete the gate.

The final instance only plugs in the total area of all windows (partial + MT, M, A-envelope,
Theorem Z); nothing else changes.  The hard floor is `g > 21.608143` (pay threshold
`eta > 29.595908`).
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.GenD D58
noncomputable section

/-- The exponent of the denominator growth for a ledger of total gain `g`. -/
def gDg (g : ℝ) : ℝ := 24733 / 4 + (2673 / 8) * Real.log 2 - g

/-- The chosen decay rate. -/
def etaG : ℝ := 29596 / 1000

theorem gD_eq : Bank540.gD = gDg (21 + 68168 / 100000) := by
  unfold Bank540.gD gDg Bank540.gain
  ring

theorem gate_ineq (g : ℝ) (hg : 216083 / 10000 ≤ g) : etaG < Bank540.tDelta - gDg g := by
  obtain ⟨hl, hh⟩ := D58.log2_bounds
  unfold etaG Bank540.tDelta gDg
  norm_num [K590.target, D58.lo, D58.hi] at hl hh ⊢
  linarith

theorem gate_pay : PayW (3 / 4) D58.d0 Bank540.rho etaG Bank540.kappa D58.delta Bank540.B := by
  unfold PayW Bank540.kappa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [Bank540.B, Bank540.rho, etaG, D58.d0, D58.delta, D58.t, D58.deltaRef,
      K590.rho, K590.secondCost, D58.wcap]

theorem gate (g : ℝ) (hg : 216083 / 10000 ≤ g) :
    PayW (3 / 4) D58.d0 Bank540.rho etaG Bank540.kappa D58.delta Bank540.B ∧
      etaG < Bank540.tDelta - gDg g :=
  ⟨gate_pay, gate_ineq g hg⟩

/-- Remaining area needed on top of the partial ledger. -/
theorem gate_of_remaining (extra : ℝ) (h : 15565 / 10000 ≤ extra) :
    PayW (3 / 4) D58.d0 Bank540.rho etaG Bank540.kappa D58.delta Bank540.B ∧
      etaG < Bank540.tDelta - gDg (partialGain + extra) := by
  refine gate (partialGain + extra) ?_
  have : (20 : ℝ) < partialGain := by unfold partialGain; norm_num
  have h2 : partialGain ≥ 200518 / 10000 := by unfold partialGain; norm_num
  linarith

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger
