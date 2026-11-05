module
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Decay.Budget540
public import Submission.CatalanMeasure.GenD.Uniform.Bank.TrialFields
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

/-! D58 decay providers for the tier-1 bank `B = 540`. The trial pair, gap circle and
analytic chain are those of `Bank.TrialFields` (K590 gi witness, corrected constraints:
`u₁ ≥ 9/50`, gap `401/2500`); only `ρ`, `η`, `tΔ` come from `Budget540`.
`Decay540` bundles exactly the decay-side fields of `DesignData`. -/
namespace CatalanMeasure.GenD.Uniform.Bank540
open D58 Analytic Filter Set Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.CellCert
noncomputable section

theorem corrected_u1 : (9 / 50 : ℝ) ≤ Bank532.secondU590 1 := Cert590.first_lower

def first : FirstTrialBounds Odd.design K590.target K590.firstCost :=
  firstTrial_D58 hrow_D58 hcol_D58 K590.first_budget_log2

theorem near : ∀ y ∈ Ioo (0 : ℝ) 1,
    -gRes Odd.design * Real.log (1 + y ^ 2) +
      (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
        Bank532.secondU590 1 * y ≤ D58.nearCap := by
  intro y hy
  have h := Bank532.second_near_sup_d58_590 y hy
  rw [Instances.d58_gRes]
  have e : (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) = 47 / 58 := by
    norm_num [Odd.design]
  rw [e]
  have e2 : D58.nearCap = -(77 / 100 : ℝ) := by norm_num [D58.nearCap]
  rw [e2]
  exact h

def second : SecondFieldCert Odd.design K590.target K590.residualCap D58.nearCap
    K590.secondCost (fun x => (401 / 2500 : ℝ) ≤ |x|) :=
  { u := Bank532.secondU590, v := Bank532.secondV590, hu := Bank532.second_hu590,
    hv := Bank532.second_hv590,
    MX := (Cert590.MX : ℚ), MY := (Cert590.MY : ℚ), normCap := K590.normCap,
    fieldCap := K590.fieldCap, near_sup := near, norm_le := Bank532.second_norm_le590,
    field_sum := Bank532.second_field_sum590,
    row_sup := by
      rw [(Instances.d58_row_weights).1, (Instances.d58_row_weights).2.1,
        (Instances.d58_row_weights).2.2]
      exact Bank532.second_row_sup590,
    column_sup := by
      rw [(Instances.d58_column_weights).1, (Instances.d58_column_weights).2]
      exact Bank532.second_column_sup590,
    residual_sup := fun x hx hg => by
      rw [Instances.d58_gRes]; exact Bank532.second_residual_sup590 x hx hg,
    budget := fun ha ht => Bank532.second_budget ha ht }

theorem circle : GapCircleBound Odd.design
    (2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2))
    (1001 / 1000) 3 (52788 / 1000) := circ_hcirc

theorem delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
    |x - catalan| ≤ Real.exp (-(rho * (N : ℝ))) →
      |aeval x (deltaPoly Odd.design N)| ≤ Real.exp (-((tDelta - ε) * (N : ℝ) ^ 2)) := by
  exact delta_small_of_certificates Odd.design_admissible circ_hg0 circ_hg1 circ_ha4
    circ_hr1 circ_hr2 circle (w := rho - 58 * K590.secondCost)
    (by norm_num [rho, K590.rho, K590.secondCost, D58.wcap]) first second
    (r := 58 * K590.secondCost)
    (by norm_num [Odd.design, K590.firstCost, K590.secondCost])
    (by norm_num [Odd.design]) (by linarith)
    (by unfold tDelta; rw [show ((Odd.design.n0 : ℕ) : ℝ) = 58 by norm_num [Odd.design]]; ring)

/-- Decay-side data of a `DesignData` for the tier-1 bank (`B = 540`, window `w = 3/4`);
the denominator side supplies `gD ≤ gD` with the content `gain` and the ledger. -/
structure Decay540 where
  pay : PayW (3 / 4) D58.d0 rho eta kappa D58.delta B
  eta_le : eta < tDelta - gD
  delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
    |x - catalan| ≤ Real.exp (-(rho * (N : ℝ))) →
      |aeval x (deltaPoly Odd.design N)| ≤ Real.exp (-((tDelta - ε) * (N : ℝ) ^ 2))

theorem decay540 : Decay540 := ⟨pay, eta_lt, delta_small⟩

end
end CatalanMeasure.GenD.Uniform.Bank540
#print axioms CatalanMeasure.GenD.Uniform.Bank540.corrected_u1
#print axioms CatalanMeasure.GenD.Uniform.Bank540.first
#print axioms CatalanMeasure.GenD.Uniform.Bank540.second
#print axioms CatalanMeasure.GenD.Uniform.Bank540.circle
#print axioms CatalanMeasure.GenD.Uniform.Bank540.delta_small
#print axioms CatalanMeasure.GenD.Uniform.Bank540.decay540
