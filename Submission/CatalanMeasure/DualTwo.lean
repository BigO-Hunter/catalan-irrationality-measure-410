module

public import Submission.CatalanMeasure.Dual.Sup
public import Submission.OAI.NumberTheory.Catalan.Determinants.RealDeterminantCore
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# A new certificate for OpenAI's second energy dual

OpenAI's real-place bound takes the larger of two dual values, one for each case of the sheet
estimate.  For the second case (`κ = 2`) we replace OpenAI's trial sequences by re-optimized
ones (40 free coefficients and 27 geometric tails, `CatalanMeasure/Dual/Data.lean`).  Their
row and column fields are bounded by `MX = -0.98572217` and `MY = -1.60942387`
(`CatalanMeasure/Dual/Sup.lean`, checked by Lean's kernel) and their weighted norms by
`NP = 0.066723974`, `NV = 1.292855037`.  The dual value is then below `-2.29180925`, while
OpenAI's first case gives `-2.296789875`.  Hence `|Δ_N(G)| ≤ exp(n² (-U + ε))` with
`U = 2.29180925 - ½ log 2`.
-/

open Filter Set CatalanMeasure.Cert

namespace OAI.InternalCatalan

/-- The new trial sequences for the second case. -/
noncomputable def dualP2 : ℕ → ℝ := trialSeq CatalanMeasure.Dual.Pc CatalanMeasure.Dual.P
noncomputable def dualV2 : ℕ → ℝ := trialSeq CatalanMeasure.Dual.Vc CatalanMeasure.Dual.V

noncomputable def dualBx : ℝ := -98572217 / 100000000
noncomputable def dualBs : ℝ := -160942387 / 100000000

theorem dualP2_summable : Summable (fun k => |dualP2 k|) :=
  (trialSeq_summable (by decide +kernel)).1

theorem dualV2_summable : Summable (fun k => |dualV2 k|) :=
  (trialSeq_summable (by decide +kernel)).1

theorem dual_row_bound : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 →
    realEnergyRowTrialField 2 0 dualP2 dualV2 z ≤ dualBx := by
  intro z hz hz0
  have h := CatalanMeasure.Dual.row_sup z (by
    rcases lt_or_gt_of_ne hz0 with h | h
    · exact Or.inl ⟨hz.1, h⟩
    · exact Or.inr ⟨h, hz.2⟩)
  rw [CatalanMeasure.Dual.MX_eq] at h
  exact h

theorem dual_col_bound : ∀ z ∈ Ioo (0 : ℝ) 1,
    realEnergyColumnTrialField dualV2 z ≤ dualBs := by
  intro z hz
  have h := CatalanMeasure.Dual.col_sup z hz
  rw [CatalanMeasure.Dual.MY_eq] at h
  exact h

theorem dual_total_lt :
    -(11 / 16 : ℝ) * Real.log 2 + 2 * (33361987 / 500000000) + (1292855037 / 1000000000) / 2 +
      dualBx + dualBs < -(229180925 / 100000000 : ℝ) := by
  have := Real.log_two_gt_d9
  unfold dualBx dualBs
  norm_num at this ⊢
  linarith

theorem dual_dual_lt :
    realEnergyDualConstant 2 dualP2 dualV2 dualBx dualBs < -(229180925 / 100000000 : ℝ) := by
  have hp := CatalanMeasure.Dual.normP_le
  have hv := CatalanMeasure.Dual.normV_le
  rw [CatalanMeasure.Dual.NP_eq] at hp
  rw [CatalanMeasure.Dual.NV_eq] at hv
  unfold realEnergyDualConstant
  have := dual_total_lt
  unfold dualP2 dualV2
  nlinarith

theorem dual_row_sup_le : realEnergyRowTrialSup 2 0 dualP2 dualV2 ≤ dualBx := by
  unfold realEnergyRowTrialSup
  refine csSup_le (realEnergyRowTrialField_image_nonempty _ _ _ _) ?_
  rintro y ⟨x, hx, rfl⟩
  exact dual_row_bound x hx.1 hx.2

theorem dual_col_sup_le : realEnergyColumnTrialSup dualV2 ≤ dualBs := by
  unfold realEnergyColumnTrialSup
  refine csSup_le (realEnergyColumnTrialField_image_nonempty _) ?_
  rintro y ⟨x, hx, rfl⟩
  exact dual_col_bound x hx

/-- The real-place bound with the new second-case certificate. -/
theorem eventually_realDeterminant_abs_upper_dual {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, |determinant N| ≤
      Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + ε)) := by
  have hsup : max (realEnergyDualConstant 1 barrierP1 barrierV1
        (realEnergyRowTrialSup 1 barrierLambda1 barrierP1 barrierV1)
        (realEnergyColumnTrialSup barrierV1))
      (realEnergyDualConstant 2 dualP2 dualV2
        (realEnergyRowTrialSup 2 0 dualP2 dualV2) (realEnergyColumnTrialSup dualV2)) <
      -(229180925 / 100000000 : ℝ) := by
    apply max_lt
    · exact lt_trans realDeterminantCaseOneDual_sharp_lt (by norm_num)
    · have h1 := dual_row_sup_le
      have h2 := dual_col_sup_le
      have h3 := dual_dual_lt
      unfold realEnergyDualConstant at h3 ⊢
      linarith
  filter_upwards [realDeterminant_eventually_log_sup_dual barrier_lambdas.2.1
      barrierP1 barrierV1 dualP2 dualV2 barrier_trials_abs_summable.2.2.1
      barrier_trials_abs_summable.2.2.2 dualP2_summable dualV2_summable hε,
    eventually_ge_atTop (1 : ℕ)] with N hN hNpos
  by_cases hz : determinant N = 0
  · rw [hz, abs_zero]
    exact (Real.exp_pos _).le
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hn2 : (0 : ℝ) < (n N : ℝ) ^ 2 := sq_pos_of_pos hn
  have hlog : Real.log |determinant N| ≤ (n N : ℝ) ^ 2 *
      (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + ε) := by
    have hb : Real.log |determinant N| / (n N : ℝ) ^ 2 ≤
        -(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + ε := by
      linarith [hN hz]
    simpa only [mul_comm] using (div_le_iff₀ hn2).mp hb
  calc
    |determinant N| = Real.exp (Real.log |determinant N|) :=
      (Real.exp_log (abs_pos.mpr hz)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

end OAI.InternalCatalan
