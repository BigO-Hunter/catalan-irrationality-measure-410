module
public import Submission.CatalanMeasure.Parametric.TwoAdicCoefficientExpansion
public import Submission.CatalanMeasure.Parametric.TwoAdicSmoothingBounds
public import Submission.OAI.NumberTheory.Catalan.Polynomial.RawCoefficientEntryBound
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem paramUnconvolvedP_entry_norm_le (P : Parameters) (N r u : ℕ) :
    ‖((Chebyshev.T ℤ (rowDistance P N r : ℤ)).coeff u : ℚ_[2])‖ ≤
      (2 : ℝ) ^ (1 - (u : ℤ)) := by
  calc
    _ ≤ 1 / (2 : ℝ) ^ (u - 1) :=
      padic_two_norm_int_le_of_pow_dvd
        (chebyshev_T_coeff_two_pow_dvd (rowDistance P N r : ℤ) u)
    _ = (2 : ℝ) ^ (-((u - 1 : ℕ) : ℤ)) := by
      simp only [zpow_neg, zpow_natCast, one_div]
    _ ≤ (2 : ℝ) ^ (1 - (u : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)

theorem paramUnconvolvedD_entry_norm_le (P : Parameters) (N r u : ℕ) :
    ‖((Int.sign (rowOffset P N r) *
      (Chebyshev.U ℤ ((rowDistance P N r : ℤ) - 1)).coeff u : ℤ) : ℚ_[2])‖ ≤
      (2 : ℝ) ^ (-(u : ℤ)) := by
  have hdiv := dvd_mul_of_dvd_right
    (chebyshev_U_coeff_two_pow_dvd ((rowDistance P N r : ℤ) - 1) u)
    (Int.sign (rowOffset P N r))
  simpa only [zpow_neg, zpow_natCast, one_div] using
    padic_two_norm_int_le_of_pow_dvd hdiv

theorem paramRawCoefficientEntry_norm_le (P : Parameters) (hAdm : Admissible P) (z : ℚ) {N r j : ℕ}
    (hN : 0 < N) (hj : j < P.L N) (t : Fin 3) (u : paramRawCoefficientIndex P N t) :
    ‖paramRawCoefficientVector P N r j t u.val * paramRawCoefficientScalar P z N j t u.val‖ ≤
      (8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2) *
        (2 : ℝ) ^ (-(if t = 0 then (P.C N : ℤ)
          else if t = 1 then 2 * (u.val : ℤ) + (j : ℤ) - (P.H N : ℤ)
          else (u.val : ℤ))) := by
  have hjH : j < P.H N := by unfold Parameters.H Parameters.C at *;omega
  have hHone : 1 ≤ (P.H N : ℝ) := by
    have hH : 1 ≤ P.H N := by have :=n_pos hAdm hN;unfold Parameters.H Parameters.C Parameters.L;omega
    exact_mod_cast hH
  have hHsq : 1 ≤ (P.H N : ℝ) ^ 2 := by
    nlinarith only [hHone, sq_nonneg ((P.H N : ℝ) - 1)]
  have hFone := one_le_discrepancyNormFactor z
  have hFzero := discrepancyNormFactor_nonneg z
  have hFcommon : discrepancyNormFactor z ≤
      8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2 := by
    nlinarith only [hFone, mul_le_mul_of_nonneg_left hHsq hFzero]
  have hScommon : 8 * (P.H N : ℝ) ^ 2 ≤
      8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hFone (sq_nonneg (P.H N : ℝ))]
  have he1 : ‖4 * (z : ℚ_[2]) - smoothingMoment 0 0‖ ≤ discrepancyNormFactor z :=
    (le_max_left _ _).trans (le_max_right _ _)
  have he2 : ‖smoothingMoment 0 1‖ ≤ discrepancyNormFactor z :=
    (le_max_right _ _).trans (le_max_right _ _)
  by_cases h0 : t = 0
  · simp only [paramRawCoefficientVector, paramRawCoefficientScalar, h0, ite_eq_left, mul_one]
    have hs := (paramSmoothingColumn_norm_le P N r j hjH).trans
      (div_le_div_of_nonneg_right hScommon (by positivity :
        (0 : ℝ) ≤ (2 : ℝ) ^ P.C N))
    simpa only [zpow_neg, zpow_natCast, div_eq_mul_inv] using hs
  · have hu : u.val < P.C N := by
      simpa only [paramRawCoefficientIndex, ite_eq_right h0] using u.isLt
    by_cases h1 : t = 1
    · simp only [paramRawCoefficientVector, paramRawCoefficientScalar, h1, ite_true]
      rw [norm_mul]
      calc
        _ ≤ (2 : ℝ) ^ (1 - (u.val : ℤ)) *
            (‖4 * (z : ℚ_[2]) - smoothingMoment 0 0‖ *
              (2 : ℝ) ^ ((P.H N : ℤ) - 1 - u.val - j)) :=
          mul_le_mul (paramUnconvolvedP_entry_norm_le P N r u.val)
            (paramExceptionScalar_norm_le P z j hu) (norm_nonneg _) (by positivity)
        _ = ‖4 * (z : ℚ_[2]) - smoothingMoment 0 0‖ *
            (2 : ℝ) ^ (-(2 * (u.val : ℤ) + j - (P.H N : ℤ))) := by
          rw [mul_left_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have he : (1 - (u.val : ℤ)) + ((P.H N : ℤ) - 1 - u.val - j) =
              -(2 * (u.val : ℤ) + j - (P.H N : ℤ)) := by ring
          rw [he]
        _ ≤ _ := mul_le_mul_of_nonneg_right (he1.trans hFcommon) (by positivity)
    · have hp : (2 : ℝ) ^ Nat.log 2 (P.H N) ≤ (P.H N : ℝ) + 1 := by
        exact_mod_cast Nat.pow_log_le_add_one 2 (P.H N)
      have hp' : (2 : ℝ) ^ Nat.log 2 (P.H N) ≤ 2 * (P.H N : ℝ) := by
        linarith only [hp, hHone]
      have hlog : 2 * (2 : ℝ) ^ (2 * Nat.log 2 (P.H N)) ≤ 8 * (P.H N : ℝ) ^ 2 := by
        have hp2 := mul_nonneg (sub_nonneg.mpr hp')
          (show 0 ≤ 2 * (P.H N : ℝ) + (2 : ℝ) ^ Nat.log 2 (P.H N) by positivity)
        rw [Nat.mul_comm 2 (Nat.log 2 (P.H N)), pow_mul]
        nlinarith only [hp2]
      have hBcommon : max ‖-smoothingMoment 0 1‖
          (2 * (2 : ℝ) ^ (2 * Nat.log 2 (P.H N))) ≤
          8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2 := by
        rw [norm_neg]
        exact max_le (he2.trans hFcommon) (hlog.trans hScommon)
      simp only [paramRawCoefficientVector, paramRawCoefficientScalar, h0, h1, ite_false]
      rw [norm_mul]
      calc
        _ ≤ (2 : ℝ) ^ (-(u.val : ℤ)) *
            (8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2) :=
          mul_le_mul (paramUnconvolvedD_entry_norm_le P N r u.val)
            ((paramBoundaryScalar_norm_le P hu hjH).trans hBcommon)
            (norm_nonneg _) (by positivity)
        _ = _ := mul_comm _ _


end
end CatalanMeasure.Parametric
