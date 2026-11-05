module

public import Submission.CatalanMeasure.Parametric.PopulationFixedFields
public import Submission.CatalanMeasure.Parametric.RestrictedQuadrature
public import Submission.CatalanMeasure.GenD.Analytic.Const

@[expose] public section

/-!
# Analytic layer: exact cancellation of the common factor (design-generic)

`commonFactor_coordinate_log_full` and `population_row_field_sub_common_full` are the generic
lemmas of `Parametric.GroupedMarkedFields`, whose import closure contains the P20 certificates
(through `TwentyGroupedTrialBounds`); they are restated here, with the same proofs, so that
`GenD` stays free of `Twenty*`.  New: the first-population marked field bound for general `P`.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric OAI.InternalCatalan Polynomial Set

noncomputable section

theorem commonFactor_coordinate_log_full (P : Parameters) (N : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    Real.log |(rowCommonFactor P N).eval (realCoordinateInv x)| =
      (P.A N : ℝ) * (Real.log 2 + Real.log |x| - Real.log (1 + x ^ 2)) +
      (P.h N : ℝ) * (2 * Real.log (1 - x) - Real.log (1 + x ^ 2)) := by
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hm : 0 < 1 - x := sub_pos.mpr hx.2
  have ht0 : realCoordinateInv x ≠ 0 := by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hx0) hd.ne'
  have h1t := one_sub_realCoordinateInv_pos hx
  have hlogt : Real.log |realCoordinateInv x| =
      Real.log 2 + Real.log |x| - Real.log (1 + x ^ 2) := by
    rw [realCoordinateInv, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos hd, Real.log_div (mul_ne_zero (by norm_num) (abs_ne_zero.mpr hx0)) hd.ne',
      Real.log_mul (by norm_num) (abs_ne_zero.mpr hx0)]
  have he : 1 - realCoordinateInv x = (1 - x) ^ 2 / (1 + x ^ 2) := by
    unfold realCoordinateInv
    field_simp
    ring
  have hlogone : Real.log (1 - realCoordinateInv x) =
      2 * Real.log (1 - x) - Real.log (1 + x ^ 2) := by
    rw [he, Real.log_div (pow_ne_zero _ hm.ne') hd.ne', Real.log_pow]
    norm_num
  simp only [rowCommonFactor, eval_mul, eval_pow, eval_X, eval_sub, eval_one, abs_mul, abs_pow]
  rw [abs_of_pos h1t, Real.log_mul (pow_ne_zero _ (abs_ne_zero.mpr ht0))
    (pow_ne_zero _ h1t.ne'), Real.log_pow, Real.log_pow, hlogt, hlogone]

theorem population_row_field_sub_common_full {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) (k : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    paramPopulationRowField P N k x -
      Real.log |(rowCommonFactor P N).eval (realCoordinateInv x)| / (P.n N : ℝ) =
      -(P.A N : ℝ) / (P.n N : ℝ) * Real.log 2 -
        (k / 2 - (P.g N : ℝ) / (P.n N : ℝ)) * Real.log (1 + x ^ 2) := by
  have hn : (P.n N : ℝ) ≠ 0 := by exact_mod_cast (n_pos hP hN).ne'
  have hg : P.g N ≤ P.n N := by have := two_g_lt_n hP hN; omega
  have hH : (P.H N : ℝ) =
      (P.A N : ℝ) + (P.n N : ℝ) - (P.g N : ℝ) + (P.h N : ℝ) := by
    change ((P.C N + P.h N : ℕ) : ℝ) = _
    rw [C_eq_A_add_residual hP hN, Nat.cast_add, Nat.cast_add, Nat.cast_sub hg]
    ring
  rw [commonFactor_coordinate_log_full P N hx hx0]
  unfold paramPopulationRowField
  rw [hH]
  field_simp
  ring

theorem population_row_domain {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
  by_cases hneg : x < 0
  · exact Or.inl ⟨hx.1.le, hneg⟩
  · exact Or.inr ⟨lt_of_le_of_ne (by linarith only [hneg]) hx0.symm, hx.2⟩

/-- `A N / n N = (b0 + q0 + 2 g0) / n0`. -/
theorem ratio_A (P : Parameters) (hP : Admissible P) {N : ℕ} (hN : 0 < N) :
    (P.A N : ℝ) / (P.n N : ℝ) = ((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0 := by
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Parameters.A, Parameters.b, Parameters.q, Parameters.g, Parameters.n]
  push_cast
  field_simp

/-- `g N / n N = g0 / n0`. -/
theorem ratio_g (P : Parameters) (hP : Admissible P) {N : ℕ} (hN : 0 < N) :
    (P.g N : ℝ) / (P.n N : ℝ) = (P.g0 : ℝ) / P.n0 := by
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Parameters.g, Parameters.n]
  push_cast
  field_simp

/-- Generic form of `twenty_marked_first_field_after_common`:
the first-population marked field after the common factor is at most
`-(A0/n0) log 2 + 2 λ g0/n0`. -/
theorem marked_first_field_after_common {P : Parameters} (hP : Admissible P) {N : ℕ}
    (hN : 0 < N) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) {lambda : ℝ}
    (hlambda : 0 ≤ lambda) :
    paramPopulationRowField P N 1 x + lambda * paramCaseField P N x -
      Real.log |(rowCommonFactor P N).eval (realCoordinateInv x)| / (P.n N : ℝ) ≤
        -(((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0) * Real.log 2 + 2 * lambda * ((P.g0 : ℝ) / P.n0) := by
  have he := population_row_field_sub_common_full hP hN 1 hx hx0
  have hb := paramResidualFixedOne_le hP hN hlambda x
  have hA := ratio_A P hP hN
  have hg := ratio_g P hP hN
  have hr : lambda * 2 * (P.g N : ℝ) / (P.n N : ℝ) = 2 * lambda * ((P.g0 : ℝ) / P.n0) := by
    calc
      _ = 2 * lambda * ((P.g N : ℝ) / (P.n N : ℝ)) := by ring
      _ = _ := by rw [hg]
  rw [neg_div, hA, hr] at hb
  unfold paramResidualFixedOne at hb
  rw [neg_div, hA, hg] at hb
  rw [neg_div, hA, hg] at he
  norm_num only at he
  linarith only [he, hb]

end
end Analytic
end CatalanMeasure.GenD
