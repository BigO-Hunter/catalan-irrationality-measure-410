module

public import Submission.CatalanMeasure.Parametric.PopulationOneLogs
public import Submission.CatalanMeasure.Parametric.GroupedPopulationCanonical
public import Submission.CatalanMeasure.Parametric.WeightedPopulationValue

@[expose] public section

/-!
# Analytic layer, constants: the design-generic physical constants and field identities

Generic version of `TwentyPhysicalConstants`, `TwentyGroupedConstants` and the field identities of
`TwentyGroupedPhysicalFields`, for an arbitrary admissible `P = ⟨n0, b0, q0, g0, h0⟩`.

The design enters only through three real numbers (all with `n = n0 N`, `C = n + (b0+q0+g0) N`,
`n - g = (n0 - g0) N`):
* `gRes P   = (n0 - g0) / n0`            (`9/10` for P20; the residual field is `-gRes log (1+x²)`),
* `gKappa P = (b0 + q0 + g0) / n0`       (`3/10` for P20; `C / n = 1 + gKappa`),
* `gC0 P = 1/2 - gKappa`, `gC1 P = 1 - gKappa + gRes`   (`1/5` and `8/5` for P20).
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric OAI.InternalCatalan Filter
open scoped Topology BigOperators

noncomputable section

/-- `(n0 - g0) / n0`: residual weight of the marked field (`9/10` at P20). -/
def gRes (P : Parameters) : ℝ := ((P.n0 : ℝ) - P.g0) / P.n0

/-- `(b0 + q0 + g0) / n0`: `C / n = 1 + gKappa` (`3/10` at P20). -/
def gKappa (P : Parameters) : ℝ := ((P.b0 : ℝ) + P.q0 + P.g0) / P.n0

/-- Constant term of the budget polynomial (`1/5` at P20). -/
def gC0 (P : Parameters) : ℝ := 1 / 2 - gKappa P

/-- Linear coefficient of the second-population budget polynomial (`8/5` at P20). -/
def gC1 (P : Parameters) : ℝ := 1 - gKappa P + gRes P

/-- The grouped physical constant (copy of `groupedPhysicalConstant`, same definition). -/
def groupedConstant (P : Parameters) (N r a b : ℕ) : ℝ :=
  ((r * (P.C N - 1) + (a + b) * (P.n N - P.g N - 1) + r.choose 2 : ℕ) : ℝ) /
    (P.n N : ℝ) ^ 2 * Real.log 2

/-- The grouped marked field (copy of `groupedPhysicalMarkedField`). -/
def groupedMarkedField (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  -((P.n N - P.g N - 1 : ℕ) : ℝ) / (P.n N : ℝ) * Real.log (1 + x ^ 2)

/-- The grouped near field (copy of `groupedPhysicalNearField`). -/
def groupedNearField (P : Parameters) (N : ℕ) (y : ℝ) : ℝ :=
  groupedMarkedField P N y +
    ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ) / (P.n N : ℝ) * Real.log |y|

theorem n_cast (P : Parameters) (N : ℕ) : (P.n N : ℝ) = (P.n0 : ℝ) * N := by
  simp [Parameters.n]

theorem n0_pos {P : Parameters} (hP : Admissible P) : (0 : ℝ) < P.n0 := by
  exact_mod_cast hP.1

theorem C_nat (P : Parameters) (N : ℕ) :
    P.C N = P.n N + (P.b0 + P.q0 + P.g0) * N := by
  simp only [Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g]
  ring

theorem population_fractions {P : Parameters} (hP : Admissible P) {N p m : ℕ} (hN : 0 < N)
    (hpm : p + m = P.n N) : (p : ℝ) / (P.n N : ℝ) + (m : ℝ) / (P.n N : ℝ) = 1 := by
  have hn : (P.n N : ℝ) ≠ 0 := by exact_mod_cast (n_pos hP hN).ne'
  rw [← add_div]
  have hh : (p : ℝ) + (m : ℝ) = (P.n N : ℝ) := by exact_mod_cast hpm
  rw [hh, div_self hn]

/-- Pure algebra behind `grouped_constant_le` (clearing denominators). -/
theorem grouped_constant_alg {n n0 N k g r s b : ℝ} (hn0 : n0 ≠ 0) (hN : N ≠ 0)
    (hn : n = n0 * N) (hr : r = n - s) :
    (r * (n + k * N - 1) + s * (n - g * N - 1) + r * (r - 1) / 2) / n ^ 2 -
        (1 / 2 : ℝ) * (((n - b) / n) ^ 2 + (b / n) ^ 2) - (3 / 2 : ℝ) * (r / n) ^ 2 =
      (-(1 / 2 - k / n0) + (1 - k / n0 + (n0 - g) / n0) * (s / n) - (s / n) ^ 2 +
        b / n - (b / n) ^ 2) - ((3 / 2) * r + s) / n ^ 2 := by
  subst hn hr
  field_simp
  ring

/-- Generic form of `twenty_grouped_constant_le`. -/
theorem grouped_constant_le {P : Parameters} (hP : Admissible P) {N r a b : ℕ} (hN : 0 < N)
    (hcount : r + a + b = P.n N) :
    groupedConstant P N r a b -
        (1 / 2 : ℝ) * ((((r + a : ℕ) : ℝ) / (P.n N : ℝ)) ^ 2 +
          ((b : ℝ) / (P.n N : ℝ)) ^ 2) * Real.log 2 -
        (3 / 2 : ℝ) * ((r : ℝ) / (P.n N : ℝ)) ^ 2 * Real.log 2 ≤
      (-gC0 P + gC1 P * (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) -
        (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) ^ 2 +
        (b : ℝ) / (P.n N : ℝ) - ((b : ℝ) / (P.n N : ℝ)) ^ 2) * Real.log 2 := by
  have hg := two_g_lt_n hP hN
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnpos := n_pos hP hN
  have hC := C_nat P N
  have hCsub : 1 ≤ P.C N := by omega
  have hr : (r : ℝ) = (P.n N : ℝ) - ((a + b : ℕ) : ℝ) := by
    have h : (r : ℝ) + ((a + b : ℕ) : ℝ) = (P.n N : ℝ) := by
      exact_mod_cast (by omega : r + (a + b) = P.n N)
    linarith only [h]
  have hra : ((r + a : ℕ) : ℝ) = (P.n N : ℝ) - (b : ℝ) := by
    have h : ((r + a : ℕ) : ℝ) + (b : ℝ) = (P.n N : ℝ) := by exact_mod_cast hcount
    linarith only [h]
  have hCR : ((P.C N - 1 : ℕ) : ℝ) = (P.n N : ℝ) + ((P.b0 : ℝ) + P.q0 + P.g0) * N - 1 := by
    rw [Nat.cast_sub hCsub, hC]; push_cast; ring
  have hdR : ((P.n N - P.g N - 1 : ℕ) : ℝ) = (P.n N : ℝ) - (P.g0 : ℝ) * N - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ P.n N - P.g N), Nat.cast_sub (by omega : P.g N ≤ P.n N)]
    simp [Parameters.g]
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have hsnn : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnn : (0 : ℝ) < (P.n N : ℝ) := by exact_mod_cast hnpos
  have hconst : groupedConstant P N r a b = ((r : ℝ) * ((P.n N : ℝ) + ((P.b0 : ℝ) + P.q0 + P.g0) * N - 1) +
      ((a + b : ℕ) : ℝ) * ((P.n N : ℝ) - (P.g0 : ℝ) * N - 1) + (r : ℝ) * ((r : ℝ) - 1) / 2) /
        (P.n N : ℝ) ^ 2 * Real.log 2 := by
    unfold groupedConstant
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hCR, hdR, Nat.cast_choose_two]
  have halg := grouped_constant_alg (k := (P.b0 : ℝ) + P.q0 + P.g0) (g := (P.g0 : ℝ))
    (b := (b : ℝ)) (s := ((a + b : ℕ) : ℝ)) hn0 hNR (n_cast P N) hr
  have hT : 0 ≤ ((3 / 2) * (r : ℝ) + ((a + b : ℕ) : ℝ)) / (P.n N : ℝ) ^ 2 := by positivity
  rw [hconst, hra]
  unfold gC0 gC1 gKappa gRes
  have hkey : ((r : ℝ) * ((P.n N : ℝ) + ((P.b0 : ℝ) + P.q0 + P.g0) * N - 1) +
      ((a + b : ℕ) : ℝ) * ((P.n N : ℝ) - (P.g0 : ℝ) * N - 1) + (r : ℝ) * ((r : ℝ) - 1) / 2) /
        (P.n N : ℝ) ^ 2 - (1 / 2 : ℝ) * ((((P.n N : ℝ) - b) / (P.n N : ℝ)) ^ 2 +
          ((b : ℝ) / (P.n N : ℝ)) ^ 2) - (3 / 2 : ℝ) * ((r : ℝ) / (P.n N : ℝ)) ^ 2 ≤
      (-(1 / 2 - ((P.b0 : ℝ) + P.q0 + P.g0) / P.n0) +
        (1 - ((P.b0 : ℝ) + P.q0 + P.g0) / P.n0 + ((P.n0 : ℝ) - P.g0) / P.n0) *
          (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) - (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) ^ 2 +
        (b : ℝ) / (P.n N : ℝ) - ((b : ℝ) / (P.n N : ℝ)) ^ 2) := by
    linarith only [halg, hT]
  have := mul_le_mul_of_nonneg_right hkey hl2
  linarith only [this]

end
end Analytic
end CatalanMeasure.GenD
