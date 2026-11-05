module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Real.Basic

@[expose] public section

namespace CatalanMeasure

/-- The endpoint mixture retains the exact missing-point mass. -/
theorem averaged_energy_quadratic_identity
    (k l t N₀ N₁ b₀ b₁ lam₀ lam₁ : ℝ) :
    -(11 / 16 : ℝ) * l + (k / 2 + 1) * (2 * t - t ^ 2) * l +
      (1 - t) * N₀ + t * N₁ +
      (1 - t) * ((1 - t) * b₀ + t * b₁) +
      ((1 - t) * lam₀ + t * lam₁) * t / 6 =
    (-(11 / 16 : ℝ) * l + N₀ + b₀) +
      t * (N₁ - N₀ + b₁ - 2 * b₀ + (k + 2) * l + lam₀ / 6) +
      t ^ 2 * (b₀ - b₁ - (k / 2 + 1) * l + (lam₁ - lam₀) / 6) := by
  ring

theorem quadratic_energy_le_linear {V U C Q t : ℝ}
    (hV : V ≤ U) (hC : C ≤ 5817 / 1000) (hQ : Q ≤ 0) (ht : 0 ≤ t) :
    V + t * C + t ^ 2 * Q ≤ U + t * (5817 / 1000) := by
  have htc := mul_le_mul_of_nonneg_left hC ht
  have htq := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hQ
  linarith

/-- The old case-one margin absorbs its larger initial cost. -/
theorem case_one_quadratic_energy_le_linear {V U C Q t : ℝ}
    (hV : V ≤ U - 39845 / 8000000) (hC : C ≤ 739186 / 125000)
    (hQ : Q ≤ -(170907 / 100000)) (ht : 0 ≤ t) :
    V + t * C + t ^ 2 * Q ≤ U + t * (5817 / 1000) := by
  have htc := mul_le_mul_of_nonneg_left hC ht
  have htq := mul_le_mul_of_nonneg_left hQ (sq_nonneg t)
  nlinarith [sq_nonneg (t - 3 / 100)]

/-- A bounded correction cannot turn a first-order zero into a second-order zero. -/
theorem first_order_not_bounded_by_second_order (C : ℝ) (hC : 0 ≤ C) :
    ∃ d : ℝ, 0 < d ∧ d < 1 ∧ C * d ^ 2 < d := by
  let d : ℝ := 1 / (C + 2)
  have hden : 0 < C + 2 := by linarith
  have hd : 0 < d := div_pos zero_lt_one hden
  have hd1 : d < 1 := (div_lt_one hden).mpr (by linarith)
  have he : d * (C + 2) = 1 := by dsimp [d]; exact div_mul_cancel₀ _ hden.ne'
  refine ⟨d, hd, hd1, ?_⟩
  nlinarith [mul_pos hd hd]

end CatalanMeasure
