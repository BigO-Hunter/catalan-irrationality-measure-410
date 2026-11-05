module
public import Submission.CatalanMeasure.Parametric.RealSheetBounds
public import Submission.OAI.NumberTheory.Catalan.Energy.RealTwoSheetIntegralBound
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Set OAI.InternalCatalan
open scoped BigOperators
noncomputable section

def realFirstSheetMixedMatrix (P : Parameters) (N : ℕ) (x : Fin (P.n N) → ℝ) :
    Matrix (Fin (P.n N)) (Fin (P.n N)) ℝ :=
  Matrix.of (fun r i =>
    (x i) ^ r.rev.val +
      (if x i < 0 then (x i) ^ (P.n N - 1 - 2 * P.g N)
        else -5 * (x i) ^ (P.n N - 1 - 2 * P.g N)) * (x i) ^ r.val)

theorem realFirstSheet_far_monomial {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (r : Fin (P.n N)) {x : ℝ} (hx : x ≠ 0) :
    x ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ)) * x ^ r.rev.val =
      x ^ (-rowOffset P N r.val) := by
  calc
    _ = x ^ (((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ)) + (r.rev.val : ℤ)) := by
      rw [zpow_add₀ hx, zpow_natCast]
    _ = x ^ (-rowOffset P N r.val) := by
      congr 1
      have hr := r.isLt
      simp only [Fin.val_rev]
      unfold rowOffset at *
      omega

theorem realFirstSheet_near_monomial {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (r : Fin (P.n N)) {x : ℝ} (hx : x ≠ 0) :
    x ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ)) *
        (x ^ (P.n N - 1 - 2 * P.g N) * x ^ r.val) =
      x ^ rowOffset P N r.val := by
  calc
    _ = x ^ ((((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ)) +
        ((P.n N - 1 - 2 * P.g N : ℕ) : ℤ)) + (r.val : ℤ)) := by
      simp only [zpow_add₀ hx, zpow_natCast]
      ring
    _ = x ^ rowOffset P N r.val := by
      congr 1
      unfold rowOffset
      have hh :=two_g_lt_n hP hN
      omega

theorem realFirstSheet_entry_factor {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (r : Fin (P.n N)) {x : ℝ} (hx : x ≠ 0) :
    (if x < 0 then
      (1 / 2 : ℝ) * x ^ (-rowOffset P N r.val) +
        (1 / 2 : ℝ) * x ^ rowOffset P N r.val
    else
      -(1 / 4 : ℝ) * x ^ (-rowOffset P N r.val) +
        (5 / 4 : ℝ) * x ^ rowOffset P N r.val) =
      (if x < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
        x ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ)) *
          (x ^ r.rev.val +
            (if x < 0 then x ^ (P.n N - 1 - 2 * P.g N)
              else -5 * x ^ (P.n N - 1 - 2 * P.g N)) * x ^ r.val) := by
  by_cases hneg : x < 0
  · simp only [ite_eq_left hneg]
    rw [← realFirstSheet_far_monomial hP hN r hx,
      ← realFirstSheet_near_monomial hP hN r hx]
    ring
  · simp only [ite_eq_right hneg]
    rw [← realFirstSheet_far_monomial hP hN r hx,
      ← realFirstSheet_near_monomial hP hN r hx]
    ring

theorem realSheetDeterminant_firstSheet_factor {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (x : Fin (P.n N) → ℝ) (hx : ∀ i, x i ≠ 0) :
    realSheetDeterminant P N x =
      (∏ i, (if x i < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
        (x i) ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))) *
          Matrix.det (realFirstSheetMixedMatrix P N x) := by
  classical
  unfold realSheetDeterminant
  have hmatrix :
      Matrix.of (fun r i : Fin (P.n N) =>
        if x i < 0 then
          (1 / 2 : ℝ) * (x i) ^ (-rowOffset P N r.val) +
            (1 / 2 : ℝ) * (x i) ^ rowOffset P N r.val
        else
          -(1 / 4 : ℝ) * (x i) ^ (-rowOffset P N r.val) +
            (5 / 4 : ℝ) * (x i) ^ rowOffset P N r.val) =
        Matrix.of (fun r i : Fin (P.n N) =>
          ((if x i < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
            (x i) ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))) *
              realFirstSheetMixedMatrix P N x r i) := by
    ext r i
    exact realFirstSheet_entry_factor hP hN r (hx i)
  rw [hmatrix, Matrix.det_mul_row]

theorem realFirstSheet_far_coefficient_abs_le (x : ℝ) :
    |if x < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)| ≤ 1 := by
  by_cases hx : x < 0 <;> norm_num [hx]

theorem realFirstSheet_factor_abs_le (P : Parameters) (N : ℕ) (x : Fin (P.n N) → ℝ) :
    |∏ i, (if x i < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
      (x i) ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))| ≤
        ∏ i, |(x i) ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))| := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod₀
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [abs_mul]
    calc
      _ ≤ 1 * |(x i) ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))| :=
        mul_le_mul_of_nonneg_right (realFirstSheet_far_coefficient_abs_le (x i))
          (abs_nonneg _)
      _ = _ := one_mul _

theorem realFirstSheet_factor_abs_le_weight (P : Parameters) (N : ℕ) (x : Fin (P.n N) → ℝ) :
    |∏ i, (if x i < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
      (x i) ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))| ≤
        ∏ i, |x i| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ)) := by
  simpa only [abs_zpow] using realFirstSheet_factor_abs_le P N x

theorem realSheetDeterminant_abs_le_firstSheet_mixed {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (x : Fin (P.n N) → ℝ) (hx : ∀ i, x i ≠ 0) :
    |realSheetDeterminant P N x| ≤
      (∏ i, |x i| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))) *
        |Matrix.det (realFirstSheetMixedMatrix P N x)| := by
  rw [realSheetDeterminant_firstSheet_factor hP hN x hx, abs_mul]
  exact mul_le_mul_of_nonneg_right (realFirstSheet_factor_abs_le_weight P N x)
    (abs_nonneg _)

theorem realSheetDeterminant_first_sheet_bound {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (x : Fin (P.n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x)
    (hn48 : 48 ≤ P.n N) (hDpos : 0 < P.n N-1-2*P.g N)
    (hcase : (∑ i : Fin (P.n N), (1 - x i ^ 2) / (1 + x i ^ 2)) ≤
      ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ)) :
    |realSheetDeterminant P N x| ≤
      (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
        |∏ i : Fin (P.n N), ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
          ∏ i : Fin (P.n N), |x i| ^ P.g N := by
  have hn : 48 ≤ P.n N := hn48
  have hDn : P.n N - 1 - 2 * P.g N ≤ P.n N := by omega
  have hxabs : ∀ i, |x i| < 1 := fun i => abs_lt.mpr (hx i)
  have hweight : (∑ i : Fin (P.n N), blaschkeWeight (x i)) ≤
      ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ) := by
    simpa only [blaschkeWeight] using hcase
  have hmixed : |(realFirstSheetMixedMatrix P N x).det| ≤
      (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N * |(Matrix.vandermonde x).det| :=
    firstSheet_uniform_real_mixed_determinant_bound x hn hDpos hDn hx0 hxabs hxi hweight
  have hprod : 0 ≤ ∏ i : Fin (P.n N), |x i| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ)) :=
    Finset.prod_nonneg (fun i _ => zpow_nonneg (abs_nonneg (x i)) _)
  have hw : (∏ i : Fin (P.n N), |x i| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))) *
      |(Matrix.vandermonde x).det| =
      |∏ i : Fin (P.n N), ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
        ∏ i : Fin (P.n N), |x i| ^ P.g N := by
    simpa only [abs_zpow] using firstSheet_laurent_vandermonde_weight (P.g N) x hx0
  calc
    |realSheetDeterminant P N x| ≤
        (∏ i : Fin (P.n N), |x i| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))) *
          |(realFirstSheetMixedMatrix P N x).det| :=
      realSheetDeterminant_abs_le_firstSheet_mixed hP hN x hx0
    _ ≤ (∏ i : Fin (P.n N), |x i| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))) *
        ((1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N * |(Matrix.vandermonde x).det|) :=
      mul_le_mul_of_nonneg_left hmixed hprod
    _ = (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
        ((∏ i : Fin (P.n N), |x i| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))) *
          |(Matrix.vandermonde x).det|) := by ring
    _ = _ := by rw [hw]; ring

end
end CatalanMeasure.Parametric
