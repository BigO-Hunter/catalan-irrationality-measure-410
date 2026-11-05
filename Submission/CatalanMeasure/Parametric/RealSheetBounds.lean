module
public import Submission.CatalanMeasure.Parametric.RealSheet
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Set OAI.InternalCatalan
open scoped BigOperators
noncomputable section

private theorem sqrt_one_add_inv_sq {x : ℝ} (hx0 : x ≠ 0) :
    Real.sqrt (1 + (x⁻¹) ^ 2) = Real.sqrt (1 + x ^ 2) / |x| := by
  have heq : 1 + (x⁻¹) ^ 2 = (1 + x ^ 2) / x ^ 2 := by
    field_simp [hx0]
    ring
  rw [heq, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs]

theorem sheet_far_weight_eq (P : Parameters) (N : ℕ) {x : ℝ} (hx0 : x ≠ 0) :
    |(x⁻¹) ^ (-(P.g N : ℤ))| * Real.sqrt (1 + (x⁻¹) ^ 2) ^ (P.n N - 1) =
      Real.sqrt (1 + x ^ 2) ^ (P.n N - 1) *
        |x| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ)) := by
  rw [abs_zpow, abs_inv, sqrt_one_add_inv_sq hx0]
  simp only [zpow_neg, zpow_natCast, inv_pow, inv_inv, div_pow]
  rw [zpow_sub₀ (abs_ne_zero.mpr hx0)]
  simp only [zpow_natCast]
  ring

theorem sheet_near_weight_le {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    |x ^ (-(P.g N : ℤ))| * Real.sqrt (1 + x ^ 2) ^ (P.n N - 1) ≤
      Real.sqrt (1 + x ^ 2) ^ (P.n N - 1) *
        |x| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ)) := by
  have hdim : 2 * P.g N ≤ P.n N - 1 := by
    have hh :=two_g_lt_n hP hN
    omega
  have hexp : (P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ) ≤ -(P.g N : ℤ) := by omega
  have hp := zpow_le_zpow_right_of_le_one₀ (abs_pos.mpr hx0)
    (abs_lt.mpr hx).le hexp
  rw [abs_zpow, mul_comm]
  exact mul_le_mul_of_nonneg_left hp (pow_nonneg (Real.sqrt_nonneg _) _)

theorem sheet_choice_weight_le {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) (ε : Bool) :
    let z := if ε then x else x⁻¹
    |z ^ (-(P.g N : ℤ))| * Real.sqrt (1 + z ^ 2) ^ (P.n N - 1) ≤
      Real.sqrt (1 + x ^ 2) ^ (P.n N - 1) *
        |x| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ)) := by
  cases ε
  · simpa using (sheet_far_weight_eq P N hx0).le
  · simpa using sheet_near_weight_le hP hN hx hx0


theorem realSheetDeterminant_eq_sum (P : Parameters) (N : ℕ) (x : Fin (P.n N) → ℝ) :
    realSheetDeterminant P N x =
      ∑ ε : Fin (P.n N) → Bool,
        (∏ i, realSheetCoefficient (x i) (ε i)) *
          Matrix.det (Matrix.of (fun r i : Fin (P.n N) =>
            realSheetNode (x i) (ε i) ^ rowOffset P N r.val)) := by
  classical
  have hmatrix :
      Matrix.of (fun r i : Fin (P.n N) =>
        if x i < 0 then
          (1 / 2 : ℝ) * (x i) ^ (-rowOffset P N r.val) +
            (1 / 2 : ℝ) * (x i) ^ rowOffset P N r.val
        else
          -(1 / 4 : ℝ) * (x i) ^ (-rowOffset P N r.val) +
            (5 / 4 : ℝ) * (x i) ^ rowOffset P N r.val) =
        Matrix.of (fun r i : Fin (P.n N) => ∑ b : Bool,
          realSheetCoefficient (x i) b *
            realSheetNode (x i) b ^ rowOffset P N r.val) := by
    ext r i
    by_cases hi : x i < 0 <;>
      simp [realSheetCoefficient, realSheetNode, hi, zpow_neg] <;> ring
  unfold realSheetDeterminant
  rw [hmatrix]
  have hexpand := det_column_sum_bool (fun b => Matrix.of (fun r i : Fin (P.n N) =>
    realSheetCoefficient (x i) b * realSheetNode (x i) b ^ rowOffset P N r.val))
  simp only [Matrix.of_apply] at hexpand
  rw [hexpand]
  apply Finset.sum_congr rfl
  intro ε _
  simpa only [Matrix.of_apply] using
    Matrix.det_mul_row (fun i => realSheetCoefficient (x i) (ε i))
      (Matrix.of (fun r i : Fin (P.n N) =>
        realSheetNode (x i) (ε i) ^ rowOffset P N r.val))


theorem realSheetCoefficient_sum_abs_prod_le (P : Parameters) (N : ℕ) (x : Fin (P.n N) → ℝ) :
    (∑ ε : Fin (P.n N) → Bool,
      |∏ i, realSheetCoefficient (x i) (ε i)|) ≤ (3 / 2 : ℝ) ^ P.n N := by
  classical
  calc
    _ = ∏ i, ∑ b : Bool, |realSheetCoefficient (x i) b| := by
      simp only [Finset.abs_prod]
      exact (Fintype.prod_sum (fun i b => |realSheetCoefficient (x i) b|)).symm
    _ ≤ ∏ _i : Fin (P.n N), (3 / 2 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      · intro i _
        exact realSheetCoefficient_abs_sum_le (x i)
    _ = (3 / 2 : ℝ) ^ P.n N := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]


theorem realSheetDeterminant_abs_le_of_monomial_bound (P : Parameters) (N : ℕ)
    (x : Fin (P.n N) → ℝ) (B : ℝ)
    (hB : ∀ ε : Fin (P.n N) → Bool,
      |Matrix.det (Matrix.of (fun r i : Fin (P.n N) =>
        realSheetNode (x i) (ε i) ^ rowOffset P N r.val))| ≤ B) :
    |realSheetDeterminant P N x| ≤ (3 / 2 : ℝ) ^ P.n N * B := by
  classical
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (fun _ => false))
  rw [realSheetDeterminant_eq_sum]
  calc
    _ ≤ ∑ ε : Fin (P.n N) → Bool,
        |(∏ i, realSheetCoefficient (x i) (ε i)) *
          Matrix.det (Matrix.of (fun r i : Fin (P.n N) =>
            realSheetNode (x i) (ε i) ^ rowOffset P N r.val))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ε : Fin (P.n N) → Bool,
        |∏ i, realSheetCoefficient (x i) (ε i)| * B := by
      apply Finset.sum_le_sum
      intro ε _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB ε) (abs_nonneg _)
    _ = (∑ ε : Fin (P.n N) → Bool,
        |∏ i, realSheetCoefficient (x i) (ε i)|) * B := by rw [Finset.sum_mul]
    _ ≤ (3 / 2 : ℝ) ^ P.n N * B :=
      mul_le_mul_of_nonneg_right (realSheetCoefficient_sum_abs_prod_le P N x) hB0

theorem realSheetDeterminant_abs_le_sqrt {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (x : Fin (P.n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    |realSheetDeterminant P N x| ≤
      (3 / 2 : ℝ) ^ P.n N * (Real.sqrt (P.n N : ℝ)) ^ P.n N /
        (2 : ℝ) ^ ((P.n N).choose 2) *
        ∏ i, (Real.sqrt (1 + x i ^ 2) ^ (P.n N - 1) *
          |x i| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))) := by
  classical
  let C : ℝ := (Real.sqrt (P.n N : ℝ)) ^ P.n N / (2 : ℝ) ^ ((P.n N).choose 2)
  let W : Fin (P.n N) → ℝ := fun i =>
    Real.sqrt (1 + x i ^ 2) ^ (P.n N - 1) *
      |x i| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ))
  have hchoice (ε : Fin (P.n N) → Bool) :
      |Matrix.det (Matrix.of (fun r i : Fin (P.n N) =>
        realSheetNode (x i) (ε i) ^ rowOffset P N r.val))| ≤ C * ∏ i, W i := by
    let z : Fin (P.n N) → ℝ := fun i => realSheetNode (x i) (ε i)
    have hz (i : Fin (P.n N)) : z i ≠ 0 := by
      dsimp only [z, realSheetNode]
      split_ifs
      · exact hx0 i
      · exact inv_ne_zero (hx0 i)
    have hmon := laurent_monomial_det_abs_le (P.g N) z hz
    change |Matrix.det (Matrix.of (fun r i : Fin (P.n N) =>
      z i ^ ((r.val : ℤ) - (P.g N : ℤ))))| ≤ C * ∏ i, W i
    apply hmon.trans
    apply mul_le_mul_of_nonneg_left
    · apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg (abs_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
      · intro i _
        simpa only [z, realSheetNode, W] using
          sheet_choice_weight_le hP hN (hx i) (hx0 i) (ε i)
    · positivity
  have h := realSheetDeterminant_abs_le_of_monomial_bound P N x (C * ∏ i, W i) hchoice
  calc
    |realSheetDeterminant P N x| ≤ (3 / 2 : ℝ) ^ P.n N * (C * ∏ i, W i) := h
    _ = _ := by dsimp only [C, W]; ring


theorem realSheetDeterminant_abs_le {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (x : Fin (P.n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    |realSheetDeterminant P N x| ≤
      (3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2) /
        (2 : ℝ) ^ ((P.n N).choose 2) *
        (∏ i : Fin (P.n N),
          ((1 + x i ^ 2) ^ (((P.n N : ℝ) - 1) / 2) *
            |x i| ^ ((P.g N : ℤ) - ((P.n N - 1 : ℕ) : ℤ)))) := by
  have hdim : 1 ≤ P.n N :=Nat.succ_le_iff.mpr (n_pos hP hN)
  have hcast : ((P.n N - 1 : ℕ) : ℝ) = (P.n N : ℝ) - 1 := by
    rw [Nat.cast_sub hdim, Nat.cast_one]
  have hhead : Real.sqrt (P.n N : ℝ) ^ P.n N = (P.n N : ℝ) ^ ((P.n N : ℝ) / 2) := by
    symm
    simpa only [Real.rpow_natCast] using
      Real.rpow_div_two_eq_sqrt (P.n N : ℝ) (Nat.cast_nonneg (P.n N))
  have hrow (i : Fin (P.n N)) :
      Real.sqrt (1 + x i ^ 2) ^ (P.n N - 1) =
        (1 + x i ^ 2) ^ (((P.n N : ℝ) - 1) / 2) := by
    symm
    have h := Real.rpow_div_two_eq_sqrt ((P.n N - 1 : ℕ) : ℝ)
      (by positivity : (0 : ℝ) ≤ 1 + x i ^ 2)
    rw [Real.rpow_natCast] at h
    simpa only [hcast] using h
  simpa only [hhead, hrow] using realSheetDeterminant_abs_le_sqrt hP hN x hx hx0

end
end CatalanMeasure.Parametric
