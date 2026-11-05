module
public import Submission.CatalanMeasure.Parametric.RealIntegral
public import Submission.CatalanMeasure.Parametric.RowFrobenius
public import Submission.OAI.NumberTheory.Catalan.Energy.RealSheetIntegral
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Set OAI.InternalCatalan
open scoped BigOperators
noncomputable section
section

theorem rowP_realCoordinateInv {P : Parameters} (hP : Admissible P) {N r : ℕ} (hN : 0 < N) (hr : r < P.n N)
    {x : ℝ} (hx : x ≠ 0) :
    (realPoly (rowP P N r)).eval (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ P.h N * realCoordinateInv x ^ (P.C N - 1) *
        ((x ^ rowDistance P N r + (x⁻¹) ^ rowDistance P N r) / 2) := by
  have ht : realCoordinateInv x ≠ 0 := by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hx) (by positivity)
  unfold realPoly
  rw [← eval₂_eq_eval_map, rowP_eval₂_of_distance_lt (Int.castRingHom ℝ) (rowDistance_lt_C hP hN hr) ht,
    inv_realCoordinateInv hx, chebyshevT_eval_sheet _ hx]

theorem rowD_realCoordinateInv {P : Parameters} (hP : Admissible P) {N r : ℕ} (hN : 0 < N) (hr : r < P.n N)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    Real.sqrt (1 - realCoordinateInv x ^ 2) / realCoordinateInv x *
        (realPoly (rowD P N r)).eval (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ P.h N * realCoordinateInv x ^ (P.C N - 1) *
        (Int.sign (rowOffset P N r) : ℝ) *
          (((x⁻¹) ^ rowDistance P N r - x ^ rowDistance P N r) / 2) := by
  have ht : realCoordinateInv x ≠ 0 := by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hx0) (by positivity)
  unfold realPoly
  rw [sqrt_div_realCoordinateInv hx hx0, ← eval₂_eq_eval_map,
    rowD_eval₂_of_distance_lt (Int.castRingHom ℝ) (rowDistance_lt_C hP hN hr) ht, inv_realCoordinateInv hx0]
  calc
    _ = (1 - realCoordinateInv x) ^ P.h N * realCoordinateInv x ^ (P.C N - 1) *
        (Int.sign (rowOffset P N r) : ℝ) *
          (((x⁻¹ - x) / 2) *
            (Chebyshev.U ℤ ((rowDistance P N r : ℤ) - 1)).eval₂ (Int.castRingHom ℝ)
              ((x + x⁻¹) / 2)) := by
      rw [show (Int.castRingHom ℝ) (Int.sign (rowOffset P N r)) =
        (Int.sign (rowOffset P N r) : ℝ) from rfl]
      ring
    _ = _ := by rw [chebyshevU_eval_sheet _ hx0]

private theorem sheet_natAbs_sum (m : ℤ) (x : ℝ) :
    x ^ m.natAbs + (x⁻¹) ^ m.natAbs = x ^ m + x ^ (-m) := by
  calc
    _ = x ^ (m.natAbs : ℤ) + x ^ (-(m.natAbs : ℤ)) := by
      simp only [zpow_neg, zpow_natCast, inv_pow]
    _ = _ := by
      rcases Int.natAbs_eq m with hm | hm
      · exact congrArg (fun z : ℤ => x ^ z + x ^ (-z)) hm.symm
      · calc
          _ = x ^ (-(m.natAbs : ℤ)) + x ^ (-(-(m.natAbs : ℤ))) := by
            rw [neg_neg]
            ring
          _ = _ := congrArg (fun z : ℤ => x ^ z + x ^ (-z)) hm.symm

private theorem sheet_natAbs_difference (m : ℤ) (x : ℝ) :
    (Int.sign m : ℝ) * ((x⁻¹) ^ m.natAbs - x ^ m.natAbs) =
      x ^ (-m) - x ^ m := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [Int.sign_eq_neg_one_of_neg hm]
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul]
    calc
      _ = x ^ (m.natAbs : ℤ) - x ^ (-(m.natAbs : ℤ)) := by
        simp only [zpow_neg, zpow_natCast, inv_pow]
        ring
      _ = _ := by rw [Int.ofNat_natAbs_of_nonpos hm.le, neg_neg]
  · subst m
    simp
  · rw [Int.sign_eq_one_of_pos hm]
    simp only [Int.cast_one, one_mul]
    calc
      _ = x ^ (-(m.natAbs : ℤ)) - x ^ (m.natAbs : ℤ) := by
        simp only [zpow_neg, zpow_natCast, inv_pow]
      _ = _ := by rw [Int.natAbs_of_nonneg hm.le]

theorem rowP_realCoordinateInv_signed {P : Parameters} (hP : Admissible P) {N r : ℕ} (hN : 0 < N) (hr : r < P.n N)
    {x : ℝ} (hx : x ≠ 0) :
    (realPoly (rowP P N r)).eval (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ P.h N * realCoordinateInv x ^ (P.C N - 1) *
        ((x ^ rowOffset P N r + x ^ (-rowOffset P N r)) / 2) := by
  simpa only [rowDistance, sheet_natAbs_sum] using rowP_realCoordinateInv hP hN hr hx

theorem rowD_realCoordinateInv_signed {P : Parameters} (hP : Admissible P) {N r : ℕ} (hN : 0 < N) (hr : r < P.n N)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    Real.sqrt (1 - realCoordinateInv x ^ 2) / realCoordinateInv x *
        (realPoly (rowD P N r)).eval (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ P.h N * realCoordinateInv x ^ (P.C N - 1) *
        ((x ^ (-rowOffset P N r) - x ^ rowOffset P N r) / 2) := by
  rw [rowD_realCoordinateInv hP hN hr hx hx0]
  calc
    _ = (1 - realCoordinateInv x) ^ P.h N * realCoordinateInv x ^ (P.C N - 1) *
        (((Int.sign (rowOffset P N r) : ℝ) *
          ((x⁻¹) ^ rowDistance P N r - x ^ rowDistance P N r)) / 2) := by ring
    _ = _ := by rw [rowDistance, sheet_natAbs_difference]

theorem realRowAmplitude_sheet {P : Parameters} (hP : Admissible P) {N r : ℕ} (hN : 0 < N) (hr : r < P.n N)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    realRowAmplitude P N r (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ P.h N * realCoordinateInv x ^ (P.C N - 1) *
        (if x < 0 then
          (1 / 2 : ℝ) * x ^ (-rowOffset P N r) + (1 / 2 : ℝ) * x ^ rowOffset P N r
        else
          -(1 / 4 : ℝ) * x ^ (-rowOffset P N r) + (5 / 4 : ℝ) * x ^ rowOffset P N r) := by
  by_cases hn : x < 0
  · have ht : realCoordinateInv x < 0 := by
      unfold realCoordinateInv
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hn) (by positivity)
    rw [realRowAmplitude_of_nonpos P N r ht.le, rowP_realCoordinateInv_signed hP hN hr hx0, ite_eq_left hn]
    ring
  · have hp : 0 < x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx0)
    have ht : 0 < realCoordinateInv x := by
      unfold realCoordinateInv
      exact div_pos (mul_pos (by norm_num) hp) (by positivity)
    rw [realRowAmplitude, ite_eq_left ht, rowP_realCoordinateInv_signed hP hN hr hx0,
      rowD_realCoordinateInv_signed hP hN hr hx hx0, ite_eq_right hn]
    ring

end

section

open Set
open scoped BigOperators

def realSheetDeterminant (P : Parameters) (N : ℕ) (x : Fin (P.n N) → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun r i : Fin (P.n N) =>
    if x i < 0 then
      (1 / 2 : ℝ) * (x i) ^ (-rowOffset P N r.val) +
        (1 / 2 : ℝ) * (x i) ^ rowOffset P N r.val
    else
      -(1 / 4 : ℝ) * (x i) ^ (-rowOffset P N r.val) +
        (5 / 4 : ℝ) * (x i) ^ rowOffset P N r.val))

theorem realRowAmplitude_det_eq_sheet {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (x : Fin (P.n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    Matrix.det (Matrix.of (fun r i : Fin (P.n N) =>
      realRowAmplitude P N r.val (realCoordinateInv (x i)))) =
        realSheetDeterminant P N x *
          ∏ i : Fin (P.n N), realCoordinateInv (x i) ^ (P.C N - 1) *
            (1 - realCoordinateInv (x i)) ^ P.h N := by
  classical
  let weight : Fin (P.n N) → ℝ := fun i =>
    realCoordinateInv (x i) ^ (P.C N - 1) * (1 - realCoordinateInv (x i)) ^ P.h N
  let A : Matrix (Fin (P.n N)) (Fin (P.n N)) ℝ := Matrix.of (fun r i =>
    if x i < 0 then
      (1 / 2 : ℝ) * (x i) ^ (-rowOffset P N r.val) +
        (1 / 2 : ℝ) * (x i) ^ rowOffset P N r.val
    else
      -(1 / 4 : ℝ) * (x i) ^ (-rowOffset P N r.val) +
        (5 / 4 : ℝ) * (x i) ^ rowOffset P N r.val)
  have hmatrix :
      Matrix.of (fun r i : Fin (P.n N) => realRowAmplitude P N r.val (realCoordinateInv (x i))) =
        Matrix.of (fun r i : Fin (P.n N) => weight i * A r i) := by
    funext r i
    change realRowAmplitude P N r.val (realCoordinateInv (x i)) = weight i * A r i
    rw [realRowAmplitude_sheet hP hN r.isLt (hx i) (hx0 i)]
    dsimp only [weight, A, Matrix.of_apply]
    ring
  rw [hmatrix, Matrix.det_mul_row]
  change (∏ i : Fin (P.n N), weight i) * realSheetDeterminant P N x =
    realSheetDeterminant P N x * (∏ i : Fin (P.n N), weight i)
  exact mul_comm _ _

end

section

open scoped BigOperators

end
end
end CatalanMeasure.Parametric
