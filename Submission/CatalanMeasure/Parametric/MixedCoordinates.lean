module
public import Submission.CatalanMeasure.Parametric.MixedMajorant
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset Set OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem paramRowNodeWeight_coordinate (P : Parameters) (N : ℕ) (x : ℝ) :
    paramRowNodeWeight P N x = (2 : ℝ) ^ (P.C N - 1) * (|x| ^ (P.C N - 1) *
      (1 - x) ^ (2 * P.h N)) / (1 + x ^ 2) ^ (P.C N - 1 + P.h N) := by
  unfold paramRowNodeWeight
  rw [energy_row_weight_coordinate]
  ring

theorem param_quadratic_cancel {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) {p : ℕ} (hp : 1 ≤ p) (x : ℝ) :
    (1 + x ^ 2) ^ p / ((1 + x ^ 2) ^ (p - 1) * (1 + x ^ 2) ^ (P.C N - 1 + P.h N)) =
      1 / (1 + x ^ 2) ^ (P.H N - 2) := by
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (realCoordinateInv_denominator_pos x)
  have he : (p - 1) + (P.C N - 1 + P.h N) = p + (P.H N - 2) := by
    have hn := n_pos hP hN
    have hb : 0<P.b N :=Nat.mul_pos hP.2.1 hN
    have hq : 0<P.q N :=Nat.mul_pos hP.2.2.1 hN
    unfold Parameters.H Parameters.C Parameters.L at *
    omega
  rw [← pow_add, he, pow_add]
  field_simp

theorem paramPinPrincipal_coordinate {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) {p : ℕ} (x s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    paramPinPrincipal P N x s =
      (2 : ℝ) ^ (p * (P.C N - 1) + p.choose 2) *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (x j - x i)| *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| ^ 2 *
        (∏ i : Fin p, ∏ j ∈ Ioi i, (1 - x i * x j)) *
        (∏ j : Fin p, (s j ^ P.b N * (1 - s j) ^ P.q N)) *
        (∏ i : Fin p, (|x i| ^ (P.C N - 1) * (1 - x i) ^ (2 * P.h N))) /
        ((∏ i : Fin p, ∏ j : Fin p, (1 - 2 * x i * s j + x i ^ 2)) *
          (∏ i : Fin p, (1 + x i ^ 2) ^ (P.H N - 2))) := by
  have hcancel : (∏ i : Fin p, (1 + x i ^ 2) ^ p) /
      ((∏ i : Fin p, (1 + x i ^ 2) ^ (p - 1)) *
        (∏ i : Fin p, (1 + x i ^ 2) ^ (P.C N - 1 + P.h N))) =
      1 / (∏ i : Fin p, (1 + x i ^ 2) ^ (P.H N - 2)) := by
    rw [← prod_mul_distrib, ← prod_div_distrib]
    rw [show (1 : ℝ) / (∏ i : Fin p, (1 + x i ^ 2) ^ (P.H N - 2)) =
      ∏ i : Fin p, 1 / (1 + x i ^ 2) ^ (P.H N - 2) by
        rw [prod_div_distrib, prod_const_one]]
    apply prod_congr rfl
    intro i _
    exact param_quadratic_cancel hP hN (Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne') (x i)
  unfold paramPinPrincipal
  simp_rw [paramRowNodeWeight_coordinate]
  rw [abs_vandermonde_realCoordinateInv x hx, prod_realCoordinateInv_kernel]
  simp only [prod_div_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  calc _ = ((2 : ℝ) ^ (P.C N - 1)) ^ p * (2 : ℝ) ^ p.choose 2 *
          |∏ i : Fin p, ∏ j ∈ Ioi i, (x j - x i)| *
          |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| ^ 2 *
          (∏ i : Fin p, ∏ j ∈ Ioi i, (1 - x i * x j)) *
          (∏ j : Fin p, (s j ^ P.b N * (1 - s j) ^ P.q N)) *
          ((∏ i : Fin p, |x i| ^ (P.C N - 1)) * ∏ i : Fin p, (1 - x i) ^ (2 * P.h N)) /
          (∏ i : Fin p, ∏ j : Fin p, (1 - 2 * x i * s j + x i ^ 2)) *
        ((∏ i : Fin p, (1 + x i ^ 2) ^ p) /
          ((∏ i : Fin p, (1 + x i ^ 2) ^ (p - 1)) *
            (∏ i : Fin p, (1 + x i ^ 2) ^ (P.C N - 1 + P.h N)))) := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, prod_mul_distrib]
        ring
    _ = _ := by
        rw [hcancel, pow_add, ← pow_mul, mul_comm (P.C N - 1) p]
        simp only [div_eq_mul_inv, mul_inv_rev, prod_mul_distrib]
        ring


end
end CatalanMeasure.Parametric
