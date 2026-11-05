module

public import Submission.CatalanMeasure.Parametric.MarkedSheetExpansion
public import Submission.CatalanMeasure.Parametric.RealSheetBounds

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Set Finset
open scoped BigOperators

noncomputable section

/-- Node-first Laurent matrix: marked nodes use the original polynomial P row,
not the positive actual amplitude. -/
def markedLaurentMatrix {n : ℕ} (g : ℕ) (x : Fin n → ℝ)
    (marked : Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i r => if marked i then
    (1 / 2 : ℝ) * x i ^ ((g : ℤ) - r) + (1 / 2 : ℝ) * x i ^ ((r : ℤ) - g)
    else actualLaurentEntry g r (x i)

theorem marked_laurent_hadamard_sqrt {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) (x : Fin (P.n N) → ℝ) (marked : Fin (P.n N) → Bool)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    |(markedLaurentMatrix (P.g N) x marked).det| ≤
      (3 / 2 : ℝ) ^ P.n N * Real.sqrt (P.n N : ℝ) ^ P.n N /
        2 ^ ((P.n N).choose 2) *
        ∏ i, (Real.sqrt (1 + x i ^ 2) ^ (P.n N - 1) *
          |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) := by
  classical
  let V := fun (i : Fin (P.n N)) (b : Bool) (r : Fin (P.n N)) =>
    realSheetNode (x i) b ^ ((r : ℤ) - P.g N)
  let c := fun (i : Fin (P.n N)) (b : Bool) =>
    if marked i then (1 / 2 : ℝ) else realSheetCoefficient (x i) b
  let C : ℝ := Real.sqrt (P.n N : ℝ) ^ P.n N / 2 ^ ((P.n N).choose 2)
  let W := fun i : Fin (P.n N) =>
    Real.sqrt (1 + x i ^ 2) ^ (P.n N - 1) *
      |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))
  have hm : markedLaurentMatrix (P.g N) x marked =
      Matrix.of fun i r => ∑ b : Bool, c i b * V i b r := by
    ext i r
    cases hmi : marked i <;> by_cases hxi : x i < 0 <;>
      simp [markedLaurentMatrix, c, V, hmi, realSheetCoefficient,
        realSheetNode, actualLaurentEntry, hxi, zpow_sub₀ (hx0 i),
        zpow_natCast] <;> ring
  have hbound (t : Fin (P.n N) → Bool) :
      |(Matrix.of fun i r => V i (t i) r).det| ≤ C * ∏ i, W i := by
    let z := fun i => realSheetNode (x i) (t i)
    have hz (i : Fin (P.n N)) : z i ≠ 0 := by
      dsimp [z, realSheetNode]
      split_ifs
      · exact hx0 i
      · exact inv_ne_zero (hx0 i)
    have ht : (Matrix.of fun i r => V i (t i) r) =
        (Matrix.of fun r i : Fin (P.n N) => z i ^ ((r : ℤ) - P.g N)).transpose := rfl
    rw [ht, Matrix.det_transpose]
    apply (laurent_monomial_det_abs_le (P.g N) z hz).trans
    apply mul_le_mul_of_nonneg_left
    · apply prod_le_prod₀
      · intro i _
        exact mul_nonneg (abs_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
      · intro i _
        simpa only [z, W, realSheetNode] using
          sheet_choice_weight_le hP hN (hx i) (hx0 i) (t i)
    · positivity
  have hcoef (i : Fin (P.n N)) : (∑ b : Bool, |c i b|) ≤ 3 / 2 := by
    cases hmi : marked i <;> by_cases hxi : x i < 0 <;>
      norm_num [c, hmi, realSheetCoefficient, hxi]
  rw [hm]
  have hh := abs_det_binary_rows_le V c (show 0 ≤ C * ∏ i, W i by
    dsimp [C, W]; positivity) hbound
  calc
    _ ≤ (C * ∏ i, W i) * ∏ i, (∑ b : Bool, |c i b|) := hh
    _ ≤ (C * ∏ i, W i) * (3 / 2 : ℝ) ^ P.n N := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [C, W]; positivity)
      calc
        _ ≤ ∏ _i : Fin (P.n N), (3 / 2 : ℝ) :=
          prod_le_prod₀ (fun i _ => sum_nonneg fun _ _ => abs_nonneg _) (fun i _ => hcoef i)
        _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin]
    _ = _ := by dsimp [C, W]; ring

theorem marked_laurent_hadamard {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) (x : Fin (P.n N) → ℝ) (marked : Fin (P.n N) → Bool)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    |(markedLaurentMatrix (P.g N) x marked).det| ≤
      (3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2) /
        2 ^ ((P.n N).choose 2) *
        ∏ i, ((1 + x i ^ 2) ^ (((P.n N : ℝ) - 1) / 2) *
          |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) := by
  have hdim : 1 ≤ P.n N := Nat.succ_le_iff.mpr (n_pos hP hN)
  have hcast : ((P.n N - 1 : ℕ) : ℝ) = (P.n N : ℝ) - 1 := by
    rw [Nat.cast_sub hdim, Nat.cast_one]
  have hhead : Real.sqrt (P.n N : ℝ) ^ P.n N = (P.n N : ℝ) ^ ((P.n N : ℝ) / 2) := by
    symm
    simpa only [Real.rpow_natCast] using
      Real.rpow_div_two_eq_sqrt (P.n N : ℝ) (Nat.cast_nonneg (P.n N))
  have hrow (i : Fin (P.n N)) : Real.sqrt (1 + x i ^ 2) ^ (P.n N - 1) =
      (1 + x i ^ 2) ^ (((P.n N : ℝ) - 1) / 2) := by
    symm
    have h := Real.rpow_div_two_eq_sqrt ((P.n N - 1 : ℕ) : ℝ)
      (by positivity : (0 : ℝ) ≤ 1 + x i ^ 2)
    rw [Real.rpow_natCast] at h
    simpa only [hcast] using h
  simpa only [hhead, hrow] using marked_laurent_hadamard_sqrt hP hN x marked hx hx0

end
end CatalanMeasure.Parametric
