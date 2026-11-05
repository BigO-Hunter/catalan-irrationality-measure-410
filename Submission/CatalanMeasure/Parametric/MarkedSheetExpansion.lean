module

public import Submission.CatalanMeasure.DetExpansion
public import Submission.CatalanMeasure.Parametric.GroupedLaurentSheet

/-!
# Expanding marked P-only rows into actual and near sheets

All determinant terms keep the actual free rows. The total absolute coefficient
cost is at most five for each marked row and one for every free row.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open Finset
open scoped BigOperators

noncomputable section

theorem det_binary_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Bool → ι → ℝ) (c : ι → Bool → ℝ) :
    (Matrix.of fun i j => ∑ b : Bool, c i b * V i b j).det =
      ∑ t : ι → Bool, (∏ i, c i (t i)) * (Matrix.of fun i j => V i (t i) j).det := by
  have hm := (Matrix.detRowAlternating (R := ℝ) (n := ι)).toMultilinearMap.map_sum
    (fun i b => c i b • V i b)
  rw [AlternatingMap.coe_multilinearMap] at hm
  have he : (Matrix.of fun i j => ∑ b : Bool, c i b * V i b j) =
      fun i => ∑ b : Bool, c i b • V i b := by
    funext i j
    simp only [Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  change Matrix.detRowAlternating _ = _
  rw [hm]
  apply sum_congr rfl
  intro t _
  have hs := (Matrix.detRowAlternating (R := ℝ) (n := ι)).toMultilinearMap.map_smul_univ
    (fun i => c i (t i)) (fun i => V i (t i))
  rw [AlternatingMap.coe_multilinearMap] at hs
  exact hs

theorem abs_det_binary_rows_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Bool → ι → ℝ) (c : ι → Bool → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hV : ∀ t : ι → Bool, |(Matrix.of fun i j => V i (t i) j).det| ≤ M) :
    |(Matrix.of fun i j => ∑ b : Bool, c i b * V i b j).det| ≤
      M * ∏ i, (∑ b : Bool, |c i b|) := by
  rw [det_binary_rows]
  calc
    _ ≤ ∑ t : ι → Bool, |(∏ i, c i (t i)) *
        (Matrix.of fun i j => V i (t i) j).det| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : ι → Bool, M * ∏ i, |c i (t i)| := by
      apply sum_le_sum
      intro t _
      rw [abs_mul, abs_prod, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hV t) (prod_nonneg fun _ _ => abs_nonneg _)
    _ = _ := by
      rw [← mul_sum]
      exact congrArg (fun z => M * z) (Fintype.prod_sum (fun (i : ι) (b : Bool) => |c i b|)).symm

def markedActualCoefficient (marked : Bool) (x : ℝ) : ℝ :=
  if marked && decide (0 ≤ x) then -2 else 1

def markedNearCoefficient (marked : Bool) (x : ℝ) : ℝ :=
  if marked && decide (0 ≤ x) then 3 else 0

theorem marked_laurent_decomposition (marked : Bool) (g r : ℕ) (x : ℝ) :
    (if marked then
      (1 / 2 : ℝ) * x ^ ((g : ℤ) - r) + (1 / 2 : ℝ) * x ^ ((r : ℤ) - g)
    else actualLaurentEntry g r x) =
      markedActualCoefficient marked x * actualLaurentEntry g r x +
        markedNearCoefficient marked x * x ^ ((r : ℤ) - g) := by
  cases marked <;> by_cases hx : x < 0 <;>
    simp [actualLaurentEntry, markedActualCoefficient, markedNearCoefficient,
      hx, show (0 ≤ x) = (¬x < 0) from propext not_lt.symm] <;> ring

theorem marked_coefficient_cost (marked : Bool) (x : ℝ) :
    |markedActualCoefficient marked x| + |markedNearCoefficient marked x| ≤
      if marked then 5 else 1 := by
  cases marked <;> by_cases hx : 0 ≤ x <;>
    norm_num [markedActualCoefficient, markedNearCoefficient, hx]

theorem marked_laurent_det_bound {n g : ℕ} (x : Fin n → ℝ) (marked : Fin n → Bool)
    {M : ℝ} (hM : 0 ≤ M)
    (hV : ∀ t : Fin n → Bool,
      |(Matrix.of fun i r : Fin n => if t i && marked i && decide (0 ≤ x i) then x i ^ ((r : ℤ) - g)
        else actualLaurentEntry g r (x i)).det| ≤ M) :
    |(Matrix.of fun i r : Fin n => if marked i then
        (1 / 2 : ℝ) * x i ^ ((g : ℤ) - r) + (1 / 2 : ℝ) * x i ^ ((r : ℤ) - g)
      else actualLaurentEntry g r (x i)).det| ≤
      M * ∏ i, (if marked i then (5 : ℝ) else 1) := by
  let V : Fin n → Bool → Fin n → ℝ := fun i t r =>
    if t && marked i && decide (0 ≤ x i) then x i ^ ((r : ℤ) - g)
      else actualLaurentEntry g r (x i)
  let c : Fin n → Bool → ℝ := fun i t =>
    if t then markedNearCoefficient (marked i) (x i)
      else markedActualCoefficient (marked i) (x i)
  have hm : (Matrix.of fun i r : Fin n => if marked i then
        (1 / 2 : ℝ) * x i ^ ((g : ℤ) - r) + (1 / 2 : ℝ) * x i ^ ((r : ℤ) - g)
      else actualLaurentEntry g r (x i)) =
      Matrix.of (fun i r => ∑ b : Bool, c i b * V i b r) := by
    ext i r
    have hd := marked_laurent_decomposition (marked i) g r (x i)
    cases hmi : marked i <;> by_cases hx : 0 ≤ x i <;>
      simpa [V, c, hmi, hx, markedActualCoefficient, markedNearCoefficient, add_comm] using hd
  rw [hm]
  apply (abs_det_binary_rows_le V c hM hV).trans
  apply mul_le_mul_of_nonneg_left _ hM
  apply prod_le_prod₀
  · intro i _
    exact sum_nonneg fun _ _ => abs_nonneg _
  · intro i _
    simpa [c, add_comm] using marked_coefficient_cost (marked i) (x i)

end

end CatalanMeasure.Parametric
