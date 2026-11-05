module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Option

@[expose] public section

/-!
# Expanding `det (A + δ Φ β)` column by column

If every column of a perturbation is a combination `∑_a β_{a,k} Φ(·, a)` of `J` fixed
vectors, multilinearity of the determinant in the columns gives

  `det (A + δ Φ β) = ∑_{f : columns → Option atoms} (∏_k w_{f k, k}) det M_f`,

where `M_f` keeps column `k` of `A` when `f k = none` and uses `Φ(·, a)` when `f k = some a`,
and `w_{none,k} = 1`, `w_{some a, k} = δ β_{a,k}`.  If `|det M_f| ≤ M c ^ #{k | f k ≠ none}`
and `|β| ≤ B`, then `|det (A + δ Φ β) - det A| ≤ M ((1 + J |δ| B c) ^ n - 1)`.
-/

open Finset

namespace CatalanMeasure

variable {n J : ℕ}

/-- The matrix whose column `k` is `A`'s when `f k = none` and `Φ(·, a)` when `f k = some a`. -/
def atomMatrix (A : Matrix (Fin n) (Fin n) ℝ) (Φ : Fin n → Fin J → ℝ)
    (f : Fin n → Option (Fin J)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun r k => (f k).elim (A r k) (fun a => Φ r a)

/-- The weight of a choice in column `k`. -/
def atomWeight (β : Fin J → Fin n → ℝ) (δ : ℝ) (o : Option (Fin J)) (k : Fin n) : ℝ :=
  o.elim 1 (fun a => δ * β a k)

theorem det_add_atoms (A : Matrix (Fin n) (Fin n) ℝ) (Φ : Fin n → Fin J → ℝ)
    (β : Fin J → Fin n → ℝ) (δ : ℝ) :
    (Matrix.of fun r k => A r k + δ * ∑ a, Φ r a * β a k).det =
      ∑ f : Fin n → Option (Fin J),
        (∏ k, atomWeight β δ (f k) k) * (atomMatrix A Φ f).det := by
  classical
  let V : Fin n → Option (Fin J) → (Fin n → ℝ) := fun k o r =>
    (o.elim (A r k) (fun a => Φ r a))
  have hcol : (Matrix.of fun r k => A r k + δ * ∑ a, Φ r a * β a k).transpose =
      fun k => ∑ o : Option (Fin J), atomWeight β δ o k • V k o := by
    funext k r
    simp only [Matrix.transpose_apply, Matrix.of_apply, Fintype.sum_option, atomWeight, V,
      Option.elim, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul,
      mul_sum]
    congr 1
    apply sum_congr rfl
    intro a _
    ring
  rw [← Matrix.det_transpose, hcol]
  change Matrix.detRowAlternating (fun k => ∑ o : Option (Fin J), atomWeight β δ o k • V k o) = _
  have hms := (Matrix.detRowAlternating (R := ℝ) (n := Fin n)).toMultilinearMap.map_sum
    (fun k o => atomWeight β δ o k • V k o)
  rw [AlternatingMap.coe_multilinearMap] at hms
  rw [hms]
  apply sum_congr rfl
  intro f _
  have hsm := (Matrix.detRowAlternating (R := ℝ) (n := Fin n)).toMultilinearMap.map_smul_univ
    (fun k => atomWeight β δ (f k) k) (fun k => V k (f k))
  rw [AlternatingMap.coe_multilinearMap] at hsm
  rw [hsm, smul_eq_mul]
  congr 1
  change Matrix.det (fun k => V k (f k)) = _
  rw [← Matrix.det_transpose]
  rfl

/-- **Bound on the perturbation.** -/
theorem abs_det_add_atoms_sub_le (A : Matrix (Fin n) (Fin n) ℝ) (Φ : Fin n → Fin J → ℝ)
    (β : Fin J → Fin n → ℝ) (δ : ℝ) {M B c : ℝ} (hM : 0 ≤ M) (hB0 : 0 ≤ B)
    (hB : ∀ a k, |β a k| ≤ B) (hc : 0 ≤ c)
    (hD : ∀ f : Fin n → Option (Fin J),
      |(atomMatrix A Φ f).det| ≤ M * ∏ k, (f k).elim 1 (fun _ => c)) :
    |(Matrix.of fun r k => A r k + δ * ∑ a, Φ r a * β a k).det - A.det| ≤
      M * ((1 + J * (|δ| * B * c)) ^ n - 1) := by
  classical
  set y : ℝ := |δ| * B * c with hy
  have hy0 : 0 ≤ y := by positivity
  let u : Option (Fin J) → ℝ := fun o => o.elim 1 (fun _ => y)
  let T : (Fin n → Option (Fin J)) → ℝ := fun f =>
    (∏ k, atomWeight β δ (f k) k) * (atomMatrix A Φ f).det
  have hT : ∀ f, |T f| ≤ M * ∏ k, u (f k) := by
    intro f
    have hw : ∀ k, |atomWeight β δ (f k) k| * (f k).elim 1 (fun _ => c) ≤ u (f k) := by
      intro k
      rcases hfk : f k with _ | a
      · simp [atomWeight, u]
      · simp only [atomWeight, u, Option.elim, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hB a k) (abs_nonneg _)) hc
    calc |T f| = (∏ k, |atomWeight β δ (f k) k|) * |(atomMatrix A Φ f).det| := by
          simp only [T, abs_mul, abs_prod]
      _ ≤ (∏ k, |atomWeight β δ (f k) k|) * (M * ∏ k, (f k).elim 1 (fun _ => c)) :=
          mul_le_mul_of_nonneg_left (hD f) (prod_nonneg fun _ _ => abs_nonneg _)
      _ = M * ∏ k, (|atomWeight β δ (f k) k| * (f k).elim 1 (fun _ => c)) := by
          rw [prod_mul_distrib]
          ring
      _ ≤ M * ∏ k, u (f k) := by
          apply mul_le_mul_of_nonneg_left _ hM
          apply prod_le_prod₀
          · intro k _
            apply mul_nonneg (abs_nonneg _)
            rcases f k with _ | a
            · exact zero_le_one
            · exact hc
          · intro k _
            exact hw k
  let f₀ : Fin n → Option (Fin J) := fun _ => none
  have hT₀ : T f₀ = A.det := by
    simp only [T, f₀, atomWeight, Option.elim, prod_const_one, one_mul]
    congr 1
  have hsum : ∑ f : Fin n → Option (Fin J), ∏ k, u (f k) = (1 + J * y) ^ n := by
    rw [← Fintype.prod_sum (fun _ o => u o)]
    simp only [Fintype.sum_option, u, Option.elim, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, prod_const]
  have hu₀ : ∏ k, u (f₀ k) = 1 := by simp [u, f₀]
  rw [det_add_atoms A Φ β δ]
  change |∑ f, T f - A.det| ≤ _
  rw [← add_sum_erase _ _ (mem_univ f₀), hT₀, add_sub_cancel_left]
  calc |∑ f ∈ univ.erase f₀, T f| ≤ ∑ f ∈ univ.erase f₀, |T f| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ f ∈ univ.erase f₀, M * ∏ k, u (f k) := sum_le_sum fun f _ => hT f
    _ = M * (∑ f : Fin n → Option (Fin J), ∏ k, u (f k) - ∏ k, u (f₀ k)) := by
        rw [← mul_sum, ← sum_erase_add univ (fun f : Fin n → Option (Fin J) => ∏ k, u (f k)) (mem_univ f₀)]
        ring
    _ = M * ((1 + J * y) ^ n - 1) := by rw [hsum, hu₀]

/-- `(1 + t) ^ n ≤ exp (n t)`. -/
theorem one_add_pow_le_exp {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (1 + t) ^ n ≤ Real.exp (n * t) := by
  calc (1 + t) ^ n ≤ (Real.exp t) ^ n := by
        apply pow_le_pow_left₀ (by linarith)
        linarith [Real.add_one_le_exp t]
    _ = Real.exp (n * t) := by rw [← Real.exp_nat_mul]

end CatalanMeasure
