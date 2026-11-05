module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Submission.CatalanMeasure.DeltaPoly

@[expose] public section

/-!
# Lemma 1: `deg Δ_N ≤ 44 N`

Row `r` of the coefficient matrix `L` depends only on `rowP N r`, which depends only on
`|r - g|`.  So rows `r` and `2g - r` of `L` agree for `r < g`.  Subtracting row `r` from row
`2g - r` (a unipotent lower-triangular change of rows, determinant `1`) kills `g` rows of `L`,
and a determinant of `X • A + B` whose `A` has only `n - g` nonzero rows has degree at most
`n - g = 44 N`.
-/

open Polynomial Matrix

namespace OAI.InternalCatalan

/-- Degree of `det (X • A + B)` when `A` vanishes outside the rows `S`. -/
theorem natDegree_det_X_smul_add_le_of_rows {m R : Type*} [Fintype m] [DecidableEq m]
    [CommRing R] (A B : Matrix m m R) (S : Finset m) (hA : ∀ i, i ∉ S → ∀ j, A i j = 0) :
    natDegree (det ((X : R[X]) • A.map C + B.map C)) ≤ S.card := by
  rw [det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro σ
  calc
    natDegree (Equiv.Perm.sign σ • ∏ i : m, ((X : R[X]) • A.map C + B.map C) (σ i) i) ≤
        natDegree (∏ i : m, ((X : R[X]) • A.map C + B.map C) (σ i) i) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with sg | sg
      · rw [sg, one_smul]
      · rw [sg, Units.neg_smul, one_smul, natDegree_neg]
    _ ≤ ∑ i : m, natDegree (((X : R[X]) • A.map C + B.map C) (σ i) i) :=
      natDegree_prod_le (Finset.univ : Finset m)
        fun i : m => ((X : R[X]) • A.map C + B.map C) (σ i) i
    _ ≤ ∑ i : m, (if σ i ∈ S then 1 else 0) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with h
      · dsimp only [Matrix.add_apply, Matrix.smul_apply, map_apply, smul_eq_mul]
        compute_degree
      · simp [hA (σ i) h]
    _ = S.card := by
      rw [Equiv.sum_comp σ (fun j => if j ∈ S then 1 else 0)]
      simp

theorem rowDistance_reflect {N r : ℕ} (hr : r ≤ 2 * g N) :
    rowDistance N (2 * g N - r) = rowDistance N r := by
  unfold rowDistance rowOffset
  rw [Int.natAbs_eq_natAbs_iff]
  right
  push_cast [Nat.cast_sub hr]
  ring

theorem filteredCatalanCoeffRat_reflect {N r : ℕ} (hr : r ≤ 2 * g N) (k : ℕ) :
    filteredCatalanCoeffRat N (2 * g N - r) k = filteredCatalanCoeffRat N r k := by
  unfold filteredCatalanCoeffRat rawCatalanCoeffRat rowP
  rw [rowDistance_reflect hr]

/-- `P i j = 1` exactly when `j < g` and `i = 2g - j`. -/
noncomputable def reflectMatrix (N : ℕ) : Matrix (Fin (n N)) (Fin (n N)) ℚ :=
  Matrix.of fun i j => if j.val < g N ∧ i.val = 2 * g N - j.val then 1 else 0

theorem det_one_sub_reflectMatrix (N : ℕ) : (1 - reflectMatrix N).det = 1 := by
  have hlt : (1 - reflectMatrix N).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    simp only [Matrix.sub_apply, reflectMatrix, Matrix.of_apply]
    rw [Matrix.one_apply_ne (ne_of_lt hij')]
    have : ¬ (j.val < g N ∧ i.val = 2 * g N - j.val) := by
      have := Fin.lt_def.mp hij'
      omega
    simp [this]
  rw [Matrix.det_of_lowerTriangular _ hlt]
  apply Finset.prod_eq_one
  intro i _
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, reflectMatrix, Matrix.of_apply]
  have : ¬ (i.val < g N ∧ i.val = 2 * g N - i.val) := by omega
  simp [this]

/-- The rows outside `(g, 2g]`. -/
def keptRows (N : ℕ) : Finset (Fin (n N)) :=
  Finset.univ.filter fun i => ¬ (g N < i.val ∧ i.val ≤ 2 * g N)

theorem keptRows_card (N : ℕ) : (keptRows N).card = 44 * N := by
  have hdrop : (Finset.univ.filter fun i : Fin (n N) => g N < i.val ∧ i.val ≤ 2 * g N).card =
      g N := by
    have h := Finset.card_bij (s := Finset.univ.filter fun i : Fin (n N) =>
        g N < i.val ∧ i.val ≤ 2 * g N) (t := Finset.Ioc (g N) (2 * g N))
      (fun i _ => i.val)
      (by intro a ha; simpa using ha)
      (by intro a _ b _ hab; exact Fin.ext hab)
      (by
        intro x hx
        simp only [Finset.mem_Ioc] at hx
        refine ⟨⟨x, by unfold n g at *; omega⟩, by simpa using hx, rfl⟩)
    rw [h, Nat.card_Ioc]
    omega
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n N)))) (fun i : Fin (n N) => g N < i.val ∧ i.val ≤ 2 * g N)
  rw [hdrop, Finset.card_univ, Fintype.card_fin] at hsum
  unfold keptRows
  unfold n g at hsum ⊢
  omega

theorem reflect_mul_catalan_row_eq_zero {N : ℕ} (i : Fin (n N)) (hi : i ∉ keptRows N)
    (k : Fin (n N)) : ((1 - reflectMatrix N) * measureCatalanMatrix N) i k = 0 := by
  simp only [keptRows, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
  have hj0 : 2 * g N - i.val < n N := by unfold n g at *; omega
  obtain ⟨j0, hj0v⟩ : ∃ j0 : Fin (n N), j0.val = 2 * g N - i.val := ⟨⟨_, hj0⟩, rfl⟩
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_apply,
    Finset.sum_eq_single j0]
  · simp only [reflectMatrix, measureCatalanMatrix, Matrix.of_apply]
    have hcond : j0.val < g N ∧ i.val = 2 * g N - j0.val := by omega
    rw [if_pos hcond, one_mul]
    have hr : j0.val ≤ 2 * g N := by omega
    rw [hcond.2, filteredCatalanCoeffRat_reflect hr]
    ring
  · intro j _ hj
    simp only [reflectMatrix, Matrix.of_apply]
    have : ¬ (j.val < g N ∧ i.val = 2 * g N - j.val) := by
      intro h
      apply hj
      ext
      omega
    rw [if_neg this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Lemma 1.**  `deg Δ_N ≤ 44 N`. -/
theorem natDegree_deltaPoly_le_44 (N : ℕ) : (deltaPoly N).natDegree ≤ 44 * N := by
  set E := 1 - reflectMatrix N with hE
  have hdetE : det (E.map C) = (1 : ℚ[X]) := by
    have h := RingHom.map_det (C : ℚ →+* ℚ[X]) E
    rw [RingHom.mapMatrix_apply] at h
    rw [← h, hE, det_one_sub_reflectMatrix, map_one]
  have hM : E.map C * ((X : ℚ[X]) • (measureCatalanMatrix N).map C + (measureBaseMatrix N).map C) =
      (X : ℚ[X]) • (E * measureCatalanMatrix N).map C + (E * measureBaseMatrix N).map C := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.map_mul, Matrix.map_mul]
  have hdelta : deltaPoly N =
      det ((X : ℚ[X]) • (E * measureCatalanMatrix N).map C + (E * measureBaseMatrix N).map C) := by
    rw [← hM, det_mul, hdetE, one_mul]
    rfl
  rw [hdelta, ← keptRows_card N]
  exact natDegree_det_X_smul_add_le_of_rows _ _ _
    (fun i hi k => reflect_mul_catalan_row_eq_zero i hi k)

end OAI.InternalCatalan
