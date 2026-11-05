module
public import Submission.CatalanMeasure.Parametric.Polynomial
public import Submission.CatalanMeasure.Degree
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial Matrix
noncomputable section

def reflectMatrix (P : Parameters) (N : ℕ) : Matrix (Fin (P.n N)) (Fin (P.n N)) ℚ :=
  Matrix.of fun i j => if j.val < P.g N ∧ i.val = 2 * P.g N - j.val then 1 else 0

theorem det_one_sub_reflectMatrix (P : Parameters) (N : ℕ) : (1 - reflectMatrix P N).det = 1 := by
  have hlt : (1 - reflectMatrix P N).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    simp only [Matrix.sub_apply, reflectMatrix, Matrix.of_apply]
    rw [Matrix.one_apply_ne (ne_of_lt hij')]
    have : ¬ (j.val < P.g N ∧ i.val = 2 * P.g N - j.val) := by
      have := Fin.lt_def.mp hij'
      omega
    simp [this]
  rw [Matrix.det_of_lowerTriangular _ hlt]
  apply Finset.prod_eq_one
  intro i _
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, reflectMatrix, Matrix.of_apply]
  have : ¬ (i.val < P.g N ∧ i.val = 2 * P.g N - i.val) := by omega
  simp [this]

def keptRows (P : Parameters) (N : ℕ) : Finset (Fin (P.n N)) :=
  Finset.univ.filter fun i => ¬ (P.g N < i.val ∧ i.val ≤ 2 * P.g N)

theorem keptRows_card {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) :
    (keptRows P N).card = P.n N - P.g N := by
  have hg := two_g_lt_n hP hN
  have hdrop : (Finset.univ.filter fun i : Fin (P.n N) => P.g N < i.val ∧ i.val ≤ 2 * P.g N).card =
      P.g N := by
    have h := Finset.card_bij (s := Finset.univ.filter fun i : Fin (P.n N) =>
        P.g N < i.val ∧ i.val ≤ 2 * P.g N) (t := Finset.Ioc (P.g N) (2 * P.g N))
      (fun i _ => i.val)
      (by intro a ha; simpa using ha)
      (by intro a _ b _ hab; exact Fin.ext hab)
      (by
        intro x hx
        simp only [Finset.mem_Ioc] at hx
        refine ⟨⟨x, by omega⟩, by simpa using hx, rfl⟩)
    rw [h, Nat.card_Ioc]
    omega
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (P.n N))))
    (fun i : Fin (P.n N) => P.g N < i.val ∧ i.val ≤ 2 * P.g N)
  rw [hdrop, Finset.card_univ, Fintype.card_fin] at hsum
  unfold keptRows
  omega

theorem reflect_mul_catalan_row_eq_zero {P : Parameters} (hP : Admissible P) {N : ℕ}
    (hN : 0 < N) (i : Fin (P.n N)) (hi : i ∉ keptRows P N) (k : Fin (P.n N)) :
    ((1 - reflectMatrix P N) * measureCatalanMatrix P N) i k = 0 := by
  have hg := two_g_lt_n hP hN
  simp only [keptRows, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
  have hj0 : 2 * P.g N - i.val < P.n N := by omega
  obtain ⟨j0, hj0v⟩ : ∃ j0 : Fin (P.n N), j0.val = 2 * P.g N - i.val := ⟨⟨_, hj0⟩, rfl⟩
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_apply,
    Finset.sum_eq_single j0]
  · simp only [reflectMatrix, measureCatalanMatrix, Matrix.of_apply]
    have hcond : j0.val < P.g N ∧ i.val = 2 * P.g N - j0.val := by omega
    rw [if_pos hcond, one_mul]
    have hr : j0.val ≤ 2 * P.g N := by omega
    rw [hcond.2, filteredCatalanCoeffRat_reflect P hr]
    ring
  · intro j _ hj
    simp only [reflectMatrix, Matrix.of_apply]
    have : ¬ (j.val < P.g N ∧ i.val = 2 * P.g N - j.val) := by
      intro h
      apply hj
      ext
      omega
    rw [if_neg this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem natDegree_deltaPoly_le_ng {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) :
    (deltaPoly P N).natDegree ≤ P.n N - P.g N := by
  set E := 1 - reflectMatrix P N with hE
  have hdetE : det (E.map C) = (1 : ℚ[X]) := by
    have h := RingHom.map_det (C : ℚ →+* ℚ[X]) E
    rw [RingHom.mapMatrix_apply] at h
    rw [← h, hE, det_one_sub_reflectMatrix, map_one]
  have hM : E.map C * ((X : ℚ[X]) • (measureCatalanMatrix P N).map C + (measureBaseMatrix P N).map C) =
      (X : ℚ[X]) • (E * measureCatalanMatrix P N).map C + (E * measureBaseMatrix P N).map C := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.map_mul, Matrix.map_mul]
  have hdelta : deltaPoly P N =
      det ((X : ℚ[X]) • (E * measureCatalanMatrix P N).map C + (E * measureBaseMatrix P N).map C) := by
    rw [← hM, det_mul, hdetE, one_mul]
    rfl
  rw [hdelta, ← keptRows_card hP hN]
  exact OAI.InternalCatalan.natDegree_det_X_smul_add_le_of_rows _ _ _
    (fun i hi k => reflect_mul_catalan_row_eq_zero hP hN i hi k)

theorem natDegree_deltaPoly_proposed_le (N : ℕ) : (deltaPoly proposed N).natDegree ≤ 89 * N := by
  by_cases hN : N = 0
  · subst N
    simpa [Parameters.n, proposed] using natDegree_deltaPoly_le proposed 0
  · have h := natDegree_deltaPoly_le_ng proposed_admissible (Nat.pos_of_ne_zero hN)
    rw [proposed_degree] at h
    exact h

end
end CatalanMeasure.Parametric
