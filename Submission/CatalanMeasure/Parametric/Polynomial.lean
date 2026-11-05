module
public import Submission.CatalanMeasure.Parametric.Parameters
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Submission.OAI.NumberTheory.Catalan.Determinants.RealColumnDeterminant
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial Matrix Finset
open scoped BigOperators
noncomputable section

def rowP (P : Parameters) (N r : ℕ) : ℤ[X] :=
  (1 - X) ^ P.h N * OAI.InternalCatalan.reversedRow (P.C N)
    (Chebyshev.T ℤ (rowDistance P N r : ℤ))

def rowD (P : Parameters) (N r : ℕ) : ℤ[X] :=
  C (Int.sign (rowOffset P N r)) * (1 - X) ^ P.h N *
    OAI.InternalCatalan.reversedRow (P.C N)
      (Chebyshev.U ℤ ((rowDistance P N r : ℤ) - 1))

def rawEntryRat (P : Parameters) (z : ℚ) (N r j : ℕ) : ℚ :=
  (∑ i ∈ range (P.H N), ((rowP P N r).coeff i : ℚ) *
    (OAI.InternalCatalan.momentRat i j + 4 * z *
      OAI.InternalCatalan.centralCoeffKernel ((i : ℤ) - j))) -
  (3 / 2 : ℚ) * ∑ i ∈ range (P.H N), ((rowD P N r).coeff i : ℚ) *
    OAI.InternalCatalan.zetaRat i j

def rawCatalanCoeffRat (P : Parameters) (N r j : ℕ) : ℚ :=
  ∑ i ∈ range (P.H N), ((rowP P N r).coeff i : ℚ) *
    (4 * OAI.InternalCatalan.centralCoeffKernel ((i : ℤ) - j))

theorem rawEntryRat_affine (P : Parameters) (z : ℚ) (N r j : ℕ) :
    rawEntryRat P z N r j = rawEntryRat P 0 N r j + z * rawCatalanCoeffRat P N r j := by
  unfold rawEntryRat rawCatalanCoeffRat
  simp only [mul_zero, zero_mul, add_zero]
  have hs : (∑ i ∈ range (P.H N), ((rowP P N r).coeff i : ℚ) *
      (OAI.InternalCatalan.momentRat i j + 4 * z *
        OAI.InternalCatalan.centralCoeffKernel ((i : ℤ) - j))) =
      (∑ i ∈ range (P.H N), ((rowP P N r).coeff i : ℚ) * OAI.InternalCatalan.momentRat i j) +
      z * ∑ i ∈ range (P.H N), ((rowP P N r).coeff i : ℚ) *
        (4 * OAI.InternalCatalan.centralCoeffKernel ((i : ℤ) - j)) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

def filterCoeffRat (P : Parameters) (N v : ℕ) : ℚ := (-1 : ℚ) ^ v * (P.q N).choose v

def filteredEntryRat (P : Parameters) (z : ℚ) (N r k : ℕ) : ℚ :=
  ∑ v ∈ range (P.q N + 1), filterCoeffRat P N v * rawEntryRat P z N r (P.b N + k + v)

def filteredCatalanCoeffRat (P : Parameters) (N r k : ℕ) : ℚ :=
  ∑ v ∈ range (P.q N + 1), filterCoeffRat P N v * rawCatalanCoeffRat P N r (P.b N + k + v)

theorem filteredEntryRat_affine (P : Parameters) (z : ℚ) (N r k : ℕ) :
    filteredEntryRat P z N r k = filteredEntryRat P 0 N r k + z * filteredCatalanCoeffRat P N r k := by
  unfold filteredEntryRat filteredCatalanCoeffRat
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  rw [rawEntryRat_affine]
  ring

def determinantRat (P : Parameters) (z : ℚ) (N : ℕ) : ℚ :=
  det (fun r k : Fin (P.n N) => filteredEntryRat P z N r.val k.val)

def measureBaseMatrix (P : Parameters) (N : ℕ) : Matrix (Fin (P.n N)) (Fin (P.n N)) ℚ :=
  Matrix.of fun r k => filteredEntryRat P 0 N r.val k.val

def measureCatalanMatrix (P : Parameters) (N : ℕ) : Matrix (Fin (P.n N)) (Fin (P.n N)) ℚ :=
  Matrix.of fun r k => filteredCatalanCoeffRat P N r.val k.val

def deltaPoly (P : Parameters) (N : ℕ) : ℚ[X] :=
  det ((X : ℚ[X]) • (measureCatalanMatrix P N).map C + (measureBaseMatrix P N).map C)

theorem natDegree_deltaPoly_le (P : Parameters) (N : ℕ) : (deltaPoly P N).natDegree ≤ P.n N := by
  have h := Polynomial.natDegree_det_X_add_C_le (measureCatalanMatrix P N) (measureBaseMatrix P N)
  rw [Fintype.card_fin] at h
  exact h

theorem deltaPoly_matrix_entry (P : Parameters) (N : ℕ) (r k : Fin (P.n N)) :
    ((X : ℚ[X]) • (measureCatalanMatrix P N).map C + (measureBaseMatrix P N).map C) r k =
      X * C (filteredCatalanCoeffRat P N r.val k.val) + C (filteredEntryRat P 0 N r.val k.val) := by
  simp [measureCatalanMatrix, measureBaseMatrix]

theorem eval_deltaPoly (P : Parameters) (z : ℚ) (N : ℕ) :
    (deltaPoly P N).eval z = determinantRat P z N := by
  have h := RingHom.map_det (evalRingHom z)
    ((X : ℚ[X]) • (measureCatalanMatrix P N).map C + (measureBaseMatrix P N).map C)
  rw [coe_evalRingHom] at h
  unfold deltaPoly determinantRat
  rw [h]
  congr 1
  ext r k
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, deltaPoly_matrix_entry, coe_evalRingHom]
  simp only [eval_add, eval_mul, eval_X, eval_C]
  rw [filteredEntryRat_affine P z]
  ring

theorem rowDistance_reflect (P : Parameters) {N r : ℕ} (hr : r ≤ 2 * P.g N) :
    rowDistance P N (2 * P.g N - r) = rowDistance P N r := by
  unfold rowDistance rowOffset
  rw [Int.natAbs_eq_natAbs_iff]
  right
  push_cast [Nat.cast_sub hr]
  ring

theorem filteredCatalanCoeffRat_reflect (P : Parameters) {N r : ℕ}
    (hr : r ≤ 2 * P.g N) (k : ℕ) :
    filteredCatalanCoeffRat P N (2 * P.g N - r) k = filteredCatalanCoeffRat P N r k := by
  unfold filteredCatalanCoeffRat rawCatalanCoeffRat rowP
  rw [rowDistance_reflect P hr]

end
end CatalanMeasure.Parametric
