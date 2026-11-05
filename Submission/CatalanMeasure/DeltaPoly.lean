module

public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Submission.OAI.NumberTheory.Catalan.Polynomial.Rationality

@[expose] public section

/-!
# The Catalan determinant as a polynomial in the constant

OpenAI's rational matrix `filteredEntryRat z N r k` is affine in `z`
(`rawEntryRat_affine`).  So `z ↦ determinantRat z N` is the restriction of a polynomial
`deltaPoly N ∈ ℚ[X]` of degree at most `n N = 48 N`:

* `eval_deltaPoly`: `(deltaPoly N).eval z = determinantRat z N` for every rational `z`;
* `natDegree_deltaPoly_le`: `natDegree (deltaPoly N) ≤ n N`;
* `aeval_catalan_deltaPoly`: at `X = G` (Catalan's constant) the polynomial is OpenAI's real
  determinant `determinant N`, the determinant of the moment integrals of the paper.

So `deltaPoly N` is the polynomial `Δ_N(X)` of the write-up.
-/

open Polynomial Matrix

namespace OAI.InternalCatalan

open scoped BigOperators

/-- The coefficient of `z` in OpenAI's filtered rational entry. -/
noncomputable def filteredCatalanCoeffRat (N r k : ℕ) : ℚ :=
  ∑ v ∈ Finset.range (q N + 1), filterCoeffRat N v * rawCatalanCoeffRat N r (b N + k + v)

theorem filteredEntryRat_affine (z : ℚ) (N r k : ℕ) :
    filteredEntryRat z N r k =
      filteredEntryRat 0 N r k + z * filteredCatalanCoeffRat N r k := by
  unfold filteredEntryRat filteredCatalanCoeffRat
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [rawEntryRat_affine z N r]
  ring

/-- Constant part `A₀` of the matrix. -/
noncomputable def measureBaseMatrix (N : ℕ) : Matrix (Fin (n N)) (Fin (n N)) ℚ :=
  Matrix.of fun r k => filteredEntryRat 0 N r.val k.val

/-- Coefficient `L` of the constant in the matrix. -/
noncomputable def measureCatalanMatrix (N : ℕ) : Matrix (Fin (n N)) (Fin (n N)) ℚ :=
  Matrix.of fun r k => filteredCatalanCoeffRat N r.val k.val

/-- `Δ_N(X) = det (A₀ + X L)`. -/
noncomputable def deltaPoly (N : ℕ) : ℚ[X] :=
  det ((X : ℚ[X]) • (measureCatalanMatrix N).map C + (measureBaseMatrix N).map C)

theorem natDegree_deltaPoly_le (N : ℕ) : (deltaPoly N).natDegree ≤ n N := by
  have h := Polynomial.natDegree_det_X_add_C_le (measureCatalanMatrix N) (measureBaseMatrix N)
  rw [Fintype.card_fin] at h
  exact h

theorem deltaPoly_matrix_entry (N : ℕ) (r k : Fin (n N)) :
    ((X : ℚ[X]) • (measureCatalanMatrix N).map C + (measureBaseMatrix N).map C) r k =
      X * C (filteredCatalanCoeffRat N r.val k.val) + C (filteredEntryRat 0 N r.val k.val) := by
  simp [measureCatalanMatrix, measureBaseMatrix]

theorem eval_deltaPoly (z : ℚ) (N : ℕ) : (deltaPoly N).eval z = determinantRat z N := by
  have h := RingHom.map_det (evalRingHom z)
    ((X : ℚ[X]) • (measureCatalanMatrix N).map C + (measureBaseMatrix N).map C)
  rw [coe_evalRingHom] at h
  unfold deltaPoly determinantRat
  rw [h]
  congr 1
  ext r k
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, deltaPoly_matrix_entry, coe_evalRingHom]
  simp only [eval_add, eval_mul, eval_X, eval_C]
  rw [filteredEntryRat_affine z]
  ring

/-! ### The value at Catalan's constant -/

theorem rawEntry_real_affine {N r j : ℕ} (hN : 0 < N) (hr : r < n N) (hj : j < L N) :
    (rawEntryRat 0 N r j : ℝ) + catalan * (rawCatalanCoeffRat N r j : ℝ) =
      mixedMoment (realPoly (rowP N r)) (X ^ j) -
        (3 / 2 : ℝ) * zetaMoment (realPoly (rowD N r)) (X ^ j) := by
  rw [mixedMoment_rowP_evaluation hN hr hj, zetaMoment_rowD_evaluation hN hj]
  have e1 : (rawEntryRat 0 N r j : ℝ) =
      (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℝ) * (momentRat i j : ℝ)) -
        (3 / 2 : ℝ) * ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℝ) * (zetaRat i j : ℝ) := by
    simp only [rawEntryRat, mul_zero, zero_mul, add_zero]
    push_cast
    try ring
  have e2 : (rawCatalanCoeffRat N r j : ℝ) =
      ∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℝ) * (4 * (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℝ)) := by
    simp only [rawCatalanCoeffRat]
    push_cast
    try ring
  have e3 : (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℝ) *
        ((momentRat i j : ℝ) + 4 * catalan * (centralCoeffKernel ((i : ℤ) - j) : ℝ))) =
      (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℝ) * (momentRat i j : ℝ)) +
        catalan * ∑ i ∈ Finset.range (H N),
          ((rowP N r).coeff i : ℝ) * (4 * (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [e1, e2, e3]
  ring

theorem filteredEntry_real_affine {N r k : ℕ} (hN : 0 < N) (hr : r < n N) (hk : k < n N) :
    (filteredEntryRat 0 N r k : ℝ) + catalan * (filteredCatalanCoeffRat N r k : ℝ) =
      determinantEntry N r k := by
  unfold filteredEntryRat filteredCatalanCoeffRat determinantEntry
  push_cast
  rw [mixedMoment_filteredColumn, zetaMoment_filteredColumn]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  have hvq : v ≤ q N := by
    have := Finset.mem_range.mp hv
    omega
  have h := rawEntry_real_affine hN hr (rawColumn_lt_L hk hvq)
  linear_combination (filterCoeffRat N v : ℝ) * h

/-- At `X = G`, `Δ_N(X)` is OpenAI's real determinant of moment integrals. -/
theorem aeval_catalan_deltaPoly {N : ℕ} (hN : 0 < N) :
    aeval catalan (deltaPoly N) = determinant N := by
  have h := AlgHom.map_det (aeval (R := ℚ) catalan)
    ((X : ℚ[X]) • (measureCatalanMatrix N).map C + (measureBaseMatrix N).map C)
  unfold deltaPoly determinant
  rw [h]
  congr 1
  ext r k
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, deltaPoly_matrix_entry]
  simp only [map_add, map_mul, aeval_X, aeval_C, eq_ratCast]
  rw [← filteredEntry_real_affine hN r.isLt k.isLt]
  ring

/-- For real `x`, `Δ_N(x)` is the determinant of the real matrix `A₀ + x L`. -/
theorem aeval_deltaPoly (x : ℝ) (N : ℕ) :
    aeval x (deltaPoly N) =
      det (fun r k : Fin (n N) =>
        (filteredEntryRat 0 N r.val k.val : ℝ) + x * (filteredCatalanCoeffRat N r.val k.val : ℝ)) := by
  have h := AlgHom.map_det (aeval (R := ℚ) x)
    ((X : ℚ[X]) • (measureCatalanMatrix N).map C + (measureBaseMatrix N).map C)
  unfold deltaPoly
  rw [h]
  congr 1
  ext r k
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, deltaPoly_matrix_entry]
  simp only [map_add, map_mul, aeval_X, aeval_C, eq_ratCast]
  ring

end OAI.InternalCatalan
