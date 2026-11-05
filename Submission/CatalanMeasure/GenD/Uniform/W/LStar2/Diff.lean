module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Theorem
public import Mathlib.Algebra.Polynomial.Coeff
@[expose] public section
set_option Elab.async false

/-!
# The `m`-th difference identity (lane G6d, Theorem L* for `h < p`)

For a polynomial `Q` over a commutative ring and `m : ℕ`,
`coeff ((X-1)^m Q) i = Σ_{s ≤ m} (-1)^{m-s} C(m,s) coeff Q (i - s)`.
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar2
open Polynomial CatalanMeasure.GenD.Uniform.Prefix
noncomputable section

/-- Coefficient of the `m`-th difference: `(-1)^{m-s} C(m,s)`. -/
def wc (m s : ℕ) : ℤ := (-1) ^ (m - s) * (m.choose s : ℤ)

theorem wc_self (m : ℕ) : wc m m = 1 := by simp [wc]

theorem intrinsicCoeff_X_pow_mul {R : Type*} [CommRing R] (s : ℕ) (Q : R[X]) (i : ℤ) :
    intrinsicCoeff (X ^ s * Q) i = intrinsicCoeff Q (i - s) := by
  unfold intrinsicCoeff
  by_cases h : 0 ≤ i
  · rw [if_pos h, coeff_X_pow_mul']
    by_cases h2 : s ≤ i.toNat
    · rw [if_pos h2, if_pos (by omega)]
      congr 1
      omega
    · rw [if_neg h2, if_neg (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem intrinsicCoeff_sum {R : Type*} [CommRing R] {ι : Type*} (S : Finset ι) (f : ι → R[X])
    (i : ℤ) : intrinsicCoeff (∑ x ∈ S, f x) i = ∑ x ∈ S, intrinsicCoeff (f x) i := by
  unfold intrinsicCoeff
  split_ifs
  · exact finset_sum_coeff _ _ _
  · simp

theorem intrinsicCoeff_C_mul {R : Type*} [CommRing R] (a : R) (Q : R[X]) (i : ℤ) :
    intrinsicCoeff (C a * Q) i = a * intrinsicCoeff Q i := by
  unfold intrinsicCoeff
  split_ifs
  · exact coeff_C_mul _
  · simp

/-- **`m`-th difference.** -/
theorem intrinsicCoeff_xsub_pow_mul {R : Type*} [CommRing R] (m : ℕ) (Q : R[X]) (i : ℤ) :
    intrinsicCoeff ((X - 1) ^ m * Q) i =
      ∑ s ∈ Finset.range (m + 1), (wc m s : R) * intrinsicCoeff Q (i - s) := by
  have h : ((X : R[X]) - 1) ^ m =
      ∑ s ∈ Finset.range (m + 1), C ((wc m s : R)) * X ^ s := by
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun s hs => ?_
    simp only [wc]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, map_mul,
      map_pow, map_neg, map_one, map_natCast]
    ring
  rw [h, Finset.sum_mul, intrinsicCoeff_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show C (wc m s : R) * X ^ s * Q = C (wc m s : R) * (X ^ s * Q) by ring,
    intrinsicCoeff_C_mul, intrinsicCoeff_X_pow_mul]

#print axioms intrinsicCoeff_xsub_pow_mul
end
end CatalanMeasure.GenD.Uniform.W.LStar2
