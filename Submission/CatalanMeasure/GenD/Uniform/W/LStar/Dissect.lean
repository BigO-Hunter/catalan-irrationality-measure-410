module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponseReflect
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Degree.Support
@[expose] public section
set_option Elab.async false

/-!
# `p`-dissection of a product `expand p a * Q` (lane G6c, Theorem L*)

If `Q` has degree `< e0 + p` with `e0 < p`, then the coefficient of `expand p a * Q` at the index
`e0 + p m` is `a_m * Q_{e0}`: only the *single live position* `e0` of `Q` contributes.  This is the
coefficient formula behind the per-residue local relation of Theorem L*.
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar
open Polynomial CatalanMeasure.GenD.Uniform.Prefix
noncomputable section
variable {R : Type*} [CommRing R]

/-- Single live position: `coeff (expand p a * Q) (e0 + p m) = a_m * Q_{e0}`. -/
theorem coeff_expand_mul_live {p : ℕ} (hp : 0 < p) (a Q : R[X]) {e0 : ℕ} (he : e0 < p)
    (hQ : Q.natDegree < e0 + p) (m : ℕ) :
    (expand R p a * Q).coeff (e0 + p * m) = a.coeff m * Q.coeff e0 := by
  classical
  conv_lhs => rw [Q.as_sum_range' (e0 + p) hQ]
  rw [Finset.mul_sum, finset_sum_coeff]
  rw [Finset.sum_eq_single e0]
  · rw [show expand R p a * (monomial e0 (Q.coeff e0)) =
        C (Q.coeff e0) * (expand R p a * X ^ e0) by
      rw [← C_mul_X_pow_eq_monomial]; ring]
    rw [coeff_C_mul, coeff_mul_X_pow', if_pos (by omega), coeff_expand hp,
      show e0 + p * m - e0 = p * m by omega, if_pos (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ hp]
    ring
  · intro i hi hne
    have hi' : i < e0 + p := Finset.mem_range.mp hi
    rw [show expand R p a * (monomial i (Q.coeff i)) =
        C (Q.coeff i) * (expand R p a * X ^ i) by
      rw [← C_mul_X_pow_eq_monomial]; ring]
    rw [coeff_C_mul, coeff_mul_X_pow', coeff_expand hp]
    by_cases hle : i ≤ e0 + p * m
    · by_cases hd : p ∣ e0 + p * m - i
      · exfalso
        obtain ⟨t, ht⟩ := hd
        have h1 : (i : ℤ) = e0 + p * ((m : ℤ) - t) := by
          have : ((e0 + p * m - i : ℕ) : ℤ) = ((p * t : ℕ) : ℤ) := by rw [ht]
          push_cast [Nat.cast_sub hle] at this
          linarith
        have hpz : (0 : ℤ) < p := by exact_mod_cast hp
        have h2 : (m : ℤ) - t = 0 := by
          rcases lt_trichotomy ((m : ℤ) - t) 0 with h | h | h
          · exfalso
            have : (p : ℤ) * ((m : ℤ) - t) ≤ -p := by nlinarith
            have : (0 : ℤ) ≤ i := by positivity
            omega
          · exact h
          · exfalso
            have : (p : ℤ) ≤ (p : ℤ) * ((m : ℤ) - t) := by nlinarith
            omega
        rw [h2] at h1
        apply hne
        omega
      · rw [if_pos hle, if_neg hd]; ring
    · rw [if_neg hle]; ring
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- Integer-index form: negative indices vanish. -/
theorem intrinsicCoeff_expand_mul_live {p : ℕ} (hp : 0 < p) (a Q : R[X]) {e0 : ℕ} (he : e0 < p)
    (hQ : Q.natDegree < e0 + p) (m : ℤ) :
    intrinsicCoeff (expand R p a * Q) (e0 + p * m) = intrinsicCoeff a m * Q.coeff e0 := by
  by_cases hm : 0 ≤ m
  · obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le hm
    have h1 : ((e0 : ℤ) + p * (m' : ℤ)) = ((e0 + p * m' : ℕ) : ℤ) := by push_cast; ring
    rw [h1, intrinsicCoeff_nat, intrinsicCoeff_nat, coeff_expand_mul_live hp a Q he hQ]
  · have hm' : m ≤ -1 := by omega
    have hpz : (p : ℤ) ≤ p := le_refl _
    have hneg : (e0 : ℤ) + p * m < 0 := by
      have : (p : ℤ) * m ≤ -p := by nlinarith
      omega
    rw [intrinsicCoeff, if_neg (by omega), intrinsicCoeff, if_neg hm]
    ring

#print axioms coeff_expand_mul_live
#print axioms intrinsicCoeff_expand_mul_live
end
end CatalanMeasure.GenD.Uniform.W.LStar
