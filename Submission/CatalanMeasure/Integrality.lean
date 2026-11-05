module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Integrality of `b ^ D * Q (a / b)`

For an integer polynomial `Q` of degree at most `D` and a rational point `a / b`,
the number `b ^ D * Q (a / b)` is an integer.  If it is nonzero, its absolute value
is at least one.  This is the Liouville step of the irrationality-measure argument.
-/

open Polynomial

namespace CatalanMeasure

theorem exists_int_eq_pow_mul_aeval (Q : ℤ[X]) {D : ℕ} (hD : Q.natDegree ≤ D)
    (a : ℤ) {b : ℕ} (hb : 0 < b) :
    ∃ m : ℤ, (b : ℝ) ^ D * aeval ((a : ℝ) / b) Q = m := by
  refine ⟨∑ i ∈ Finset.range (D + 1), Q.coeff i * a ^ i * (b : ℤ) ^ (D - i), ?_⟩
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hD), Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hpow : (b : ℝ) ^ D = (b : ℝ) ^ (D - i) * (b : ℝ) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [hpow, zsmul_eq_mul, div_pow]
  field_simp

/-- If `Q (a / b) ≠ 0` then `1 ≤ b ^ D * |Q (a / b)|`. -/
theorem one_le_pow_mul_abs_aeval (Q : ℤ[X]) {D : ℕ} (hD : Q.natDegree ≤ D)
    (a : ℤ) {b : ℕ} (hb : 0 < b) (hne : aeval ((a : ℝ) / b) Q ≠ 0) :
    1 ≤ (b : ℝ) ^ D * |aeval ((a : ℝ) / b) Q| := by
  obtain ⟨m, hm⟩ := exists_int_eq_pow_mul_aeval Q hD a hb
  have hbpos : (0 : ℝ) < (b : ℝ) ^ D := by positivity
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_eq_zero] at hm
    rcases hm with h | h
    · exact (ne_of_gt hbpos) h
    · exact hne h
  have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    have := Int.one_le_abs hm0
    exact_mod_cast this
  calc (1 : ℝ) ≤ |(m : ℝ)| := h1
    _ = |(b : ℝ) ^ D * aeval ((a : ℝ) / b) Q| := by rw [hm]
    _ = (b : ℝ) ^ D * |aeval ((a : ℝ) / b) Q| := by
        rw [abs_mul, abs_of_pos hbpos]

end CatalanMeasure
