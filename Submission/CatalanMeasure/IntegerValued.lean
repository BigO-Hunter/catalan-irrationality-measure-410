module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Integer-valued polynomials

If `f ∈ ℚ[X]` has degree at most `D` and takes integer values at every natural number, then
`D! • f` has integer coefficients.

The leading coefficient is controlled by the `D`-th forward difference, `Δ^D f = D! · lc(f)`,
which is an integer combination of the values `f 0, …, f D`.  Subtracting `lc(f) · X(X-1)⋯(X-D+1)`
lowers the degree and keeps the values integral, and induction finishes the proof.

This is how the coefficient-wise denominator of the Catalan determinant polynomial is bounded:
we only need denominators of its values at integers, where OpenAI's local estimates apply.
-/

open Polynomial Nat

namespace CatalanMeasure

theorem exists_int_coeff_mul_factorial {D : ℕ} (f : ℚ[X]) (hdeg : f.natDegree ≤ D)
    (hval : ∀ i : ℕ, ∃ m : ℤ, f.eval (i : ℚ) = m) :
    ∃ m : ℤ, f.coeff D * (D ! : ℚ) = m := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact ⟨0, by rw [coeff_eq_zero_of_natDegree_lt hlt]; simp⟩
  · choose m hm using hval
    refine ⟨∑ k ∈ Finset.range (D + 1), (-1 : ℤ) ^ (D - k) * (D.choose k : ℤ) * m k, ?_⟩
    have h1 := congrFun (Polynomial.fwdDiff_iter_degree_eq_factorial f) 0
    rw [fwdDiff_iter_eq_sum_shift] at h1
    have hlc : f.leadingCoeff = f.coeff D := by rw [leadingCoeff, heq]
    rw [heq, hlc] at h1
    simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul, zero_add, nsmul_eq_mul,
      mul_one] at h1
    rw [← h1]
    push_cast
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [zsmul_eq_mul, hm k]
    push_cast
    ring

theorem factorial_mul_mem_lifts (D : ℕ) : ∀ f : ℚ[X], f.natDegree ≤ D →
    (∀ i : ℕ, ∃ m : ℤ, f.eval (i : ℚ) = m) →
    C ((D ! : ℕ) : ℚ) * f ∈ lifts (Int.castRingHom ℚ) := by
  induction D with
  | zero =>
    intro f hdeg hval
    obtain ⟨m, hm⟩ := hval 0
    have hf : f = C (f.coeff 0) := eq_C_of_natDegree_le_zero hdeg
    have hc : f.coeff 0 = m := by
      have h0 : f.eval ((0 : ℕ) : ℚ) = f.coeff 0 := by
        rw [Nat.cast_zero, ← coeff_zero_eq_eval_zero]
      rw [← h0, hm]
    rw [hf, hc]
    simp only [factorial_zero, Nat.cast_one, C_1, one_mul]
    exact C'_mem_lifts ⟨m, by simp⟩
  | succ D ih =>
    intro f hdeg hval
    obtain ⟨c, hc⟩ := exists_int_coeff_mul_factorial f hdeg hval
    have hPmonic : (descPochhammer ℚ (D + 1)).Monic := monic_descPochhammer ℚ (D + 1)
    have hPdeg : (descPochhammer ℚ (D + 1)).natDegree = D + 1 := descPochhammer_natDegree ℚ (D + 1)
    have hP1 : (descPochhammer ℚ (D + 1)).coeff (D + 1) = 1 := by
      have h := hPmonic.coeff_natDegree
      rwa [hPdeg] at h
    -- `h = f - lc(f) · X(X-1)⋯(X-D)` has degree `≤ D` and integer values
    have hhdeg : (f - C (f.coeff (D + 1)) * descPochhammer ℚ (D + 1)).natDegree ≤ D := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_sub, coeff_C_mul]
      rcases (show D + 1 ≤ k by omega).lt_or_eq with hk' | hk'
      · have e1 : f.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hk')
        have e2 : (descPochhammer ℚ (D + 1)).coeff k = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hPdeg]; exact hk')
        rw [e1, e2]
        ring
      · subst hk'
        rw [hP1]
        ring
    have hhval : ∀ i : ℕ, ∃ m : ℤ,
        (f - C (f.coeff (D + 1)) * descPochhammer ℚ (D + 1)).eval (i : ℚ) = m := by
      intro i
      obtain ⟨mi, hmi⟩ := hval i
      refine ⟨mi - c * (i.choose (D + 1) : ℤ), ?_⟩
      rw [eval_sub, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
        Nat.descFactorial_eq_factorial_mul_choose, hmi]
      push_cast
      linear_combination (-(i.choose (D + 1) : ℚ)) * hc
    have hPl : descPochhammer ℚ (D + 1) ∈ lifts (Int.castRingHom ℚ) := by
      rw [mem_lifts]
      exact ⟨descPochhammer ℤ (D + 1), descPochhammer_map _ _⟩
    have key : C (((D + 1)! : ℕ) : ℚ) * f =
        C (((D + 1 : ℕ) : ℚ)) *
            (C ((D ! : ℕ) : ℚ) * (f - C (f.coeff (D + 1)) * descPochhammer ℚ (D + 1))) +
          C ((c : ℤ) : ℚ) * descPochhammer ℚ (D + 1) := by
      rw [← hc, Nat.factorial_succ]
      simp only [Nat.cast_mul, C_mul]
      ring
    rw [key]
    refine add_mem (mul_mem ?_ (ih _ hhdeg hhval)) (mul_mem ?_ hPl)
    · exact C'_mem_lifts ⟨((D + 1 : ℕ) : ℤ), by simp⟩
    · exact C'_mem_lifts ⟨c, by simp⟩

/-- An integer-valued rational polynomial of degree `≤ D`, multiplied by `D!`, is the image of
an integer polynomial of degree `≤ D`. -/
theorem exists_int_poly_factorial_mul {D : ℕ} (f : ℚ[X]) (hdeg : f.natDegree ≤ D)
    (hval : ∀ i : ℕ, ∃ m : ℤ, f.eval (i : ℚ) = m) :
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C ((D ! : ℕ) : ℚ) * f ∧ Q.natDegree ≤ D := by
  obtain ⟨Q, hQ, hQdeg⟩ := exists_natDegree_eq_of_mem_lifts (factorial_mul_mem_lifts D f hdeg hval)
  exact ⟨Q, hQ, hQdeg ▸ (natDegree_C_mul_le _ _).trans hdeg⟩

end CatalanMeasure
