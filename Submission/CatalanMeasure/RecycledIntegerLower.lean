module

public import Submission.CatalanMeasure.Integrality
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

/-!
# Recycling coefficient divisibility in the integer evaluation bound

If `B ∣ b` and `B ^ i ∣ Q.coeff i`, then the integer
`b ^ D * Q (a / b)` has an additional factor `B ^ D`.  Removing that
factor gives the stronger lower bound `(b / B) ^ D * |Q (a / b)| ≥ 1`.
No coprimality hypothesis on the numerator and denominator is required.
-/

open Polynomial

namespace CatalanMeasure

/-- Every term of the usual integer evaluation sum has the recycled factor. -/
theorem recycled_dvd_integer_sum (Q : ℤ[X]) (a : ℤ) {b B D : ℕ}
    (hBb : B ∣ b) (hcoeff : ∀ i ≤ D, (B : ℤ) ^ i ∣ Q.coeff i) :
    (B : ℤ) ^ D ∣
      ∑ i ∈ Finset.range (D + 1), Q.coeff i * a ^ i * (b : ℤ) ^ (D - i) := by
  obtain ⟨c, hc⟩ := hBb
  have hbcast : (b : ℤ) = (B : ℤ) * (c : ℤ) := by exact_mod_cast hc
  apply Finset.dvd_sum
  intro i hi
  have hiD : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  obtain ⟨z, hz⟩ := hcoeff i hiD
  refine ⟨z * a ^ i * (c : ℤ) ^ (D - i), ?_⟩
  have hpow : (B : ℤ) ^ D = (B : ℤ) ^ i * (B : ℤ) ^ (D - i) := by
    rw [← pow_add, Nat.add_sub_of_le hiD]
  rw [hz, hbcast, mul_pow, hpow]
  ring

/-- The quotient by the recycled factor is still an integer. -/
theorem exists_int_eq_recycled_pow_mul_aeval (Q : ℤ[X]) {D : ℕ}
    (hD : Q.natDegree ≤ D) (a : ℤ) {b B : ℕ} (hb : 0 < b)
    (hBb : B ∣ b) (hcoeff : ∀ i ≤ D, (B : ℤ) ^ i ∣ Q.coeff i) :
    ∃ m : ℤ, ((b : ℝ) / B) ^ D * aeval ((a : ℝ) / b) Q = m := by
  let z : ℤ := ∑ i ∈ Finset.range (D + 1),
    Q.coeff i * a ^ i * (b : ℤ) ^ (D - i)
  have hz : (b : ℝ) ^ D * aeval ((a : ℝ) / b) Q = z := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hD), Finset.mul_sum]
    dsimp [z]
    push_cast
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hiD : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have hpow : (b : ℝ) ^ D = (b : ℝ) ^ (D - i) * (b : ℝ) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hiD]
    rw [hpow, zsmul_eq_mul, div_pow]
    field_simp
  obtain ⟨m, hm⟩ := recycled_dvd_integer_sum Q a hBb hcoeff
  have hmreal : (z : ℝ) = (B : ℝ) ^ D * (m : ℝ) := by
    exact_mod_cast hm
  have hBpos : 0 < B := Nat.pos_of_dvd_of_pos hBb hb
  have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
  refine ⟨m, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero D hBne)
  calc
    (B : ℝ) ^ D * (((b : ℝ) / B) ^ D * aeval ((a : ℝ) / b) Q) =
        (b : ℝ) ^ D * aeval ((a : ℝ) / b) Q := by
          rw [div_pow]
          field_simp
    _ = (B : ℝ) ^ D * (m : ℝ) := hz.trans hmreal

/-- The recycled Liouville bound, with a real quotient in its useful form. -/
theorem one_le_recycled_pow_mul_abs_aeval (Q : ℤ[X]) {D : ℕ}
    (hD : Q.natDegree ≤ D) (a : ℤ) {b B : ℕ} (hb : 0 < b)
    (hBb : B ∣ b) (hcoeff : ∀ i ≤ D, (B : ℤ) ^ i ∣ Q.coeff i)
    (hne : aeval ((a : ℝ) / b) Q ≠ 0) :
    1 ≤ ((b : ℝ) / B) ^ D * |aeval ((a : ℝ) / b) Q| := by
  obtain ⟨m, hm⟩ := exists_int_eq_recycled_pow_mul_aeval Q hD a hb hBb hcoeff
  have hBpos : 0 < B := Nat.pos_of_dvd_of_pos hBb hb
  have hpos : (0 : ℝ) < ((b : ℝ) / B) ^ D := by positivity
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_eq_zero] at hm
    rcases hm with h | h
    · exact (ne_of_gt hpos) h
    · exact hne h
  have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    have := Int.one_le_abs hm0
    exact_mod_cast this
  calc
    (1 : ℝ) ≤ |(m : ℝ)| := h1
    _ = |((b : ℝ) / B) ^ D * aeval ((a : ℝ) / b) Q| := by rw [hm]
    _ = ((b : ℝ) / B) ^ D * |aeval ((a : ℝ) / b) Q| := by
      rw [abs_mul, abs_of_pos hpos]

/-- Distinct prime squares dividing a natural number divide it jointly. -/
theorem prime_square_prod_dvd (S : Finset ℕ) (b : ℕ)
    (hprime : ∀ q ∈ S, Nat.Prime q) (hdiv : ∀ q ∈ S, q ^ 2 ∣ b) :
    (∏ q ∈ S, q ^ 2) ∣ b := by
  have hprod : (∏ q ∈ S, (q : ℤ) ^ 2) ∣ (b : ℤ) := by
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      simpa only [Nat.cast_pow] using
        (Nat.coprime_pow_primes 2 2 (hprime p hp) (hprime q hq) hpq).cast (R := ℤ)
    · intro q hq
      exact_mod_cast hdiv q hq
  exact_mod_cast hprod

/-- Prime-square coefficient divisibility aggregates with the same exponent. -/
theorem prime_square_prod_pow_dvd_coeff (Q : ℤ[X]) (S : Finset ℕ) {D : ℕ}
    (hprime : ∀ q ∈ S, Nat.Prime q)
    (hcoeff : ∀ q ∈ S, ∀ i ≤ D, (q : ℤ) ^ (2 * i) ∣ Q.coeff i) :
    ∀ i ≤ D, ((∏ q ∈ S, q ^ 2 : ℕ) : ℤ) ^ i ∣ Q.coeff i := by
  intro i hi
  have hprod : (∏ q ∈ S, (q : ℤ) ^ (2 * i)) ∣ Q.coeff i := by
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      simpa only [Nat.cast_pow] using
        (Nat.coprime_pow_primes (2 * i) (2 * i)
          (hprime p hp) (hprime q hq) hpq).cast (R := ℤ)
    · intro q hq
      exact hcoeff q hq i hi
  simpa only [pow_mul, Finset.prod_pow, Nat.cast_prod, Nat.cast_pow] using hprod

/-- Recycled lower bound with all prime-square aggregation exposed. -/
theorem one_le_prime_square_prod_recycled_pow_mul_abs_aeval (Q : ℤ[X]) {D : ℕ}
    (hD : Q.natDegree ≤ D) (a : ℤ) {b : ℕ} (hb : 0 < b) (S : Finset ℕ)
    (hprime : ∀ q ∈ S, Nat.Prime q) (hdiv : ∀ q ∈ S, q ^ 2 ∣ b)
    (hcoeff : ∀ q ∈ S, ∀ i ≤ D, (q : ℤ) ^ (2 * i) ∣ Q.coeff i)
    (hne : aeval ((a : ℝ) / b) Q ≠ 0) :
    1 ≤ ((b : ℝ) / (∏ q ∈ S, q ^ 2 : ℕ)) ^ D * |aeval ((a : ℝ) / b) Q| := by
  exact one_le_recycled_pow_mul_abs_aeval Q hD a hb
    (prime_square_prod_dvd S b hprime hdiv)
    (prime_square_prod_pow_dvd_coeff Q S hprime hcoeff) hne

end CatalanMeasure
