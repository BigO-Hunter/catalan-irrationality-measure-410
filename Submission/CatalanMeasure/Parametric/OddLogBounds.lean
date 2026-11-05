module
public import Submission.CatalanMeasure.Parametric.Polynomial
public import Submission.OAI.NumberTheory.Catalan.Arithmetic.SmallOddPrimePartition
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

private theorem param_prime_add_lower {p : ℕ} [Fact p.Prime] (a b : ℚ) (B : ℤ)
    (hB : B ≤ 0) (ha : B ≤ padicValRat p a) (hb : B ≤ padicValRat p b) :
    B ≤ padicValRat p (a+b) :=by
  simpa using prime_sub_valuation_lower a (-b) B hB ha (by simpa using hb)

theorem paramRawEntryRat_odd_prime_log_lower (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (N r j : ℕ) (hj : j < P.H N) :
    -6 * (Nat.log p (P.H N) : ℤ) - (padicValNat p z.den : ℤ) ≤
      padicValRat p (rawEntryRat P z N r j) := by
  let B : ℤ := -6 * (Nat.log p (P.H N) : ℤ) - (padicValNat p z.den : ℤ)
  have hl : 0 ≤ (Nat.log p (P.H N) : ℤ) := by positivity
  have hd : 0 ≤ (padicValNat p z.den : ℤ) := by positivity
  have hB : B ≤ 0 := by dsimp [B]; omega
  have hfour : padicValRat p (4 : ℚ) = 0 := by
    rw [show (4 : ℚ) = (2 : ℚ) ^ 2 by norm_num, padicValRat.pow,
      two_odd_prime_valuation hp2]
    norm_num
  have hfourz : -(padicValNat p z.den : ℤ) ≤ padicValRat p (4 * z) := by
    simpa using prime_mul_valuation_lower (4 : ℚ) z 0
      (-(padicValNat p z.den : ℤ)) (by omega) (by rw [hfour])
      (rational_prime_valuation_den_lower p z)
  have h32 : 0 ≤ padicValRat p (3 / 2 : ℚ) := by
    rw [padicValRat.div (by norm_num) (by norm_num), two_odd_prime_valuation hp2]
    simpa using int_prime_valuation_nonneg p 3
  unfold rawEntryRat
  apply prime_sub_valuation_lower _ _ B hB
  · apply prime_sum_valuation_lower _ _ B hB
    intro i hi
    have hi' : i < P.H N := Finset.mem_range.mp hi
    have hm := momentRat_odd_prime_log_lower hp2 i j (P.H N) hi' hj
    have he := prime_mul_valuation_lower (4 * z)
      (centralCoeffKernel ((i : ℤ) - j)) (-(padicValNat p z.den : ℤ)) 0
      (by omega) hfourz (centralCoeffKernel_odd_prime_nonneg hp2 _)
    have hs : B ≤ padicValRat p
        (momentRat i j + 4 * z * centralCoeffKernel ((i : ℤ) - j)) :=
      param_prime_add_lower _ _ B hB (by dsimp [B]; omega) (by dsimp [B]; omega)
    simpa using prime_mul_valuation_lower ((rowP P N r).coeff i : ℚ) _ 0 B
      (by simpa using hB) (int_prime_valuation_nonneg p _) hs
  · have hs : B ≤ padicValRat p
        (∑ i ∈ Finset.range (P.H N), ((rowD P N r).coeff i : ℚ) * zetaRat i j) := by
      apply prime_sum_valuation_lower _ _ B hB
      intro i hi
      have hz := zetaRat_prime_log_lower (p := p) (P.H N) i j (Finset.mem_range.mp hi) hj
      have hzB : B ≤ padicValRat p (zetaRat i j) := by dsimp [B]; omega
      simpa using prime_mul_valuation_lower ((rowD P N r).coeff i : ℚ) _ 0 B
        (by simpa using hB) (int_prime_valuation_nonneg p _) hzB
    simpa using prime_mul_valuation_lower (3 / 2 : ℚ) _ 0 B
      (by simpa using hB) h32 hs

theorem paramFilteredEntryRat_odd_prime_log_lower (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (N r k : ℕ) (hk : k < P.n N) :
    -6 * (Nat.log p (P.H N) : ℤ) - (padicValNat p z.den : ℤ) ≤
      padicValRat p (filteredEntryRat P z N r k) := by
  let B : ℤ := -6 * (Nat.log p (P.H N) : ℤ) - (padicValNat p z.den : ℤ)
  have hB : B ≤ 0 := by
    have : 0 ≤ (Nat.log p (P.H N) : ℤ) := by positivity
    have : 0 ≤ (padicValNat p z.den : ℤ) := by positivity
    dsimp [B]
    omega
  unfold filteredEntryRat
  apply prime_sum_valuation_lower _ _ B hB
  intro v hv
  have hv' : v ≤ P.q N := by have := Finset.mem_range.mp hv; omega
  have hj : P.b N + k + v < P.H N := by
    have h := rawColumn_lt_L hk hv'
    unfold Parameters.H Parameters.C at *
    omega
  have hfilter : 0 ≤ padicValRat p (filterCoeffRat P N v) := by
    simpa [filterCoeffRat] using
      int_prime_valuation_nonneg p ((-1 : ℤ) ^ v * ((P.q N).choose v : ℤ))
  simpa using prime_mul_valuation_lower (filterCoeffRat P N v) _ 0 B
    (by simpa using hB) hfilter (paramRawEntryRat_odd_prime_log_lower P hp2 z N r _ hj)


theorem paramDeterminantRat_odd_prime_log_lower (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (N : ℕ) :
    (P.n N : ℤ) * (-6 * (Nat.log p (P.H N) : ℤ) - (padicValNat p z.den : ℤ)) ≤
      padicValRat p (determinantRat P z N) := by
  have hB : -6 * (Nat.log p (P.H N) : ℤ) - (padicValNat p z.den : ℤ) ≤ 0 := by
    have : 0 ≤ (Nat.log p (P.H N) : ℤ) := by positivity
    have : 0 ≤ (padicValNat p z.den : ℤ) := by positivity
    omega
  simpa only [determinantRat, Fintype.card_fin] using
    prime_det_valuation_lower (fun r k : Fin (P.n N) => filteredEntryRat P z N r.val k.val)
      _ hB (fun r k => paramFilteredEntryRat_odd_prime_log_lower P hp2 z N r.val k.val k.isLt)


theorem paramDeterminantRat_above_degrees_local_integral (P : Parameters)
    {p N : ℕ} [Fact p.Prime] (hp2 : p≠2) (hH : P.H N<p)
    (z : ℚ) (hz : (z.den : ZMod p)≠0) :
    0 ≤ padicValRat p (determinantRat P z N) :=by
  have hlog : Nat.log p (P.H N)=0 :=Nat.log_eq_zero_iff.mpr (Or.inl hH)
  have hdiv : ¬p∣z.den :=fun hd =>hz ((ZMod.natCast_eq_zero_iff z.den p).mpr hd)
  have hden : padicValNat p z.den=0 :=padicValNat.eq_zero_of_not_dvd hdiv
  simpa [hlog,hden] using paramDeterminantRat_odd_prime_log_lower P hp2 z N

end
end CatalanMeasure.Parametric
