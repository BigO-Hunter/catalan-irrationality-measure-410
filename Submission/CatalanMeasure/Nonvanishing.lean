module

public import Submission.OAI.NumberTheory.Catalan.Arithmetic.PrimeNonvanishing

@[expose] public section

/-!
# Nonvanishing at rational points with denominator prime to `p`  (Proposition 4)

OpenAI prove `determinantRat z p ≠ 0` and `v_p(determinantRat z p) = -96 p` for primes
`p > max fixedDeterminantPrimeCutoff z.den`.  Their proof only uses `z.den ≢ 0 (mod p)`,
so the cutoff need not depend on `z`.  This uniformity is what an irrationality measure
needs: the point `z = a / b` varies, but for one prime `p ∤ b` in the window
`Δ_p(a / b) ≠ 0`.  The proofs below are OpenAI's, with the hypothesis on `z.den` exposed.
-/

namespace OAI.InternalCatalan

theorem determinantRat_prime_ne_zero_of_den {z : ℚ} {p : ℕ} [Fact p.Prime]
    (hp : fixedDeterminantPrimeCutoff < p) (hz : (z.den : ZMod p) ≠ 0) :
    determinantRat z p ≠ 0 := by
  have hp260 : 260 < p := lt_of_le_of_lt fixedDeterminantPrimeCutoff_ge_260 hp
  have hdet := fixedDeterminants_mod_prime_ne_zero_of_lt fixedMatrix_zero_det_ne_zero
    fixedMatrix_one_det_ne_zero fixedMatrix_neg_one_det_ne_zero hp
  apply determinantRat_ne_zero_of_scaledResidueMatrix z
    (palindromicScaledRatMatrix_entry_den_ne_zero hp260 z hz)
  rw [palindromicScaledResidueMatrix_eq_extracted hp260 z hz]
  exact det_palindromicExtractedResidueMatrix_ne_zero_of_fixed
    hp260 hdet.1 hdet.2.1 hdet.2.2

theorem determinantRat_prime_valuation_of_den {z : ℚ} {p : ℕ} [hpPrime : Fact p.Prime]
    (hp : fixedDeterminantPrimeCutoff < p) (hz : (z.den : ZMod p) ≠ 0) :
    padicValRat p (determinantRat z p) = -96 * (p : ℤ) := by
  have hp260 : 260 < p := lt_of_le_of_lt fixedDeterminantPrimeCutoff_ge_260 hp
  have hfixedres := fixedDeterminants_mod_prime_ne_zero_of_lt fixedMatrix_zero_det_ne_zero
    fixedMatrix_one_det_ne_zero fixedMatrix_neg_one_det_ne_zero hp
  have hdetres : (palindromicScaledResidueMatrix z p).det ≠ 0 := by
    rw [palindromicScaledResidueMatrix_eq_extracted hp260 z hz]
    exact det_palindromicExtractedResidueMatrix_ne_zero_of_fixed
      hp260 hfixedres.1 hfixedres.2.1 hfixedres.2.2
  have hres := palindromicScaledRatMatrix_det_residue z
    (palindromicScaledRatMatrix_entry_den_ne_zero hp260 z hz)
  have hval : padicValRat p (palindromicScaledRatMatrix z p).det = 0 := by
    apply padicValRat_eq_zero_of_palindromicRatResidue_ne_zero hres.1
    rw [hres.2]
    exact hdetres
  have hdet := determinantRat_prime_ne_zero_of_den hp hz
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hpPrime.out.ne_zero
  rw [det_palindromicScaledRatMatrix,
    padicValRat.mul (pow_ne_zero _ hpq) hdet, padicValRat.pow,
    padicValRat.self hpPrime.out.one_lt, mul_one] at hval
  simp only [n, Nat.cast_mul, Nat.cast_ofNat] at hval
  omega

/-- For `a / b` with `p ∤ b` (and `p` beyond a fixed cutoff), `Δ_p(a / b) ≠ 0`. -/
theorem determinantRat_div_ne_zero {p : ℕ} [Fact p.Prime] (hp : fixedDeterminantPrimeCutoff < p)
    (a : ℤ) {b : ℕ} (_hb : 0 < b) (hpb : ¬ p ∣ b) :
    determinantRat ((a : ℚ) / b) p ≠ 0 := by
  apply determinantRat_prime_ne_zero_of_den hp
  intro h0
  have hden : ((a : ℚ) / b).den ∣ b := by
    have h := Rat.den_dvd a (b : ℤ)
    rw [Rat.divInt_eq_div] at h
    push_cast at h
    exact_mod_cast h
  exact hpb (dvd_trans ((ZMod.natCast_eq_zero_iff _ p).mp h0) hden)

end OAI.InternalCatalan
