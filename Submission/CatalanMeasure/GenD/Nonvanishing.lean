module

public import Submission.CatalanMeasure.Parametric.GoodPrimes
public import Submission.CatalanMeasure.Parametric.BlockAlgebra
public import Submission.CatalanMeasure.Parametric.Polynomial
public import Submission.CatalanMeasure.SquareNonvanishing

@[expose] public section

/-!
# Arithmetic nonvanishing at `N = p` from the C3 certificate (generic)

If the three `n0 × n0` base residue matrices `B0`, `B0 + B1`, `B0 - B1` modulo one fixed prime
`ℓ0 ≥ H(1)` are invertible (the C3 certificate), then for all large primes `p` and every
`a / b` with `p² ∤ b`, `Δ_p(a / b) ≠ 0`.  Generic port of `TwentyBase.Nonvanishing` and the
nonvanishing step of `TwentyMain`.
-/

namespace CatalanMeasure.GenD

open Polynomial CatalanMeasure.Parametric OAI.InternalCatalan

noncomputable section

theorem baseMatrixRat_det_ne_zero_of_residue {P : Parameters} {ℓ0 : ℕ} [Fact ℓ0.Prime]
    (h2 : ℓ0 ≠ 2) (hH : P.H 1 ≤ ℓ0) (σ : ℤ)
    (h : (baseB0Residue P ℓ0 + (σ : ZMod ℓ0) • baseB1Residue P ℓ0).det ≠ 0) :
    (baseMatrixRat P σ).det ≠ 0 := by
  have hh := baseMatrix_det_residue (P := P) (p := ℓ0) h2 hH σ
  intro hz
  rw [hz] at hh
  apply h
  rw [← hh]
  simp [palindromicRatResidue]

theorem aeval_ratCast_eq' (f : ℚ[X]) (q : ℚ) : aeval (q : ℝ) f = ((f.eval q : ℚ) : ℝ) := by
  rw [aeval_def, ← eq_ratCast (algebraMap ℚ ℝ) q, eval₂_at_apply, eq_ratCast]

/-- **Nonvanishing from the C3 certificate.** -/
theorem nonvanishing_of_c3 (P : Parameters) (hP : Admissible P) {ℓ0 : ℕ} [Fact ℓ0.Prime]
    (h2 : ℓ0 ≠ 2) (hH : P.H 1 ≤ ℓ0)
    (c0 : (baseB0Residue P ℓ0).det ≠ 0)
    (cp : (baseB0Residue P ℓ0 + baseB1Residue P ℓ0).det ≠ 0)
    (cm : (baseB0Residue P ℓ0 - baseB1Residue P ℓ0).det ≠ 0) :
    ∃ N1 : ℕ, ∀ p : ℕ, N1 ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Parametric.deltaPoly P p) ≠ 0 := by
  have r0 : (baseMatrixRat P 0).det ≠ 0 :=
    baseMatrixRat_det_ne_zero_of_residue h2 hH 0 (by simpa using c0)
  have rp : (baseMatrixRat P 1).det ≠ 0 :=
    baseMatrixRat_det_ne_zero_of_residue h2 hH 1 (by simpa using cp)
  have rm : (baseMatrixRat P (-1)).det ≠ 0 :=
    baseMatrixRat_det_ne_zero_of_residue h2 hH (-1) (by simpa [sub_eq_add_neg] using cm)
  refine ⟨finitePrimeCutoff P + 1, fun p hp hprime a b hb hpb => ?_⟩
  have : Fact p.Prime := ⟨hprime⟩
  have hx : (a : ℝ) / b = (((a : ℚ) / b : ℚ) : ℝ) := by
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  rw [hx, aeval_ratCast_eq', Parametric.eval_deltaPoly]
  have hd := determinantRat_prime_ne_zero P hP (by omega) r0 rp rm ((a : ℚ) / b)
    (prime_mul_div_den_unit a hb hpb)
  exact_mod_cast hd

end

end CatalanMeasure.GenD
