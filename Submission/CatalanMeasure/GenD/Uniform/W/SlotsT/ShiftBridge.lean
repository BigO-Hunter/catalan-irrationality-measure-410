module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.GlueOne
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ShiftMoments
public import Submission.OAI.NumberTheory.Catalan.Arithmetic.OddPrimeFilterDigits
public import Submission.OAI.NumberTheory.Catalan.Estimates.PalindromicBlockInverse
@[expose] public section
set_option Elab.async false

/-!
# Lemma S for slot profiles (bridge to `ZoneZ.shift_lemma`)

`psi_shift` : for a profile map `F` with `deg Gy ≤ s+1` and `deg Ty ≤ s`,
`ψ(J+1, s+1)(y) = ψ(J, s)(y) + (J+1)⁻¹ ψ_s(y)` with `ψ_s` independent of `J`.
`shiftUnits_of_lt` : the unit hypotheses hold for `p > (s+3)(J+2)` (denominators of the moments).
`J2_of_shift` : the overflow equation of Theorem MT (b) on a digit `J+1` follows from the main-window
equation on `J` and the global condition `ψ_s(y) + ψ_s(u) = 0`.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Unit hypotheses of the shift lemma for large primes. -/
theorem shiftUnits_of_lt (hp2 : p ≠ 2) (S J : ℕ) (h : (S + 3) * (J + 2) < p) :
    ZoneZ.ShiftUnits p S J where
  hM i hi := momentRat_odd_prime_small_den_ne_zero hp2 (by nlinarith) (by nlinarith)
  hμ i hi := rational_den_ne_zero_of_valuation_nonneg
    (momentScalar_odd_prime_valuation_nonneg (Fact.out : p.Prime) hp2 (by nlinarith))
  hZ w hw := zetaRat_small_den_ne_zero (by nlinarith) (by nlinarith)
  hp := h

/-- **Lemma S for a slot profile.** -/
theorem psi_shift {K s J : ℕ} (F : Prof p K) (hu : ZoneZ.ShiftUnits p s J) (H : ℕ) (hH : s + 3 ≤ H)
    (y : Fin K → ZMod p) (hG : (F.Gy y).natDegree ≤ s + 1) (hT : (F.Ty y).natDegree ≤ s) :
    F.psi H (J + 1) ((s : ℤ) + 1) y =
      F.psi H J (s : ℤ) y + ((J + 1 : ℕ) : ZMod p)⁻¹ * ZoneZ.psiS s (F.Gy y) (F.Ty y) (3 / 2) := by
  show digitPhi H ((s : ℤ) + 1) (sourceM (p := p) (J + 1)) (sourceZ (p := p) (J + 1))
      (F.Gy y) (F.Ty y) (3 / 2) = digitPhi H (s : ℤ) (sourceM (p := p) J) (sourceZ (p := p) J)
      (F.Gy y) (F.Ty y) (3 / 2) + _
  rw [ZoneZ.shift_lemma hu H hH (F.Gy y) (F.Ty y) (3 / 2)]
  have h1 : intrinsicCoeff (F.Gy y) ((s : ℤ) + 2) = 0 := by
    unfold intrinsicCoeff
    rw [if_pos (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  have h2 : intrinsicCoeff (F.Ty y) ((s : ℤ) + 1) = 0 := by
    unfold intrinsicCoeff
    rw [if_pos (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  unfold ZoneZ.shiftBdry
  rw [h1, h2]; ring

/-- **The overflow equation of Theorem MT (b) from the main-window equation one digit below**
(Lemma S with the global condition `ψ_s(y) + ψ_s(u) = 0`). -/
theorem J2_of_shift {K s J : ℕ} (F1 F2 : Prof p K) (hu : ZoneZ.ShiftUnits p s J) (H : ℕ)
    (hH : s + 3 ≤ H) (y u : Fin K → ZMod p)
    (hG1 : (F1.Gy y).natDegree ≤ s + 1) (hT1 : (F1.Ty y).natDegree ≤ s)
    (hG2 : (F2.Gy u).natDegree ≤ s + 1) (hT2 : (F2.Ty u).natDegree ≤ s)
    (hΨ : ZoneZ.psiS s (F1.Gy y) (F1.Ty y) (3 / 2) + ZoneZ.psiS s (F2.Gy u) (F2.Ty u) (3 / 2) = 0)
    (A B : ZMod p) (h1 : F1.psi H J (s : ℤ) y = A) (h2 : F2.psi H J (s : ℤ) u = B) :
    F1.psi H (J + 1) ((s : ℤ) + 1) y + F2.psi H (J + 1) ((s : ℤ) + 1) u = A + B := by
  rw [psi_shift F1 hu H hH y hG1 hT1, psi_shift F2 hu H hH u hG2 hT2, h1, h2]
  linear_combination ((J + 1 : ℕ) : ZMod p)⁻¹ * hΨ

#print axioms psi_shift
#print axioms shiftUnits_of_lt
#print axioms J2_of_shift

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
