module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ShiftAbs
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponseWindow
@[expose] public section
set_option Elab.async false

/-!
# Shift Lemma for the actual moment residues

`sourceM J v = res M(v-1,J)`, `sourceZ J v = res Z(v,J)` satisfy the one-step relations
of `ShiftAbs` (from `momentRat_step`, `zetaRat_step`), so

    Φ(J+1,S+1;a,b) = Φ(J,S;a,b) + ψ_S(a,b)/(J+1) + boundary,

with `ψ_S` independent of `J`.  Only units are assumed: the denominators of the finitely many
moments involved are prime to `p` (these are the bad-prime hypotheses).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Polynomial Finset CatalanMeasure.GenD.Uniform.Prefix OAI.InternalCatalan
noncomputable section
variable {p S J : ℕ} [Fact p.Prime]

/-- A rational whose denominator is a unit mod `p`. -/
def RU (p : ℕ) [Fact p.Prime] (q : ℚ) : Prop := ((q.den : ℕ) : ZMod p) ≠ 0

theorem res_sub {a b : ℚ} (ha : RU p a) (hb : RU p b) :
    RU p (a - b) ∧ palindromicRatResidue p (a - b) =
      palindromicRatResidue p a - palindromicRatResidue p b :=
  rational_residue_sub ha hb

theorem res_mul {a b : ℚ} (ha : RU p a) (hb : RU p b) :
    RU p (a * b) ∧ palindromicRatResidue p (a * b) =
      palindromicRatResidue p a * palindromicRatResidue p b :=
  rational_residue_mul ha hb

theorem res_inv_nat {n : ℕ} (h0 : 0 < n) (hnp : n < p) :
    RU p (1 / (n : ℚ)) ∧ palindromicRatResidue p (1 / (n : ℚ)) = ((n : ℕ) : ZMod p)⁻¹ := by
  have hn : ((n : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff n p).mp h
    exact absurd (Nat.le_of_dvd h0 this) (by omega)
  have hq : (1 / (n : ℚ)) = (n : ℚ)⁻¹ := by simp
  have hnum : ((n : ℚ)⁻¹).num = 1 := Rat.inv_natCast_num_of_pos h0
  have hden : ((n : ℚ)⁻¹).den = n := Rat.inv_natCast_den_of_pos h0
  refine ⟨?_, ?_⟩
  · unfold RU; rw [hq, hden]; exact hn
  · unfold palindromicRatResidue; rw [hq, hnum, hden]; simp

/-- Moment unit hypotheses for the shift `(J,S) → (J+1,S+1)`. -/
structure ShiftUnits (p S J : ℕ) [Fact p.Prime] : Prop where
  hM : ∀ i < S + 2, RU p (momentRat i J)
  hμ : ∀ i < S + 2, RU p (momentScalar i)
  hZ : ∀ w < S + 2, RU p (zetaRat w J)
  hp : (S + 3) * (J + 2) < p

theorem sourceM_shift_zero (J : ℕ) : sourceM (p := p) (J + 1) 1 = sourceM (p := p) J 0 := by
  unfold sourceM
  have h1 : momentRatSigned (((1 : ℕ) : ℤ) - 1) (J + 1) = momentRat 0 (J + 1) := by
    have : ((1 : ℕ) : ℤ) - 1 = ((0 : ℕ) : ℤ) := by norm_num
    rw [this, momentRatSigned_natCast]
  have h2 : momentRatSigned (((0 : ℕ) : ℤ) - 1) J = boundaryPlus (J + 1) := by
    have : ((0 : ℕ) : ℤ) - 1 = -1 := by norm_num
    rw [this, momentRatSigned_neg_one, momentRatNegOne_eq]
  rw [h1, h2, momentRat_zero_left]

theorem sourceM_shift_step (hu : ShiftUnits p S J) (i : ℕ) (hi : i < S + 2) :
    sourceM (p := p) (J + 1) (i + 2) = sourceM (p := p) J (i + 1) -
      palindromicRatResidue p (momentScalar i) * ((J + 1 : ℕ) : ZMod p)⁻¹ := by
  unfold sourceM
  have e1 : ((i + 2 : ℕ) : ℤ) - 1 = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
  have e2 : ((i + 1 : ℕ) : ℤ) - 1 = ((i : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2, momentRatSigned_natCast, momentRatSigned_natCast]
  have hstep := momentRat_step i J
  have hJ := res_inv_nat (p := p) (n := J + 1) (by omega)
    (by have := hu.hp; nlinarith)
  have hmul := res_mul (p := p) (hu.hμ i hi) hJ.1
  have hsub := res_sub (p := p) (hu.hM i hi) hmul.1
  have : momentRat (i + 1) (J + 1) = momentRat i J - momentScalar i * (1 / ((J + 1 : ℕ) : ℚ)) := by
    have := hstep
    rw [mul_one_div]; linarith
  rw [this, hsub.2, hmul.2, hJ.2]

theorem sourceZ_shift_step (hu : ShiftUnits p S J) (w : ℕ) (hw : w < S + 2) :
    sourceZ (p := p) (J + 1) (w + 1) = sourceZ (p := p) J w -
      ((w + 1 : ℕ) : ZMod p)⁻¹ * ((J + 1 : ℕ) : ZMod p)⁻¹ := by
  unfold sourceZ
  have hstep := zetaRat_step w J
  have hw1 := res_inv_nat (p := p) (n := w + 1) (by omega)
    (by have := hu.hp; nlinarith)
  have hJ := res_inv_nat (p := p) (n := J + 1) (by omega)
    (by have := hu.hp; nlinarith)
  have hmul := res_mul (p := p) hw1.1 hJ.1
  have hsub := res_sub (p := p) (hu.hZ w hw) hmul.1
  have : zetaRat (w + 1) (J + 1) = zetaRat w J -
      (1 / ((w + 1 : ℕ) : ℚ)) * (1 / ((J + 1 : ℕ) : ℚ)) := by
    rw [one_div_mul_one_div]; linarith
  rw [this, hsub.2, hmul.2, hw1.2, hJ.2]

/-- The `J`-independent covector `ψ_S(a,b)` (with `c = 3/2` in the application). -/
def psiS (S : ℕ) (a b : (ZMod p)[X]) (c : ZMod p) : ZMod p :=
  shiftPsi S a b c (fun i => palindromicRatResidue p (momentScalar i))
    (fun w => ((w + 1 : ℕ) : ZMod p)⁻¹)

/-- **Shift Lemma.** -/
theorem shift_lemma (hu : ShiftUnits p S J) (H : ℕ) (hH : S + 3 ≤ H) (a b : (ZMod p)[X])
    (c : ZMod p) :
    digitPhi H ((S : ℤ) + 1) (sourceM (J + 1)) (sourceZ (J + 1)) a b c =
      digitPhi H (S : ℤ) (sourceM J) (sourceZ J) a b c +
        ((J + 1 : ℕ) : ZMod p)⁻¹ * psiS S a b c +
        shiftBdry S a b c (sourceM (J + 1)) (sourceZ (J + 1)) := by
  rw [digitPhi_cutoff_signed H (S + 3) _ hH (by push_cast; omega),
    digitPhi_cutoff_signed H (S + 3) _ hH (by push_cast; omega)]
  exact digitPhi_shift S a b c _ _ _ _ _ _ _ (sourceM_shift_zero J)
    (fun i hi => sourceM_shift_step hu i hi) (fun w hw => sourceZ_shift_step hu w hw)

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
