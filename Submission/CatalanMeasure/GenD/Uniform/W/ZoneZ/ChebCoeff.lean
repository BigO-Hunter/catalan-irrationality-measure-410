module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.QForms
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.TPoly
@[expose] public section
set_option Elab.async false

/-!
# Chebyshev coefficients and the unit subring

* `tc`, `uc` (computable integer coefficient functions) are the coefficients of `T_n`, `U_n`
  over any commutative ring;
* `unitSub p`: the subring of rationals with denominator prime to `p`, and `resHom : unitSub p →+* ZMod p`
  (reduction mod `p`), so that rational identities transfer to `ZMod p` by `map_*`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Polynomial OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
noncomputable section

section Cheb
variable (R : Type*) [CommRing R]

theorem T_coeff (n i : ℕ) : (Chebyshev.T R (n : ℤ)).coeff i = (Q.tc n i : R) := by
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    match n with
    | 0 => simp [Q.tc, Chebyshev.T_zero, coeff_one, eq_comm]
    | 1 => simp [Q.tc, Chebyshev.T_one, coeff_X, eq_comm]
    | m + 2 =>
      have e : Chebyshev.T R ((m + 2 : ℕ) : ℤ) =
          2 * X * Chebyshev.T R ((m + 1 : ℕ) : ℤ) - Chebyshev.T R (m : ℤ) := by
        have := Chebyshev.T_add_two R (m : ℤ)
        simpa using this
      rw [e, coeff_sub, ih m (by omega), Q.tc]
      have : (2 * X * Chebyshev.T R ((m + 1 : ℕ) : ℤ)).coeff i =
          2 * (if i = 0 then 0 else (Chebyshev.T R ((m + 1 : ℕ) : ℤ)).coeff (i - 1)) := by
        rw [mul_assoc, coeff_ofNat_mul]
        rcases i with _ | i
        · simp
        · rw [coeff_X_mul]; simp
      rw [this]
      by_cases hi : i = 0
      · simp [hi]
      · rw [if_neg hi, if_neg hi, ih (m + 1) (by omega)]; push_cast; ring

theorem U_coeff (n i : ℕ) : (Chebyshev.U R (n : ℤ)).coeff i = (Q.uc n i : R) := by
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    match n with
    | 0 => simp [Q.uc, Chebyshev.U_zero, coeff_one, eq_comm]
    | 1 =>
      simp [Q.uc, Chebyshev.U_one, coeff_X]
      by_cases hi : i = 1 <;> simp [hi, coeff_C_mul, coeff_X, eq_comm]
    | m + 2 =>
      have e : Chebyshev.U R ((m + 2 : ℕ) : ℤ) =
          2 * X * Chebyshev.U R ((m + 1 : ℕ) : ℤ) - Chebyshev.U R (m : ℤ) := by
        have := Chebyshev.U_add_two R (m : ℤ)
        simpa using this
      rw [e, coeff_sub, ih m (by omega), Q.uc]
      have : (2 * X * Chebyshev.U R ((m + 1 : ℕ) : ℤ)).coeff i =
          2 * (if i = 0 then 0 else (Chebyshev.U R ((m + 1 : ℕ) : ℤ)).coeff (i - 1)) := by
        rw [mul_assoc, coeff_ofNat_mul]
        rcases i with _ | i
        · simp
        · rw [coeff_X_mul]; simp
      rw [this]
      by_cases hi : i = 0
      · simp [hi]
      · rw [if_neg hi, if_neg hi, ih (m + 1) (by omega)]; push_cast; ring

/-- `U_{k-1}` for `k : ℕ` (zero at `k = 0`). -/
theorem Um_coeff (k i : ℕ) : (Chebyshev.U R ((k : ℤ) - 1)).coeff i = (Q.ucm k i : R) := by
  rcases k with _ | k
  · simp [Q.ucm, Chebyshev.U_neg_one]
  · have : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
    rw [this, U_coeff]; simp [Q.ucm]

theorem Am_coeff (k i : ℕ) :
    ((X ^ 2 - 1 : R[X]) * Chebyshev.U R ((k : ℤ) - 1)).coeff i = (Q.aTm k i : R) := by
  rw [sub_mul, coeff_sub, one_mul, coeff_X_pow_mul']
  simp only [Um_coeff]
  by_cases h : 2 ≤ i
  · rw [if_pos h]; simp [Q.aTm, show ¬ i < 2 from by omega]
  · rw [if_neg h]; simp [Q.aTm, show i < 2 from by omega]

end Cheb

/-- The rationals whose denominator is prime to `p`. -/
def unitSub (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {q | ((q.den : ℕ) : ZMod p) ≠ 0}
  mul_mem' := fun {a b} ha hb => (rational_residue_mul ha hb).1
  one_mem' := by
    have : ((1 : ℚ).den : ZMod p) = 1 := by simp
    simp [this]
  add_mem' := fun {a b} ha hb => (rational_residue_add ha hb).1
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa [Rat.neg_den] using ha

/-- Reduction mod `p` on the unit subring. -/
def resHom (p : ℕ) [Fact p.Prime] : unitSub p →+* ZMod p where
  toFun q := palindromicRatResidue p q.1
  map_one' := by simp [palindromicRatResidue]
  map_mul' := fun a b => (rational_residue_mul a.2 b.2).2
  map_zero' := by simp [palindromicRatResidue]
  map_add' := fun a b => (rational_residue_add a.2 b.2).2

theorem resHom_apply (p : ℕ) [Fact p.Prime] (q : unitSub p) :
    resHom p q = palindromicRatResidue p q.1 := rfl

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
