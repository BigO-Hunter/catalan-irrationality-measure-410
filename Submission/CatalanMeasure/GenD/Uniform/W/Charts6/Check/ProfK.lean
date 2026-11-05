module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.ProfB
@[expose] public section
set_option Elab.async false

/-!
# Integer coefficient tables of the profile for any `k0`, block count `b` and number `ex` of graph coordinates

Same as `ProfB` with the block index `κ = k0 + k` and the centre coefficients `T_{k0}`, `U_{k0-1}` (so `k0 = -2` is covered).
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open CatalanMeasure.GenD.D58.Odd CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Slots Polynomial
  Polynomial.Chebyshev CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts
  CatalanMeasure.GenD.Uniform.W.Charts5 CatalanMeasure.GenD.Uniform.W.Charts6
noncomputable section

def tcz (n : ℤ) (i : ℕ) : ℤ := ucz n i - shl (ucz (n - 1)) i

def blockGk (k0 : ℤ) (k u : ℕ) : ℕ → ℤ :=
  let κ : ℤ := k0 + (k : ℤ)
  let g := if u < 2 then mO (vcz κ) else mY (wcz κ)
  if u % 2 = 1 then mY g else g
def blockTk (k0 : ℤ) (k u : ℕ) : ℕ → ℤ :=
  let κ : ℤ := k0 + (k : ℤ)
  let t := if u < 2 then wcz κ else vcz κ
  if u % 2 = 1 then mY t else t
def centGk (k0 : ℤ) (z : ℕ) : ℕ → ℤ := if z = 0 then tcz k0 else mY (tcz k0)
def centTk (k0 : ℤ) (z : ℕ) : ℕ → ℤ := if z = 0 then ucz (k0 - 1) else mY (ucz (k0 - 1))

def pdK (k0 : ℤ) (b : ℕ) : ProfData where
  g := fun c i => if c < 4 * b then blockGk k0 (c / 4) (c % 4) i
    else if c < 4 * b + 2 then centGk k0 (c - 4 * b) i else 0
  t := fun c i => if c < 4 * b then blockTk k0 (c / 4) (c % 4) i
    else if c < 4 * b + 2 then centTk k0 (c - 4 * b) i else 0

theorem Co_Tz {R : Type*} [CommRing R] (n : ℤ) : Co (tcz n) (T R n) := by
  rw [T_eq_U_sub_X_mul_U]
  exact Co_sub (Co_Uz n) (Co_shl (Co_Uz (n - 1)))

section real
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem realises_absK {k0 : ℤ} {b0 b ex K : ℕ} (hb : b = b0) (hK : K = b * 4 + 2 + ex)
    (hck : ∀ k : Fin (b0 * 4 + 2 + ex), ckEquiv (rfl : b0 * 4 + 2 + ex = b0 * 4 + 2 + ex) k = ckOfB b0 ex k) :
    (pdK k0 b0).Realises (⟨sumProf hK (uCoefs k0 0), sumProf hK (tCoefs k0 0)⟩ : Prof p K) := by
  subst hb; subst hK
  intro k i
  simp only [sumProf_single]
  rw [show ckEquiv _ k = ckOfB b ex k from hck k]
  by_cases h : k.val < 4 * b
  · have hc : ckOfB b ex k = Sum.inl (⟨k.val / 4, by omega⟩, ⟨k.val % 4, by omega⟩) := by simp [ckOfB, h]
    rw [hc]
    have hu : k.val % 4 = 0 ∨ k.val % 4 = 1 ∨ k.val % 4 = 2 ∨ k.val % 4 = 3 := by omega
    have hg : (pdK k0 b).g k i = blockGk k0 (k.val / 4) (k.val % 4) i := by simp [pdK, h]
    have ht : (pdK k0 b).t k i = blockTk k0 (k.val / 4) (k.val % 4) i := by simp [pdK, h]
    rw [hg, ht]
    rcases hu with hu | hu | hu | hu
    · simp only [tCoefs, uCoefs, coefC, hu, blockGk, blockTk]
      simp only [pow_zero, mul_one]
      exact ⟨(Co_mO (Co_Uz_sub _)) i, (Co_Uz_add _) i⟩
    · simp only [tCoefs, uCoefs, coefC, hu, blockGk, blockTk]
      simp only [pow_zero, mul_one]
      exact ⟨(Co_right (Co_mO (Co_Uz_sub _))) i, (Co_right (Co_Uz_add _)) i⟩
    · simp only [tCoefs, uCoefs, coefC, hu, blockGk, blockTk]
      simp only [pow_zero, mul_one]
      exact ⟨(Co_mY (Co_Uz_add _)) i, (Co_Uz_sub _) i⟩
    · simp only [tCoefs, uCoefs, coefC, hu, blockGk, blockTk]
      simp only [pow_zero, mul_one]
      exact ⟨(Co_right (Co_mY (Co_Uz_add _))) i, (Co_right (Co_Uz_sub _)) i⟩
  · by_cases h2 : k.val < 4 * b + 2
    · have hc : ckOfB b ex k = Sum.inr (Sum.inl ⟨k.val - 4 * b, by omega⟩) := by simp [ckOfB, h, h2]
      rw [hc]
      have hz : k.val = 4 * b ∨ k.val = 4 * b + 1 := by omega
      rcases hz with hz | hz
      · have e1 : (pdK k0 b).g k i = centGk k0 0 i := by simp [pdK, h, h2, hz]
        have e2 : (pdK k0 b).t k i = centTk k0 0 i := by simp [pdK, h, h2, hz]
        rw [e1, e2]
        simp only [tCoefs, uCoefs, coefC, hz]
        have s0 : 4 * b - 4 * b = 0 := Nat.sub_self _
        simp only [pow_zero, mul_one, centGk, centTk, if_true, s0]
        exact ⟨(Co_Tz k0) i, (Co_Uz (k0 - 1)) i⟩
      · have e1 : (pdK k0 b).g k i = centGk k0 1 i := by simp [pdK, h, h2, hz]
        have e2 : (pdK k0 b).t k i = centTk k0 1 i := by simp [pdK, h, h2, hz]
        rw [e1, e2]
        simp only [tCoefs, uCoefs, coefC, hz]
        have s1 : 4 * b + 1 - 4 * b = 1 := by omega
        simp only [pow_zero, mul_one, centGk, centTk, s1]
        exact ⟨(Co_right (Co_Tz k0)) i, (Co_right (Co_Uz (k0 - 1))) i⟩
    · have hc : ckOfB b ex k = Sum.inr (Sum.inr ⟨k.val - (4 * b + 2), by omega⟩) := by simp [ckOfB, h, h2]
      rw [hc]
      simp [tCoefs, uCoefs, coefC, pdK, h, h2]

end real
end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
