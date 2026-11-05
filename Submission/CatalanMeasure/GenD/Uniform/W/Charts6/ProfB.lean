module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts5.Prof146
@[expose] public section
set_option Elab.async false

/-!
# Integer coefficient tables of the profile for any block count `b` and any number `ex` of graph coordinates

`pdB b` is `pd146` with `10` replaced by `b`: block coordinates `4 k + u`, centre `4 b, 4 b + 1`, then zero graph coordinates.
`realises_absB` shows that `monoProfile` (with `k0 = -1`, `a_h = 0`) realises it, given the coordinate-kind
identification `ckEquiv = ckOfB` (a finite `decide +kernel` check for each `(b, ex)`).
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.D58.Odd CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Slots Polynomial
  Polynomial.Chebyshev CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts
  CatalanMeasure.GenD.Uniform.W.Charts5
noncomputable section

def pdB (b : ℕ) : ProfData where
  g := fun c i => if c < 4 * b then blockG (c / 4) (c % 4) i
    else if c < 4 * b + 2 then centG (c - 4 * b) i else 0
  t := fun c i => if c < 4 * b then blockT (c / 4) (c % 4) i
    else if c < 4 * b + 2 then centT (c - 4 * b) i else 0

/-- Decomposition of a packet coordinate into a profile coordinate kind. -/
def ckOfB (b ex : ℕ) (k : Fin (b * 4 + 2 + ex)) : CK b ex :=
  if h : k.val < 4 * b then Sum.inl (⟨k.val / 4, by omega⟩, ⟨k.val % 4, by omega⟩)
  else if h2 : k.val < 4 * b + 2 then Sum.inr (Sum.inl ⟨k.val - 4 * b, by omega⟩)
  else Sum.inr (Sum.inr ⟨k.val - (4 * b + 2), by omega⟩)

section real
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem realises_absB {b0 b ex K : ℕ} (hb : b = b0) (hK : K = b * 4 + 2 + ex)
    (hck : ∀ k : Fin (b0 * 4 + 2 + ex), ckEquiv (rfl : b0 * 4 + 2 + ex = b0 * 4 + 2 + ex) k = ckOfB b0 ex k) :
    (pdB b0).Realises (⟨sumProf hK (uCoefs (-1) 0), sumProf hK (tCoefs (-1) 0)⟩ : Prof p K) := by
  subst hb; subst hK
  intro k i
  simp only [sumProf_single]
  rw [show ckEquiv _ k = ckOfB b ex k from hck k]
  by_cases h : k.val < 4 * b
  · have hc : ckOfB b ex k = Sum.inl (⟨k.val / 4, by omega⟩, ⟨k.val % 4, by omega⟩) := by simp [ckOfB, h]
    rw [hc]
    have hu : k.val % 4 = 0 ∨ k.val % 4 = 1 ∨ k.val % 4 = 2 ∨ k.val % 4 = 3 := by omega
    have hg : (pdB b).g k i = blockG (k.val / 4) (k.val % 4) i := by simp [pdB, h]
    have ht : (pdB b).t k i = blockT (k.val / 4) (k.val % 4) i := by simp [pdB, h]
    rw [hg, ht]
    rcases hu with hu | hu | hu | hu
    · simp only [tCoefs, uCoefs, coefC, hu, blockG, blockT]
      simp only [pow_zero, mul_one]
      exact ⟨(Co_mO (Co_Uz_sub _)) i, (Co_Uz_add _) i⟩
    · simp only [tCoefs, uCoefs, coefC, hu, blockG, blockT]
      simp only [pow_zero, mul_one]
      exact ⟨(Co_right (Co_mO (Co_Uz_sub _))) i, (Co_right (Co_Uz_add _)) i⟩
    · simp only [tCoefs, uCoefs, coefC, hu, blockG, blockT]
      simp only [pow_zero, mul_one]
      exact ⟨(Co_mY (Co_Uz_add _)) i, (Co_Uz_sub _) i⟩
    · simp only [tCoefs, uCoefs, coefC, hu, blockG, blockT]
      simp only [pow_zero, mul_one]
      exact ⟨(Co_right (Co_mY (Co_Uz_add _))) i, (Co_right (Co_Uz_sub _)) i⟩
  · by_cases h2 : k.val < 4 * b + 2
    · have hc : ckOfB b ex k = Sum.inr (Sum.inl ⟨k.val - 4 * b, by omega⟩) := by simp [ckOfB, h, h2]
      rw [hc]
      have hz : k.val = 4 * b ∨ k.val = 4 * b + 1 := by omega
      rcases hz with hz | hz
      · have e1 : (pdB b).g k i = centG 0 i := by simp [pdB, h, h2, hz]
        have e2 : (pdB b).t k i = centT 0 i := by simp [pdB, h, h2, hz]
        rw [e1, e2]
        simp only [tCoefs, uCoefs, coefC, hz]
        have s0 : 4 * b - 4 * b = 0 := Nat.sub_self _
        simp only [pow_zero, mul_one, centG, centT, if_true, s0]
        exact ⟨Co_T i, Co_U2 i⟩
      · have e1 : (pdB b).g k i = centG 1 i := by simp [pdB, h, h2, hz]
        have e2 : (pdB b).t k i = centT 1 i := by simp [pdB, h, h2, hz]
        rw [e1, e2]
        simp only [tCoefs, uCoefs, coefC, hz]
        have s1 : 4 * b + 1 - 4 * b = 1 := by omega
        simp only [pow_zero, mul_one, centG, centT, s1]
        exact ⟨(Co_right Co_T) i, (Co_right Co_U2) i⟩
    · have hc : ckOfB b ex k = Sum.inr (Sum.inr ⟨k.val - (4 * b + 2), by omega⟩) := by simp [ckOfB, h, h2]
      rw [hc]
      simp [tCoefs, uCoefs, coefC, pdB, h, h2]

end real
end
end CatalanMeasure.GenD.Uniform.W.Charts6
