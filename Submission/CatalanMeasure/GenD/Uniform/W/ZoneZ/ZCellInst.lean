module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZMain2
@[expose] public section
set_option Elab.async false

/-!
# The Law_H cells as a `CellHyp`

For `p ≠ 2`, `p ∤ ZcH'` (the integer `ZcH` with the numerators of the two independence
determinants) the residue cells satisfy `CellHyp` and the independence hypotheses of
`zH_le_nullity`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- Independence determinants of the Law_H cells (blocks 2, 3). -/
def DqU : ℚ := Q.uH 2 * Q.u2H 3 - Q.uH 3 * Q.u2H 2
def DqY : ℚ := Q.y1H 2 * Q.y2H 3 - Q.y1H 3 * Q.y2H 2

/-- Final bad-prime integer for Law_H. -/
def ZcH' : ℕ := Nat.lcm ZcH (Nat.lcm DqU.num.natAbs DqY.num.natAbs)

theorem DqU_num_ne : DqU.num ≠ 0 := by unfold DqU; decide +kernel
theorem DqY_num_ne : DqY.num ≠ 0 := by unfold DqY; decide +kernel

theorem hind_gen (a b c d : ZMod p) (hD : a * d - c * b ≠ 0) (c1 c2 : ZMod p)
    (h1 : c1 * a + c2 * b = 0) (h2 : c1 * c + c2 * d = 0) : c1 = 0 ∧ c2 = 0 := by
  constructor
  · have : c1 * (a * d - c * b) = 0 := by linear_combination d * h1 - b * h2
    exact (mul_eq_zero.mp this).resolve_right hD
  · have : c2 * (a * d - c * b) = 0 := by linear_combination a * h2 - c * h1
    exact (mul_eq_zero.mp this).resolve_right hD

theorem res_ne_zero_of_num (q : ℚ) (hq : q ∈ unitSub p) (hn : ¬ p ∣ q.num.natAbs) :
    palindromicRatResidue p q ≠ 0 := by
  unfold palindromicRatResidue
  have hd : ((q.den : ℕ) : ZMod p) ≠ 0 := hq
  have hn' : ((q.num : ℤ) : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact hn (Int.natCast_dvd.mp h)
  exact div_ne_zero hn' hd

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
