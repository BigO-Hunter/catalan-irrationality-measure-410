module

public import Submission.CatalanMeasure.GenD.Signed.Data.S1.Bridge

@[expose] public section

/-!
# S1: the gap parameter and the circle-cover plumbing (lane D3)

`aQ = 2 g / (1 + g^2)` for `g = 401/2500` (the D58 gap), as a rational, and the generic
`circCover` list lemmas used by every per-radius module `Circ0 .. Circ13`.
-/

namespace CatalanMeasure.GenD.Signed.Data.S1
open CatalanMeasure.GenD.Analytic

noncomputable section

def aQ : ℚ := 2005000 / 6410801

/-- The gap parameter as a real number. -/
def aGap : ℝ := ((aQ : ℚ) : ℝ)

theorem aGap_eq : aGap = 2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2) := by
  unfold aGap aQ; push_cast; norm_num

theorem aQ_pos : (0 : ℝ) < ((aQ : ℚ) : ℝ) := by unfold aQ; norm_num
theorem aQ_lt_one : ((aQ : ℚ) : ℝ) < 1 := by unfold aQ; norm_num
theorem aGap_pos : 0 < aGap := aQ_pos
theorem aGap_lt_one : aGap < 1 := aQ_lt_one
theorem aGap_ha4 : 1 - aGap ^ 2 ≤ 4 * aGap := by unfold aGap aQ; push_cast; norm_num
theorem aGap_le_half : aGap ≤ 1 / 2 := by unfold aGap aQ; push_cast; norm_num

theorem circCover_cons' {a r E Csq : ℚ} {d m : ℕ} {c : ℚ} {p : CircPiece} {l : List CircPiece}
    (hc : p.lo = c) (hp : p.ok a r E Csq d m = true)
    (hl : circCover a r E Csq d m p.hi l = true) :
    circCover a r E Csq d m c (p :: l) = true := by
  simp only [circCover, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hc, hp⟩, hl⟩

theorem circCover_nil' {a r E Csq : ℚ} {d m : ℕ} {c : ℚ} (hc : c = r) :
    circCover a r E Csq d m c [] = true := by
  simp only [circCover, decide_eq_true_eq]
  exact hc

end

end CatalanMeasure.GenD.Signed.Data.S1
