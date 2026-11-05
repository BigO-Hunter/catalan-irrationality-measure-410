module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.QForms
@[expose] public section
set_option Elab.async false

/-!
# Law_H cells at `s = 4` (blocks `0..3`)

Rational profile vectors `u*` (single `T+`), `u2` (raw `Td`), `y1`, `y2` (raw `T-`), the exact
checks of their defining properties, and the identity (P*) of zone2 sec. 2 (one rational
identity, `Δ_s = Σ μ_J (v_J - v_1) + ν t + ρ b0`).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ.Q
open OAI.InternalCatalan

def vecOf (l : List ℚ) : ℕ → ℚ := fun k => l.getD k 0

def uH : ℕ → ℚ := vecOf [(-72731/27905), (-6140684/1925445), (-1223492/1925445), (-422708/1155267)]
def u2H : ℕ → ℚ := vecOf [(5960813/507698), (3139473/253849), (542686/253849), 1]
def y1H : ℕ → ℚ := vecOf [(-1519607/204357), (610301/68119), (1143/68119), 1]
def y2H : ℕ → ℚ := vecOf [(-128911946/13549857), (40711497/4516619), (-29478/4516619), 1]

/-- `Φ_{T+}(J,S;z)` over blocks `0..K-1`. -/
def fTp (K : ℕ) (z : ℕ → ℚ) (J S : ℕ) : ℚ := comb K z fun k => PhiTp k J S
def fTm (K : ℕ) (z : ℕ → ℚ) (J S : ℕ) : ℚ := comb K z fun k => PhiTm k J S
def fTd (K : ℕ) (z : ℕ → ℚ) (J S : ℕ) : ℚ := comb K z fun k => PhiTd k J S

-- cell properties
theorem uH_fold : ∀ J ∈ [1, 2, 3, 4], fTp 4 uH J 4 = 1 := by decide +kernel
theorem u2H_raw : ∀ J ∈ [1, 2, 3], fTd 4 u2H J 4 = 0 := by decide +kernel
theorem y1H_raw : ∀ J ∈ [1, 2, 3], fTm 4 y1H J 4 = 0 := by decide +kernel
theorem y2H_raw : ∀ J ∈ [2, 3, 4], fTm 4 y2H J 5 = 0 := by decide +kernel

end CatalanMeasure.GenD.Uniform.W.ZoneZ.Q
