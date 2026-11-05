module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts5.Cover
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts5
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O CatalanMeasure.GenD.D58.Odd CatalanMeasure.Parametric
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts Finset
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem low146_apply (y : Fin packetO.d → Fp) : low146 p y = emb packetO p 44 y 42 := rfl

/-- The slack jets: for `e ≥ 8N - p` some group `6..9` has the reversed jet `proj e`. -/
theorem slack_jet (hW : Win N p) (e : Fin p) (he : 8 * N - p ≤ e.val) :
    ∃ g k, g < 11 ∧ k < wd N p g ∧ jetP N p g k = LinearMap.proj e ∧ hasRow g (unitL 43) = true := by
  have hN := hW.1; have hp6 := hW.2.1; have hp152 := hW.2.2.1
  have w6 := wd6 hW; have w7 := wd7 hW; have w8 := wd8 hW; have w9 := wd9 hW
  obtain ⟨i6, i7, i8, i9⟩ := inf_low
  have hep := e.isLt
  by_cases h6 : p - 1 - e.val < wd N p 6
  · exact ⟨6, p - 1 - e.val, by norm_num, h6, by rw [show jetP N p 6 (p - 1 - e.val) = jetInf (p - 1 - e.val) by simp [jetP]]; exact jetInf_eq _ e rfl, i6⟩
  by_cases h7 : p - 1 - e.val < wd N p 6 + wd N p 7
  · refine ⟨7, p - 1 - e.val - wd N p 6, by norm_num, by omega, ?_, i7⟩
    rw [show jetP N p 7 (p - 1 - e.val - wd N p 6) = jetInf (wd N p 6 + (p - 1 - e.val - wd N p 6)) by simp [jetP]]
    exact jetInf_eq _ e (by omega)
  by_cases h8 : p - 1 - e.val < wd N p 6 + wd N p 7 + wd N p 8
  · refine ⟨8, p - 1 - e.val - (wd N p 6 + wd N p 7), by norm_num, by omega, ?_, i8⟩
    rw [show jetP N p 8 (p - 1 - e.val - (wd N p 6 + wd N p 7)) =
      jetInf (wd N p 6 + wd N p 7 + (p - 1 - e.val - (wd N p 6 + wd N p 7))) by simp [jetP]]
    exact jetInf_eq _ e (by omega)
  · refine ⟨9, p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8), by norm_num, by omega, ?_, i9⟩
    rw [show jetP N p 9 (p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8)) =
      jetInf (wd N p 6 + wd N p 7 + wd N p 8 + (p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8))) by simp [jetP]]
    exact jetInf_eq _ e (by omega)

end
end CatalanMeasure.GenD.Uniform.W.Charts5
