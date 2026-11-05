module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZFlat
@[expose] public section
set_option Elab.async false

/-!
# Window-`s` response formula and the digit conclusions
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- **Window-`s` formula**: `ψ+(J,4)(u) fold(π1)[r] + dotv J r`. -/
theorem regionI_eq {K hp : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (τ1 τ2 : Fin (hp + 1) → ZMod p)
    (σ1 σ2 : Fin hp → ZMod p) (J r : ℕ)
    (hf2 : piSeq P N p τ2 r + piSeq P N p τ2 (r + p) = 0)
    (hl1 : laSeq P N p (Aext σ1) (r + p) = 0) (hl2 : laSeq P N p (Aext σ2) (r + p) = 0) :
    termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J ((4 : ℕ) : ℤ) r +
        termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J ((3 : ℕ) : ℤ) (r + p) =
      fuV p K (P.H N) u J ((4 : ℕ) : ℤ) * (piSeq P N p τ1 r + piSeq P N p τ1 (r + p)) +
        dotc (vv p K (P.H N) u u2 y1 y2 J) (piSeq P N p τ1) (piSeq P N p τ2)
          (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r := by
  have e : piSeq P N p τ2 r = - piSeq P N p τ2 (r + p) := by linear_combination hf2
  rw [dotc_expand]
  simp only [termAt, vv, fuV, e, hl1, hl2]
  ring

/-- If the sequences vanish at position `r`, so does every `dotc`. -/
theorem dotc_zero_of_seq (v : ℕ → ZMod p) (π1 π2 l1 l2 : ℕ → ZMod p) (p' r : ℕ)
    (h0 : π1 (r + p') = 0) (h1 : π2 (r + p') = 0) (h2 : l1 r = 0) (h3 : l2 r = 0) :
    dotc v π1 π2 l1 l2 p' r = 0 := by
  rw [dotc_expand, h0, h1, h2, h3]; ring

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
