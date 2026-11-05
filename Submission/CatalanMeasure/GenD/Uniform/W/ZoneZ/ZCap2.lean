module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZCap1
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZFlat6
@[expose] public section
set_option Elab.async false

/-!
# Window `s+1` zone: the response at residues `ℓ ≤ t`
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- **Window `s+1` formula**: `ψ+(J,4)(u) fold(π1)[r'] + z_J . seq'[r']` (`seq'` unshifted). -/
theorem regionII_eq {K hp : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (τ1 τ2 : Fin (hp + 1) → ZMod p)
    (σ1 σ2 : Fin hp → ZMod p) (J r : ℕ)
    (hf2 : piSeq P N p τ2 r + piSeq P N p τ2 (r + p) = 0)
    (hl1 : laSeq P N p (Aext σ1) (r + p) = 0) (hl2 : laSeq P N p (Aext σ2) (r + p) = 0) :
    termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J ((5 : ℕ) : ℤ) r +
        termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J ((4 : ℕ) : ℤ) (r + p) =
      fuV p K (P.H N) u J ((4 : ℕ) : ℤ) * (piSeq P N p τ1 r + piSeq P N p τ1 (r + p)) +
        dotc (zz p K (P.H N) u u2 y1 y2 J) (piSeq P N p τ1) (piSeq P N p τ2)
          (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) 0 r := by
  have e : piSeq P N p τ2 (r + p) = - piSeq P N p τ2 r := by linear_combination hf2
  rw [dotc_expand]
  simp only [termAt, zz, fuV, Nat.add_zero, e, hl1, hl2]
  ring

section Cap
variable {K : ℕ} {u u2 y1 y2 : Fin K → ZMod p} {H : ℕ}
  (hc : CellHypCap p K H u u2 y1 y2) (h3 : (3 : ZMod p) ≠ 0) (h2 : (2 : ZMod p) ≠ 0)
  (π1 π2 l1 l2 : ℕ → ZMod p) (r : ℕ)

include hc h3 h2

/-- `J = 3, 4` follow from `J = 2` in the window `s+1` zone. -/
theorem dotz_34 (hY : dotc (zz p K H u u2 y1 y2 2) π1 π2 l1 l2 0 r = 0) :
    dotc (zz p K H u u2 y1 y2 3) π1 π2 l1 l2 0 r = 0 ∧
    dotc (zz p K H u u2 y1 y2 4) π1 π2 l1 l2 0 r = 0 := by
  have a3 : dotc (fun c => 3 * zz p K H u u2 y1 y2 3 c) π1 π2 l1 l2 0 r =
      dotc (fun c => 2 * zz p K H u u2 y1 y2 2 c) π1 π2 l1 l2 0 r :=
    dotc_congr _ _ _ _ _ _ _ _ (fun c hc4 => hc.zr3 c hc4)
  have a4 : dotc (fun c => 2 * zz p K H u u2 y1 y2 4 c) π1 π2 l1 l2 0 r =
      dotc (zz p K H u u2 y1 y2 2) π1 π2 l1 l2 0 r :=
    dotc_congr _ _ _ _ _ _ _ _ (fun c hc4 => hc.zr4 c hc4)
  rw [dotc_smul, dotc_smul, hY, mul_zero] at a3
  rw [dotc_smul, hY] at a4
  exact ⟨(mul_eq_zero.mp a3).resolve_left h3, (mul_eq_zero.mp a4).resolve_left h2⟩

end Cap

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
