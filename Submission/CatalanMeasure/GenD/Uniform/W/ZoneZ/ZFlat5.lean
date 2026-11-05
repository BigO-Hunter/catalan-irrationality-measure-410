module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZFlat4
@[expose] public section
set_option Elab.async false

/-!
# Column-by-column flatness (Law_H(4), no cap)
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

section Col
variable (hp2 : p ≠ 2) {hp : ℕ} (hphp : hp = (p - 1) / 2) (hhp : P.h N + hp ≤ p - 1)
  {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) {μ2 μ3 ν ρ : ZMod p} {ktop k0 : Fin K}
  (hcell : CellHyp p K (P.H N) u u2 y1 y2 μ2 μ3 ν ρ ktop k0)
  (τ1 τ2 : Fin (hp + 1) → ZMod p) (σ1 σ2 : Fin hp → ZMod p) (e2 : ℕ)
  (hdv2 : ((X - 1) ^ e2 : (ZMod p)[X]) ∣ tpoly τ2) (he2 : p ≤ P.h N + (p - 1) / 2 + e2)
  (rt g r0 : ℕ)
  (hvt : ∀ d : Fin (hp + 1), rt < (d : ℕ) →
    (u ktop * τ1 d + u2 ktop * τ2 d) + (y1 ktop * Aext σ1 d + y2 ktop * Aext σ2 d) = 0)
  (hv0 : ∀ d : Fin (hp + 1), g < (d : ℕ) →
    (u k0 * τ1 d + u2 k0 * τ2 d) - (y1 k0 * Aext σ1 d + y2 k0 * Aext σ2 d) = 0)
  (hmain : ∀ r, r0 ≤ r → r < P.h N + hp →
    dotc (fun c => vv p K (P.H N) u u2 y1 y2 2 c - vv p K (P.H N) u u2 y1 y2 1 c)
      (piSeq P N p τ1) (piSeq P N p τ2) (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0)
  (hds : ∀ r, r0 ≤ r → g + P.h N ≤ r → r < P.h N + max g rt → r < P.h N + hp →
    dotc (vv p K (P.H N) u u2 y1 y2 4) (piSeq P N p τ1) (piSeq P N p τ2)
      (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0)
  (hd0 : ∀ r : ℕ, r0 ≤ r → r < p → ((P.b N : ℤ) ≤ ((P.H N : ℤ) - 1 - 4 * p) - (r : ℤ)) →
    (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) * (piSeq P N p τ1 r + piSeq P N p τ1 (r + p)) +
      dotc (vv p K (P.H N) u u2 y1 y2 0) (piSeq P N p τ1) (piSeq P N p τ2)
        (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0)

include hp2 hphp hhp hcell hdv2 he2 hvt hv0 hmain hds hd0

/-- **Window `s` columns** (`ℓ ≤ η`): the response is the fold. -/
theorem col_I (r : ℕ) (hr : r < p) (hr0 : r0 ≤ r) (J : ℕ) (hJ : J ≤ 4)
    (hJ0 : J = 0 → ((P.b N : ℤ) ≤ ((P.H N : ℤ) - 1 - 4 * p) - (r : ℤ)))
    (hJ4 : J = 4 → g + P.h N ≤ r) :
    termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J ((4 : ℕ) : ℤ) r +
      termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J ((3 : ℕ) : ℤ) (r + p) =
      piSeq P N p τ1 r + piSeq P N p τ1 (r + p) := by
  have hf := fold2 (P := P) (N := N) hp2 hphp hhp τ2 e2 hdv2 he2 r hr
  have hl1 : laSeq P N p (Aext σ1) (r + p) = 0 := laSeq_hi_zero hp2 _ _ (by omega)
  have hl2 : laSeq P N p (Aext σ2) (r + p) = 0 := laSeq_hi_zero hp2 _ _ (by omega)
  rw [regionI_eq u u2 y1 y2 τ1 τ2 σ1 σ2 J r hf.1 hl1 hl2]
  obtain ⟨⟨d1, d2, d3⟩, d4⟩ := dot_digits hp2 hphp hhp u u2 y1 y2 hcell τ1 τ2 σ1 σ2 e2 hdv2 he2
    rt g r0 hvt hv0 hmain hds r hr hr0
  have hu := fun J' (h : J' ∈ [1, 2, 3, 4]) => hcell.fold J' h
  interval_cases J
  · have := hd0 r hr0 hr (hJ0 rfl)
    linear_combination this
  · rw [hu 1 (by simp), d1]; ring
  · rw [hu 2 (by simp), d2]; ring
  · rw [hu 3 (by simp), d3]; ring
  · rw [hu 4 (by simp), d4 (hJ4 rfl)]; ring

end Col

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
