module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZFlat3
@[expose] public section
set_option Elab.async false

/-!
# J-flatness of a Theorem Z atom, Law_H(4), no cap (`η < p`)

`flatH`: every column `j = J p + ℓ ∈ [b, L)` has response `fold(π1)[r]`, `r = (H-1-ℓ) mod p`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- All four sequences vanish at `r ≥ h + hp` (position `r < p`). -/
theorem seq_zero_hi (hp2 : p ≠ 2) {hp : ℕ} (hphp : hp = (p - 1) / 2) (hhp : P.h N + hp ≤ p - 1)
    (τ1 τ2 : Fin (hp + 1) → ZMod p) (σ1 σ2 : Fin hp → ZMod p) (e2 : ℕ)
    (hdv2 : ((X - 1) ^ e2 : (ZMod p)[X]) ∣ tpoly τ2) (he2 : p ≤ P.h N + (p - 1) / 2 + e2)
    (r : ℕ) (hr : r < p) (hrr : P.h N + hp ≤ r) :
    piSeq P N p τ1 (r + p) = 0 ∧ piSeq P N p τ2 r = 0 ∧ piSeq P N p τ2 (r + p) = 0 ∧
      laSeq P N p (Aext σ1) r = 0 ∧ laSeq P N p (Aext σ2) r = 0 := by
  have hf := fold2 (P := P) (N := N) hp2 hphp hhp τ2 e2 hdv2 he2 r hr
  refine ⟨piSeq_hi_zero hp2 τ1 _ (by omega), (hf.2 hrr).1, (hf.2 hrr).2,
    laSeq_hi_zero hp2 _ r hrr, laSeq_hi_zero hp2 _ r hrr⟩

section Flat
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

include hp2 hphp hhp hcell hdv2 he2 hvt hv0 hmain hds

/-- `dotc (vv J) r` vanishes for `J = 1,2,3,4` (given the digit-`s` presence `g + h ≤ r` for `J = 4`). -/
theorem dot_digits (r : ℕ) (hr : r < p) (hr0 : r0 ≤ r) :
    (dotc (vv p K (P.H N) u u2 y1 y2 1) (piSeq P N p τ1) (piSeq P N p τ2)
        (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0 ∧
      dotc (vv p K (P.H N) u u2 y1 y2 2) (piSeq P N p τ1) (piSeq P N p τ2)
        (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0 ∧
      dotc (vv p K (P.H N) u u2 y1 y2 3) (piSeq P N p τ1) (piSeq P N p τ2)
        (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0) ∧
    (g + P.h N ≤ r →
      dotc (vv p K (P.H N) u u2 y1 y2 4) (piSeq P N p τ1) (piSeq P N p τ2)
        (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0) := by
  by_cases hrr : P.h N + hp ≤ r
  · obtain ⟨a1, a2, a3, a4, a5⟩ := seq_zero_hi hp2 hphp hhp τ1 τ2 σ1 σ2 e2 hdv2 he2 r hr hrr
    exact ⟨⟨dotc_zero_of_seq _ _ _ _ _ _ _ a1 a3 a4 a5, dotc_zero_of_seq _ _ _ _ _ _ _ a1 a3 a4 a5,
      dotc_zero_of_seq _ _ _ _ _ _ _ a1 a3 a4 a5⟩,
      fun _ => dotc_zero_of_seq _ _ _ _ _ _ _ a1 a3 a4 a5⟩
  · have hrr' : r < P.h N + hp := by omega
    have hW := hmain r hr0 hrr'
    refine ⟨dot_J123 hcell _ _ _ _ r hW, fun hgr => ?_⟩
    by_cases hmx : r < P.h N + max g rt
    · exact hds r hr0 hgr hmx hrr'
    · refine dot_J4_implied hcell _ _ _ _ r hW ?_ ?_
      · exact Qtop_zero hp2 (by omega) u u2 y1 y2 τ1 τ2 σ1 σ2 ktop rt hvt r (by omega)
      · exact Qzero_zero hp2 (by omega) u u2 y1 y2 τ1 τ2 σ1 σ2 k0 g hv0 r (by omega)

end Flat

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
