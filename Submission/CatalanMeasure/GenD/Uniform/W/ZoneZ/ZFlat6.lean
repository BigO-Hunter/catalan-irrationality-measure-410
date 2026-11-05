module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZFlat5
@[expose] public section
set_option Elab.async false

/-!
# Law_H(4) without cap: every column is flat

`flatH`: for `ℓ < p` and `b ≤ J p + ℓ < L`, the slot response of the atom is
`fold(π1)[r] = π1[r] + π1[r+p]`, `r = (H-1-ℓ) mod p`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `termAt` vanishes at positions `≥ emax`. -/
theorem termAt_hi_zero (hp2 : p ≠ 2) {hp : ℕ} (hphp : hp = (p - 1) / 2) (hhp : P.h N + hp ≤ p - 1)
    {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (τ1 τ2 : Fin (hp + 1) → ZMod p)
    (σ1 σ2 : Fin hp → ZMod p) (e2 : ℕ) (hdv2 : ((X - 1) ^ e2 : (ZMod p)[X]) ∣ tpoly τ2)
    (he2 : p ≤ P.h N + (p - 1) / 2 + e2) (J : ℕ) (σ : ℤ) (r : ℕ) (hr : r < p)
    (hrr : P.h N + hp ≤ r) :
    termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J σ (r + p) = 0 := by
  have hf := fold2 (P := P) (N := N) hp2 hphp hhp τ2 e2 hdv2 he2 r hr
  have h1 : piSeq P N p τ1 (r + p) = 0 := piSeq_hi_zero hp2 τ1 _ (by omega)
  have h2 : piSeq P N p τ2 (r + p) = 0 := (hf.2 hrr).2
  have h3 : laSeq P N p (Aext σ1) (r + p) = 0 := laSeq_hi_zero hp2 _ _ (by omega)
  have h4 : laSeq P N p (Aext σ2) (r + p) = 0 := laSeq_hi_zero hp2 _ _ (by omega)
  simp only [termAt, h1, h2, h3, h4]; ring

section Flat6
variable (hp2 : p ≠ 2) {hp : ℕ} (hphp : hp = (p - 1) / 2) (hhp : P.h N + hp ≤ p - 1)
  {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) {μ2 μ3 ν ρ : ZMod p} {ktop k0 : Fin K}
  (hcell : CellHyp p K (P.H N) u u2 y1 y2 μ2 μ3 ν ρ ktop k0)
  (τ1 τ2 : Fin (hp + 1) → ZMod p) (σ1 σ2 : Fin hp → ZMod p) (e2 : ℕ)
  (hdv2 : ((X - 1) ^ e2 : (ZMod p)[X]) ∣ tpoly τ2) (he2 : p ≤ P.h N + (p - 1) / 2 + e2)
  (rt g : ℕ)
  (hvt : ∀ d : Fin (hp + 1), rt < (d : ℕ) →
    (u ktop * τ1 d + u2 ktop * τ2 d) + (y1 ktop * Aext σ1 d + y2 ktop * Aext σ2 d) = 0)
  (hv0 : ∀ d : Fin (hp + 1), g < (d : ℕ) →
    (u k0 * τ1 d + u2 k0 * τ2 d) - (y1 k0 * Aext σ1 d + y2 k0 * Aext σ2 d) = 0)
  (hmain : ∀ r, 0 ≤ r → r < P.h N + hp →
    dotc (fun c => vv p K (P.H N) u u2 y1 y2 2 c - vv p K (P.H N) u u2 y1 y2 1 c)
      (piSeq P N p τ1) (piSeq P N p τ2) (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0)
  (hds : ∀ r, 0 ≤ r → g + P.h N ≤ r → r < P.h N + max g rt → r < P.h N + hp →
    dotc (vv p K (P.H N) u u2 y1 y2 4) (piSeq P N p τ1) (piSeq P N p τ2)
      (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0)
  (hd0 : ∀ r : ℕ, 0 ≤ r → r < p → ((P.b N : ℤ) ≤ ((P.H N : ℤ) - 1 - 4 * p) - (r : ℤ)) →
    (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) * (piSeq P N p τ1 r + piSeq P N p τ1 (r + p)) +
      dotc (vv p K (P.H N) u u2 y1 y2 0) (piSeq P N p τ1) (piSeq P N p τ2)
        (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0)
  (hw : ∀ r : ℕ, ((P.H N : ℤ) - 1 - 4 * p) < (r : ℤ) → r < p → piSeq P N p τ1 r = 0)
  (hη1 : ((P.h N + hp : ℕ) : ℤ) - 1 ≤ (P.H N : ℤ) - 1 - 4 * p)
  (hη2 : (P.H N : ℤ) - 1 - 4 * p < p)
  (hb : P.b N < p) (hgP : g = P.g N)

include hp2 hphp hhp hcell hdv2 he2 hvt hv0 hmain hds hd0 hw hη1 hη2 hb hgP

/-- **Every column is flat** (Law_H(4), `η < p`). -/
theorem flatH (hD : hp + 1 ≤ (p - 1) / 2 + 1)
    (hemax : P.h N + (p - 1) + (hp + 1) ≤ 2 * p) (ell : ℕ) (hl : ell < p) (J : ℕ)
    (hJ1 : P.b N ≤ J * p + ell) (hJ2 : J * p + ell < P.L N) :
    (zSys P N p hp2 K (hp + 1) hD).resp J ell
        (mergeData (Sdata u u2 τ1 τ2) (Adata y1 y2 σ1 σ2)) =
      piSeq P N p τ1 ((((P.H N : ℤ) - 1 - ell) % p).toNat) +
        piSeq P N p τ1 ((((P.H N : ℤ) - 1 - ell) % p).toNat + p) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [zSys_resp_two hp2 hD hemax]
  have hHL : P.H N = P.L N + P.g N + P.h N := by
    simp [Parameters.H, Parameters.C]
  by_cases hle : (ell : ℤ) ≤ (P.H N : ℤ) - 1 - 4 * p
  · -- window s
    have hdm := divmod_eq ((P.H N : ℤ) - 1 - ell) 4 (((P.H N : ℤ) - 1 - 4 * p) - ell) p hp0
      (by ring) (by omega) (by omega)
    rw [hdm.1, hdm.2]
    have hJ5 : J ≤ 4 := by
      by_contra hcon
      have : 5 * p ≤ J * p := Nat.mul_le_mul_right p (by omega)
      omega
    set r : ℕ := (((P.H N : ℤ) - 1 - 4 * p) - ell).toNat with hr
    have hrz : (r : ℤ) = ((P.H N : ℤ) - 1 - 4 * p) - ell := Int.toNat_of_nonneg (by omega)
    have hrp : r < p := by omega
    have e4 : (4 : ℤ) = ((4 : ℕ) : ℤ) := by norm_num
    have e3 : (4 : ℤ) - 1 = ((3 : ℕ) : ℤ) := by norm_num
    rw [e3, e4]
    have hsec : (if r + p < P.h N + (p - 1) + (hp + 1) then
        termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J ((3 : ℕ) : ℤ) (r + p) else 0) =
        termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J ((3 : ℕ) : ℤ) (r + p) := by
      split_ifs with h1
      · rfl
      · exact (termAt_hi_zero hp2 hphp hhp u u2 y1 y2 τ1 τ2 σ1 σ2 e2 hdv2 he2 J _ r hrp
          (by omega)).symm
    rw [if_pos (by omega), hsec]
    exact col_I hp2 hphp hhp u u2 y1 y2 hcell τ1 τ2 σ1 σ2 e2 hdv2 he2 rt g 0 hvt hv0 hmain hds hd0
      r hrp (Nat.zero_le _) J hJ5 (fun h => by subst h; omega) (fun h => by subst h; omega)
  · -- window s-1 (ℓ > η)
    have hdm := divmod_eq ((P.H N : ℤ) - 1 - ell) 3 (((P.H N : ℤ) - 1 - 4 * p) - ell + p) p hp0
      (by ring) (by omega) (by omega)
    rw [hdm.1, hdm.2]
    set r : ℕ := (((P.H N : ℤ) - 1 - 4 * p) - ell + p).toNat with hr
    have hrz : (r : ℤ) = ((P.H N : ℤ) - 1 - 4 * p) - ell + p := Int.toNat_of_nonneg (by omega)
    have hrp : r < p := by omega
    have hrr : P.h N + hp ≤ r := by omega
    have e3 : (3 : ℤ) = ((3 : ℕ) : ℤ) := by norm_num
    rw [e3, if_pos (by omega), if_neg (by omega), add_zero]
    have hf := fold2 (P := P) (N := N) hp2 hphp hhp τ2 e2 hdv2 he2 r hrp
    have h1 : piSeq P N p τ1 (r + p) = 0 := piSeq_hi_zero hp2 τ1 _ (by omega)
    have h0 : piSeq P N p τ1 r = 0 := hw r (by omega) hrp
    have h2 : piSeq P N p τ2 r = 0 := (hf.2 hrr).1
    have h3 : laSeq P N p (Aext σ1) r = 0 := laSeq_hi_zero hp2 _ _ hrr
    have h4 : laSeq P N p (Aext σ2) r = 0 := laSeq_hi_zero hp2 _ _ hrr
    simp only [termAt, h0, h1, h2, h3, h4]; ring

end Flat6

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
