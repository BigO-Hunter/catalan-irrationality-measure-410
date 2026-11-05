module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZGroupsCap
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZCap3
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ2.CellsLZ
@[expose] public section
set_option Elab.async false

/-!
# Cap window with digit `s+1 = 5` columns (`L > 5p`) (G2h)

`flatCap5`: as `flatCap`, but the columns `J = 5` (residues `ℓ ≤ t` with `ℓ + g + h ≤ t`) are allowed;
they are flat under the single linear condition `c5` at the position `r' = t - ℓ ∈ [g+h, t]`:
`(ψ+(5,4)(u*) - 1) fold(π1)[r'] + z_5 . seq'[r'] = 0` (the window-`(s+1)` response at `J = 5`).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p hp : ℕ} [Fact p.Prime] {K : ℕ}

/-- The digit-`5` group: positions `off + i`, `i < m`. -/
def c5M (P : Parameters) (N p hp K off m : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) :
    ZPar p hp →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.pi fun r : Fin m =>
    (fuV p K (P.H N) u 5 ((4 : ℕ) : ℤ) - 1) • foldL P N p hp (off + r) +
      dotL0 P N p hp (zz p K (P.H N) u u2 y1 y2 5) (off + r)

theorem c5M_apply (off m : ℕ) (u u2 y1 y2 : Fin K → ZMod p) (a : ZPar p hp) (r : Fin m) :
    c5M P N p hp K off m u u2 y1 y2 a r =
      (fuV p K (P.H N) u 5 ((4 : ℕ) : ℤ) - 1) *
          (piSeq P N p a.1 (off + r) + piSeq P N p a.1 (off + r + p)) +
        dotc (zz p K (P.H N) u u2 y1 y2 5) (piSeq P N p a.1) (piSeq P N p a.2.1)
          (laSeq P N p (Aext a.2.2.1)) (laSeq P N p (Aext a.2.2.2)) 0 (off + r) := by
  simp [c5M, foldL_apply, dotL0_apply]

section FlatCap5
variable (hp2 : p ≠ 2) (hphp : hp = (p - 1) / 2) (hhp : P.h N + hp ≤ p - 1)
  (u u2 y1 y2 : Fin K → ZMod p) {μ2 μ3 ν ρ : ZMod p} {ktop k0 : Fin K}
  (hcell : CellHyp p K (P.H N) u u2 y1 y2 μ2 μ3 ν ρ ktop k0)
  (hcap : CellHypCap p K (P.H N) u u2 y1 y2) (h3 : (3 : ZMod p) ≠ 0)
  (τ1 τ2 : Fin (hp + 1) → ZMod p) (σ1 σ2 : Fin hp → ZMod p) (e2 : ℕ)
  (hdv2 : ((X - 1) ^ e2 : (ZMod p)[X]) ∣ tpoly τ2) (he2 : p ≤ P.h N + (p - 1) / 2 + e2)
  (rt g t : ℕ)
  (hvt : ∀ d : Fin (hp + 1), rt < (d : ℕ) →
    (u ktop * τ1 d + u2 ktop * τ2 d) + (y1 ktop * Aext σ1 d + y2 ktop * Aext σ2 d) = 0)
  (hv0 : ∀ d : Fin (hp + 1), g < (d : ℕ) →
    (u k0 * τ1 d + u2 k0 * τ2 d) - (y1 k0 * Aext σ1 d + y2 k0 * Aext σ2 d) = 0)
  (hmain : ∀ r, t + 1 ≤ r → r < P.h N + hp →
    dotc (fun c => vv p K (P.H N) u u2 y1 y2 2 c - vv p K (P.H N) u u2 y1 y2 1 c)
      (piSeq P N p τ1) (piSeq P N p τ2) (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0)
  (hds : ∀ r, t + 1 ≤ r → g + P.h N ≤ r → r < P.h N + max g rt → r < P.h N + hp →
    dotc (vv p K (P.H N) u u2 y1 y2 4) (piSeq P N p τ1) (piSeq P N p τ2)
      (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0)
  (hd0 : ∀ r : ℕ, t + 1 ≤ r → r < p → ((P.b N : ℤ) ≤ ((P.H N : ℤ) - 1 - 4 * p) - (r : ℤ)) →
    (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) * (piSeq P N p τ1 r + piSeq P N p τ1 (r + p)) +
      dotc (vv p K (P.H N) u u2 y1 y2 0) (piSeq P N p τ1) (piSeq P N p τ2)
        (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r = 0)
  (hY : ∀ r, r ≤ t →
    dotc (zz p K (P.H N) u u2 y1 y2 2) (piSeq P N p τ1) (piSeq P N p τ2)
      (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) 0 r = 0)
  (hC1 : ∀ r, r ≤ t →
    dotc (zz p K (P.H N) u u2 y1 y2 1) (piSeq P N p τ1) (piSeq P N p τ2)
      (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) 0 r = 0)
  (hC0 : ∀ r, r ≤ t → P.b N + r ≤ t →
    (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) * (piSeq P N p τ1 r + piSeq P N p τ1 (r + p)) +
      dotc (zz p K (P.H N) u u2 y1 y2 0) (piSeq P N p τ1) (piSeq P N p τ2)
        (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) 0 r = 0)
  (hC5 : ∀ r, r ≤ t → P.g N + P.h N ≤ r →
    (fuV p K (P.H N) u 5 ((4 : ℕ) : ℤ) - 1) * (piSeq P N p τ1 r + piSeq P N p τ1 (r + p)) +
      dotc (zz p K (P.H N) u u2 y1 y2 5) (piSeq P N p τ1) (piSeq P N p τ2)
        (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) 0 r = 0)
  (hη1 : P.h N + hp ≤ P.H N - 4 * p) (hHt : P.H N = t + 1 + 5 * p) (ht : t < p)
  (hb : P.b N < p) (hgP : g = P.g N)

include hp2 hphp hhp hcell hcap h3 hdv2 he2 hvt hv0 hmain hds hd0 hY hC1 hC0 hC5 hHt ht hb hgP

/-- **Every column is flat** (cap window, with the digit-`5` columns). -/
theorem flatCap5 (hD : hp + 1 ≤ (p - 1) / 2 + 1)
    (hemax : P.h N + (p - 1) + (hp + 1) ≤ 2 * p) (ell : ℕ) (hl : ell < p)
    (J : ℕ) (hJ1 : P.b N ≤ J * p + ell) (hJ2 : J * p + ell < P.L N) :
    (zSys P N p hp2 K (hp + 1) hD).resp J ell
        (mergeData (Sdata u u2 τ1 τ2) (Adata y1 y2 σ1 σ2)) =
      piSeq P N p τ1 ((((P.H N : ℤ) - 1 - ell) % p).toNat) +
        piSeq P N p τ1 ((((P.H N : ℤ) - 1 - ell) % p).toNat + p) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [zSys_resp_two hp2 hD hemax]
  have hHL : P.H N = P.L N + P.g N + P.h N := by
    simp [Parameters.H, Parameters.C]
  by_cases hle : ell ≤ t
  · -- window s+1 first
    have hJ5 : J ≤ 5 := by
      by_contra hcon
      have : 6 * p ≤ J * p := Nat.mul_le_mul_right p (by omega)
      omega
    have hdm := divmod_eq ((P.H N : ℤ) - 1 - ell) 5 ((t : ℤ) - ell) p hp0 (by omega) (by omega)
      (by omega)
    rw [hdm.1, hdm.2]
    set r : ℕ := ((t : ℤ) - ell).toNat with hr
    have hrz : (r : ℤ) = (t : ℤ) - ell := Int.toNat_of_nonneg (by omega)
    have hrp : r < p := by omega
    have e5 : (5 : ℤ) = ((5 : ℕ) : ℤ) := by norm_num
    have e4 : (5 : ℤ) - 1 = ((4 : ℕ) : ℤ) := by norm_num
    rw [e4, e5]
    have hsec : (if r + p < P.h N + (p - 1) + (hp + 1) then
        termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J ((4 : ℕ) : ℤ) (r + p) else 0) =
        termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J ((4 : ℕ) : ℤ) (r + p) := by
      split_ifs with h1
      · rfl
      · exact (termAt_hi_zero hp2 hphp hhp u u2 y1 y2 τ1 τ2 σ1 σ2 e2 hdv2 he2 J _ r hrp
          (by omega)).symm
    rw [if_pos (by omega), hsec]
    have hf := fold2 (P := P) (N := N) hp2 hphp hhp τ2 e2 hdv2 he2 r hrp
    have hl1 : laSeq P N p (Aext σ1) (r + p) = 0 := laSeq_hi_zero hp2 _ _ (by omega)
    have hl2 : laSeq P N p (Aext σ2) (r + p) = 0 := laSeq_hi_zero hp2 _ _ (by omega)
    rw [regionII_eq u u2 y1 y2 τ1 τ2 σ1 σ2 J r hf.1 hl1 hl2]
    have hYr := hY r (by omega)
    obtain ⟨hz3, hz4⟩ := dotz_34 hcap h3 (two_ne_zero_zmod hp2) _ _ _ _ r hYr
    have hu := fun J' (h : J' ∈ [1, 2, 3, 4]) => hcell.fold J' h
    interval_cases J
    · have := hC0 r (by omega) (by omega)
      linear_combination this
    · rw [hu 1 (by simp), hC1 r (by omega)]; ring
    · rw [hu 2 (by simp), hYr]; ring
    · rw [hu 3 (by simp), hz3]; ring
    · rw [hu 4 (by simp), hz4]; ring
    · have := hC5 r (by omega) (by omega)
      linear_combination this
  · -- window s first
    have hJ4 : J ≤ 4 := by
      by_contra hcon
      have h5 : J = 5 ∨ 6 ≤ J := by omega
      rcases h5 with h5 | h5
      · subst h5; omega
      · have : 6 * p ≤ J * p := Nat.mul_le_mul_right p h5
        omega
    have hdm := divmod_eq ((P.H N : ℤ) - 1 - ell) 4 (((P.H N : ℤ) - 1 - 4 * p) - ell) p hp0
      (by ring) (by omega) (by omega)
    rw [hdm.1, hdm.2]
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
    exact col_I hp2 hphp hhp u u2 y1 y2 hcell τ1 τ2 σ1 σ2 e2 hdv2 he2 rt g (t + 1) hvt hv0 hmain
      hds hd0 r hrp (by omega) J hJ4 (fun h => by subst h; omega) (fun h => by subst h; omega)

end FlatCap5

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
