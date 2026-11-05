module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Column
public import Submission.CatalanMeasure.GenD.Uniform.W.Tier3.FlatRank
@[expose] public section
set_option Elab.async false

/-!
# The per-residue local relation (lane G6c, Theorem L*)

For an admissible residue `ℓ` (single live position `e0`, `h = p + dh`, `dh + (p-1)/2 ≤ e0`), the
J-flatness map `flatPhi id Jset J0 ℓ` has rank at most the number of *non-`D`-virtual blocks*
`|NV|`, where `D = p - 1 - e0 + dh` and block `k` is `D`-virtual when no real row `k p + d` with
`|d| ≤ D` exists.  This is the only analytic step of Theorem L*.
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Tier3
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Block index of the row `r` (signed index `r - g = k p + d`, `|d| ≤ (p-1)/2`). -/
def blkK (p g r : ℕ) : ℤ := (((r : ℤ) - g) + (((p - 1) / 2 : ℕ) : ℤ)) / p

/-- Offset of the row `r` inside its block. -/
def blkD (p g r : ℕ) : ℤ := (((r : ℤ) - g) + (((p - 1) / 2 : ℕ) : ℤ)) % p - (((p - 1) / 2 : ℕ) : ℤ)

theorem blk_eq (hp2 : p ≠ 2) (g r : ℕ) : (r : ℤ) - g = blkK p g r * p + blkD p g r := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h := Int.emod_add_mul_ediv (((r : ℤ) - g) + (((p - 1) / 2 : ℕ) : ℤ)) p
  unfold blkK blkD
  linarith

theorem blkD_natAbs_le (hp2 : p ≠ 2) (g r : ℕ) : (blkD p g r).natAbs ≤ (p - 1) / 2 := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hodd : p = 2 * ((p - 1) / 2) + 1 := by
    have := (Fact.out : p.Prime).two_le
    have := (Fact.out : p.Prime).eq_two_or_odd
    omega
  have h1 := Int.emod_nonneg (((r : ℤ) - g) + (((p - 1) / 2 : ℕ) : ℤ)) hp0.ne'
  have h2 := Int.emod_lt_of_pos (((r : ℤ) - g) + (((p - 1) / 2 : ℕ) : ℤ)) hp0
  unfold blkD
  omega

/-- **The per-residue local relation.**  For an admissible residue the J-flatness map has rank at
most `|NV|`. -/
theorem flatPhi_rank_le (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {dh : ℕ} (hh : P.h N = p + dh) (ℓ : ZMod p) (Jset : ZMod p → Finset ℕ) (J0 : ZMod p → ℕ)
    (hJset : ∀ J ∈ Jset ℓ, J * p + ℓ.val < P.H N) (hJ0 : J0 ℓ * p + ℓ.val < P.H N)
    (he : dh + (p - 1) / 2 ≤ idxRes (P.H N) p ℓ.val) (NV : Finset ℤ)
    (hNV : ∀ r : Fin (P.n N),
      (blkD p (P.g N) r.val).natAbs + idxRes (P.H N) p ℓ.val < p + dh → blkK p (P.g N) r.val ∈ NV) :
    finrank (ZMod p) (LinearMap.range (flatPhi (P := P) (N := N) (p := p) LinearMap.id Jset J0 ℓ)) ≤
      NV.card := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hℓ : ℓ.val < p := ZMod.val_lt ℓ
  have he0 := idxRes_lt hp0 (P.H N) ℓ.val
  let G : ℤ → (↥(Jset ℓ) → ZMod p) := fun k J =>
    Sresp (P.H N) p ℓ.val J.1 k - Sresp (P.H N) p ℓ.val (J0 ℓ) k
  let S : Submodule (ZMod p) (↥(Jset ℓ) → ZMod p) := Submodule.span (ZMod p) (NV.image G : Set _)
  have hcol : ∀ r : Fin (P.n N), flatPhi (P := P) (N := N) (p := p) LinearMap.id Jset J0 ℓ
      (Pi.single r 1) ∈ S := by
    intro r
    set k := blkK p (P.g N) r.val with hk
    set d := blkD p (P.g N) r.val with hd
    have hrd := blk_eq hp2 (P.g N) r.val
    have hdle := blkD_natAbs_le hp2 (P.g N) r.val
    have hfun : flatPhi (P := P) (N := N) (p := p) LinearMap.id Jset J0 ℓ (Pi.single r 1) =
        (qOne p dh d).coeff (idxRes (P.H N) p ℓ.val) • G k := by
      funext J
      simp only [flatPhi, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, G]
      rw [uResp_single hP hN hp2 hH hh hℓ (hJset J.1 J.2) he r k d hrd hdle,
        uResp_single hP hN hp2 hH hh hℓ hJ0 he r k d hrd hdle]
      ring
    rw [hfun]
    by_cases hD : d.natAbs + idxRes (P.H N) p ℓ.val < p + dh
    · exact Submodule.smul_mem _ _ (Submodule.subset_span
        (by simpa using ⟨k, hNV r hD, rfl⟩))
    · rw [qOne_coeff_eq_zero hp2 he0 hdle (by omega), zero_smul]
      exact S.zero_mem
  have hrange : LinearMap.range (flatPhi (P := P) (N := N) (p := p) LinearMap.id Jset J0 ℓ) ≤ S := by
    rintro _ ⟨c, rfl⟩
    have hc : c = ∑ r, c r • (Pi.single r 1 : Fin (P.n N) → ZMod p) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hc, map_sum]
    refine Submodule.sum_mem _ fun r _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (hcol r)
  calc finrank (ZMod p) (LinearMap.range (flatPhi (P := P) (N := N) (p := p) LinearMap.id Jset J0 ℓ))
      ≤ finrank (ZMod p) S := Submodule.finrank_mono hrange
    _ ≤ (NV.image G).card := finrank_span_finset_le_card _
    _ ≤ NV.card := Finset.card_image_le

#print axioms flatPhi_rank_le
end
end CatalanMeasure.GenD.Uniform.W.LStar
