module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZRes
@[expose] public section
set_option Elab.async false

/-!
# Theorem Z atoms and their two-coefficient response

Parameters `τ1 τ2 : F^{hp+1}`, `σ1 σ2 : F^{hp}`; cell vectors `u, u2` (T+ profiles) and `y1, y2`
(T- profiles).  The sequences `π_i[e] = Σ_d zpLam_d[e] τ_{i,d}`, `λ_i[e] = Σ_d zaLam_d[e] σ_{i,d}`
and `termAt J σ e = π1[e] ψ+(J,σ)(u) + π2[e] ψ+(J,σ)(u2) + λ1[e] ψ-(J,σ)(y1) + λ2[e] ψ-(J,σ)(y2)`
give, for `ℓ < p`,

    resp J ℓ = [r < emax] termAt J σ0 r + [r + p < emax] termAt J (σ0 - 1) (r + p),

`r = (H-1-ℓ) mod p`, `σ0 = (H-1-ℓ-r)/p`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Antisymmetric parameters extended by `0` at offset `0`. -/
def Aext {hp : ℕ} (σ : Fin hp → ZMod p) : Fin (hp + 1) → ZMod p := Fin.cases 0 σ

/-- Symmetric data of the atom. -/
def Sdata {K hp : ℕ} (u u2 : Fin K → ZMod p) (τ1 τ2 : Fin (hp + 1) → ZMod p) :
    Fin (hp + 1) → Fin K → ZMod p := fun d k => u k * τ1 d + u2 k * τ2 d

/-- Antisymmetric data of the atom. -/
def Adata {K hp : ℕ} (y1 y2 : Fin K → ZMod p) (σ1 σ2 : Fin hp → ZMod p) :
    Fin (hp + 1) → Fin K → ZMod p := fun d k => y1 k * Aext σ1 d + y2 k * Aext σ2 d

/-- Coefficient sequences. -/
def piSeq (P : Parameters) (N p : ℕ) {D : ℕ} (τ : Fin D → ZMod p) (e : ℕ) : ZMod p :=
  ∑ d : Fin D, (zpLam P N p d).coeff e * τ d

def laSeq (P : Parameters) (N p : ℕ) {D : ℕ} (σ : Fin D → ZMod p) (e : ℕ) : ZMod p :=
  ∑ d : Fin D, (zaLam P N p d).coeff e * σ d

/-- The four-cell combination of the covectors. -/
def termAt (P : Parameters) (N p : ℕ) [Fact p.Prime] {K hp : ℕ} (u u2 y1 y2 : Fin K → ZMod p)
    (τ1 τ2 : Fin (hp + 1) → ZMod p) (σ1 σ2 : Fin hp → ZMod p) (J : ℕ) (σ : ℤ) (e : ℕ) : ZMod p :=
  piSeq P N p τ1 e * (profTp' p K).psi (P.H N) J σ u +
    piSeq P N p τ2 e * (profTp' p K).psi (P.H N) J σ u2 +
    laSeq P N p (Aext σ1) e * (profTm' p K).psi (P.H N) J σ y1 +
    laSeq P N p (Aext σ2) e * (profTm' p K).psi (P.H N) J σ y2

theorem prof_split {K : ℕ} (F : Prof p K) (H J : ℕ) (a : ℤ) (c1 c2 : ZMod p)
    (v1 v2 : Fin K → ZMod p) :
    F.psi H J a (fun k => c1 * v1 k + c2 * v2 k) = c1 * F.psi H J a v1 + c2 * F.psi H J a v2 := by
  have : (fun k => c1 * v1 k + c2 * v2 k) = c1 • v1 + c2 • v2 := by
    funext k; simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem profile_S {K hp : ℕ} (u u2 : Fin K → ZMod p) (τ1 τ2 : Fin (hp + 1) → ZMod p) (e : ℕ) :
    (fun k => ∑ d : Fin (hp + 1), (zpLam P N p d).coeff e * Sdata u u2 τ1 τ2 d k) =
      fun k => piSeq P N p τ1 e * u k + piSeq P N p τ2 e * u2 k := by
  funext k
  simp only [Sdata, piSeq, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

theorem profile_A {K hp : ℕ} (y1 y2 : Fin K → ZMod p) (σ1 σ2 : Fin hp → ZMod p) (e : ℕ) :
    (fun k => ∑ d : Fin (hp + 1), (zaLam P N p d).coeff e * Adata y1 y2 σ1 σ2 d k) =
      fun k => laSeq P N p (Aext σ1) e * y1 k + laSeq P N p (Aext σ2) e * y2 k := by
  funext k
  simp only [Adata, laSeq, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

theorem zSys_resp_term {K hp : ℕ} (hp2 : p ≠ 2) (hD : hp + 1 ≤ (p - 1) / 2 + 1)
    (u u2 y1 y2 : Fin K → ZMod p) (τ1 τ2 : Fin (hp + 1) → ZMod p) (σ1 σ2 : Fin hp → ZMod p)
    (J ell : ℕ) :
    (zSys P N p hp2 K (hp + 1) hD).resp J ell
        (mergeData (Sdata u u2 τ1 τ2) (Adata y1 y2 σ1 σ2)) =
      ∑ e ∈ Finset.range (P.h N + (p - 1) + (hp + 1)),
        if (p : ℤ) ∣ ((P.H N : ℤ) - 1 - ell) - e then
          termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J ((((P.H N : ℤ) - 1 - ell) - e) / p) e
        else 0 := by
  rw [zSys_resp]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : (p : ℤ) ∣ (P.H N : ℤ) - 1 - ell - e
  · rw [if_pos h, if_pos h, profile_S, profile_A, prof_split, prof_split]
    unfold termAt; ring
  · rw [if_neg h, if_neg h]

/-- **Two-coefficient response**: `r = (H-1-ℓ) mod p`, `q0 = (H-1-ℓ) / p`. -/
theorem zSys_resp_two {K hp : ℕ} (hp2 : p ≠ 2) (hD : hp + 1 ≤ (p - 1) / 2 + 1)
    (hemax : P.h N + (p - 1) + (hp + 1) ≤ 2 * p)
    (u u2 y1 y2 : Fin K → ZMod p) (τ1 τ2 : Fin (hp + 1) → ZMod p) (σ1 σ2 : Fin hp → ZMod p)
    (J ell : ℕ) :
    (zSys P N p hp2 K (hp + 1) hD).resp J ell
        (mergeData (Sdata u u2 τ1 τ2) (Adata y1 y2 σ1 σ2)) =
      (if (((P.H N : ℤ) - 1 - ell) % p).toNat < P.h N + (p - 1) + (hp + 1) then
        termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J (((P.H N : ℤ) - 1 - ell) / p)
          (((P.H N : ℤ) - 1 - ell) % p).toNat else 0) +
      (if (((P.H N : ℤ) - 1 - ell) % p).toNat + p < P.h N + (p - 1) + (hp + 1) then
        termAt P N p u u2 y1 y2 τ1 τ2 σ1 σ2 J (((P.H N : ℤ) - 1 - ell) / p - 1)
          ((((P.H N : ℤ) - 1 - ell) % p).toNat + p) else 0) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : (0 : ℤ) < p := by exact_mod_cast hp0
  rw [zSys_resp_term, sum_two_coeffs hp0 ((P.H N : ℤ) - 1 - ell) _ hemax]
  set T : ℤ := (P.H N : ℤ) - 1 - ell with hT
  have hr0 : (0 : ℤ) ≤ T % p := Int.emod_nonneg _ hp1.ne'
  have hrp : (((T % p).toNat : ℕ) : ℤ) = T % p := Int.toNat_of_nonneg hr0
  have e1 : (T - ((T % p).toNat : ℤ)) / p = T / p := by
    rw [hrp, Int.emod_def]
    have : T - (T - p * (T / p)) = p * (T / p) := by ring
    rw [this, Int.mul_ediv_cancel_left _ hp1.ne']
  have e2 : (T - (((T % p).toNat + p : ℕ) : ℤ)) / p = T / p - 1 := by
    rw [Nat.cast_add, hrp, Int.emod_def]
    have : T - (T - p * (T / p) + p) = p * (T / p - 1) := by ring
    rw [this, Int.mul_ediv_cancel_left _ hp1.ne']
  rw [e1, e2]

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
