module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZSys
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.PsiCells
@[expose] public section
set_option Elab.async false

/-!
# The response of a Theorem Z atom

Parameters `(τ1, τ2, σ1, σ2)`; symmetric data `S_{δk} = u_k τ1_δ + u2_k τ2_δ`, antisymmetric
data `A_{δk} = y1_k σ1_{δ-1} + y2_k σ2_{δ-1}` (`A_0 = 0`).  With the slot polynomials

    π_i = Σ τ_{i,δ} zpLam_δ,     λ_i = Σ σ_{i,δ-1} zaLam_δ,

the slot response is

    resp J ℓ = Σ_e [p ∣ H-1-ℓ-e] ( π1[e] ψ+(J,σ_e)(u) + π2[e] ψ+(J,σ_e)(u2)
                                   + λ1[e] ψ-(J,σ_e)(y1) + λ2[e] ψ-(J,σ_e)(y2) ).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Merge diagonal blocks into slot data. -/
def mergeData {K D : ℕ} (S A : Fin D → Fin K → ZMod p) : Fin (D + D) → Fin (K + K) → ZMod p :=
  fun d k => Fin.addCases
    (fun d1 => Fin.addCases (fun k1 => S d1 k1) (fun _ => 0) k)
    (fun d2 => Fin.addCases (fun _ => 0) (fun k2 => A d2 k2) k) d

theorem merge_cc {K D : ℕ} (S A : Fin D → Fin K → ZMod p) (d : Fin D) (k : Fin K) :
    mergeData S A (Fin.castAdd D d) (Fin.castAdd K k) = S d k := by
  simp only [mergeData, Fin.addCases_left]

theorem merge_cn {K D : ℕ} (S A : Fin D → Fin K → ZMod p) (d : Fin D) (k : Fin K) :
    mergeData S A (Fin.castAdd D d) (Fin.natAdd K k) = 0 := by
  simp only [mergeData, Fin.addCases_left, Fin.addCases_right]

theorem merge_nc {K D : ℕ} (S A : Fin D → Fin K → ZMod p) (d : Fin D) (k : Fin K) :
    mergeData S A (Fin.natAdd D d) (Fin.castAdd K k) = 0 := by
  simp only [mergeData, Fin.addCases_left, Fin.addCases_right]

theorem merge_nn {K D : ℕ} (S A : Fin D → Fin K → ZMod p) (d : Fin D) (k : Fin K) :
    mergeData S A (Fin.natAdd D d) (Fin.natAdd K k) = A d k := by
  simp only [mergeData, Fin.addCases_right]

theorem blk11_merge {K D : ℕ} (S A : Fin D → Fin K → ZMod p) : blk11 D D K K (mergeData S A) = S := by
  funext d k; exact merge_cc S A d k

theorem blk22_merge {K D : ℕ} (S A : Fin D → Fin K → ZMod p) : blk22 D D K K (mergeData S A) = A := by
  funext d k; exact merge_nn S A d k

theorem blk12_merge {K D : ℕ} (S A : Fin D → Fin K → ZMod p) : blk12 D D K K (mergeData S A) = 0 := by
  funext d k; exact merge_cn S A d k

theorem blk21_merge {K D : ℕ} (S A : Fin D → Fin K → ZMod p) : blk21 D D K K (mergeData S A) = 0 := by
  funext d k; exact merge_nc S A d k

theorem mergeData_mem {K D : ℕ} (S A : Fin D → Fin K → ZMod p) (hc : ZCons P N p 0 S A)
    (hA0 : ∀ d : Fin D, (d : ℕ) = 0 → ∀ k, A d k = 0) : mergeData S A ∈ zDom P N p K D := by
  rw [mem_zDom, blk11_merge, blk22_merge, blk12_merge, blk21_merge]
  exact ⟨rfl, rfl, hc, hA0⟩

/-- The source covector of the sum profile. -/
theorem zSys_psi (hp2 : p ≠ 2) (K D : ℕ) (hD : D ≤ (p - 1) / 2 + 1) (H J : ℕ) (a : ℤ)
    (z : Fin (K + K) → ZMod p) :
    (zSys P N p hp2 K D hD).prof.psi H J a z =
      (profTp' p K).psi H J a (fl1 K K z) + (profTm' p K).psi H J a (fl2 K K z) := by
  show digitPhi H a (sourceM (p := p) J) (sourceZ (p := p) J)
      ((profAdd (profTp' p K) (profTm' p K)).Gy z) ((profAdd (profTp' p K) (profTm' p K)).Ty z)
      (3 / 2) = _
  simp only [profAdd, LinearMap.add_apply, LinearMap.comp_apply]
  show _ = digitPhi H a (sourceM (p := p) J) (sourceZ (p := p) J) ((profTp' p K).Gy (fl1 K K z))
      ((profTp' p K).Ty (fl1 K K z)) (3 / 2) + digitPhi H a (sourceM (p := p) J)
      (sourceZ (p := p) J) ((profTm' p K).Gy (fl2 K K z)) ((profTm' p K).Ty (fl2 K K z)) (3 / 2)
  unfold digitPhi
  simp only [intrinsicCoeff_add', add_mul, Finset.sum_add_distrib, mul_add]
  ring

/-- Coefficient-`e` profile of merged data: the two blocks. -/
theorem fl1_wv {K D : ℕ} (hp2 : p ≠ 2) (hD : D ≤ (p - 1) / 2 + 1) (S A : Fin D → Fin K → ZMod p)
    (e : ℕ) :
    fl1 K K (wv (zSys P N p hp2 K D hD).lam (mergeData S A) e) =
      fun k => ∑ d : Fin D, (zpLam P N p d).coeff e * S d k := by
  funext k
  simp only [wv, fl1_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  show ∑ d : Fin (D + D), ((Fin.append (fun d : Fin D => zpLam P N p d)
      (fun d : Fin D => zaLam P N p d)) d).coeff e * mergeData S A d (Fin.castAdd K k) = _
  rw [Fin.sum_univ_add]
  simp only [merge_cc, merge_nc, Fin.append_left, Fin.append_right, mul_zero, Finset.sum_const_zero,
    add_zero]

theorem fl2_wv {K D : ℕ} (hp2 : p ≠ 2) (hD : D ≤ (p - 1) / 2 + 1) (S A : Fin D → Fin K → ZMod p)
    (e : ℕ) :
    fl2 K K (wv (zSys P N p hp2 K D hD).lam (mergeData S A) e) =
      fun k => ∑ d : Fin D, (zaLam P N p d).coeff e * A d k := by
  funext k
  simp only [wv, fl2_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  show ∑ d : Fin (D + D), ((Fin.append (fun d : Fin D => zpLam P N p d)
      (fun d : Fin D => zaLam P N p d)) d).coeff e * mergeData S A d (Fin.natAdd K k) = _
  rw [Fin.sum_univ_add]
  simp only [merge_cn, merge_nn, Fin.append_left, Fin.append_right, mul_zero, Finset.sum_const_zero,
    zero_add]

/-- **Response formula for merged atoms.** -/
theorem zSys_resp {K D : ℕ} (hp2 : p ≠ 2) (hD : D ≤ (p - 1) / 2 + 1) (S A : Fin D → Fin K → ZMod p)
    (J ell : ℕ) :
    (zSys P N p hp2 K D hD).resp J ell (mergeData S A) =
      ∑ e ∈ Finset.range (P.h N + (p - 1) + D),
        if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ell - e then
          (profTp' p K).psi (P.H N) J (((P.H N : ℤ) - 1 - ell - e) / p)
              (fun k => ∑ d : Fin D, (zpLam P N p d).coeff e * S d k) +
            (profTm' p K).psi (P.H N) J (((P.H N : ℤ) - 1 - ell - e) / p)
              (fun k => ∑ d : Fin D, (zaLam P N p d).coeff e * A d k)
        else 0 := by
  unfold SlotSystem.resp
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs
  · have h1 := zSys_psi (P := P) (N := N) hp2 K D hD (P.H N) J (((P.H N : ℤ) - 1 - ell - e) / p)
      (wv (zSys P N p hp2 K D hD).lam (mergeData S A) e)
    refine h1.trans ?_
    rw [fl1_wv hp2 hD, fl2_wv hp2 hD]
  · rfl

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
