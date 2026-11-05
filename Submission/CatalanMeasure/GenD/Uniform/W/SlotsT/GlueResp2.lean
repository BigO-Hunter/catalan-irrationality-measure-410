module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.GlueResp
@[expose] public section
set_option Elab.async false

/-!
# `resp_fam`: the response of the overflow-below family
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem wv_famData (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) {K D1 m : ℕ} (k0 : ℤ)
    (hD : D1 ≤ (p - 1) / 2) (y u : Fin m → Fin K → ZMod p)
    (στ : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) (e : ℕ) :
    wv (mtSystem' P N p hp2 hph K D1 k0 hD).lam (famData y u στ) e =
      emb1 K K (∑ i, (lamPoly P N p (στ.1 i)).coeff e • y i) +
        emb2 K K (∑ i, (pPoly P N p (στ.2 i)).coeff e • u i) := by
  show ∑ d : Fin (D1 + (D1 + 1)),
      (Fin.append (fun d : Fin D1 => Thin.lam P N p (d : ℕ))
        (fun d : Fin (D1 + 1) => tpLam P N p (d : ℕ)) d).coeff e • famData y u στ d = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, famData_left, famData_right]
  congr 1
  · simp only [lamPoly_coeff, map_sum, map_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun d _ => ?_
    rw [mul_comm]
  · simp only [pPoly_coeff, map_sum, map_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun d _ => ?_
    rw [mul_comm]

theorem psi_emb (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) {K D1 : ℕ} (k0 : ℤ)
    (hD : D1 ≤ (p - 1) / 2) (H J : ℕ) (a : ℤ) (v1 v2 : Fin K → ZMod p) :
    (mtSystem' P N p hp2 hph K D1 k0 hD).prof.psi H J a (emb1 K K v1 + emb2 K K v2) =
      (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).psi H J a v1 +
        (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).psi H J a v2 := by
  have := profAdd_psi (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K)
    (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K) H J a (emb1 K K v1 + emb2 K K v2)
  refine this.trans ?_
  simp only [map_add, fl1_emb1, fl2_emb1, fl1_emb2, fl2_emb2, map_zero, add_zero, zero_add]

/-- Coefficient `e` of `f = Σ_i A_i lam_i + B_i P_i`. -/
def fcoef {D1 m : ℕ} (A B : Fin m → ZMod p)
    (στ : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) (e : ℕ) : ZMod p :=
  ∑ i, (A i * (lamPoly P N p (στ.1 i)).coeff e + B i * (pPoly P N p (στ.2 i)).coeff e)

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
