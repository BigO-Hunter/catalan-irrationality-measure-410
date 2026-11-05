module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.GlueResp2
@[expose] public section
set_option Elab.async false

/-!
# `resp_fam`
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem psi_wv_fam (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) {K D1 m : ℕ} (k0 : ℤ)
    (hD : D1 ≤ (p - 1) / 2) (y u : Fin m → Fin K → ZMod p)
    (στ : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) (H J : ℕ) (a : ℤ) (e : ℕ) :
    (mtSystem' P N p hp2 hph K D1 k0 hD).prof.psi H J a
        (wv (mtSystem' P N p hp2 hph K D1 k0 hD).lam (famData y u στ) e) =
      ∑ i, ((lamPoly P N p (στ.1 i)).coeff e *
          (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).psi H J a (y i) +
        (pPoly P N p (στ.2 i)).coeff e *
          (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).psi H J a (u i)) := by
  have hw := wv_famData hp2 hph k0 hD y u στ e
  erw [hw]
  rw [psi_emb hp2 hph k0 hD]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.sum_add_distrib]

set_option maxHeartbeats 800000 in
/-- **Response of the overflow-below family.** -/
theorem resp_fam (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) {K D1 m s elo : ℕ} (k0 : ℤ)
    (hD : D1 ≤ (p - 1) / 2) (y u : Fin m → Fin K → ZMod p) (A B : Fin m → ZMod p)
    (J1 J2 : Finset ℕ)
    (hs : s * p + 1 ≤ P.H N) (hpη : p ≤ P.H N - 1 - s * p) (hη2 : P.H N - 1 - s * p < 2 * p)
    (hdeg : P.h N + D1 ≤ (P.H N - 1 - s * p) + 1)
    (hJ1 : ∀ i J, J ∈ J1 →
      (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).psi (P.H N) J s (y i) = A i ∧
      (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).psi (P.H N) J s (u i) = B i)
    (hJ2 : ∀ i J, J ∈ J2 →
      (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).psi (P.H N) J ((s : ℤ) + 1) (y i) +
        (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).psi (P.H N) J ((s : ℤ) + 1) (u i) = A i + B i)
    (στ : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p))
    (hjet : ∀ i e, e < elo → (lamPoly P N p (στ.1 i)).coeff e = 0 ∧ (pPoly P N p (στ.2 i)).coeff e = 0)
    (hglue : ∀ i e, elo ≤ e → e ≤ P.H N - 1 - s * p - p →
      (lamPoly P N p (στ.1 i)).coeff e = (pPoly P N p (στ.2 i)).coeff e)
    (j : ℕ)
    (hcov1 : P.H N - 1 - s * p - (P.h N + D1 - 1) ≤ j % p → j / p ∈ J1)
    (hcov2 : j % p + elo + p ≤ P.H N - 1 - s * p → j / p ∈ J2) :
    (mtSystem' P N p hp2 hph K D1 k0 hD).resp (j / p) (j % p) (famData y u στ) =
      fcoef (P := P) (N := N) A B στ (P.H N - 1 - s * p - j % p) +
        (if p + j % p ≤ P.H N - 1 - s * p then
          fcoef (P := P) (N := N) A B στ (P.H N - 1 - s * p - p - j % p) else 0) := by
  classical
  have hell : j % p < p := Nat.mod_lt _ (Fact.out : p.Prime).pos
  set η := P.H N - 1 - s * p with hη
  have hetaz : (P.H N : ℤ) - 1 - η = s * p := by
    rw [hη, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hdegx : ∀ e, η < e → ∀ i, (lamPoly P N p (στ.1 i)).coeff e = 0 ∧
      (pPoly P N p (στ.2 i)).coeff e = 0 := by
    intro e he i
    exact ⟨coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (lamPoly_natDegree_le hp2 _) (by omega)),
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (pPoly_natDegree_le hp2 hph _) (by omega))⟩
  have hhi : ∀ e, η < e →
      wv (mtSystem' P N p hp2 hph K D1 k0 hD).lam (famData y u στ) e = 0 := by
    intro e he
    rw [wv_famData hp2 hph k0 hD]
    simp only [(hdegx e he _).1, (hdegx e he _).2, zero_smul, Finset.sum_const_zero, map_zero,
      add_zero]
  have hlo : ∀ e, e + 2 * p ≤ η →
      wv (mtSystem' P N p hp2 hph K D1 k0 hD).lam (famData y u στ) e = 0 := by
    intro e he; omega
  rw [SlotSystem.resp_two (mtSystem' P N p hp2 hph K D1 k0 hD) hetaz (j / p) (j % p) hell _ hhi hlo]
  rw [if_pos (by omega)]
  congr 1
  · -- main window
    rw [psi_wv_fam hp2 hph k0 hD]
    unfold fcoef
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hc : η - (P.h N + D1 - 1) ≤ j % p
    · obtain ⟨h1, h2⟩ := hJ1 i (j / p) (hcov1 hc)
      rw [h1, h2]; ring
    · have e1 : (lamPoly P N p (στ.1 i)).coeff (η - j % p) = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (lamPoly_natDegree_le hp2 _) (by omega))
      have e2 : (pPoly P N p (στ.2 i)).coeff (η - j % p) = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (pPoly_natDegree_le hp2 hph _) (by omega))
      rw [e1, e2]; simp
  · by_cases hpl : p + j % p ≤ η
    · rw [if_pos hpl, if_pos hpl, psi_wv_fam hp2 hph k0 hD]
      unfold fcoef
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hc : η - p - j % p < elo
      · obtain ⟨e1, e2⟩ := hjet i _ hc
        rw [e1, e2]; simp
      · have hc' : elo ≤ η - p - j % p := by omega
        have hg := hglue i _ hc' (by omega)
        have hJ := hcov2 (by omega)
        have h2 := hJ2 i (j / p) hJ
        rw [← hg]
        linear_combination (lamPoly P N p (στ.1 i)).coeff (η - p - j % p) * h2
    · rw [if_neg hpl, if_neg hpl]

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
