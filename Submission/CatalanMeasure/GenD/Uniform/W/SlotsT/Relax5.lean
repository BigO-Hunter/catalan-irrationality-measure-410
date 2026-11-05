module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Relax4
@[expose] public section
set_option Elab.async false

/-!
# Atom count for the relaxed mixed system

`mixMiss P N p K D1 k0` = number of missing rows among `c_k ± (d+1)` (`d < D1`) and `c_k`.
`finrank_atoms_relax_ge` : `D1 dim V1 + (D1+1) dim V2 ≤ dim (dom ⊓ Π V) + mixMiss`.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem emb1_castAdd {K1 K2 : ℕ} (y : Fin K1 → ZMod p) (k : Fin K1) :
    emb1 K1 K2 y (Fin.castAdd K2 k) = y k := Fin.append_left _ _ k

theorem emb1_natAdd {K1 K2 : ℕ} (y : Fin K1 → ZMod p) (k : Fin K2) :
    emb1 K1 K2 y (Fin.natAdd K1 k) = 0 := Fin.append_right _ _ k

theorem emb2_castAdd {K1 K2 : ℕ} (y : Fin K2 → ZMod p) (k : Fin K1) :
    emb2 K1 K2 y (Fin.castAdd K2 k) = 0 := Fin.append_left _ _ k

theorem emb2_natAdd {K1 K2 : ℕ} (y : Fin K2 → ZMod p) (k : Fin K2) :
    emb2 K1 K2 y (Fin.natAdd K1 k) = y k := Fin.append_right _ _ k

/-- Missing rows `c_k + (d+1)`. -/
def mmP (P : Parameters) (N p K D1 : ℕ) (k0 : ℤ) : Finset (Fin D1 × Fin K) :=
  Finset.univ.filter fun dk => ¬ InRange P N (cen p K k0 dk.2 + (((dk.1 : ℕ) : ℤ) + 1))

/-- Missing rows `c_k - (d+1)`. -/
def mmM (P : Parameters) (N p K D1 : ℕ) (k0 : ℤ) : Finset (Fin D1 × Fin K) :=
  Finset.univ.filter fun dk => ¬ InRange P N (cen p K k0 dk.2 - (((dk.1 : ℕ) : ℤ) + 1))

/-- Missing centre rows `c_k`. -/
def mm0 (P : Parameters) (N p K : ℕ) (k0 : ℤ) : Finset (Fin K) :=
  Finset.univ.filter fun k => ¬ InRange P N (cen p K k0 k)

/-- The number of missing rows (number of linear conditions of the relaxed domain). -/
def mixMiss (P : Parameters) (N p K D1 : ℕ) (k0 : ℤ) : ℕ :=
  (mmP P N p K D1 k0).card + (mmM P N p K D1 k0).card + (mm0 P N p K k0).card

/-- The conditions as a linear map on the profile data. -/
def condMap (P : Parameters) (N p K D1 : ℕ) (k0 : ℤ) (V1 V2 : Submodule (ZMod p) (Fin K → ZMod p)) :
    ((Fin D1 → V1) × (Fin (D1 + 1) → V2)) →ₗ[ZMod p]
      ((mmP P N p K D1 k0 → ZMod p) × ((mmM P N p K D1 k0 → ZMod p) × (mm0 P N p K k0 → ZMod p))) :=
  LinearMap.prod
    (LinearMap.pi fun i : mmP P N p K D1 k0 =>
      ((LinearMap.proj i.1.2 : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).comp
        (V1.subtype.comp ((LinearMap.proj i.1.1).comp (LinearMap.fst _ _ _)))) +
      ((LinearMap.proj i.1.2 : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).comp
        (V2.subtype.comp ((LinearMap.proj i.1.1.succ).comp (LinearMap.snd _ _ _)))))
    (LinearMap.prod
      (LinearMap.pi fun i : mmM P N p K D1 k0 =>
        ((LinearMap.proj i.1.2 : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).comp
          (V2.subtype.comp ((LinearMap.proj i.1.1.succ).comp (LinearMap.snd _ _ _)))) -
        ((LinearMap.proj i.1.2 : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).comp
          (V1.subtype.comp ((LinearMap.proj i.1.1).comp (LinearMap.fst _ _ _)))))
      (LinearMap.pi fun i : mm0 P N p K k0 =>
        (LinearMap.proj i.1 : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).comp
          (V2.subtype.comp ((LinearMap.proj (0 : Fin (D1 + 1))).comp (LinearMap.snd _ _ _)))))

theorem profAdd_psi {K1 K2 : ℕ} (F1 : Prof p K1) (F2 : Prof p K2) (H J : ℕ) (a : ℤ)
    (z : Fin (K1 + K2) → ZMod p) :
    (profAdd F1 F2).psi H J a z = F1.psi H J a (fl1 K1 K2 z) + F2.psi H J a (fl2 K1 K2 z) := by
  show digitPhi H a (sourceM (p := p) J) (sourceZ (p := p) J)
      ((profAdd F1 F2).Gy z) ((profAdd F1 F2).Ty z) (3 / 2) = _
  simp only [profAdd, LinearMap.add_apply, LinearMap.comp_apply]
  show _ = digitPhi H a (sourceM (p := p) J) (sourceZ (p := p) J) (F1.Gy (fl1 K1 K2 z))
      (F1.Ty (fl1 K1 K2 z)) (3 / 2) + digitPhi H a (sourceM (p := p) J)
      (sourceZ (p := p) J) (F2.Gy (fl2 K1 K2 z)) (F2.Ty (fl2 K1 K2 z)) (3 / 2)
  unfold digitPhi
  simp only [intrinsicCoeff_add', add_mul, Finset.sum_add_distrib, mul_add]
  ring

set_option maxHeartbeats 800000 in
/-- **Atom dimension of the relaxed mixed system.** -/
theorem finrank_atoms_relax_ge (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) (K D1 : ℕ) (k0 : ℤ)
    (hD : D1 ≤ (p - 1) / 2)
    (V1 V2 : Submodule (ZMod p) (Fin K → ZMod p))
    (V : Submodule (ZMod p) (Fin (K + K) → ZMod p))
    (hV : ∀ y, y ∈ V ↔ fl1 K K y ∈ V1 ∧ fl2 K K y ∈ V2) :
    D1 * finrank (ZMod p) V1 + (D1 + 1) * finrank (ZMod p) V2 ≤
      finrank (ZMod p) ((mtSystem' P N p hp2 hph K D1 k0 hD).atoms V) + mixMiss P N p K D1 k0 := by
  classical
  let m := blockEmb D1 (D1 + 1) K K V1 V2
  have m_left : ∀ uw i, m uw (Fin.castAdd (D1 + 1) i) =
      emb1 K K (uw.1 i : Fin K → ZMod p) := fun uw i => blockEmb_left _ _ _ _ V1 V2 uw i
  have m_right : ∀ uw j, m uw (Fin.natAdd D1 j) =
      emb2 K K (uw.2 j : Fin K → ZMod p) := fun uw j => blockEmb_right _ _ _ _ V1 V2 uw j
  have hm : Function.Injective m := by
    refine Thin.injective_of_zero _ fun uw h0 => ?_
    have hu : ∀ i, (uw.1 i : Fin K → ZMod p) = 0 := fun i => by
      have := congrArg (fl1 K K) (m_left uw i ▸ congrFun h0 (Fin.castAdd (D1 + 1) i))
      simpa [fl1_emb1] using this
    have hw : ∀ j, (uw.2 j : Fin K → ZMod p) = 0 := fun j => by
      have := congrArg (fl2 K K) (m_right uw j ▸ congrFun h0 (Fin.natAdd D1 j))
      simpa [fl2_emb2] using this
    exact Prod.ext (funext fun i => Subtype.ext (hu i)) (funext fun j => Subtype.ext (hw j))
  let g := condMap P N p K D1 k0 V1 V2
  let h : LinearMap.ker g →ₗ[ZMod p] (mtSystem' P N p hp2 hph K D1 k0 hD).atoms V :=
    LinearMap.codRestrict ((mtSystem' P N p hp2 hph K D1 k0 hD).atoms V) (m.comp (LinearMap.ker g).subtype)
      (fun a => by
        have hg0 := LinearMap.mem_ker.mp a.2
        have hgP : ∀ i : mmP P N p K D1 k0, (a.1.1 i.1.1 : Fin K → ZMod p) i.1.2 +
            (a.1.2 i.1.1.succ : Fin K → ZMod p) i.1.2 = 0 := fun i => by
          have := congrFun (congrArg Prod.fst hg0) i
          exact this
        have hgM : ∀ i : mmM P N p K D1 k0, (a.1.2 i.1.1.succ : Fin K → ZMod p) i.1.2 -
            (a.1.1 i.1.1 : Fin K → ZMod p) i.1.2 = 0 := fun i => by
          have := congrFun (congrArg Prod.fst (congrArg Prod.snd hg0)) i
          exact this
        have hg0' : ∀ i : mm0 P N p K k0, (a.1.2 0 : Fin K → ZMod p) i.1 = 0 := fun i => by
          have := congrFun (congrArg Prod.snd (congrArg Prod.snd hg0)) i
          exact this
        refine (Slots.SlotSystem.mem_atoms (S := mtSystem' P N p hp2 hph K D1 k0 hD) (V := V)).mpr
          ⟨?_, fun d => ?_⟩
        · show m a.1 ∈ relaxDom P N p K D1 k0
          rw [mem_relaxDom]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · funext i k
            show m a.1 (Fin.castAdd (D1 + 1) i) (Fin.natAdd K k) = 0
            rw [m_left]; exact emb1_natAdd _ k
          · funext j k
            show m a.1 (Fin.natAdd D1 j) (Fin.castAdd K k) = 0
            rw [m_right]; exact emb2_castAdd _ k
          · intro d k hk
            have := hgP ⟨(d, k), by simp [mmP, hk]⟩
            show m a.1 (Fin.castAdd (D1 + 1) d) (Fin.castAdd K k) +
              m a.1 (Fin.natAdd D1 d.succ) (Fin.natAdd K k) = 0
            rw [m_left, m_right, emb1_castAdd, emb2_natAdd]
            exact this
          · intro d k hk
            have := hgM ⟨(d, k), by simp [mmM, hk]⟩
            show m a.1 (Fin.natAdd D1 d.succ) (Fin.natAdd K k) -
              m a.1 (Fin.castAdd (D1 + 1) d) (Fin.castAdd K k) = 0
            rw [m_left, m_right, emb1_castAdd, emb2_natAdd]
            exact this
          · intro k hk
            have := hg0' ⟨k, by simp [mm0, hk]⟩
            show m a.1 (Fin.natAdd D1 0) (Fin.natAdd K k) = 0
            rw [m_right, emb2_natAdd]
            exact this
        · refine Fin.addCases (fun i => ?_) (fun j => ?_) d
          · show m a.1 (Fin.castAdd (D1 + 1) i) ∈ V
            rw [m_left, hV, fl1_emb1, fl2_emb1]
            exact ⟨(a.1.1 i).2, V2.zero_mem⟩
          · show m a.1 (Fin.natAdd D1 j) ∈ V
            rw [m_right, hV, fl1_emb2, fl2_emb2]
            exact ⟨V1.zero_mem, (a.1.2 j).2⟩)
  have hh : Function.Injective h := by
    intro a b hab
    apply Subtype.ext
    apply hm
    exact congrArg Subtype.val hab
  have h1 := LinearMap.finrank_le_finrank_of_injective hh
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  have h3 : finrank (ZMod p) (LinearMap.range g) ≤ mixMiss P N p K D1 k0 := by
    have := Submodule.finrank_le (LinearMap.range g)
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
      Fintype.card_coe, Fintype.card_coe] at this
    unfold mixMiss
    omega
  have hdim : finrank (ZMod p) ((Fin D1 → V1) × (Fin (D1 + 1) → V2)) =
      D1 * finrank (ZMod p) V1 + (D1 + 1) * finrank (ZMod p) V2 := by
    rw [Module.finrank_prod]
    simp [Module.finrank_pi_fintype]
  omega

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
