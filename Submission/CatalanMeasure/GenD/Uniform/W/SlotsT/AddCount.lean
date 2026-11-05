module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Add
@[expose] public section
set_option Elab.async false

/-!
# Counting for the sum of two slot systems

* `addSystem_psi` : the source covector of the sum system is the sum of the two covectors on the
  two coordinate blocks.
* `finrank_atoms_add_ge` : for `V = {y | y₁ ∈ V₁, y₂ ∈ V₂}` the atoms `dom ⊓ Π V` of the sum system
  have dimension `≥ D₁ dim V₁ + D₂ dim V₂ - |bad₁| - |bad₂|`.
* `finrank_prod_sub_le` : `dim V ≤ dim V₁ + dim V₂` for such `V`.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem addSystem_psi (S1 S2 : SlotSystem P N p)
    (hsep : ∀ a ∈ S1.dom, ∀ b ∈ S2.dom, S1.rows a + S2.rows b = 0 → a = 0 ∧ b = 0)
    (H J : ℕ) (a : ℤ) (z : Fin (S1.K + S2.K) → ZMod p) :
    (addSystem S1 S2 hsep).prof.psi H J a z =
      S1.prof.psi H J a (fl1 S1.K S2.K z) + S2.prof.psi H J a (fl2 S1.K S2.K z) := by
  show digitPhi H a (sourceM (p := p) J) (sourceZ (p := p) J)
      ((profAdd S1.prof S2.prof).Gy z) ((profAdd S1.prof S2.prof).Ty z) (3 / 2) = _
  simp only [profAdd, LinearMap.add_apply, LinearMap.comp_apply]
  show _ = digitPhi H a (sourceM (p := p) J) (sourceZ (p := p) J) (S1.prof.Gy (fl1 S1.K S2.K z))
      (S1.prof.Ty (fl1 S1.K S2.K z)) (3 / 2) + digitPhi H a (sourceM (p := p) J)
      (sourceZ (p := p) J) (S2.prof.Gy (fl2 S1.K S2.K z)) (S2.prof.Ty (fl2 S1.K S2.K z)) (3 / 2)
  unfold digitPhi
  simp only [intrinsicCoeff_add', add_mul, Finset.sum_add_distrib, mul_add]
  ring

/-- Embedding of a profile vector into the first / second coordinate block. -/
def emb1 (K1 K2 : ℕ) : (Fin K1 → ZMod p) →ₗ[ZMod p] (Fin (K1 + K2) → ZMod p) where
  toFun y := Fin.append y (0 : Fin K2 → ZMod p)
  map_add' y y' := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [Fin.append_left, Fin.append_right]
  map_smul' c y := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [Fin.append_left, Fin.append_right]

def emb2 (K1 K2 : ℕ) : (Fin K2 → ZMod p) →ₗ[ZMod p] (Fin (K1 + K2) → ZMod p) where
  toFun y := Fin.append (0 : Fin K1 → ZMod p) y
  map_add' y y' := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [Fin.append_left, Fin.append_right]
  map_smul' c y := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [Fin.append_left, Fin.append_right]

theorem fl1_emb1 (K1 K2 : ℕ) (y : Fin K1 → ZMod p) : fl1 K1 K2 (emb1 K1 K2 y) = y := by
  funext k; simp [fl1_apply, emb1, Fin.append_left]

theorem fl2_emb1 (K1 K2 : ℕ) (y : Fin K1 → ZMod p) : fl2 K1 K2 (emb1 K1 K2 y) = 0 := by
  funext k; simp [fl2_apply, emb1, Fin.append_right]

theorem fl1_emb2 (K1 K2 : ℕ) (y : Fin K2 → ZMod p) : fl1 K1 K2 (emb2 K1 K2 y) = 0 := by
  funext k; simp [fl1_apply, emb2, Fin.append_left]

theorem fl2_emb2 (K1 K2 : ℕ) (y : Fin K2 → ZMod p) : fl2 K1 K2 (emb2 K1 K2 y) = y := by
  funext k; simp [fl2_apply, emb2, Fin.append_right]

/-- Block-diagonal embedding of profile data. -/
def blockEmb (D1 D2 K1 K2 : ℕ) (V1 : Submodule (ZMod p) (Fin K1 → ZMod p))
    (V2 : Submodule (ZMod p) (Fin K2 → ZMod p)) :
    ((Fin D1 → V1) × (Fin D2 → V2)) →ₗ[ZMod p] (Fin (D1 + D2) → Fin (K1 + K2) → ZMod p) where
  toFun uw := Fin.append (fun i => emb1 K1 K2 (uw.1 i : Fin K1 → ZMod p))
    (fun j => emb2 K1 K2 (uw.2 j : Fin K2 → ZMod p))
  map_add' uw uw' := by
    funext d
    refine Fin.addCases (fun i => ?_) (fun j => ?_) d <;>
      simp [Fin.append_left, Fin.append_right]
  map_smul' c uw := by
    funext d
    refine Fin.addCases (fun i => ?_) (fun j => ?_) d <;>
      simp [Fin.append_left, Fin.append_right]

theorem blockEmb_left (D1 D2 K1 K2 : ℕ) (V1 : Submodule (ZMod p) (Fin K1 → ZMod p))
    (V2 : Submodule (ZMod p) (Fin K2 → ZMod p)) (uw : (Fin D1 → V1) × (Fin D2 → V2)) (i : Fin D1) :
    blockEmb D1 D2 K1 K2 V1 V2 uw (Fin.castAdd D2 i) = emb1 K1 K2 (uw.1 i : Fin K1 → ZMod p) := by
  simp [blockEmb, Fin.append_left]

theorem blockEmb_right (D1 D2 K1 K2 : ℕ) (V1 : Submodule (ZMod p) (Fin K1 → ZMod p))
    (V2 : Submodule (ZMod p) (Fin K2 → ZMod p)) (uw : (Fin D1 → V1) × (Fin D2 → V2)) (j : Fin D2) :
    blockEmb D1 D2 K1 K2 V1 V2 uw (Fin.natAdd D1 j) = emb2 K1 K2 (uw.2 j : Fin K2 → ZMod p) := by
  simp [blockEmb, Fin.append_right]

/-- `dim V ≤ dim V₁ + dim V₂` for `V = {y | y₁ ∈ V₁, y₂ ∈ V₂}`. -/
theorem finrank_blocks_le {K1 K2 : ℕ} (V1 : Submodule (ZMod p) (Fin K1 → ZMod p))
    (V2 : Submodule (ZMod p) (Fin K2 → ZMod p))
    (V : Submodule (ZMod p) (Fin (K1 + K2) → ZMod p))
    (hV : ∀ y, y ∈ V ↔ fl1 K1 K2 y ∈ V1 ∧ fl2 K1 K2 y ∈ V2) :
    finrank (ZMod p) V ≤ finrank (ZMod p) V1 + finrank (ZMod p) V2 := by
  let g : V →ₗ[ZMod p] (V1 × V2) :=
    LinearMap.prod
      (LinearMap.codRestrict V1 ((fl1 K1 K2).comp V.subtype) (fun y => ((hV y.1).mp y.2).1))
      (LinearMap.codRestrict V2 ((fl2 K1 K2).comp V.subtype) (fun y => ((hV y.1).mp y.2).2))
  have hg : Function.Injective g := by
    refine Thin.injective_of_zero _ fun y hy => ?_
    have h1 : fl1 K1 K2 y.1 = 0 := congrArg Subtype.val (congrArg Prod.fst hy)
    have h2 : fl2 K1 K2 y.1 = 0 := congrArg Subtype.val (congrArg Prod.snd hy)
    apply Subtype.ext
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · exact congrFun h1 i
    · exact congrFun h2 j
  have := LinearMap.finrank_le_finrank_of_injective hg
  rw [show finrank (ZMod p) (V1 × V2) = finrank (ZMod p) V1 + finrank (ZMod p) V2 from
    Module.finrank_prod] at this
  exact this

/-- **Atom dimension of the sum system.** -/
theorem finrank_atoms_add_ge (S1 S2 : SlotSystem P N p)
    (hsep : ∀ a ∈ S1.dom, ∀ b ∈ S2.dom, S1.rows a + S2.rows b = 0 → a = 0 ∧ b = 0)
    (V1 : Submodule (ZMod p) (Fin S1.K → ZMod p)) (V2 : Submodule (ZMod p) (Fin S2.K → ZMod p))
    (V : Submodule (ZMod p) (Fin (S1.K + S2.K) → ZMod p))
    (hV : ∀ y, y ∈ V ↔ fl1 S1.K S2.K y ∈ V1 ∧ fl2 S1.K S2.K y ∈ V2)
    (bad1 : Finset (Fin S1.D × Fin S1.K)) (bad2 : Finset (Fin S2.D × Fin S2.K))
    (hd1 : ∀ x, x ∈ S1.dom ↔ x ∈ badDom p S1.K S1.D bad1)
    (hd2 : ∀ x, x ∈ S2.dom ↔ x ∈ badDom p S2.K S2.D bad2) :
    S1.D * finrank (ZMod p) V1 + S2.D * finrank (ZMod p) V2 ≤
      finrank (ZMod p) ((addSystem S1 S2 hsep).atoms V) + bad1.card + bad2.card := by
  classical
  let m := blockEmb S1.D S2.D S1.K S2.K V1 V2
  have m_left : ∀ uw i, m uw (Fin.castAdd S2.D i) =
      emb1 S1.K S2.K (uw.1 i : Fin S1.K → ZMod p) := by
    intro uw i; exact blockEmb_left _ _ _ _ V1 V2 uw i
  have m_right : ∀ uw j, m uw (Fin.natAdd S1.D j) =
      emb2 S1.K S2.K (uw.2 j : Fin S2.K → ZMod p) := by
    intro uw j; exact blockEmb_right _ _ _ _ V1 V2 uw j
  have hm : Function.Injective m := by
    refine Thin.injective_of_zero _ fun uw h0 => ?_
    have hu : ∀ i, (uw.1 i : Fin S1.K → ZMod p) = 0 := fun i => by
      have := congrArg (fl1 S1.K S2.K) (m_left uw i ▸ congrFun h0 (Fin.castAdd S2.D i))
      simpa [fl1_emb1] using this
    have hw : ∀ j, (uw.2 j : Fin S2.K → ZMod p) = 0 := fun j => by
      have := congrArg (fl2 S1.K S2.K) (m_right uw j ▸ congrFun h0 (Fin.natAdd S1.D j))
      simpa [fl2_emb2] using this
    exact Prod.ext (funext fun i => Subtype.ext (hu i)) (funext fun j => Subtype.ext (hw j))
  let g : ((Fin S1.D → V1) × (Fin S2.D → V2)) →ₗ[ZMod p] ((bad1 → ZMod p) × (bad2 → ZMod p)) :=
    LinearMap.prod
      ((LinearMap.pi fun b : bad1 => (LinearMap.proj b.1.2 : (Fin S1.K → ZMod p) →ₗ[ZMod p] ZMod p).comp
        (V1.subtype.comp (LinearMap.proj b.1.1))).comp (LinearMap.fst _ _ _))
      ((LinearMap.pi fun b : bad2 => (LinearMap.proj b.1.2 : (Fin S2.K → ZMod p) →ₗ[ZMod p] ZMod p).comp
        (V2.subtype.comp (LinearMap.proj b.1.1))).comp (LinearMap.snd _ _ _))
  let h : LinearMap.ker g →ₗ[ZMod p] (addSystem S1 S2 hsep).atoms V :=
    LinearMap.codRestrict ((addSystem S1 S2 hsep).atoms V) (m.comp (LinearMap.ker g).subtype)
      (fun a => by
        have hg0 := LinearMap.mem_ker.mp a.2
        have hg1 : ∀ b ∈ bad1, (a.1.1 b.1 : Fin S1.K → ZMod p) b.2 = 0 := fun b hb => by
          have := congrFun (congrArg Prod.fst hg0) ⟨b, hb⟩
          exact this
        have hg2 : ∀ b ∈ bad2, (a.1.2 b.1 : Fin S2.K → ZMod p) b.2 = 0 := fun b hb => by
          have := congrFun (congrArg Prod.snd hg0) ⟨b, hb⟩
          exact this
        refine (Slots.SlotSystem.mem_atoms (S := addSystem S1 S2 hsep) (V := V)).mpr ⟨?_, fun d => ?_⟩
        · show m a.1 ∈ addDom S1 S2
          rw [mem_addDom]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hd1, mem_badDom]
            intro b hb
            show m a.1 (Fin.castAdd S2.D b.1) (Fin.castAdd S2.K b.2) = 0
            rw [m_left]
            simpa [emb1, Fin.append_left] using hg1 b hb
          · rw [hd2, mem_badDom]
            intro b hb
            show m a.1 (Fin.natAdd S1.D b.1) (Fin.natAdd S1.K b.2) = 0
            rw [m_right]
            simpa [emb2, Fin.append_right] using hg2 b hb
          · funext i k
            show m a.1 (Fin.castAdd S2.D i) (Fin.natAdd S1.K k) = 0
            rw [m_left]; simp [emb1, Fin.append_right]
          · funext j k
            show m a.1 (Fin.natAdd S1.D j) (Fin.castAdd S2.K k) = 0
            rw [m_right]; simp [emb2, Fin.append_left]
        · refine Fin.addCases (fun i => ?_) (fun j => ?_) d
          · show m a.1 (Fin.castAdd S2.D i) ∈ V
            rw [m_left, hV, fl1_emb1, fl2_emb1]
            exact ⟨(a.1.1 i).2, V2.zero_mem⟩
          · show m a.1 (Fin.natAdd S1.D j) ∈ V
            rw [m_right, hV, fl1_emb2, fl2_emb2]
            exact ⟨V1.zero_mem, (a.1.2 j).2⟩)
  have hh : Function.Injective h := by
    intro a b hab
    apply Subtype.ext
    apply hm
    exact congrArg Subtype.val hab
  have h1 := LinearMap.finrank_le_finrank_of_injective hh
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  have h3 : finrank (ZMod p) (LinearMap.range g) ≤ bad1.card + bad2.card := by
    have := Submodule.finrank_le (LinearMap.range g)
    rw [show finrank (ZMod p) ((bad1 → ZMod p) × (bad2 → ZMod p)) =
      bad1.card + bad2.card by
        rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
          Fintype.card_coe, Fintype.card_coe]] at this
    exact this
  have hdim : finrank (ZMod p) ((Fin S1.D → V1) × (Fin S2.D → V2)) =
      S1.D * finrank (ZMod p) V1 + S2.D * finrank (ZMod p) V2 := by
    rw [Module.finrank_prod]
    simp [Module.finrank_pi_fintype]
  omega

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
