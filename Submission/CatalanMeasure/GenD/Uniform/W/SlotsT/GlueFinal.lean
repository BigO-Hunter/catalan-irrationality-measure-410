module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.GlueCount4
@[expose] public section
set_option Elab.async false

/-!
# Theorem MT (b), final count
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

set_option maxHeartbeats 1600000 in
/-- **Theorem MT, overflow below (variant (b)), with the profile family as input.** -/
theorem mt_glue_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K D1 m s elo : ℕ} (k0 : ℤ) (hD : D1 ≤ (p - 1) / 2) (hph : p ≤ P.h N + (p - 1) / 2)
    (hv : P.h N + (p - 1) / 2 - p < p)
    (hs : s * p + 1 ≤ P.H N) (hpη : p ≤ P.H N - 1 - s * p) (hη2 : P.H N - 1 - s * p < 2 * p)
    (hdeg : P.h N + D1 ≤ (P.H N - 1 - s * p) + 1) (helo : elo ≤ P.H N - 1 - s * p - p + 1)
    (y u : Fin m → Fin K → ZMod p) (A B : Fin m → ZMod p)
    (hy : LinearIndependent (ZMod p) y) (hu : LinearIndependent (ZMod p) u)
    (J1 J2 : Finset ℕ)
    (hJ1 : ∀ i J, J ∈ J1 →
      (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).psi (P.H N) J s (y i) = A i ∧
      (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).psi (P.H N) J s (u i) = B i)
    (hJ2 : ∀ i J, J ∈ J2 →
      (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).psi (P.H N) J ((s : ℤ) + 1) (y i) +
        (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).psi (P.H N) J ((s : ℤ) + 1) (u i) = A i + B i)
    (hcov1 : ∀ j, P.b N ≤ j → j < P.L N →
      P.H N - 1 - s * p - (P.h N + D1 - 1) ≤ j % p → j / p ∈ J1)
    (hcov2 : ∀ j, P.b N ≤ j → j < P.L N →
      j % p + elo + p ≤ P.H N - 1 - s * p → j / p ∈ J2) :
    m * D1 + m * (D1 + 1) ≤ nullity P N p +
      (m * ((P.H N - 1 - s * p - p + 1) + elo) + mixMiss P N p K D1 k0) +
        (p - P.q N - (P.h N + (p - 1) / 2 - p)) := by
  classical
  set η := P.H N - 1 - s * p with hη
  set S := mtSystem' P N p hp2 hph K D1 k0 hD with hS
  set Aτ := LinearMap.ker (totalCond P N p K D1 m η elo k0 y u) with hAτ
  have hξ : ∀ a : Aτ, (famData y u).comp Aτ.subtype a ∈ S.dom := fun a =>
    famData_mem_relaxDom K D1 m η elo k0 y u a
  have hξi : Function.Injective ((famData y u).comp Aτ.subtype) :=
    (famData_injective y u hy hu).comp (Submodule.subtype_injective _)
  have hres := S.slot_nullity_jflat0 hP hN hp2 hH ((famData y u).comp Aτ.subtype) hξ hξi
    (P.h N + (p - 1) / 2 - p)
    (LinearMap.pi fun ℓ : ZMod p => (omegaL P N p D1 m η A B ℓ).comp Aτ.subtype)
    (fun a => by
      obtain ⟨G, hG, hGe⟩ := fold_poly hp2 hph hv hpη hη2 hdeg A B a.1
      refine ⟨G, hG, fun ℓ => ?_⟩
      rw [← hGe ℓ]
      simp [omegaL_apply])
    (fun a j h1 h2 => by
      have hΨ := LinearMap.mem_ker.mp a.2
      have hgc : ∀ i (c : glueIdx η p elo),
          (if c.1.2 then lamL P N p D1 m i c.1.1 - pL P N p D1 m i c.1.1
            else pL P N p D1 m i c.1.1) a.1 = 0 := fun i c => by
        have := congrFun (congrFun (congrArg Prod.fst hΨ) i) c
        simpa [totalCond, glueCond] using this
      have hmemT : ∀ e, e < η - p + 1 → (e, true) ∈ glueIdx η p elo := fun e he => by
        simp [glueIdx]; omega
      have hmemF : ∀ e, e < elo → (e, false) ∈ glueIdx η p elo := fun e he => by
        simp [glueIdx, he]
      have hjet : ∀ i e, e < elo → (lamPoly P N p (a.1.1 i)).coeff e = 0 ∧
          (pPoly P N p (a.1.2 i)).coeff e = 0 := by
        intro i e he
        have h1 := hgc i ⟨(e, true), hmemT e (by omega)⟩
        have h2 := hgc i ⟨(e, false), hmemF e he⟩
        simp only [if_true, LinearMap.sub_apply, lamL_apply, pL_apply] at h1
        simp only [Bool.false_eq_true, if_false, pL_apply] at h2
        exact ⟨by linear_combination h1 + h2, h2⟩
      have hglue : ∀ i e, elo ≤ e → e ≤ η - p →
          (lamPoly P N p (a.1.1 i)).coeff e = (pPoly P N p (a.1.2 i)).coeff e := by
        intro i e he1 he2
        have h1 := hgc i ⟨(e, true), hmemT e (by omega)⟩
        simp only [if_true, LinearMap.sub_apply, lamL_apply, pL_apply] at h1
        linear_combination h1
      have hr := resp_fam hp2 hph k0 hD y u A B J1 J2 hs hpη hη2 hdeg hJ1 hJ2 a.1 hjet hglue j
        (hcov1 j h1 h2) (hcov2 j h1 h2)
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply, omegaL_apply,
        ZMod.val_natCast]
      have hell : j % p < p := Nat.mod_lt _ (Fact.out : p.Prime).pos
      rw [if_pos (by omega : j % p ≤ η)]
      exact hr)
  have hdim := finrank_ker_totalCond (P := P) (N := N) K D1 m η elo k0 y u
  have hdim' : m * D1 + m * (D1 + 1) ≤ finrank (ZMod p) Aτ +
      (m * ((η - p + 1) + elo) + mixMiss P N p K D1 k0) := hdim
  omega

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
