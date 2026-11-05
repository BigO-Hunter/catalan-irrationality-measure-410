module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Core
@[expose] public section
set_option Elab.async false

/-!
# Dimension count for the atoms of a slot system

The domain of a pair system is cut out by the *virtual* coordinates (`bad`), where a pair
member is not an actual row.  `finrank_atoms_ge` : the atoms `dom ⊓ Π V` have dimension
`≥ D · dim V - |bad|`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Coordinate functional of a datum. -/
def coordF (p K D : ℕ) [Fact p.Prime] (d : Fin D) (k : Fin K) :
    (Fin D → Fin K → ZMod p) →ₗ[ZMod p] ZMod p := coordLin p K D d k

/-- The domain on which the coordinates in `bad` vanish. -/
def badDom (p K D : ℕ) [Fact p.Prime] (bad : Finset (Fin D × Fin K)) :
    Submodule (ZMod p) (Fin D → Fin K → ZMod p) where
  carrier := {x | ∀ b ∈ bad, x b.1 b.2 = 0}
  add_mem' := fun ha hb b hb' => by simp [ha b hb', hb b hb']
  zero_mem' := fun b _ => rfl
  smul_mem' := fun c x hx b hb => by simp [hx b hb]

theorem mem_badDom {K D : ℕ} (bad : Finset (Fin D × Fin K)) (x : Fin D → Fin K → ZMod p) :
    x ∈ badDom p K D bad ↔ ∀ b ∈ bad, x b.1 b.2 = 0 := Iff.rfl

namespace SlotSystem
variable (S : SlotSystem P N p)

/-- **Atom dimension.** If the domain is cut out by the vanishing of the coordinates in
`bad`, then `dim (dom ⊓ Π V) + |bad| ≥ D · dim V`. -/
theorem finrank_atoms_ge (V : Submodule (ZMod p) (Fin S.K → ZMod p))
    (bad : Finset (Fin S.D × Fin S.K)) (hdom : ∀ x, x ∈ S.dom ↔ x ∈ badDom p S.K S.D bad) :
    S.D * finrank (ZMod p) V ≤ finrank (ZMod p) (S.atoms V) + bad.card := by
  classical
  let m : (Fin S.D → V) →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p) :=
    LinearMap.pi fun d => V.subtype.comp (LinearMap.proj d)
  let g : (Fin S.D → V) →ₗ[ZMod p] (bad → ZMod p) :=
    LinearMap.pi fun b => (LinearMap.proj b.1.2 : (Fin S.K → ZMod p) →ₗ[ZMod p] ZMod p).comp
      (V.subtype.comp (LinearMap.proj b.1.1))
  have hm : Function.Injective m := by
    intro a b hab
    funext d
    apply Subtype.ext
    simpa [m] using congrFun hab d
  let h : LinearMap.ker g →ₗ[ZMod p] S.atoms V :=
    LinearMap.codRestrict (S.atoms V) (m.comp (LinearMap.ker g).subtype) (fun a => by
      rw [mem_atoms, hdom, mem_badDom]
      refine ⟨fun b hb => ?_, fun d => (a.1 d).2⟩
      have := congrFun (LinearMap.mem_ker.mp a.2) ⟨b, hb⟩
      simpa [g, m] using this)
  have hh : Function.Injective h := by
    intro a b hab
    apply Subtype.ext
    apply hm
    simpa [h] using congrArg Subtype.val hab
  have h1 := LinearMap.finrank_le_finrank_of_injective hh
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  have h3 : finrank (ZMod p) (LinearMap.range g) ≤ bad.card := by
    have := Submodule.finrank_le (LinearMap.range g)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
    exact this
  have hdim : finrank (ZMod p) (Fin S.D → V) = S.D * finrank (ZMod p) V := by
    simp [Module.finrank_pi_fintype]
  omega


/-- **Domain count.**  `D · dim V ≤ ν + e0 · dim V + |bad|` when the covectors seen by the
slots of index `≥ e0` kill `V`. -/
theorem slot_nullity_dom (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ)
    (hseen : ∀ j e (a : ℤ), P.b N ≤ j → j < P.L N → e0 ≤ e → e < S.emax →
      (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e = a * p →
        ∀ y ∈ V, S.prof.psi (P.H N) (j / p) a y = 0)
    (bad : Finset (Fin S.D × Fin S.K)) (hdom : ∀ x, x ∈ S.dom ↔ x ∈ badDom p S.K S.D bad) :
    S.D * finrank (ZMod p) V ≤ nullity P N p + e0 * finrank (ZMod p) V + bad.card := by
  have h1 := S.slot_nullity_pi hP hN hp2 hH V e0 hseen
  have h2 := S.finrank_atoms_ge V bad hdom
  omega
end SlotSystem
end
end CatalanMeasure.GenD.Uniform.W.Slots
