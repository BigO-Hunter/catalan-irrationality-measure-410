module
public import Submission.CatalanMeasure.GenD.Uniform.W.Nullity
public import Submission.CatalanMeasure.GenD.Uniform.W.RankStep
@[expose] public section
set_option Elab.async false

/-!
# Family templates over Theorem W

Two ready-made shapes, so that a family instance is a count lemma plus the construction of its
atom map:

* `w_product` (Frobenius products, KERNEL-FAMILY-THEOREM (LB)): atoms `Π ⊗ V` with
  `V = ker E` the profiles (τ-windows) killed by `e` seen functionals on `β` coordinates, and
  `Π` of dimension `m`; if every atom has polynomial raw response of degree `< q`, then
  `ν ≥ m · (β - e)`.
* `w_mixed` (Theorem U / Theorem M): profiles `v = (v_C, v_H) ∈ X × Y` with conditions
  `α v_C = 0` (`n_C`) and `β v_C + Γ v_H = 0` (`n_mix`); for a section `V` of the projection to
  `X` the atoms `Π ⊗ V` give `ν ≥ m · (dim X - n_C - (n_mix - rank Γ))`.
  `rank Γ` may be bounded below by `rat_minor_rank` (one fixed minor) or replaced by `0`.
-/

namespace CatalanMeasure.GenD.Uniform.W
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Every atom of a family is killed (polynomial raw responses of degree `< q` on `[b,L)`). -/
def RawKilled (P : Parameters) (N p : ℕ) [Fact p.Prime] (c : Fin (P.n N) → ZMod p) : Prop :=
  ∃ F : (ZMod p)[X], F.natDegree < P.q N ∧
    ∀ j, P.b N ≤ j → j < P.L N → uResp P N p j c = F.eval (j : ZMod p)

/-- `ν ≥ dim A` for an injective family of killed atoms. -/
theorem w_killed (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) {A : Type*} [AddCommGroup A]
    [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    (ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (hι : Function.Injective ι)
    (hraw : ∀ a, RawKilled P N p (ι a)) : finrank (ZMod p) A ≤ nullity P N p := by
  have h := w_raw hp2 hH ι hι (0 : A →ₗ[ZMod p] (Fin 0 → ZMod p)) (fun a _ => hraw a)
  rw [LinearMap.range_zero, finrank_bot, Nat.sub_zero] at h
  exact h

/-- **Product template.** -/
theorem w_product (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) {m β e : ℕ}
    (E : (Fin β → ZMod p) →ₗ[ZMod p] (Fin e → ZMod p))
    (ι : (Fin m → LinearMap.ker E) →ₗ[ZMod p] (Fin (P.n N) → ZMod p))
    (hι : Function.Injective ι) (hraw : ∀ x, RawKilled P N p (ι x)) :
    m * (β - e) ≤ nullity P N p := by
  have h := w_killed hp2 hH ι hι hraw
  have hk := kappa_ge E
  have hd : finrank (ZMod p) (Fin m → LinearMap.ker E) = m * finrank (ZMod p) (LinearMap.ker E) := by
    simp [Module.finrank_pi_fintype]
  rw [hd] at h
  exact (Nat.mul_le_mul_left m hk).trans h

section Mixed
variable {K : Type*} [Field K] {U X : Type*} [AddCommGroup U] [Module K U]
  [FiniteDimensional K U] [AddCommGroup X] [Module K X] [FiniteDimensional K X]

/-- A section inside a given subspace. -/
theorem exists_section_in (W : Submodule K U) (f : U →ₗ[K] X) :
    ∃ V : Submodule K U, V ≤ W ∧ finrank K V = finrank K (W.map f) ∧
      Function.Injective (f.comp V.subtype) := by
  obtain ⟨V', hd, hi⟩ := exists_section (f.comp W.subtype)
  refine ⟨V'.map W.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨w, _, rfl⟩
    exact w.2
  · rw [LinearMap.range_comp, Submodule.range_subtype] at hd
    rw [← hd]
    exact (Submodule.equivMapOfInjective _ W.subtype_injective V').finrank_eq.symm
  · intro a b h
    obtain ⟨w1, hw1, e1⟩ := Submodule.mem_map.mp a.2
    obtain ⟨w2, hw2, e2⟩ := Submodule.mem_map.mp b.2
    simp only [Submodule.subtype_apply] at e1 e2
    have hab : f a.1 = f b.1 := h
    have h' : (f.comp W.subtype).comp V'.subtype ⟨w1, hw1⟩ =
        (f.comp W.subtype).comp V'.subtype ⟨w2, hw2⟩ := by
      show f (w1 : U) = f (w2 : U)
      rw [e1, e2]
      exact hab
    have h12 : w1 = w2 := congrArg Subtype.val (hi h')
    apply Subtype.ext
    rw [← e1, ← e2, h12]

end Mixed

/-- **Mixed (Theorem U) template.**  `ι V` is the atom map on `Π ⊗ V` (`m = dim Π`) for a
subspace `V` of profile pairs; it must be injective whenever `V` lies in the mixed kernel and
the projection to `X` is injective on `V`, and its atoms must be killed. -/
theorem w_mixed (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) {X Y : Type*} [AddCommGroup X]
    [Module (ZMod p) X] [FiniteDimensional (ZMod p) X] [AddCommGroup Y] [Module (ZMod p) Y]
    [FiniteDimensional (ZMod p) Y] {nC nM m : ℕ}
    (α : X →ₗ[ZMod p] (Fin nC → ZMod p)) (β : X →ₗ[ZMod p] (Fin nM → ZMod p))
    (Γ : Y →ₗ[ZMod p] (Fin nM → ZMod p))
    (ι : ∀ V : Submodule (ZMod p) (X × Y), (Fin m → V) →ₗ[ZMod p] (Fin (P.n N) → ZMod p))
    (hι : ∀ V, V ≤ LinearMap.ker (mixedMap α β Γ) →
      Function.Injective ((LinearMap.fst (ZMod p) X Y).comp V.subtype) → Function.Injective (ι V))
    (hraw : ∀ V, V ≤ LinearMap.ker (mixedMap α β Γ) → ∀ x, RawKilled P N p (ι V x)) :
    m * (finrank (ZMod p) X - nC - (nM - finrank (ZMod p) (LinearMap.range Γ))) ≤
      nullity P N p := by
  obtain ⟨V, hV, hd, hinj⟩ := exists_section_in (LinearMap.ker (mixedMap α β Γ))
    (LinearMap.fst (ZMod p) X Y)
  have h := w_killed hp2 hH (ι V) (hι V hV hinj) (hraw V hV)
  have hm := mixed_proj_finrank α β Γ
  have hdim : finrank (ZMod p) (Fin m → V) = m * finrank (ZMod p) V := by
    simp [Module.finrank_pi_fintype]
  rw [hdim, hd] at h
  exact (Nat.mul_le_mul_left m hm).trans h

end
end CatalanMeasure.GenD.Uniform.W
