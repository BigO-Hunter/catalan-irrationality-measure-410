module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.Mono
@[expose] public section
set_option Elab.async false

/-!
# `MonoData` from a forward map

If the physical rows `c` map by an INJECTIVE linear `Θ` to monomial atoms with the two slot identities
holding for every `c`, then `dom = range Θ` and `rows = ` a linear left inverse of `Θ` is a `MonoData`.
The whole physical content of `MonoData` is the forward identity; membership of the atoms (jet kernel)
in `range Θ` is the separate hypothesis `hdom` of `monoHost`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts3 CatalanMeasure.GenD.Uniform.Prefix
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

def monoOfForward {K : ℕ} (prof : Prof p K)
    (Θ : (Fin (P.n N) → ZMod p) →ₗ[ZMod p] (Fin p → Fin K → ZMod p))
    (hΘ : Function.Injective Θ)
    (hU : ∀ c, (X - 1) ^ P.h N * intrinsicU P N p c =
      ∑ e : Fin p, X ^ (e : ℕ) * (prof.Ty (Θ c e)).comp (X ^ p))
    (hT : ∀ c, (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * intrinsicT P N p c =
      ∑ e : Fin p, X ^ (e : ℕ) * (prof.Gy (Θ c e)).comp (X ^ p)) : MonoData P N p K :=
  let L := Classical.choose (LinearMap.exists_leftInverse_of_injective Θ
    (LinearMap.ker_eq_bot.mpr hΘ))
  have hL : L.comp Θ = LinearMap.id := Classical.choose_spec (LinearMap.exists_leftInverse_of_injective Θ
    (LinearMap.ker_eq_bot.mpr hΘ))
  { prof := prof
    rows := L
    dom := LinearMap.range Θ
    repU := by
      rintro x ⟨c, rfl⟩
      have : L (Θ c) = c := by simpa using congrArg (fun f => f c) hL
      rw [this]; exact hU c
    repT := by
      rintro x ⟨c, rfl⟩
      have : L (Θ c) = c := by simpa using congrArg (fun f => f c) hL
      rw [this]; exact hT c
    inj := by
      rintro x ⟨c, rfl⟩ h
      have : L (Θ c) = c := by simpa using congrArg (fun f => f c) hL
      rw [this] at h; rw [h, map_zero] }

theorem monoOfForward_dom {K : ℕ} (prof : Prof p K)
    (Θ : (Fin (P.n N) → ZMod p) →ₗ[ZMod p] (Fin p → Fin K → ZMod p))
    (hΘ : Function.Injective Θ) (hU hT) :
    (monoOfForward (P := P) (N := N) prof Θ hΘ hU hT).dom = LinearMap.range Θ := rfl

end
end CatalanMeasure.GenD.Uniform.W.Charts4
