module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.NativeBasis
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial
variable {K : Type*} [Field K]
noncomputable section

theorem NativeBasis.linearIndependent {f : K[X]} {h d : Nat} (B : NativeBasis f h d) :
    LinearIndependent K B.vectors := by
  have hq : LinearIndependent K B.quotient := by
    have hs := B.sequence.linearIndependent.comp (fun i : Fin d => i.val) Fin.val_injective
    simpa only [Function.comp_def,NativeBasis.sequence,dif_pos (Fin.is_lt _)] using hs
  have hk : LinearMap.ker (LinearMap.mulLeft K f)=⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro u v huv
    exact mul_left_cancel₀ B.factor_ne_zero huv
  have he : (LinearMap.mulLeft K f) ∘ B.quotient=B.vectors :=
    funext fun i => (B.factor_quotient i).symm
  rw [←he]
  exact hq.map' _ hk

/-- Unique coordinates on the exact native polynomial space. -/
def NativeBasis.coordinateEquiv {f : K[X]} {h d : Nat} (B : NativeBasis f h d) :
    (Fin d → K) ≃ₗ[K] Submodule.span K (Set.range B.vectors) :=
  (Module.Basis.span B.linearIndependent).equivFun.symm

#print axioms NativeBasis.coordinateEquiv
end
end CatalanMeasure.GenD.Uniform.Prefix


