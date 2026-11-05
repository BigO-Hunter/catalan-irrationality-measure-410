module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PhysicalIndex
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.TilingCoefficients
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
variable {K : Type*} [Field K]
noncomputable section
abbrev TilingCoordinates (b h : Nat) :=
  ((Fin (b*h) → K) × (Fin (b*h) → K)) × (Fin (b+1) → K)

/-- Repack the coefficient path and the two noncentral pair members without
adding or suppressing any coordinate. -/
def packRows (b h : Nat) : TilingCoordinates (K := K) b h ≃ₗ[K] (RowLabels b h → K) where
  toFun x := fun i => match i with
    | .inl k => x.2 k
    | .inr (k,j,true) => x.1.1 (finProdFinEquiv (k,j))
    | .inr (k,j,false) => x.1.2 (finProdFinEquiv (k,j))
  invFun w := ((fun i => w (.inr ((finProdFinEquiv.symm i).1,(finProdFinEquiv.symm i).2,true)),
    fun i => w (.inr ((finProdFinEquiv.symm i).1,(finProdFinEquiv.symm i).2,false))),
    fun k => w (.inl k))
  left_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · funext i
        exact congrArg x.1.1 (finProdFinEquiv.apply_symm_apply i)
      · funext i
        exact congrArg x.1.2 (finProdFinEquiv.apply_symm_apply i)
    · rfl
  right_inv w := by
    funext i
    rcases i with k|⟨k,j,s⟩
    · rfl
    · cases s <;> simp
  map_add' x y := by
    funext i
    rcases i with k|⟨k,j,s⟩
    · rfl
    · cases s <;> rfl
  map_smul' a x := by
    funext i
    rcases i with k|⟨k,j,s⟩
    · rfl
    · cases s <;> rfl

/-- The actual complete coefficient tiling is a linear equivalence to all
physical rows in the enlarged interval, including K=0 and both endpoint centers. -/
def physicalTilingEquiv (b h p : Nat) (hp : p=2*h+1) (h2 : (2 : K)≠0) :
    TilingCoordinates (K := K) b h ≃ₗ[K] (Fin (b*p+1) → K) :=
  ((tilingEquiv b h h2).trans (packRows b h)).trans
    (LinearEquiv.piCongrLeft K (fun _ => K) (fullRowIndexEquiv b h p hp))

theorem physicalTiling_injective (b h p : Nat) (hp : p=2*h+1) (h2 : (2 : K)≠0) :
    Function.Injective (physicalTilingEquiv b h p hp h2) :=
  (physicalTilingEquiv b h p hp h2).injective

#print axioms physicalTilingEquiv
end
end CatalanMeasure.GenD.Uniform.Prefix

