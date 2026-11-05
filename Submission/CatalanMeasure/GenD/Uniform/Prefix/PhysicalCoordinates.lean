module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PhysicalTiling
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Uniform.Prefix
variable {K : Type*} [Field K]
noncomputable section

theorem physicalTiling_apply_label (b h p : Nat) (hp : p=2*h+1) (h2 : (2 : K)≠0)
    (x : TilingCoordinates (K := K) b h) (i : RowLabels b h) :
    physicalTilingEquiv b h p hp h2 x (fullRowIndexEquiv b h p hp i)=
      packRows b h (tilingEquiv b h h2 x) i := by
  unfold physicalTilingEquiv
  simp only [LinearEquiv.trans_apply]
  exact Equiv.piCongrLeft_apply_apply (fun _ => K) (fullRowIndexEquiv b h p hp) _ i

theorem physicalTiling_pair_plus (b h p : Nat) (hp : p=2*h+1) (h2 : (2 : K)≠0)
    (x : TilingCoordinates (K := K) b h) (k : Fin b) (j : Fin h) :
    physicalTilingEquiv b h p hp h2 x (fullRowIndexEquiv b h p hp (.inr (k,j,true)))=
      x.1.1 (finProdFinEquiv (k,j))+x.1.2 (finProdFinEquiv (k,j)) := by
  rw [physicalTiling_apply_label]
  rfl

theorem physicalTiling_pair_minus (b h p : Nat) (hp : p=2*h+1) (h2 : (2 : K)≠0)
    (x : TilingCoordinates (K := K) b h) (k : Fin b) (j : Fin h) :
    physicalTilingEquiv b h p hp h2 x (fullRowIndexEquiv b h p hp (.inr (k,j,false)))=
      x.1.1 (finProdFinEquiv (k,j))-x.1.2 (finProdFinEquiv (k,j)) := by
  rw [physicalTiling_apply_label]
  rfl

theorem physicalTiling_center (b h p : Nat) (hp : p=2*h+1) (h2 : (2 : K)≠0)
    (x : TilingCoordinates (K := K) b h) (k : Fin (b+1)) :
    physicalTilingEquiv b h p hp h2 x (fullRowIndexEquiv b h p hp (.inl k))=
      centerMap (b+1) x.2 k := by
  rw [physicalTiling_apply_label]
  rfl
end
end CatalanMeasure.GenD.Uniform.Prefix
