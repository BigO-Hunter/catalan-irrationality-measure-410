module
public import Submission.CatalanMeasure.Parametric.ResidueRank
@[expose] public section
namespace CatalanMeasure.Parametric
open Matrix Module
noncomputable section

/-- A coefficient kernel with at most r constraints gives at least g-r
independent left-null vectors, provided their embedding is injective. -/
theorem matrix_rank_le_of_kernel_embedding {K : Type*} [Field K] {n g r : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (B : (Fin g → K) →ₗ[K] (Fin r → K))
    (J : (Fin g → K) →ₗ[K] (Fin n → K)) (hJ : Function.Injective J)
    (hker : ∀ c,B c=0 → M.transpose.mulVecLin (J c)=0) :
    M.rank+(g-r) ≤ n :=by
  let V :=LinearMap.ker B
  let W :=LinearMap.ker M.transpose.mulVecLin
  let f : V →ₗ[K] W :=(J.comp V.subtype).codRestrict W (by
    intro c
    change M.transpose.mulVecLin (J c.val)=0
    apply hker
    exact c.property)
  have hf : Function.Injective f :=by
    intro a b hab
    apply Subtype.ext
    apply hJ
    exact congrArg (fun x : W =>x.val) hab
  have hdim :=LinearMap.finrank_le_finrank_of_injective hf
  have hb :=B.finrank_range_add_finrank_ker
  have hbr : Module.finrank K (LinearMap.range B) ≤ Module.finrank K (Fin r → K) :=
    Submodule.finrank_le _
  have hm :=M.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hpi_g : Module.finrank K (Fin g → K)=g :=by simp
  have hpi_r : Module.finrank K (Fin r → K)=r :=by simp
  have hpi_n : Module.finrank K (Fin n → K)=n :=by simp
  rw [hpi_g] at hb
  rw [hpi_r] at hbr
  rw [hpi_n] at hm
  change Module.finrank K (LinearMap.ker B) ≤ Module.finrank K (LinearMap.ker M.transpose.mulVecLin) at hdim
  have hRank : Module.finrank K (LinearMap.range M.transpose.mulVecLin)=M.rank :=by
    exact Matrix.rank_transpose M
  rw [hRank] at hm
  omega

end
end CatalanMeasure.Parametric
