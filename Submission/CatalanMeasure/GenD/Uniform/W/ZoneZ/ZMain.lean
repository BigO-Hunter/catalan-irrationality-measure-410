module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZGroups
@[expose] public section
set_option Elab.async false

/-!
# Theorem Z, Law_H(4) without cap: the nullity bound

`zH_le_nullity`: for `p ∤ ZcH`-type unit hypotheses (packaged in `CellHyp`, `hind1`, `hind2`),
`4hp + 2 - virt - groups ≤ ν`, the condition-count form `N_H` of zone2 sec. 5 in the regime
`η < p`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem finrank_ker_ge_codom {M E : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [FiniteDimensional (ZMod p) M] [AddCommGroup E] [Module (ZMod p) E]
    [FiniteDimensional (ZMod p) E] (f : M →ₗ[ZMod p] E) :
    finrank (ZMod p) M - finrank (ZMod p) E ≤ finrank (ZMod p) (LinearMap.ker f) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := Submodule.finrank_le (LinearMap.range f)
  omega

theorem finrank_ZPar (hp : ℕ) : finrank (ZMod p) (ZPar p hp) = 4 * hp + 2 := by
  simp [ZPar, Module.finrank_prod, Module.finrank_fin_fun]; ring

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
