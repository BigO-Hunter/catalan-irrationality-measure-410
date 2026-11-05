module
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option Elab.async false

/-!
# Theorem W, abstract core

For a square matrix `M` over a field, the left kernel is `ker Mᵀ.mulVecLin`, of dimension
`n - rank M`.  A W-construction is

* a finite-dimensional atom space `A` with an injective linear map `ι` into the row vectors,
* a linear jet map `Φ` on `A` (window coefficients, Taylor coefficients, responses, ...),
* a linear "filter obstruction" `χ` on `ker Φ` whose kernel lies in the left kernel.

`w_master` : `dim A - rank Φ - rank χ ≤ n - rank M`.

Theorem W proper (`w_core`) is the case where `χ` is the response on the columns outside a kill
set `Kset`, so `rank χ ≤ n - |Kset|`.  The J-flat form is the case of polynomial responses
(`GenD/Uniform/W/Flat`).
-/

namespace CatalanMeasure.GenD.Uniform.W
open Module Matrix
noncomputable section
variable {K : Type*} [Field K] {n : ℕ}

/-- The dimension of the left kernel of a square matrix. -/
theorem finrank_leftKer (M : Matrix (Fin n) (Fin n) K) :
    finrank K (LinearMap.ker M.transpose.mulVecLin) = n - M.rank := by
  have hm := M.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hr : finrank K (LinearMap.range M.transpose.mulVecLin) = M.rank :=
    Matrix.rank_transpose M
  rw [hr, Module.finrank_pi, Fintype.card_fin] at hm
  omega

/-- An injective linear map into the left kernel bounds the left nullity from below. -/
theorem le_nullity_of_injective {U : Type*} [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (M : Matrix (Fin n) (Fin n) K) (J : U →ₗ[K] (Fin n → K))
    (hJ : Function.Injective J) (hker : ∀ u, M.transpose.mulVec (J u) = 0) :
    finrank K U ≤ n - M.rank := by
  rw [← finrank_leftKer M]
  let f : U →ₗ[K] LinearMap.ker M.transpose.mulVecLin :=
    J.codRestrict _ (fun u => by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hker u)
  have hf : Function.Injective f := fun a b hab => hJ (congrArg Subtype.val hab)
  exact LinearMap.finrank_le_finrank_of_injective hf

/-- **Theorem W, master form.**  `χ` is any linear obstruction on `ker Φ` whose vanishing puts
the row into the left kernel. -/
theorem w_master {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    {E Q : Type*} [AddCommGroup E] [Module K E] [AddCommGroup Q] [Module K Q]
    (M : Matrix (Fin n) (Fin n) K) (ι : A →ₗ[K] (Fin n → K)) (hι : Function.Injective ι)
    (Φ : A →ₗ[K] E) (χ : LinearMap.ker Φ →ₗ[K] Q)
    (hkill : ∀ u : LinearMap.ker Φ, χ u = 0 → M.transpose.mulVec (ι u) = 0) :
    finrank K A - finrank K (LinearMap.range Φ) - finrank K (LinearMap.range χ) ≤
      n - M.rank := by
  have h1 := Φ.finrank_range_add_finrank_ker
  have h2 := χ.finrank_range_add_finrank_ker
  let J : LinearMap.ker χ →ₗ[K] (Fin n → K) :=
    ι.comp ((LinearMap.ker Φ).subtype.comp (LinearMap.ker χ).subtype)
  have hJ : Function.Injective J := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (hι hab))
  have h3 := le_nullity_of_injective M J hJ (fun u => hkill u.1 u.2)
  omega

/-- The responses of a row on the columns outside a kill set. -/
def offCols (M : Matrix (Fin n) (Fin n) K) (Kset : Finset (Fin n)) :
    (Fin n → K) →ₗ[K] ({k : Fin n // k ∉ Kset} → K) :=
  (LinearMap.funLeft K K Subtype.val).comp M.transpose.mulVecLin

theorem card_off (Kset : Finset (Fin n)) :
    Fintype.card {k : Fin n // k ∉ Kset} = n - Kset.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

/-- **Theorem W.**  If every row of `ker Φ` has zero response on every column of `Kset`, then
`ν ≥ dim A - rank Φ - (n - |Kset|)`. -/
theorem w_core {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    {E : Type*} [AddCommGroup E] [Module K E]
    (M : Matrix (Fin n) (Fin n) K) (ι : A →ₗ[K] (Fin n → K)) (hι : Function.Injective ι)
    (Φ : A →ₗ[K] E) (Kset : Finset (Fin n))
    (hkill : ∀ a, Φ a = 0 → ∀ k ∈ Kset, M.transpose.mulVec (ι a) k = 0) :
    finrank K A - finrank K (LinearMap.range Φ) - (n - Kset.card) ≤ n - M.rank := by
  let χ := (offCols M Kset).comp (ι.comp (LinearMap.ker Φ).subtype)
  have hχ : finrank K (LinearMap.range χ) ≤ n - Kset.card := by
    have := Submodule.finrank_le (LinearMap.range χ)
    rwa [Module.finrank_fintype_fun_eq_card, card_off] at this
  have h := w_master M ι hι Φ χ (by
    intro u hu
    funext k
    by_cases hk : k ∈ Kset
    · exact hkill u.1 u.2 k hk
    · exact congrFun hu ⟨k, hk⟩)
  omega

/-- Counting form of Theorem W: `rank Φ ≤ dim E`. -/
theorem w_core_count {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (M : Matrix (Fin n) (Fin n) K) (ι : A →ₗ[K] (Fin n → K)) (hι : Function.Injective ι)
    (Φ : A →ₗ[K] E) (Kset : Finset (Fin n))
    (hkill : ∀ a, Φ a = 0 → ∀ k ∈ Kset, M.transpose.mulVec (ι a) k = 0) :
    finrank K A - finrank K E - (n - Kset.card) ≤ n - M.rank := by
  have h := w_core M ι hι Φ Kset hkill
  have := Submodule.finrank_le (LinearMap.range Φ)
  omega

/-- Theorem W with every column killed (`K` = all columns): `ν ≥ dim A - rank Φ`. -/
theorem w_core_all {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    {E : Type*} [AddCommGroup E] [Module K E]
    (M : Matrix (Fin n) (Fin n) K) (ι : A →ₗ[K] (Fin n → K)) (hι : Function.Injective ι)
    (Φ : A →ₗ[K] E) (hkill : ∀ a, Φ a = 0 → M.transpose.mulVec (ι a) = 0) :
    finrank K A - finrank K (LinearMap.range Φ) ≤ n - M.rank := by
  have h := w_core M ι hι Φ Finset.univ (fun a ha k _ => by rw [hkill a ha]; rfl)
  rw [Finset.card_univ, Fintype.card_fin, Nat.sub_self, Nat.sub_zero] at h
  exact h

end
end CatalanMeasure.GenD.Uniform.W
