module
public import Submission.CatalanMeasure.GenD.Uniform.W.Core
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Dimension.Constructions
@[expose] public section
set_option Elab.async false

/-!
# Jet maps for Theorem W

A jet map is a finite stack of linear functionals (or of linear maps with values in arbitrary
modules).  The rank of a stack is at most the sum of the ranks of its groups, and a group of
`w` scalar jets has rank at most `w`.  These are the "plain count" rank steps.

Scalar jets on polynomial atoms: a coefficient (`coeffJet`, window position at `0` or, after
reversal, at infinity) and a Taylor coefficient at a point (`taylorJet`, used at `y = ±1`).
-/

namespace CatalanMeasure.GenD.Uniform.W
open Module
noncomputable section
variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A]

/-- Stack of scalar jets indexed by a finite type. -/
def jetMap {J : Type*} (φ : J → A →ₗ[K] K) : A →ₗ[K] (J → K) := LinearMap.pi φ

theorem jetMap_eq_zero_iff {J : Type*} (φ : J → A →ₗ[K] K) (a : A) :
    jetMap φ a = 0 ↔ ∀ j, φ j a = 0 := by
  simp [jetMap, funext_iff]

/-- A stack of `#J` scalar jets has rank at most `#J`. -/
theorem rank_jetMap_le {J : Type*} [Fintype J] (φ : J → A →ₗ[K] K) :
    finrank K (LinearMap.range (jetMap φ)) ≤ Fintype.card J := by
  have := Submodule.finrank_le (LinearMap.range (jetMap φ))
  rwa [Module.finrank_fintype_fun_eq_card] at this

/-- A linear map into `Fin w → K` has rank at most `w`. -/
theorem rank_le_width {w : ℕ} (f : A →ₗ[K] (Fin w → K)) :
    finrank K (LinearMap.range f) ≤ w := by
  have := Submodule.finrank_le (LinearMap.range f)
  rwa [Module.finrank_fin_fun] at this

/-- Stack of jet groups with values in arbitrary modules. -/
def stackMap {C : Type*} {W : C → Type*} [∀ c, AddCommGroup (W c)] [∀ c, Module K (W c)]
    (Φ : ∀ c, A →ₗ[K] W c) : A →ₗ[K] (∀ c, W c) := LinearMap.pi Φ

theorem stackMap_eq_zero_iff {C : Type*} {W : C → Type*} [∀ c, AddCommGroup (W c)]
    [∀ c, Module K (W c)] (Φ : ∀ c, A →ₗ[K] W c) (a : A) :
    stackMap Φ a = 0 ↔ ∀ c, Φ c a = 0 := by
  simp [stackMap, funext_iff]

/-- **Rank of a stack.**  The rank of stacked jet groups is at most the sum of their ranks
(independence of the groups is not needed). -/
theorem rank_stackMap_le [FiniteDimensional K A] {C : Type*} [Fintype C] {W : C → Type*}
    [∀ c, AddCommGroup (W c)] [∀ c, Module K (W c)] (Φ : ∀ c, A →ₗ[K] W c) :
    finrank K (LinearMap.range (stackMap Φ)) ≤ ∑ c, finrank K (LinearMap.range (Φ c)) := by
  let r : A →ₗ[K] (∀ c, LinearMap.range (Φ c)) := LinearMap.pi fun c => (Φ c).rangeRestrict
  let s : (∀ c, LinearMap.range (Φ c)) →ₗ[K] (∀ c, W c) :=
    LinearMap.pi fun c => (Φ c).range.subtype.comp (LinearMap.proj c)
  have hs : stackMap Φ = s.comp r := by
    ext a c
    rfl
  rw [hs, LinearMap.range_comp]
  calc finrank K (Submodule.map s (LinearMap.range r)) ≤ finrank K (LinearMap.range r) :=
        Submodule.finrank_map_le _ _
    _ ≤ finrank K (∀ c, LinearMap.range (Φ c)) := Submodule.finrank_le _
    _ = ∑ c, finrank K (LinearMap.range (Φ c)) := Module.finrank_pi_fintype K

/-- Two jet groups. -/
theorem rank_prod_le [FiniteDimensional K A] {E F : Type*} [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (f : A →ₗ[K] E) (g : A →ₗ[K] F) :
    finrank K (LinearMap.range (f.prod g)) ≤
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g) := by
  let r : A →ₗ[K] (LinearMap.range f × LinearMap.range g) := f.rangeRestrict.prod g.rangeRestrict
  let s : (LinearMap.range f × LinearMap.range g) →ₗ[K] (E × F) :=
    (LinearMap.range f).subtype.prodMap (LinearMap.range g).subtype
  have hs : f.prod g = s.comp r := by
    ext a <;> rfl
  rw [hs, LinearMap.range_comp]
  calc finrank K (Submodule.map s (LinearMap.range r)) ≤ finrank K (LinearMap.range r) :=
        Submodule.finrank_map_le _ _
    _ ≤ finrank K (LinearMap.range f × LinearMap.range g) := Submodule.finrank_le _
    _ = _ := Module.finrank_prod

/-- Restricting a jet map to a subspace (or precomposing) does not raise its rank. -/
theorem rank_comp_le [FiniteDimensional K A] {B E : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup E] [Module K E] (f : A →ₗ[K] E) (g : B →ₗ[K] A) :
    finrank K (LinearMap.range (f.comp g)) ≤ finrank K (LinearMap.range f) := by
  rw [LinearMap.range_comp]
  exact Submodule.finrank_mono LinearMap.map_le_range

/-- A jet group that vanishes identically costs nothing. -/
theorem rank_eq_zero_of_eq_zero {E : Type*} [AddCommGroup E] [Module K E]
    (f : A →ₗ[K] E) (hf : ∀ a, f a = 0) : finrank K (LinearMap.range f) = 0 := by
  have : LinearMap.range f = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨a, rfl⟩
    simp [hf a]
  rw [this, finrank_bot]

/-! ### Scalar jets on polynomial atoms -/

/-- The coefficient of `y^k` (a window position at `0`; at infinity after a reversal). -/
def coeffJet (k : ℕ) : Polynomial K →ₗ[K] K := Polynomial.lcoeff K k

/-- The `k`-th Taylor coefficient at the point `a` (used at `y = 1` and `y = -1`). -/
def taylorJet (a : K) (k : ℕ) : Polynomial K →ₗ[K] K :=
  (Polynomial.lcoeff K k).comp (Polynomial.taylor a)

theorem coeffJet_apply (k : ℕ) (f : Polynomial K) : coeffJet k f = f.coeff k := rfl

theorem taylorJet_apply (a : K) (k : ℕ) (f : Polynomial K) :
    taylorJet a k f = (Polynomial.taylor a f).coeff k := rfl

/-- A slot polynomial space with prescribed order data: `Q * g` with `deg g < m`.  All order
conditions at `0`, `±1` (and the slot factors) are carried by the fixed factor `Q`; the cap at
infinity is `deg Q + m - 1`.  Coordinates are the `m` coefficients of `g`. -/
def slotPoly (Q : Polynomial K) (m : ℕ) : (Fin m → K) →ₗ[K] Polynomial K :=
  (LinearMap.mulLeft K Q).comp
    ((Polynomial.degreeLT K m).subtype.comp (Polynomial.degreeLTEquiv K m).symm.toLinearMap)

theorem slotPoly_injective {Q : Polynomial K} (hQ : Q ≠ 0) (m : ℕ) :
    Function.Injective (slotPoly Q m) := by
  intro a b hab
  have h : Q * ((Polynomial.degreeLTEquiv K m).symm a : Polynomial K) =
      Q * ((Polynomial.degreeLTEquiv K m).symm b : Polynomial K) := hab
  have h2 := mul_left_cancel₀ hQ h
  exact (Polynomial.degreeLTEquiv K m).symm.injective (Subtype.ext h2)

end
end CatalanMeasure.GenD.Uniform.W
