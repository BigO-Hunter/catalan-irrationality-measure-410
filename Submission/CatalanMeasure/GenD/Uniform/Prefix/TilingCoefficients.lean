module
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

namespace CatalanMeasure.GenD.Uniform.Prefix
variable {K : Type*} [Field K]
noncomputable section

/-- Centers of consecutive full p-blocks: the outer center is an independent
coordinate, and each internal edge contributes to both its endpoint centers. -/
def centerMap (n : Nat) : (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun u i := u i + if h : i.val+1<n then u ⟨i.val+1,h⟩ else 0
  map_add' u v := by
    funext i
    by_cases h : i.val+1<n <;> simp [h, add_assoc, add_comm, add_left_comm]
  map_smul' a u := by
    funext i
    by_cases h : i.val+1<n <;> simp [h, mul_add]

theorem centerMap_injective (n : Nat) : Function.Injective (centerMap (K := K) n) := by
  have hz : ∀ u : Fin n → K, centerMap n u = 0 → u = 0 := by
    intro u hu
    have step : ∀ t : Nat, ∀ i : Fin n, i.val+t+1=n → u i=0 := by
      intro t
      induction t with
      | zero =>
        intro i hi
        have heq := congrFun hu i
        change u i + (if h : i.val+1<n then u ⟨i.val+1,h⟩ else 0) = 0 at heq
        simpa only [dif_neg (show ¬ i.val+1<n by omega), add_zero] using heq
      | succ t ih =>
        intro i hi
        have hnext : i.val+1<n := by omega
        let j : Fin n := ⟨i.val+1,hnext⟩
        have hj : j.val+t+1=n := by dsimp [j]; omega
        have huj := ih j hj
        have heq := congrFun hu i
        change u i + (if h : i.val+1<n then u ⟨i.val+1,h⟩ else 0) = 0 at heq
        rw [dif_pos hnext] at heq
        change u i + u j = 0 at heq
        simpa only [huj, add_zero] using heq
    funext i
    exact step (n-1-i.val) i (by have := i.is_lt; omega)
  intro u v huv
  have hzero : centerMap n (u-v)=0 := by rw [map_sub,huv,sub_self]
  exact sub_eq_zero.mp (hz (u-v) hzero)

/-- Unit-triangular center path, including n=1 (one block's outside center)
and n=0 (the empty coordinate space). -/
def centerEquiv (n : Nat) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofBijective (centerMap n)
    ⟨centerMap_injective n, LinearMap.injective_iff_surjective.mp (centerMap_injective n)⟩

/-- Symmetric and antisymmetric noncentral pair coefficients; inverse division
uses only2, exactly the excluded characteristic in the physical source. -/
def pairEquiv (n : Nat) (h2 : (2 : K) ≠ 0) :
    ((Fin n → K) × (Fin n → K)) ≃ₗ[K] ((Fin n → K) × (Fin n → K)) where
  toFun x := (x.1+x.2,x.1-x.2)
  invFun x := ((2 : K)⁻¹ • (x.1+x.2),(2 : K)⁻¹ • (x.1-x.2))
  left_inv x := by
    apply Prod.ext <;> funext i <;>
      simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] <;> field_simp [h2] <;> ring
  right_inv x := by
    apply Prod.ext <;> funext i <;>
      simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] <;> field_simp [h2] <;> ring
  map_add' x y := by
    apply Prod.ext <;> funext i <;> simp <;> ring
  map_smul' a x := by
    apply Prod.ext <;> funext i <;> simp [mul_add,mul_sub]

/-- The entire full-block coefficient tiling, including its outer-center
coordinate, is an equivalence rather than a selected row family. -/
def tilingEquiv (blocks half : Nat) (h2 : (2 : K) ≠ 0) :
    (((Fin (blocks*half) → K) × (Fin (blocks*half) → K)) × (Fin (blocks+1) → K)) ≃ₗ[K]
    (((Fin (blocks*half) → K) × (Fin (blocks*half) → K)) × (Fin (blocks+1) → K)) :=
  LinearEquiv.prodCongr (pairEquiv _ h2) (centerEquiv _)

theorem tiling_dimension (blocks half p : Nat) (hp : p=2*half+1) :
    Module.finrank K (((Fin (blocks*half) → K) × (Fin (blocks*half) → K)) ×
      (Fin (blocks+1) → K)) = blocks*p+1 := by
  simp only [Module.finrank_prod,Module.finrank_pi,Fintype.card_fin]
  rw [hp]
  ring

#print axioms centerMap_injective
#print axioms tilingEquiv
end
end CatalanMeasure.GenD.Uniform.Prefix
