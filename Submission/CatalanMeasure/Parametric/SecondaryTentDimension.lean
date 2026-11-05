module
public import Submission.CatalanMeasure.Parametric.KernelEmbeddingRank
@[expose] public section

namespace CatalanMeasure.Parametric
open Matrix Module
open scoped BigOperators
noncomputable section

/-- The simultaneous linear conditions in the secondary tent proof.  Their
targets record upper bounds for the number of equations, without asserting
that any of the equations are independent. -/
def secondaryTentConstraintMap {K V C : Type*} [Field K]
    [AddCommGroup V] [Module K V] (cost : C → ℕ)
    (B : ∀ i, V →ₗ[K] (Fin (cost i) → K)) :
    V →ₗ[K] (∀ i, Fin (cost i) → K) := LinearMap.pi B

theorem secondaryTentConstraintMap_eq_zero_iff {K V C : Type*} [Field K]
    [AddCommGroup V] [Module K V] (cost : C → ℕ)
    (B : ∀ i, V →ₗ[K] (Fin (cost i) → K)) (v : V) :
    secondaryTentConstraintMap cost B v = 0 ↔ ∀ i, B i v = 0 := by
  simp only [secondaryTentConstraintMap, LinearMap.pi_apply, funext_iff, Pi.zero_apply]

/-- Exact parameter-count inequality for an arbitrary finite family of
linear conditions, including redundant and zero conditions. -/
theorem secondaryTent_constraints_finrank {K V C : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype C]
    (cost : C → ℕ) (B : ∀ i, V →ₗ[K] (Fin (cost i) → K)) :
    finrank K V - ∑ i, cost i ≤
      finrank K (LinearMap.ker (secondaryTentConstraintMap cost B)) := by
  have h := (secondaryTentConstraintMap cost B).finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range (secondaryTentConstraintMap cost B))
  have ht : finrank K (∀ i, Fin (cost i) → K) = ∑ i, cost i := by
    simp [Module.finrank_pi_fintype]
  rw [ht] at hr
  omega

/-- It suffices to inject the constrained parameters into the left kernel.
No injectivity of the raw response or projection onto polynomial responses
is required. -/
theorem secondaryTent_rank_of_constraints {K V C : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype C]
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (cost : C → ℕ) (B : ∀ i, V →ₗ[K] (Fin (cost i) → K))
    (J : LinearMap.ker (secondaryTentConstraintMap cost B) →ₗ[K] (Fin n → K))
    (hJ : Function.Injective J)
    (hker : ∀ v, M.transpose.mulVecLin (J v) = 0) :
    M.rank + (finrank K V - ∑ i, cost i) ≤ n := by
  let W := LinearMap.ker M.transpose.mulVecLin
  let f : LinearMap.ker (secondaryTentConstraintMap cost B) →ₗ[K] W :=
    J.codRestrict W hker
  have hf : Function.Injective f := by
    intro a b hab
    apply hJ
    exact congrArg (fun w : W => w.val) hab
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  have hc := secondaryTent_constraints_finrank cost B
  have hm := M.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hr : finrank K (LinearMap.range M.transpose.mulVecLin) = M.rank :=
    Matrix.rank_transpose M
  rw [hr, Module.finrank_pi, Fintype.card_fin] at hm
  change finrank K (LinearMap.ker (secondaryTentConstraintMap cost B)) ≤
    finrank K (LinearMap.ker M.transpose.mulVecLin) at hd
  omega

/-- Explicit coefficient packets: the polynomial response, two kernel
inputs, the unavailable initial macroblock, and the boundary input.
The negative side uses boundary dimension zero. -/
abbrev SecondaryTentParameters (K : Type*) (N g boundary : ℕ) :=
  (Fin N → K) × (Fin g → K) × (Fin g → K) ×
    (Fin (3 * N) → K) × (Fin boundary → K)

theorem secondaryTent_parameters_finrank (K : Type*) [Field K] (N g boundary : ℕ) :
    finrank K (SecondaryTentParameters K N g boundary) = N + 2 * g + 3 * N + boundary := by
  simp [SecondaryTentParameters, Module.finrank_prod]
  omega

def secondaryTentPositiveCosts (N p half : ℕ) : Fin 4 → ℕ :=
  ![3 * N, N, half, 8 * N - p + 1]

def secondaryTentNegativeCosts (N p half g d : ℕ) : Fin 6 → ℕ :=
  ![g, N, half, 8 * N - p + 1, 4 * d, 4 * d]

theorem secondaryTent_positive_count {N p half delta g : ℕ}
    (hp : p = 6 * N + delta) (hodd : p = 2 * half + 1)
    (hg : g + 4 * p = 27 * N) (hcap : p ≤ 8 * N) :
    (N + 2 * g + 3 * N + 4 * delta) -
        ∑ i, secondaryTentPositiveCosts N p half i =
      N - (7 * delta + 1) / 2 := by
  simp only [secondaryTentPositiveCosts, Fin.sum_univ_succ, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  omega

theorem secondaryTent_negative_count {N p half d g : ℕ}
    (hp : p + d = 6 * N) (hodd : p = 2 * half + 1)
    (hg : g + 4 * p = 27 * N) (hcap : p ≤ 8 * N) :
    (N + 2 * g + 3 * N + 0) -
        ∑ i, secondaryTentNegativeCosts N p half g d i =
      N - (9 * d + 1) / 2 := by
  simp only [secondaryTentNegativeCosts, Fin.sum_univ_succ, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  omega

/-- Positive-side rank conclusion, with the actual source reconstruction
and flag maps left as explicit mathematical hypotheses. -/
theorem secondaryTent_positive_rank {K : Type*} [Field K]
    {N p half delta g : ℕ} (M : Matrix (Fin (20 * N)) (Fin (20 * N)) K)
    (hp : p = 6 * N + delta) (hodd : p = 2 * half + 1)
    (hg : g + 4 * p = 27 * N) (hcap : p ≤ 8 * N)
    (B : ∀ i, SecondaryTentParameters K N g (4 * delta) →ₗ[K]
      (Fin (secondaryTentPositiveCosts N p half i) → K))
    (J : LinearMap.ker (secondaryTentConstraintMap
      (secondaryTentPositiveCosts N p half) B) →ₗ[K] (Fin (20 * N) → K))
    (hJ : Function.Injective J)
    (hker : ∀ v, M.transpose.mulVecLin (J v) = 0) :
    M.rank + (N - (7 * delta + 1) / 2) ≤ 20 * N := by
  have h := secondaryTent_rank_of_constraints M _ B J hJ hker
  rw [secondaryTent_parameters_finrank,
    secondaryTent_positive_count hp hodd hg hcap] at h
  exact h

/-- Negative-side rank conclusion, including both sets of `4d` boundary
conditions and the zero-dimensional fifth input. -/
theorem secondaryTent_negative_rank {K : Type*} [Field K]
    {N p half d g : ℕ} (M : Matrix (Fin (20 * N)) (Fin (20 * N)) K)
    (hp : p + d = 6 * N) (hodd : p = 2 * half + 1)
    (hg : g + 4 * p = 27 * N) (hcap : p ≤ 8 * N)
    (B : ∀ i, SecondaryTentParameters K N g 0 →ₗ[K]
      (Fin (secondaryTentNegativeCosts N p half g d i) → K))
    (J : LinearMap.ker (secondaryTentConstraintMap
      (secondaryTentNegativeCosts N p half g d) B) →ₗ[K] (Fin (20 * N) → K))
    (hJ : Function.Injective J)
    (hker : ∀ v, M.transpose.mulVecLin (J v) = 0) :
    M.rank + (N - (9 * d + 1) / 2) ≤ 20 * N := by
  have h := secondaryTent_rank_of_constraints M _ B J hJ hker
  rw [secondaryTent_parameters_finrank,
    secondaryTent_negative_count hp hodd hg hcap] at h
  exact h

end
end CatalanMeasure.Parametric
