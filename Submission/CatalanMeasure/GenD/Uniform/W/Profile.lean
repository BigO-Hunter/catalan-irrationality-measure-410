module
public import Submission.CatalanMeasure.GenD.Uniform.W.Jets
public import Submission.CatalanCore.Uniform.Content.RankLayer
@[expose] public section
set_option Elab.async false

/-!
# Theorem W, partial-rank (constant-subspace) form

Atoms `Π ⊗ V` are represented as `Fin m → V`: `m` polynomial coordinates (a basis of the full
polynomial coordinate space `Π`) with values in a constant profile subspace `V`.  A jet group
`c` consists of `width c` jets on `Π` (`jet c k`, linear `Fin m → V → V`; for scalar jets use
`scalarJet`) followed by one constant covector map `B c` on profiles.  The stacked jet map is
`constraintMap` of `CatalanCore.Uniform.Content.RankLayer`.

`w_prof` : `ν ≥ m·dim V - Σ_c width c · rank(B c) - rank χ`,

with `χ` the filter cost of `w_master`; `w_prof_cols` is the kill-set version (cost `n - |K|`)
and `w_prof_all` the version with every column killed (cost `0`).
-/

namespace CatalanMeasure.GenD.Uniform.W
open Module CatalanCore.Uniform.Content
noncomputable section
variable {K : Type*} [Field K] {n : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {C : Type*} [Fintype C] {Wc : C → Type*} [∀ c, AddCommGroup (Wc c)]
  [∀ c, Module K (Wc c)]

/-- A scalar jet on `Π` (a covector on the `m` polynomial coordinates), applied to
profile-valued coordinates. -/
def scalarJet {m : ℕ} (lam : Fin m → K) : (Fin m → V) →ₗ[K] V :=
  ∑ i, lam i • LinearMap.proj i

theorem scalarJet_apply {m : ℕ} (lam : Fin m → K) (x : Fin m → V) :
    scalarJet lam x = ∑ i, lam i • x i := by
  simp [scalarJet]

/-- Atom rows of `Π ⊗ V`: `x ↦ Σ_i row_i (x_i)`. -/
def tensorAtoms {m : ℕ} (row : Fin m → V →ₗ[K] (Fin n → K)) : (Fin m → V) →ₗ[K] (Fin n → K) :=
  ∑ i, (row i).comp (LinearMap.proj i)

theorem tensorAtoms_apply {m : ℕ} (row : Fin m → V →ₗ[K] (Fin n → K)) (x : Fin m → V) :
    tensorAtoms row x = ∑ i, row i (x i) := by
  simp [tensorAtoms]

/-- Rank of the stacked partial-rank jet map. -/
theorem rank_constraintMap_le {m : ℕ} (width : C → ℕ) (B : ∀ c, V →ₗ[K] Wc c)
    (jet : ∀ c, Fin (width c) → (Fin m → V) →ₗ[K] V) :
    finrank K (LinearMap.range (constraintMap width B jet)) ≤
      ∑ c, width c * finrank K (LinearMap.range (B c)) := by
  have hr := Submodule.finrank_le (LinearMap.range (constraintMap width B jet))
  have ht : finrank K (∀ c, Fin (width c) → LinearMap.range (B c)) =
      ∑ c, width c * finrank K (LinearMap.range (B c)) := by
    simp [Module.finrank_pi_fintype, Module.finrank_pi]
  rwa [ht] at hr

/-- **Theorem W-prof** (master form). -/
theorem w_prof {m : ℕ} (M : Matrix (Fin n) (Fin n) K) (width : C → ℕ) (B : ∀ c, V →ₗ[K] Wc c)
    (jet : ∀ c, Fin (width c) → (Fin m → V) →ₗ[K] V)
    (ι : (Fin m → V) →ₗ[K] (Fin n → K)) (hι : Function.Injective ι)
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (χ : LinearMap.ker (constraintMap width B jet) →ₗ[K] Q)
    (hkill : ∀ u : LinearMap.ker (constraintMap width B jet), χ u = 0 →
      M.transpose.mulVec (ι u) = 0) :
    m * finrank K V - ∑ c, width c * finrank K (LinearMap.range (B c)) -
      finrank K (LinearMap.range χ) ≤ n - M.rank := by
  have h := w_master M ι hι (constraintMap width B jet) χ hkill
  have hr := rank_constraintMap_le width B jet
  have hd : finrank K (Fin m → V) = m * finrank K V := by
    simp [Module.finrank_pi_fintype]
  rw [hd] at h
  omega

/-- **Theorem W-prof**, kill-set form: cost `n - |Kset|`. -/
theorem w_prof_cols {m : ℕ} (M : Matrix (Fin n) (Fin n) K) (width : C → ℕ)
    (B : ∀ c, V →ₗ[K] Wc c) (jet : ∀ c, Fin (width c) → (Fin m → V) →ₗ[K] V)
    (ι : (Fin m → V) →ₗ[K] (Fin n → K)) (hι : Function.Injective ι) (Kset : Finset (Fin n))
    (hkill : ∀ x, (∀ c k, B c (jet c k x) = 0) → ∀ k ∈ Kset, M.transpose.mulVec (ι x) k = 0) :
    m * finrank K V - ∑ c, width c * finrank K (LinearMap.range (B c)) - (n - Kset.card) ≤
      n - M.rank := by
  have h := w_core M ι hι (constraintMap width B jet) Kset (fun x hx =>
    hkill x ((constraintMap_eq_zero_iff width B jet x).mp hx))
  have hr := rank_constraintMap_le width B jet
  have hd : finrank K (Fin m → V) = m * finrank K V := by
    simp [Module.finrank_pi_fintype]
  rw [hd] at h
  omega

/-- **Theorem W-prof** with every column killed. -/
theorem w_prof_all {m : ℕ} (M : Matrix (Fin n) (Fin n) K) (width : C → ℕ)
    (B : ∀ c, V →ₗ[K] Wc c) (jet : ∀ c, Fin (width c) → (Fin m → V) →ₗ[K] V)
    (ι : (Fin m → V) →ₗ[K] (Fin n → K)) (hι : Function.Injective ι)
    (hkill : ∀ x, (∀ c k, B c (jet c k x) = 0) → M.transpose.mulVec (ι x) = 0) :
    m * finrank K V - ∑ c, width c * finrank K (LinearMap.range (B c)) ≤ n - M.rank := by
  have h := w_prof_cols M width B jet ι hι Finset.univ
    (fun x hx k _ => by rw [hkill x hx]; rfl)
  rw [Finset.card_univ, Fintype.card_fin, Nat.sub_self, Nat.sub_zero] at h
  exact h

/-- Certificate form: upper bounds `ranks c` for the restriction ranks suffice. -/
theorem w_prof_of_bounds {m : ℕ} (M : Matrix (Fin n) (Fin n) K) (width ranks : C → ℕ)
    (B : ∀ c, V →ₗ[K] Wc c) (jet : ∀ c, Fin (width c) → (Fin m → V) →ₗ[K] V)
    (hB : ∀ c, finrank K (LinearMap.range (B c)) ≤ ranks c)
    (ι : (Fin m → V) →ₗ[K] (Fin n → K)) (hι : Function.Injective ι) (Kset : Finset (Fin n))
    (hkill : ∀ x, (∀ c k, B c (jet c k x) = 0) → ∀ k ∈ Kset, M.transpose.mulVec (ι x) k = 0) :
    m * finrank K V - ∑ c, width c * ranks c - (n - Kset.card) ≤ n - M.rank := by
  have h := w_prof_cols M width B jet ι hι Kset hkill
  have hc : (∑ c, width c * finrank K (LinearMap.range (B c))) ≤ ∑ c, width c * ranks c :=
    Finset.sum_le_sum fun c _ => Nat.mul_le_mul_left _ (hB c)
  omega

/-! ### Profile subspaces -/

/-- `κ ≥ #profile coordinates - #cell equations`: the kernel of `e` cell equations on `β`
profile coordinates. -/
theorem kappa_ge {β e : ℕ} (E : (Fin β → K) →ₗ[K] (Fin e → K)) :
    β - e ≤ finrank K (LinearMap.ker E) := by
  have h := E.finrank_range_add_finrank_ker
  have hr := rank_le_width E
  rw [Module.finrank_fin_fun] at h
  omega

/-- Exact kernel dimension from the rank of the cell equations. -/
theorem kappa_eq {β e : ℕ} (E : (Fin β → K) →ₗ[K] (Fin e → K)) :
    finrank K (LinearMap.ker E) = β - finrank K (LinearMap.range E) := by
  have h := E.finrank_range_add_finrank_ker
  rw [Module.finrank_fin_fun] at h
  omega

end
end CatalanMeasure.GenD.Uniform.W
