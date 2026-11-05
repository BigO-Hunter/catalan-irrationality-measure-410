module
public import Submission.CatalanMeasure.GenD.Uniform.W.Profile
public import Mathlib.Algebra.Polynomial.Taylor
@[expose] public section
set_option Elab.async false

/-!
# Order conditions are jet groups: the cumulative-flag charts, generically

At one point `a` (any of `-1, 0, 1, ∞`), a *prefix system* is a list of rows `ρ_i` (covectors on the
profile coordinates) with orders `t_i`: the condition is `ord_a (ρ_i ∘ x) ≥ t_i`, i.e. the Taylor
coefficients `k < t_i` of `ρ_i ∘ x` vanish.  Grouping by `k`, the conditions at coefficient `k` are
`B_k (jet_k x) = 0` where `B_k = stackMap ρ t k` is the stack of the rows with `t_i > k` (the
*order-difference chart*: it changes only at the distinct orders).  Hence the whole system is a
`constraintMap` with groups `Fin T`, width one, and Theorem W-prof charges `Σ_k rank (B_k | V)`
(`flag_rank_le`).  Nothing here is design- or point-specific.

* `stackMap`           : the chart `B_k` (rows with `t_i > k`, other rows masked to zero);
* `flag_iff`           : the order conditions are exactly `B_k (jet_k x) = 0` for `k < T`;
* `flagJets`, `flag_rank_le` : the groups and the rank bound;
* `taylorJet`, `taylorJet_coeff` : the Taylor jet of a coordinate polynomial at `a`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts3
open Finset Module Polynomial CatalanCore.Uniform.Content CatalanMeasure.GenD.Uniform.W
noncomputable section
variable {F : Type*} [Field F] {d : ℕ}

/-- The chart at coefficient `k`: rows with order `> k` kept, others masked. -/
def stackMap {r : ℕ} (ρ : Fin r → (Fin d → F) →ₗ[F] F) (t : Fin r → ℕ) (k : ℕ) :
    (Fin d → F) →ₗ[F] (Fin r → F) :=
  LinearMap.pi fun i => if k < t i then ρ i else 0

theorem stackMap_apply {r : ℕ} (ρ : Fin r → (Fin d → F) →ₗ[F] F) (t : Fin r → ℕ) (k : ℕ)
    (v : Fin d → F) (i : Fin r) :
    stackMap ρ t k v i = if k < t i then ρ i v else 0 := by
  unfold stackMap
  by_cases h : k < t i <;> simp [h]

theorem stackMap_eq_zero_iff {r : ℕ} (ρ : Fin r → (Fin d → F) →ₗ[F] F) (t : Fin r → ℕ) (k : ℕ)
    (v : Fin d → F) : stackMap ρ t k v = 0 ↔ ∀ i, k < t i → ρ i v = 0 := by
  constructor
  · intro h i hi
    have := congrFun h i
    rwa [stackMap_apply, if_pos hi] at this
  · intro h
    funext i
    rw [stackMap_apply]
    by_cases hi : k < t i
    · rw [if_pos hi]; exact h i hi
    · rw [if_neg hi]; rfl

/-- The jets of the flag groups: group `k < T`, one jet, the `k`-th coefficient jet `jetc k`. -/
def flagJets {m : ℕ} (T : ℕ) (jetc : ℕ → (Fin m → (Fin d → F)) →ₗ[F] (Fin d → F)) :
    ∀ k : Fin T, Fin 1 → (Fin m → (Fin d → F)) →ₗ[F] (Fin d → F) := fun k _ => jetc k

/-- **The order conditions are the flag groups**: `ord(ρ_i ∘ x) ≥ t_i` for all `i`
(coefficients `k < t_i` of `ρ_i ∘ x` vanish) iff `B_k (jet_k x) = 0` for every `k < T`,
`T` any bound `≥ max t_i`. -/
theorem flag_iff {m r : ℕ} (ρ : Fin r → (Fin d → F) →ₗ[F] F) (t : Fin r → ℕ) (T : ℕ)
    (hT : ∀ i, t i ≤ T) (jetc : ℕ → (Fin m → (Fin d → F)) →ₗ[F] (Fin d → F))
    (x : Fin m → (Fin d → F)) :
    (∀ i k, k < t i → ρ i (jetc k x) = 0) ↔ ∀ k : Fin T, stackMap ρ t k (jetc k x) = 0 := by
  constructor
  · intro h k
    exact (stackMap_eq_zero_iff ρ t k _).mpr fun i hi => h i k hi
  · intro h i k hk
    exact (stackMap_eq_zero_iff ρ t k _).mp (h ⟨k, lt_of_lt_of_le hk (hT i)⟩) i hk

/-- **Rank of a prefix system**: the stacked jet map has rank at most `Σ_{k<T} rank (B_k | V)`,
for `V` any subspace of profiles realised as the ambient `Fin d → F` (`d = dim V`). -/
theorem flag_rank_le {m r : ℕ} (ρ : Fin r → (Fin d → F) →ₗ[F] F) (t : Fin r → ℕ) (T : ℕ)
    (jetc : ℕ → (Fin m → (Fin d → F)) →ₗ[F] (Fin d → F)) :
    finrank F (LinearMap.range (constraintMap (fun _ : Fin T => 1)
      (fun k : Fin T => stackMap ρ t k) (flagJets T jetc))) ≤
      ∑ k : Fin T, finrank F (LinearMap.range (stackMap ρ t k)) := by
  have := rank_constraintMap_le (m := m) (fun _ : Fin T => 1)
    (fun k : Fin T => stackMap ρ t k) (flagJets T jetc)
  simpa using this

/-- The kernel of the flag groups is the set of atoms satisfying every order condition. -/
theorem flag_ker_iff {m r : ℕ} (ρ : Fin r → (Fin d → F) →ₗ[F] F) (t : Fin r → ℕ) (T : ℕ)
    (hT : ∀ i, t i ≤ T) (jetc : ℕ → (Fin m → (Fin d → F)) →ₗ[F] (Fin d → F))
    (x : Fin m → (Fin d → F)) :
    constraintMap (fun _ : Fin T => 1) (fun k : Fin T => stackMap ρ t k) (flagJets T jetc) x = 0 ↔
      ∀ i k, k < t i → ρ i (jetc k x) = 0 := by
  rw [constraintMap_eq_zero_iff, flag_iff ρ t T hT jetc x]
  constructor
  · intro h k; simpa [flagJets] using h k 0
  · intro h k j; simpa [flagJets] using h k

/-! ### Taylor jets at a finite point -/

/-- The `k`-th Taylor jet at `a` of the coordinate polynomial `Σ_i x_i X^i`:
`Σ_i C(i,k) a^(i-k) x_i`. -/
def taylorJet {m : ℕ} (a : F) (k : ℕ) : (Fin m → (Fin d → F)) →ₗ[F] (Fin d → F) :=
  ∑ i : Fin m, (((i : ℕ).choose k : F) * a ^ ((i : ℕ) - k)) •
    (LinearMap.proj i : (Fin m → (Fin d → F)) →ₗ[F] (Fin d → F))

/-- Coordinatewise, the Taylor jet is the `k`-th coefficient of `f(X + a)`. -/
theorem taylorJet_coeff {m : ℕ} (a : F) (k : ℕ) (x : Fin m → (Fin d → F)) (c : Fin d) :
    taylorJet a k x c =
      (taylor a (∑ i : Fin m, Polynomial.C (x i c) * Polynomial.X ^ (i : ℕ))).coeff k := by
  rw [taylor_coeff, map_sum, Polynomial.eval_finsetSum]
  simp only [taylorJet, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.C_mul_X_pow_eq_monomial, hasseDeriv_monomial, Polynomial.eval_monomial]
  first | ring | (simp only [nsmul_eq_mul]; ring) | (simp; ring)

end
end CatalanMeasure.GenD.Uniform.W.Charts3
