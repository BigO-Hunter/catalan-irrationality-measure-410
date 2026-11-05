module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Polynomial.Taylor
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

/-! The lower rank layer needs only factorization of each jet condition through
its constant image. Taylor independence is unnecessary for a lower bound. The
result works over every field, including the full prime-characteristic domain. -/
namespace CatalanCore.Uniform.Content
open scoped BigOperators
open Module
noncomputable section
variable {K V C : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype C]
variable {W : C → Type*} [∀ c, AddCommGroup (W c)] [∀ c, Module K (W c)]

/-- Stack the actual conditions into their constant images, rather than into
ambient equation spaces; this charges the restriction rank, including zero. -/
def constraintMap {p : Nat} (width : C → Nat) (B : ∀ c, V →ₗ[K] W c)
    (jet : ∀ c, Fin (width c) → (Fin p → V) →ₗ[K] V) :
    (Fin p → V) →ₗ[K] (∀ c, Fin (width c) → LinearMap.range (B c)) :=
  LinearMap.pi fun c => LinearMap.pi fun k => (B c).rangeRestrict.comp (jet c k)

theorem constraintMap_eq_zero_iff {p : Nat} (width : C → Nat)
    (B : ∀ c, V →ₗ[K] W c)
    (jet : ∀ c, Fin (width c) → (Fin p → V) →ₗ[K] V) (f : Fin p → V) :
    constraintMap width B jet f = 0 ↔ ∀ c k, B c (jet c k f) = 0 := by
  simp [constraintMap, LinearMap.pi_apply, funext_iff, Subtype.ext_iff]

/-- Uniform Content lower inequality, in truncated natural-number form. Each
point/order jet may be arbitrary linear data; only its constant image is charged. -/
theorem rank_layer_lower_nat {p : Nat} (width : C → Nat)
    (B : ∀ c, V →ₗ[K] W c)
    (jet : ∀ c, Fin (width c) → (Fin p → V) →ₗ[K] V) :
    p * finrank K V - ∑ c, width c * finrank K (LinearMap.range (B c)) ≤
      finrank K (LinearMap.ker (constraintMap width B jet)) := by
  have hk := (constraintMap width B jet).finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range (constraintMap width B jet))
  have ht : finrank K (∀ c, Fin (width c) → LinearMap.range (B c)) =
      ∑ c, width c * finrank K (LinearMap.range (B c)) := by
    simp [Module.finrank_pi_fintype, Module.finrank_pi]
  have hd : finrank K (Fin p → V) = p * finrank K V := by
    simp [Module.finrank_pi_fintype]
  rw [ht] at hr
  rw [hd] at hk
  omega

/-- The signed Euler-deficit statement appearing in the paper. -/
theorem rank_layer_lower {p : Nat} (width : C → Nat)
    (B : ∀ c, V →ₗ[K] W c)
    (jet : ∀ c, Fin (width c) → (Fin p → V) →ₗ[K] V) :
    (p : Int) * (finrank K V : Int) -
      ∑ c, (width c : Int) * (finrank K (LinearMap.range (B c)) : Int) ≤
        (finrank K (LinearMap.ker (constraintMap width B jet)) : Int) := by
  have h := rank_layer_lower_nat width B jet
  have hi : ((p * finrank K V : Nat) : Int) -
      ((∑ c, width c * finrank K (LinearMap.range (B c)) : Nat) : Int) ≤
      (finrank K (LinearMap.ker (constraintMap width B jet)) : Int) := by omega
  simpa only [Nat.cast_mul, Nat.cast_sum] using hi

/-- A finite certificate can give upper image ranks instead of computing exact ranks. -/
theorem rank_layer_lower_of_bounds {p : Nat} (width ranks : C → Nat)
    (B : ∀ c, V →ₗ[K] W c)
    (jet : ∀ c, Fin (width c) → (Fin p → V) →ₗ[K] V)
    (hr : ∀ c, finrank K (LinearMap.range (B c)) ≤ ranks c) :
    p * finrank K V - ∑ c, width c * ranks c ≤
      finrank K (LinearMap.ker (constraintMap width B jet)) := by
  have hc : (∑ c, width c * finrank K (LinearMap.range (B c))) ≤
      ∑ c, width c * ranks c :=
    Finset.sum_le_sum fun c _ => Nat.mul_le_mul_left _ (hr c)
  exact (Nat.sub_le_sub_left hc _).trans (rank_layer_lower_nat width B jet)

/-- Injecting the constrained polynomial parameters into the physical kernel
transfers the lower bound. Construction of that injection is a separate source theorem. -/
theorem rank_layer_transfer {p : Nat} (width : C → Nat) (B : ∀ c, V →ₗ[K] W c)
    (jet : ∀ c, Fin (width c) → (Fin p → V) →ₗ[K] V)
    {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (J : LinearMap.ker (constraintMap width B jet) →ₗ[K] U)
    (hJ : Function.Injective J) :
    p * finrank K V - ∑ c, width c * finrank K (LinearMap.range (B c)) ≤
      finrank K U :=
  (rank_layer_lower_nat width B jet).trans (LinearMap.finrank_le_finrank_of_injective hJ)

/-- Actual finite-point Taylor coefficient, defined for vector coefficients. -/
def taylorJet {p : Nat} (a : K) (k : Nat) : (Fin p → V) →ₗ[K] V :=
  ∑ i : Fin p, (a ^ (i.val - k) * (i.val.choose k : K)) • LinearMap.proj i

/-- The common degree-(p-1) reversal used for the point at infinity. -/
def infinityJet {p : Nat} (k : Nat) : (Fin p → V) →ₗ[K] V :=
  if h : k < p then LinearMap.proj ⟨p - 1 - k, by omega⟩ else 0

/-- A single API for all finite points and infinity, without divisions or
characteristic-dependent factorial inverses. -/
def prefixJet {p : Nat} (point : Option K) (k : Nat) : (Fin p → V) →ₗ[K] V :=
  match point with
  | some a => taylorJet a k
  | none => infinityJet k

/-- Scalar polynomial represented by its coefficient vector. -/
def scalarPolynomial {p : Nat} (f : Fin p → K) : Polynomial K :=
  ∑ i : Fin p, Polynomial.monomial i.val (f i)

/-- The vector-coefficient jet agrees with Mathlib's actual scalar Taylor map. -/
theorem taylorJet_scalar {p : Nat} (a : K) (k : Nat) (f : Fin p → K) :
    taylorJet a k f = (Polynomial.taylor a (scalarPolynomial f)).coeff k := by
  simp [taylorJet, scalarPolynomial, Polynomial.taylor_monomial,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, mul_comm]

#print axioms rank_layer_lower
#print axioms taylorJet_scalar
end
end CatalanCore.Uniform.Content