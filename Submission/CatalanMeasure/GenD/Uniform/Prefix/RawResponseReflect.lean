module
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset

/-- Negative coefficient indices are zero, never truncated to the constant term. -/
def intrinsicCoeff {R : Type*} [Semiring R] (Q : R[X]) (i : ℤ) : R :=
  if 0≤i then Q.coeff i.toNat else 0

 theorem intrinsicCoeff_nat {R : Type*} [Semiring R] (Q : R[X]) (i : ℕ) :
    intrinsicCoeff Q i=Q.coeff i := by simp [intrinsicCoeff]

 theorem reflect_coeff_intrinsic {R : Type*} [Semiring R] (Q : R[X]) (D i : ℕ)
    (hQ : Q.natDegree ≤ D) :
    Q.coeff i=intrinsicCoeff (reflect D Q) ((D:ℤ)-i) := by
  by_cases hi : i≤D
  · rw [intrinsicCoeff,if_pos (by omega)]
    have hn : ((D:ℤ)-i).toNat=D-i := by omega
    rw [hn,coeff_reflect,revAt_le (by omega : D-i≤D)]
    congr 1
    omega
  · rw [intrinsicCoeff,if_neg (by omega),coeff_eq_zero_of_natDegree_lt (by omega)]

 theorem reflect_power {R : Type*} [CommRing R] (Q : R[X]) (D k : ℕ)
    (hQ : Q.natDegree ≤ D) : reflect (D*k) (Q^k)=(reflect D Q)^k := by
  induction k with
  | zero => simp [reflect_one]
  | succ k ih =>
    have hpow : (Q^k).natDegree ≤ D*k := by
      exact natDegree_pow_le.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left k hQ)
    rw [pow_succ,show D*(k+1)=D*k+D by ring,reflect_mul _ _ hpow hQ,ih,pow_succ]

 theorem reflect_one_sub_X_pow {R : Type*} [CommRing R] (h : ℕ) :
    reflect h ((1-X : R[X])^h)=(X-1)^h := by
  have hs : reflect 1 (1-X : R[X])=X-1 := by
    rw [reflect_sub,reflect_one,reflect_one_X,pow_one]
  have hr := reflect_power (1-X : R[X]) 1 h (by compute_degree)
  rw [one_mul] at hr
  exact hr.trans (congrArg (fun A : R[X] => A^h) hs)

 theorem reflect_one_sub_X_sq_pow {R : Type*} [CommRing R] (h : ℕ) :
    reflect (2*h) ((1-X^2 : R[X])^h)=(X^2-1)^h := by
  have hs : reflect 2 (1-X^2 : R[X])=X^2-1 := by
    rw [reflect_sub,reflect_one,reflect_monomial,revAt_le (by omega : 2≤2)]
    simp
  exact (reflect_power (1-X^2 : R[X]) 2 h (by compute_degree)).trans
    (congrArg (fun A : R[X] => A^h) hs)

 theorem reflect_combination {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (Q : ι→R[X]) (c : ι→R) (D : ℕ) :
    reflect D (∑ i ∈ s,C (c i)*Q i)=∑ i ∈ s,C (c i)*reflect D (Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reflect_zero]
  | @insert a s ha ih => simp only [sum_insert ha,reflect_add,reflect_C_mul,ih]

end CatalanMeasure.GenD.Uniform.Prefix


