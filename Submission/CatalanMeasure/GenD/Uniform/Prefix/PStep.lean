module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Pi
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial
variable {R : Type*} [CommRing R] {p : Nat} [Fact p.Prime] [CharP R p]

/-- The all-quotient filter split. There is no bound on q/p, and no factorial
inversion: the proof uses only Frobenius and the exact quotient/remainder law. -/
theorem filter_polynomial_split (q : Nat) :
    (X - 1 : Polynomial R) ^ q =
      (X - 1) ^ (q % p) * (X ^ p - 1) ^ (q / p) := by
  simpa only [one_pow] using
    (sub_pow_eq_mul_pow_sub_pow_div_char (p := p) (X : Polynomial R) 1 q)

/-- The actual consecutive forward shift on raw response sequences. -/
def shift : Module.End R (Nat → R) where
  toFun f n := f (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem shift_apply (f : Nat → R) (n : Nat) : shift f n = f (n + 1) := rfl

@[simp] theorem shift_pow_apply (k : Nat) (f : Nat → R) (n : Nat) :
    (shift ^ k) f n = f (n + k) := by
  induction k generalizing f n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    simp only [shift_apply, Nat.add_assoc]

/-- Applying the polynomial identity to the actual shift preserves the physical
response space; no coordinates are introduced when removing a large quotient. -/
theorem filter_operator_split (q : Nat) :
    (shift - 1 : Module.End R (Nat → R)) ^ q =
      (shift - 1) ^ (q % p) * (shift ^ p - 1) ^ (q / p) := by
  have h := congrArg (fun F : Polynomial R => aeval (shift : Module.End R (Nat → R)) F)
    (filter_polynomial_split (R := R) (p := p) q)
  simpa using h

/-- Every p-step-shifted raw column used on the active interval stays in the
original observed interval. The original q and physical row domain are retained. -/
theorem active_column_bound {b n q k v : Nat} (hk : k < n + q % p)
    (hv : v ≤ q / p) : b + k + v * p < b + n + q := by
  have hvp := Nat.mul_le_mul_right p hv
  have hq := Nat.mod_add_div q p
  have heq : (q / p) * p = p * (q / p) := Nat.mul_comm _ _
  omega

#print axioms filter_operator_split
end CatalanMeasure.GenD.Uniform.Prefix