module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.LowFilter
public import Mathlib.Algebra.Polynomial.Taylor
@[expose] public section
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

/-- The Newton interpolant in the actual physical index, with b translated back. -/
noncomputable def physicalNewtonPolynomial (f : ℕ → ZMod p) (b r : ℕ) : (ZMod p)[X] :=
  taylor (-(b:ZMod p)) (newtonPolynomial f b r)

theorem degree_physicalNewtonPolynomial_lt (f : ℕ → ZMod p) (b r : ℕ) :
    (physicalNewtonPolynomial f b r).degree < r := by
  simpa only [physicalNewtonPolynomial,degree_taylor] using degree_newtonPolynomial_lt f b r

theorem eval_physicalNewtonPolynomial (f : ℕ → ZMod p) (b n r i : ℕ) (hr : r < p)
    (hf : ∀ j < n,(lowDiff^r) f (b+j) = 0) (hi : i < n+r) :
    (physicalNewtonPolynomial f b r).eval ((b+i:ℕ):ZMod p) = f (b+i) := by
  unfold physicalNewtonPolynomial
  rw [taylor_apply,eval_comp]
  simp only [eval_add,eval_X,eval_C,Nat.cast_add]
  have he : (b:ZMod p)+(i:ZMod p)+ -(b:ZMod p) = (i:ZMod p) := by ring
  rw [he]
  exact eval_newtonPolynomial f b n r i hr hf hi

/-- A polynomial of degree below r is determined by the first r physical
indices. Only r<p is required; the active interval may be arbitrarily long. -/
theorem physical_polynomial_unique (b n r : ℕ) (hr : r < p) (f : ℕ → ZMod p)
    (B C : (ZMod p)[X]) (hB : B.degree < r) (hC : C.degree < r)
    (hBe : ∀ i < n+r,B.eval ((b+i:ℕ):ZMod p) = f (b+i))
    (hCe : ∀ i < n+r,C.eval ((b+i:ℕ):ZMod p) = f (b+i)) : B = C := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (univ : Finset (Fin r))
    (v := fun i : Fin r => ((b+i.val:ℕ):ZMod p))
  · intro i _ j _ he
    have hc : (i.val:ZMod p) = (j.val:ZMod p) := by
      apply add_left_cancel (a := (b:ZMod p))
      simpa only [Nat.cast_add] using he
    apply Fin.ext
    have hv := congrArg ZMod.val hc
    simpa only [ZMod.val_cast_of_lt (i.isLt.trans hr),ZMod.val_cast_of_lt (j.isLt.trans hr)] using hv
  · simpa using hB
  · simpa using hC
  · intro i _
    rw [hBe i.val (by have := i.isLt;omega),hCe i.val (by have := i.isLt;omega)]

/-- The actual sequence shift agrees with polynomial translation, not just with
an abstract quotient operator. -/
theorem lowDiff_polynomial_eval (B : (ZMod p)[X]) (r b : ℕ) :
    (lowDiff^r) (fun n : ℕ => B.eval (n:ZMod p)) b =
      (fwdDiff (1:ZMod p))^[r] B.eval (b:ZMod p) := by
  rw [filter_binomial_action]
  symm
  simpa only [nsmul_eq_mul,mul_one,zsmul_eq_mul,Int.cast_mul,Int.cast_pow,
    Int.cast_neg,Int.cast_one,Int.cast_natCast,Nat.cast_add] using
    fwdDiff_iter_eq_sum_shift (h := (1:ZMod p)) B.eval r (b:ZMod p)

theorem lowDiff_polynomial_zero (B : (ZMod p)[X]) (r b : ℕ) (hB : B.degree < r) :
    (lowDiff^r) (fun n : ℕ => B.eval (n:ZMod p)) b = 0 := by
  by_cases hzero : B = 0
  · subst B
    rw [filter_binomial_action]
    simp
  rw [lowDiff_polynomial_eval]
  have hd : B.natDegree < r := (natDegree_lt_iff_degree_lt hzero).mpr hB
  exact congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hd) (b:ZMod p)

/-- Filter equations only inspect their actual r+1 points inside the interval. -/
theorem filter_congr_active (f g : ℕ → ZMod p) (b n r j : ℕ) (hj : j < n)
    (he : ∀ i < n+r,f (b+i) = g (b+i)) :
    (lowDiff^r) f (b+j) = (lowDiff^r) g (b+j) := by
  rw [filter_binomial_action,filter_binomial_action]
  apply Finset.sum_congr rfl
  intro k hk
  have hkr := mem_range.mp hk
  have hval := he (j+k) (by omega)
  simpa only [Nat.add_assoc] using congrArg (fun v : ZMod p => (-1:ZMod p)^(r-k)*(r.choose k:ZMod p)*v) hval

/-- Exact finite-interval low-filter kernel. The coordinates are unique ordinary
polynomials of degree below r, and r=0 correctly introduces only the zero polynomial. -/
theorem low_filter_iff_unique_polynomial (f : ℕ → ZMod p) (b n r : ℕ) (hr : r < p) :
    (∀ j < n,(lowDiff^r) f (b+j) = 0) ↔
      ∃! B : (ZMod p)[X],B.degree < r ∧ ∀ i < n+r,B.eval ((b+i:ℕ):ZMod p) = f (b+i) := by
  constructor
  · intro hf
    refine ⟨physicalNewtonPolynomial f b r,⟨degree_physicalNewtonPolynomial_lt f b r,?_⟩,?_⟩
    · exact fun i hi => eval_physicalNewtonPolynomial f b n r i hr hf hi
    · intro B hB
      exact physical_polynomial_unique b n r hr f B (physicalNewtonPolynomial f b r)
        hB.1 (degree_physicalNewtonPolynomial_lt f b r) hB.2
        (fun i hi => eval_physicalNewtonPolynomial f b n r i hr hf hi)
  · rintro ⟨B,⟨hB,hBe⟩,_⟩ j hj
    rw [filter_congr_active f (fun i => B.eval (i:ZMod p)) b n r j hj
      (fun i hi => (hBe i hi).symm)]
    exact lowDiff_polynomial_zero B r (b+j) hB

#print axioms low_filter_iff_unique_polynomial
end CatalanMeasure.GenD.Uniform.Prefix

