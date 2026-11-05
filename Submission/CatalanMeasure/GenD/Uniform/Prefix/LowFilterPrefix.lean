module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.LowFilterPolynomial
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Tactic.LinearCombination
@[expose] public section
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

/-- The actual reversed residue coefficient vector G_B. Field subtraction is
exactly reduction of eta-e modulo p. -/
noncomputable def residuePolynomial (eta : ZMod p) (B : (ZMod p)[X]) : (ZMod p)[X] :=
  ∑ e ∈ range p,monomial e (B.eval (eta-(e:ZMod p)))

@[simp] theorem coeff_residuePolynomial (eta : ZMod p) (B : (ZMod p)[X]) (e : ℕ) :
    (residuePolynomial eta B).coeff e = if e < p then B.eval (eta-(e:ZMod p)) else 0 := by
  classical
  simp [residuePolynomial,finsetSum_coeff,coeff_monomial]

@[simp] theorem residuePolynomial_zero (eta : ZMod p) : residuePolynomial eta 0 = 0 := by
  simp [residuePolynomial]

theorem degree_residuePolynomial_lt (eta : ZMod p) (B : (ZMod p)[X]) :
    (residuePolynomial eta B).degree < p := by
  apply Polynomial.mem_degreeLT.mp
  apply Submodule.sum_mem
  intro e he
  apply Polynomial.mem_degreeLT.mpr
  exact (degree_monomial_le _ _).trans_lt (WithBot.coe_lt_coe.mpr (mem_range.mp he))

noncomputable def polynomialDifference (B : (ZMod p)[X]) : (ZMod p)[X] := taylor 1 B-B
@[simp] theorem eval_polynomialDifference (B : (ZMod p)[X]) (a : ZMod p) :
    (polynomialDifference B).eval a = B.eval (a+1)-B.eval a := by
  simp [polynomialDifference,taylor_apply]

/-- One exact cyclic difference of G_B. The sole wrap term is X^p-1. -/
theorem residue_difference_identity (eta : ZMod p) (B : (ZMod p)[X]) :
    (X-1)*residuePolynomial eta B = residuePolynomial eta (polynomialDifference B) +
      C (B.eval (eta+1))*(X^p-1) := by
  ext e
  cases e with
  | zero =>
    have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have hpp : 0 < p := (Fact.out : p.Prime).pos
    simp [sub_mul,coeff_C_mul,coeff_one,hp0,Ne.symm hp0,hpp] <;> ring
  | succ e =>
    rw [sub_mul,one_mul,coeff_sub,coeff_X_mul,coeff_add,coeff_C_mul]
    by_cases hs : e+1 < p
    · have he : e < p := by omega
      have hne : p ≠ e+1 := by omega
      have harg : eta-((e+1:ℕ):ZMod p)+1 = eta-(e:ZMod p) := by push_cast;ring
      simp only [Nat.cast_succ] at harg
      simp [coeff_residuePolynomial,hs,he,hne,Ne.symm hne,harg,coeff_one]
    · by_cases heq : e+1 = p
      · have he : e < p := by omega
        have harg : eta-(e:ZMod p) = eta+1 := by
          have hh := congrArg (fun n : ℕ => (n:ZMod p)) heq
          simp only [Nat.cast_succ,ZMod.natCast_self] at hh
          linear_combination -hh
        simp [coeff_residuePolynomial,hs,he,heq,harg,coeff_one,(Fact.out : p.Prime).ne_zero]
      · have he : ¬ e < p := by omega
        have hne : p ≠ e+1 := Ne.symm heq
        simp [coeff_residuePolynomial,hs,he,hne,heq,coeff_one]

/-- Translation drops polynomial degree, even in positive characteristic. -/
theorem degree_polynomialDifference_lt (B : (ZMod p)[X]) (r : ℕ) (hB : B.degree < (r+1:ℕ)) :
    (polynomialDifference B).degree < r := by
  by_cases hz : B = 0
  · simp [hz,polynomialDifference]
  have ht : taylor (1:ZMod p) B ≠ 0 := (taylor_eq_zero (1:ZMod p) B).not.mpr hz
  have he := degree_sub_lt_left (p := taylor (1:ZMod p) B) (q := B)
    (degree_taylor B 1) ht (leadingCoeff_taylor 1 B)
  have hd : B.natDegree ≤ r := by
    have hnat := (natDegree_lt_iff_degree_lt hz).mpr hB
    omega
  apply lt_of_lt_of_le (by simpa only [polynomialDifference,degree_taylor] using he)
  exact degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hd)

/-- Actual G_B divisibility. Induction uses exact cyclic differences and
(X-1)^p=X^p-1, avoiding enumeration of Hasse moments. -/
theorem residuePolynomial_prefix_dvd (eta : ZMod p) (r : ℕ) (hr : r ≤ p)
    (B : (ZMod p)[X]) (hB : B.degree < r) : (X-1)^(p-r) ∣ residuePolynomial eta B := by
  induction r generalizing B with
  | zero =>
    have hz : B = 0 := by
      by_contra hzero
      have hnat := (natDegree_lt_iff_degree_lt hzero).mpr hB
      omega
    simp [hz]
  | succ r ih =>
    have hd := degree_polynomialDifference_lt B r hB
    have hdelta := ih (by omega) (polynomialDifference B) hd
    have hp : (X-1 : (ZMod p)[X])^p = X^p-1 := by
      simpa [Nat.div_self (Fact.out : p.Prime).pos] using filter_polynomial_split (R := ZMod p) (p := p) p
    have hb : (X-1 : (ZMod p)[X])^(p-r) ∣ C (B.eval (eta+1))*(X^p-1) := by
      rw [← hp]
      exact (pow_dvd_pow (X-1 : (ZMod p)[X]) (Nat.sub_le p r)).mul_left _
    have hdiv : (X-1 : (ZMod p)[X])^(p-r) ∣ (X-1)*residuePolynomial eta B := by
      rw [residue_difference_identity]
      exact hdelta.add hb
    obtain ⟨Q,hQ⟩ := hdiv
    refine ⟨Q,?_⟩
    apply mul_left_cancel₀ (X_sub_C_ne_zero (1:ZMod p))
    calc
      (X-1)*residuePolynomial eta B = (X-1)^(p-r)*Q := hQ
      _ = (X-1)*((X-1)^(p-(r+1))*Q) := by
        rw [show p-r = (p-(r+1))+1 by omega,pow_succ]
        ring

/-- The prefix quotient has exactly the requested degree window. -/
theorem residuePolynomial_prefix_lift (eta : ZMod p) (r : ℕ) (hr : r ≤ p)
    (B : (ZMod p)[X]) (hB : B.degree < r) :
    ∃ Q : (ZMod p)[X],Q.degree < r ∧ residuePolynomial eta B = (X-1)^(p-r)*Q := by
  obtain ⟨Q,hQ⟩ := residuePolynomial_prefix_dvd eta r hr B hB
  refine ⟨Q,?_,hQ⟩
  by_cases hz : Q = 0
  · simp [hz]
  have hpow : (X-1 : (ZMod p)[X])^(p-r) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero 1)
  have hG : residuePolynomial eta B ≠ 0 := by rw [hQ];exact mul_ne_zero hpow hz
  have hdeg := (natDegree_lt_iff_degree_lt hG).mpr (degree_residuePolynomial_lt eta B)
  have hzdeg : (X-1 : (ZMod p)[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1:ZMod p)
  rw [hQ,natDegree_mul hpow hz,natDegree_pow,hzdeg,mul_one] at hdeg
  apply (natDegree_lt_iff_degree_lt hz).mp
  omega
end CatalanMeasure.GenD.Uniform.Prefix


