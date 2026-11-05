module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Dissect
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PhysicalPairs
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PStep
public import Submission.CatalanMeasure.GenD.RankCommon
public import Submission.CatalanMeasure.Parametric.ChebyshevPrime
@[expose] public section
set_option Elab.async false

/-!
# Block decomposition of the Chebyshev rows in characteristic `p` (lane G6c, Theorem L*)

Write a signed row index as `j = k p + d` (block `k`, offset `d`), `y = X^p`, `W = (X^2-1)^((p-1)/2)`
and `h = p + dh`.  In `F_p[X]`, with `Q1 = (X-1)^dh W T_d`, `Q2 = (X-1)^dh U_{d-1}`:

* `(X-1)^h W T_{kp+d} = expand ((X-1) T_k) * Q1 + expand ((X-1)(X^2-1) U_{k-1}) * Q2`,
* `(X-1)^h U_{kp+d-1} = expand ((X-1) U_{k-1}) * Q1 + expand ((X-1) T_k) * Q2`.

Also `W T_d = X^p U_{d-1} + U_{p-d-1}` (the char-`p` identity (W)), which makes the coefficient
`[Q1]_{e0}` vanish for `|d| > p - 1 - e0 + dh`.
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar
open Polynomial Polynomial.Chebyshev CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.Parametric
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- The weight `W = (X^2-1)^((p-1)/2)`. -/
abbrev wt (p : ℕ) [Fact p.Prime] : (ZMod p)[X] := (X ^ 2 - 1) ^ ((p - 1) / 2)

/-- `Q1` of block offset `d`. -/
def qOne (p dh : ℕ) [Fact p.Prime] (d : ℤ) : (ZMod p)[X] :=
  (X - 1) ^ dh * wt p * T (ZMod p) d

/-- `Q2` of block offset `d`. -/
def qTwo (p dh : ℕ) [Fact p.Prime] (d : ℤ) : (ZMod p)[X] :=
  (X - 1) ^ dh * U (ZMod p) (d - 1)

theorem wt_sq (hp2 : p ≠ 2) :
    ((X : (ZMod p)[X]) ^ p) ^ 2 - 1 = (X ^ 2 - 1) * wt p * wt p := by
  have hodd : p = 1 + 2 * ((p - 1) / 2) := by
    have := (Fact.out : p.Prime).two_le
    have := (Fact.out : p.Prime).eq_two_or_odd
    omega
  have h := sub_pow_char (p := p) ((X : (ZMod p)[X]) ^ 2) 1
  rw [one_pow, ← pow_mul, mul_comm 2 p, pow_mul] at h
  rw [← h]
  calc ((X : (ZMod p)[X]) ^ 2 - 1) ^ p
      = ((X : (ZMod p)[X]) ^ 2 - 1) ^ (1 + 2 * ((p - 1) / 2)) :=
        congrArg (fun n => ((X : (ZMod p)[X]) ^ 2 - 1) ^ n) hodd
    _ = _ := by unfold wt; ring

theorem blockT (hp2 : p ≠ 2) (dh : ℕ) (k d : ℤ) :
    (X - 1) ^ (p + dh) * wt p * T (ZMod p) (k * p + d) =
      expand (ZMod p) p ((X - 1) * T (ZMod p) k) * qOne p dh d +
      expand (ZMod p) p ((X - 1) * (X ^ 2 - 1) * U (ZMod p) (k - 1)) * qTwo p dh d := by
  have hT := chebyshev_T_block (ZMod p) k p d
  rw [chebyshev_T_prime hp2, chebyshev_U_prime hp2] at hT
  have hW := wt_sq (p := p) hp2
  have hpow : (X - 1 : (ZMod p)[X]) ^ p = X ^ p - 1 := by
    simpa using sub_pow_char (p := p) (X : (ZMod p)[X]) 1
  simp only [expand_eq_comp_X_pow, mul_comp, sub_comp, X_comp, one_comp, pow_comp, ofNat_comp]
  rw [hT, pow_add, hpow, qOne, qTwo, wt]
  simp only [wt] at hW
  linear_combination
    (-((X - 1 : (ZMod p)[X]) ^ dh * (X ^ p - 1) * U (ZMod p) (d - 1) * (U (ZMod p) (k - 1)).comp (X ^ p))) * hW

theorem blockU (hp2 : p ≠ 2) (dh : ℕ) (k d : ℤ) :
    (X - 1) ^ (p + dh) * U (ZMod p) (k * p + d - 1) =
      expand (ZMod p) p ((X - 1) * U (ZMod p) (k - 1)) * qOne p dh d +
      expand (ZMod p) p ((X - 1) * T (ZMod p) k) * qTwo p dh d := by
  have hU := chebyshev_U_block (ZMod p) k p d
  rw [chebyshev_T_prime hp2, chebyshev_U_prime hp2] at hU
  have hpow : (X - 1 : (ZMod p)[X]) ^ p = X ^ p - 1 := by
    simpa using sub_pow_char (p := p) (X : (ZMod p)[X]) 1
  simp only [expand_eq_comp_X_pow, mul_comp, sub_comp, X_comp, one_comp, pow_comp, ofNat_comp]
  rw [hU, pow_add, hpow, qOne, qTwo, wt]
  ring

/-- The char-`p` identity (W): `W T_n = X^p U_{n-1} + U_{p-n-1}`. -/
theorem wt_mul_T (hp2 : p ≠ 2) (n : ℤ) :
    wt p * T (ZMod p) n = X ^ p * U (ZMod p) (n - 1) + U (ZMod p) ((p : ℤ) - n - 1) := by
  have h := chebyshev_U_block (ZMod p) 1 p (-n)
  rw [chebyshev_T_prime hp2, chebyshev_U_prime hp2, T_neg, U_neg_sub_one] at h
  simp only [sub_self, U_zero, T_one, one_comp, X_comp, one_mul, one_mul] at h
  rw [show (p : ℤ) + -n - 1 = (p : ℤ) - n - 1 by ring] at h
  rw [h, wt]
  ring

/-! ### Degree bounds -/

theorem natDegree_wt_le (hp2 : p ≠ 2) : (wt p).natDegree ≤ p - 1 := by
  have hodd : p = 2 * ((p - 1) / 2) + 1 := by
    have := (Fact.out : p.Prime).two_le
    have := (Fact.out : p.Prime).eq_two_or_odd
    omega
  refine natDegree_pow_le.trans ?_
  have : ((X : (ZMod p)[X]) ^ 2 - 1).natDegree ≤ 2 := by compute_degree
  have := Nat.mul_le_mul_left ((p - 1) / 2) this
  omega

theorem natDegree_T_le (hp2 : p ≠ 2) (d : ℤ) : (T (ZMod p) d).natDegree ≤ d.natAbs := by
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  rw [natDegree_T]

theorem natDegree_U_le (hp2 : p ≠ 2) (d : ℤ) :
    (U (ZMod p) (d - 1)).natDegree ≤ d.natAbs - 1 := by
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  rw [natDegree_U]
  simp

theorem natDegree_qOne_lt (hp2 : p ≠ 2) {dh e0 : ℕ} {d : ℤ} (hd : d.natAbs ≤ (p - 1) / 2)
    (he : dh + (p - 1) / 2 ≤ e0) : (qOne p dh d).natDegree < e0 + p := by
  have h1 : ((X - 1 : (ZMod p)[X]) ^ dh).natDegree ≤ dh := by
    refine natDegree_pow_le.trans ?_
    have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
    nlinarith
  have h2 := natDegree_wt_le (p := p) hp2
  have h3 := natDegree_T_le (p := p) hp2 d
  have hp3 := (Fact.out : p.Prime).two_le
  unfold qOne
  refine lt_of_le_of_lt (natDegree_mul_le.trans (Nat.add_le_add (natDegree_mul_le.trans
    (Nat.add_le_add h1 h2)) h3)) ?_
  omega

theorem natDegree_qTwo_lt (hp2 : p ≠ 2) {dh e0 : ℕ} {d : ℤ} (hd : d.natAbs ≤ (p - 1) / 2)
    (he : dh + (p - 1) / 2 ≤ e0) : (qTwo p dh d).natDegree < e0 := by
  have h1 : ((X - 1 : (ZMod p)[X]) ^ dh).natDegree ≤ dh := by
    refine natDegree_pow_le.trans ?_
    have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
    nlinarith
  have h3 := natDegree_U_le (p := p) hp2 d
  have hp3 := (Fact.out : p.Prime).two_le
  have hp4 := (Fact.out : p.Prime).eq_two_or_odd
  unfold qTwo
  refine lt_of_le_of_lt (natDegree_mul_le.trans (Nat.add_le_add h1 h3)) ?_
  omega

/-- The vanishing of `[Q1]_{e0}` beyond the offset bound `D = p - 1 - e0 + dh`. -/
theorem qOne_coeff_eq_zero (hp2 : p ≠ 2) {dh e0 : ℕ} {d : ℤ} (he : e0 < p)
    (hd : d.natAbs ≤ (p - 1) / 2) (hD : p + dh ≤ e0 + d.natAbs) :
    (qOne p dh d).coeff e0 = 0 := by
  have hp4 := (Fact.out : p.Prime).eq_two_or_odd
  have hp3 := (Fact.out : p.Prime).two_le
  have hT : qOne p dh d = qOne p dh (d.natAbs : ℤ) := by
    unfold qOne
    rcases Int.natAbs_eq d with h | h
    · rw [← h]
    · rw [h, T_neg]; simp
  have hid := wt_mul_T (p := p) hp2 (d.natAbs : ℤ)
  rw [hT]
  unfold qOne
  rw [mul_assoc, hid, mul_add]
  have e1 : ((X - 1 : (ZMod p)[X]) ^ dh * (X ^ p * U (ZMod p) ((d.natAbs : ℤ) - 1))) =
      ((X - 1) ^ dh * U (ZMod p) ((d.natAbs : ℤ) - 1)) * X ^ p := by ring
  rw [e1, coeff_add, coeff_mul_X_pow', if_neg (by omega), zero_add]
  apply coeff_eq_zero_of_natDegree_lt
  have h1 : ((X - 1 : (ZMod p)[X]) ^ dh).natDegree ≤ dh := by
    refine natDegree_pow_le.trans ?_
    have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
    nlinarith
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  have h3 : (U (ZMod p) ((p : ℤ) - (d.natAbs : ℤ) - 1)).natDegree ≤ p - d.natAbs - 1 := by
    rw [natDegree_U]; omega
  refine lt_of_le_of_lt (natDegree_mul_le.trans (Nat.add_le_add h1 h3)) ?_
  omega

#print axioms blockT
#print axioms blockU
#print axioms wt_mul_T
#print axioms natDegree_qOne_lt
#print axioms natDegree_qTwo_lt
#print axioms qOne_coeff_eq_zero
end
end CatalanMeasure.GenD.Uniform.W.LStar
