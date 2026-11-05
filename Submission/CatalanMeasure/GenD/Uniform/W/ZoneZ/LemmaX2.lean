module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.LemmaX
public import Submission.CatalanMeasure.Parametric.ChebyshevPrime
@[expose] public section
set_option Elab.async false

/-!
# Lemma X, polynomial core: the degree statement

`lemmaX_core`: `w · Tl c = L + X^p · Hh` with `deg L < p` and `Hh + Ul c` of degree `< R`
whenever `c` is supported on `|m| ≤ B < p`, `m ≤ R - 1`.  Iterating with the second difference
(`lemmaX_iter`) gives the statement for `(2X-2)^h`: top-block virtual rows force the degree
bound `h + rtop - 1` (and block-0 rows by reflection).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.Prefix
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem Tl_eq_sum (c : ℤ →₀ ZMod p) :
    Tl c = ∑ m ∈ c.support, c m • Chebyshev.T (ZMod p) m := by
  simp [Tl, Finsupp.lsum_apply, Finsupp.sum]

theorem Ul_eq_sum (c : ℤ →₀ ZMod p) :
    Ul c = ∑ m ∈ c.support, c m • Chebyshev.U (ZMod p) (m - 1) := by
  simp [Ul, Finsupp.lsum_apply, Finsupp.sum]

/-- `w T_d = X^p U_{d-1} + U_{p-d-1}` for `w = U_{p-1}` (tool (W) of zone2). -/
theorem wT_eq (hp2 : p ≠ 2) (d : ℤ) :
    Chebyshev.U (ZMod p) ((p : ℤ) - 1) * Chebyshev.T (ZMod p) d =
      X ^ p * Chebyshev.U (ZMod p) (d - 1) + Chebyshev.U (ZMod p) ((p : ℤ) - d - 1) := by
  have h1 := chebyshev_U_add (ZMod p) (p : ℤ) d
  have h2 := chebyshev_U_add (ZMod p) (p : ℤ) (-d)
  rw [Chebyshev.T_neg, Chebyshev.U_neg_sub_one, chebyshev_T_prime hp2] at h2
  rw [chebyshev_T_prime hp2] at h1
  have e : (p : ℤ) + -d - 1 = (p : ℤ) - d - 1 := by ring
  rw [e] at h2
  linear_combination -h2

theorem iter_supp_hi (h : ℕ) (r : ℕ) (c : ℤ →₀ ZMod p) (hc : ∀ m, (r : ℤ) < m → c m = 0) :
    ∀ m, ((r + h : ℕ) : ℤ) < m → ((Dl (p := p))^[h] c) m = 0 := by
  induction h with
  | zero => simpa using hc
  | succ h ih =>
    intro m hm
    rw [Function.iterate_succ_apply', Dl_apply]
    have a := ih (m - 1) (by push_cast at hm ⊢; omega)
    have b := ih m (by push_cast at hm ⊢; omega)
    have c' := ih (m + 1) (by push_cast at hm ⊢; omega)
    rw [a, b, c']; ring

theorem iter_supp_abs (h : ℕ) (B : ℕ) (c : ℤ →₀ ZMod p) (hc : ∀ m : ℤ, B < m.natAbs → c m = 0) :
    ∀ m : ℤ, B + h < m.natAbs → ((Dl (p := p))^[h] c) m = 0 := by
  induction h with
  | zero => simpa using hc
  | succ h ih =>
    intro m hm
    rw [Function.iterate_succ_apply', Dl_apply]
    have a := ih (m - 1) (by omega)
    have b := ih m (by omega)
    have c' := ih (m + 1) (by omega)
    rw [a, b, c']; ring

theorem iter_Tl (h : ℕ) (c : ℤ →₀ ZMod p) :
    (2 * X - 2 : (ZMod p)[X]) ^ h * Tl c = Tl ((Dl (p := p))^[h] c) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ, mul_comm _ (2 * X - 2), mul_assoc, ih, Tl_Dl, Function.iterate_succ_apply']

theorem iter_Ul (h : ℕ) (c : ℤ →₀ ZMod p) :
    (2 * X - 2 : (ZMod p)[X]) ^ h * Ul c = Ul ((Dl (p := p))^[h] c) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ, mul_comm _ (2 * X - 2), mul_assoc, ih, Ul_Dl, Function.iterate_succ_apply']

/-- **Lemma X, polynomial core.** -/
theorem lemmaX_core (hp2 : p ≠ 2) {B R : ℕ} (hBp : B < p) (c : ℤ →₀ ZMod p)
    (hB : ∀ m : ℤ, B < m.natAbs → c m = 0) (hR : ∀ m : ℤ, (R : ℤ) ≤ m → c m = 0) :
    ∃ L Hh : (ZMod p)[X],
      Chebyshev.U (ZMod p) ((p : ℤ) - 1) * Tl c = L + X ^ p * Hh ∧ L.degree < p ∧
        ∀ i, R - 1 ≤ i → (Hh + Ul c).coeff i = 0 := by
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  refine ⟨∑ m ∈ c.support, c m • Chebyshev.U (ZMod p) ((p : ℤ) - m.natAbs - 1),
    ∑ m ∈ c.support, c m • Chebyshev.U (ZMod p) ((m.natAbs : ℤ) - 1), ?_, ?_, ?_⟩
  · rw [Tl_eq_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, ← Chebyshev.T_natAbs, wT_eq hp2, smul_add]
    simp only [smul_eq_C_mul]
    ring
  · rw [Polynomial.degree_lt_iff_coeff_zero]
    intro i hi
    rw [finset_sum_coeff]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hmB : m.natAbs ≤ B := by
      by_contra hcon
      exact (Finsupp.mem_support_iff.mp hm) (hB m (by omega))
    have hdeg : (Chebyshev.U (ZMod p) ((p : ℤ) - m.natAbs - 1)).natDegree = p - m.natAbs - 1 := by
      have : ((p : ℤ) - m.natAbs - 1) = ((p - m.natAbs - 1 : ℕ) : ℤ) := by omega
      rw [this]; exact Chebyshev.natDegree_U_natCast _ _
    rw [coeff_smul, coeff_eq_zero_of_natDegree_lt (by omega), smul_zero]
  · intro i hi
    rw [coeff_add, Ul_eq_sum, finset_sum_coeff, finset_sum_coeff, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [coeff_smul, coeff_smul, ← smul_add]
    have hmR : m < R := by
      by_contra hcon
      exact (Finsupp.mem_support_iff.mp hm) (hR m (by omega))
    have hz : (Chebyshev.U (ZMod p) ((m.natAbs : ℤ) - 1)).coeff i +
        (Chebyshev.U (ZMod p) (m - 1)).coeff i = 0 := by
      rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
      · have e : (m.natAbs : ℤ) = -m := by omega
        rw [e, Chebyshev.U_neg_sub_one]; simp
      · subst hm0; simp
      · have e : (m.natAbs : ℤ) = m := by omega
        rw [e]
        have hdeg : (Chebyshev.U (ZMod p) (m - 1)).natDegree = m.toNat - 1 := by
          have : (m - 1) = ((m.toNat - 1 : ℕ) : ℤ) := by omega
          rw [this]; exact Chebyshev.natDegree_U_natCast _ _
        rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp
    rw [hz, smul_zero]

/-- **Lemma X, iterated form.**  `c` supported on `|m| ≤ B` and `m ≤ r`: with `h` powers of
`2X - 2`, the polynomial `Hh + (2X-2)^h Ul c` (where `w (2X-2)^h Tl c = L + X^p Hh`,
`deg L < p`) has degree `≤ h + r - 1`, i.e. all coefficients from `h + r` on vanish
(exactly the paper's `deg Q ≤ h + r - 1`: coefficients from `h + r` on vanish). -/
theorem lemmaX_iter (hp2 : p ≠ 2) {h r B : ℕ} (hBh : B + h < p) (c : ℤ →₀ ZMod p)
    (hB : ∀ m : ℤ, B < m.natAbs → c m = 0) (hr : ∀ m : ℤ, (r : ℤ) < m → c m = 0) :
    ∃ L Hh : (ZMod p)[X],
      Chebyshev.U (ZMod p) ((p : ℤ) - 1) * ((2 * X - 2 : (ZMod p)[X]) ^ h * Tl c) =
        L + X ^ p * Hh ∧ L.degree < p ∧
        ∀ i, h + r ≤ i → (Hh + (2 * X - 2 : (ZMod p)[X]) ^ h * Ul c).coeff i = 0 := by
  obtain ⟨L, Hh, e1, e2, e3⟩ := lemmaX_core hp2 (B := B + h) (R := r + h + 1) hBh
    ((Dl (p := p))^[h] c) (iter_supp_abs h B c hB)
    (fun m hm => iter_supp_hi h r c hr m (by push_cast at hm ⊢; omega))
  refine ⟨L, Hh, ?_, e2, fun i hi => ?_⟩
  · rw [iter_Tl]; exact e1
  · rw [iter_Ul]; exact e3 i (by omega)

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
