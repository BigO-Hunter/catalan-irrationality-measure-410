module
public import Submission.CatalanMeasure.GenD.RankCommon
public import Submission.CatalanMeasure.GenD.RankUCore
@[expose] public section

/-!
# Identity K6 for a general design (GenD, shared by Theorems U6g and S)

Over `ZMod p`, `p` odd: `2 X^p (X^2-1)^((p-1)/2) T_m - (2 X^(2p) - 1) U_{m-1} = U_{2p-m-1}`.
For a row combination `c` of any design with `2g < n`, `n + g ≤ C`, `L + g = C` and
`n ≤ 4p + 2g + 1`:
`X^L ∣ 2 X W S_c - (2 - X^(2p)) U_c`, hence `2 Qh[i] = 2 Dh[i] - Dh[i-2p]` for `i < L`.
-/

namespace CatalanMeasure.GenD
open Polynomial OAI.InternalCatalan
noncomputable section

/-- `U_{m-1} T_n - T_m U_{n-1} = U_{m-n-1}` over any commutative ring. -/
theorem cheb_U_T_sub (R : Type*) [CommRing R] (m n : ℤ) :
    Chebyshev.U R (m - 1) * Chebyshev.T R n - Chebyshev.T R m * Chebyshev.U R (n - 1) =
      Chebyshev.U R (m - n - 1) := by
  set G : ℤ → R[X] := fun n =>
    Chebyshev.U R (m - 1) * Chebyshev.T R n - Chebyshev.T R m * Chebyshev.U R (n - 1) -
      Chebyshev.U R (m - n - 1) with hG
  have hrec : ∀ n : ℤ, G (n + 2) = 2 * X * G (n + 1) - G n := by
    intro n
    have t1 := Chebyshev.T_add_two R n
    have u1 := Chebyshev.U_add_two R (n - 1)
    have u3 := Chebyshev.U_sub_two R (m - n - 1)
    rw [show n - 1 + 2 = n + 1 by ring, show n - 1 + 1 = n by ring] at u1
    have e1 : m - (n + 2) - 1 = m - n - 1 - 2 := by ring
    have e2 : m - (n + 1) - 1 = m - n - 1 - 1 := by ring
    have e3 : n + 1 - 1 = n := by ring
    have e4 : n + 2 - 1 = n + 1 := by ring
    simp only [hG, e1, e2, e3, e4]
    linear_combination (Chebyshev.U R (m - 1)) * t1 - (Chebyshev.T R m) * u1 - u3
  have h0 : G 0 = 0 := by
    simp [hG, Chebyshev.T_zero, Chebyshev.U_neg_one]
  have h1 : G 1 = 0 := by
    have c3 := Chebyshev.T_eq_U_sub_X_mul_U R m
    have c2 := Chebyshev.U_add_one R (m - 1)
    rw [show m - 1 + 1 = m by ring] at c2
    simp only [hG, Chebyshev.T_one, Chebyshev.U_zero, sub_self]
    linear_combination (-1 : R[X]) * c3 + (-1 : R[X]) * c2
  have key : ∀ k : ℤ, G k = 0 := by
    intro k
    refine Chebyshev.induct (fun k => G k = 0) h0 h1 ?_ ?_ k
    · intro n h1' h0'
      have := hrec n
      simp only [h1', h0', mul_zero, sub_zero] at this
      exact this
    · intro n h0' h1'
      have := hrec (-(n : ℤ) - 1)
      rw [show -(n : ℤ) - 1 + 2 = -(n : ℤ) + 1 by ring,
        show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring] at this
      simp only [h0', h1', mul_zero, zero_sub] at this
      exact neg_eq_zero.mp this.symm
  have := key n
  simp only [hG] at this
  linear_combination this

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem cheb_T_two_mul_prime (hp2 : p ≠ 2) :
    Chebyshev.T (ZMod p) (2 * (p : ℤ)) = 2 * X ^ (2 * p) - 1 := by
  rw [Chebyshev.T_mul, Chebyshev.T_two, CatalanMeasure.Parametric.chebyshev_T_prime hp2]
  simp only [sub_comp, mul_comp, ofNat_comp, pow_comp, X_comp, one_comp]
  rw [← pow_mul, mul_comm p 2]; simp

theorem cheb_U_two_mul_prime (hp2 : p ≠ 2) :
    Chebyshev.U (ZMod p) (2 * (p : ℤ) - 1) = 2 * X ^ p * (X ^ 2 - 1) ^ ((p - 1) / 2) := by
  have h := CatalanMeasure.Parametric.chebyshev_U_difference (ZMod p) (p : ℤ) p
  rw [show (p : ℤ) + (p : ℤ) - 1 = 2 * (p : ℤ) - 1 by ring,
    show (p : ℤ) - (p : ℤ) - 1 = -1 by ring, Chebyshev.U_neg_one,
    CatalanMeasure.Parametric.chebyshev_T_prime hp2,
    CatalanMeasure.Parametric.chebyshev_U_prime hp2] at h
  rw [sub_zero] at h
  rw [h]

/-- Identity K6 in characteristic `p`. -/
theorem cheb_K6 (hp2 : p ≠ 2) (o : ℤ) :
    2 * X ^ p * (X ^ 2 - 1) ^ ((p - 1) / 2) * Chebyshev.T (ZMod p) o -
        (2 * X ^ (2 * p) - 1) * Chebyshev.U (ZMod p) (o - 1) =
      Chebyshev.U (ZMod p) (2 * (p : ℤ) - o - 1) := by
  have i := cheb_U_T_sub (ZMod p) (2 * (p : ℤ)) o
  rw [cheb_U_two_mul_prime hp2, cheb_T_two_mul_prime hp2] at i
  exact i

theorem reflect_K6_left (hp2 : p ≠ 2) :
    reflect (2 * p) (2 * X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2)) =
      2 * X * oddPrimeWeight p := by
  have hodd := odd_of_ne_two hp2
  have hp1 := hp.out.one_le
  obtain ⟨h', hh⟩ : ∃ h', h' = (p - 1) / 2 := ⟨_, rfl⟩
  have hph : p = 2 * h' + 1 := by omega
  rw [← hh]
  have hZ : ((X ^ 2 - 1 : (ZMod p)[X]) ^ h').natDegree ≤ 2 * h' := by
    calc _ ≤ h' * (X ^ 2 - 1 : (ZMod p)[X]).natDegree := natDegree_pow_le
      _ ≤ h' * 2 := Nat.mul_le_mul_left _ (by compute_degree)
      _ = 2 * h' := by ring
  have hX : ((X : (ZMod p)[X]) ^ p).natDegree ≤ p := by simp
  have e1 : (2 * X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ h') =
      C 2 * (X ^ p * (X ^ 2 - 1) ^ h') := by
    rw [C_ofNat]; ring
  have e2 : reflect (p + 2 * h') (X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ h') =
      (1 - X ^ 2) ^ h' := by
    rw [reflect_mul _ _ hX hZ, reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero,
      reflect_pow_two, one_mul]
  have e3 : reflect (2 * p) (X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ h') =
      X * (1 - X ^ 2) ^ h' := by
    have hd : (X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ h').natDegree ≤ p + 2 * h' :=
      natDegree_mul_le.trans (Nat.add_le_add hX hZ)
    have := reflect_shift _ hd 1
    rw [show 2 * p = p + 2 * h' + 1 by omega, this, e2, pow_one]
  rw [e1, reflect_C_mul, e3, oddPrimeWeight, ← hh]
  rw [C_ofNat]; ring

theorem reflect_K6_right :
    reflect (2 * p) (2 * X ^ (2 * p) - 1 : (ZMod p)[X]) = 2 - X ^ (2 * p) := by
  have e : (2 * X ^ (2 * p) - 1 : (ZMod p)[X]) = C 2 * X ^ (2 * p) - 1 := by
    rw [C_ofNat]
  rw [e, reflect_sub, reflect_C_mul_X_pow, reflect_one, revAt_le le_rfl, Nat.sub_self, pow_zero,
    mul_one, C_ofNat]

/-- Identity K6 for one row `m` (reflection length `E`, divisibility `X^L`). -/
theorem row_K6_gen (hp2 : p ≠ 2) {E L : ℕ} {m : ℤ}
    (hT : (Chebyshev.T (ZMod p) m).natDegree ≤ E)
    (hU : (Chebyshev.U (ZMod p) (m - 1)).natDegree ≤ E)
    (hd : (Chebyshev.U (ZMod p) (2 * (p : ℤ) - m - 1)).natDegree + L ≤ 2 * p + E) :
    X ^ L ∣ 2 * X * oddPrimeWeight p * reflect E (Chebyshev.T (ZMod p) m) -
      (2 - X ^ (2 * p)) * reflect E (Chebyshev.U (ZMod p) (m - 1)) := by
  have hodd := odd_of_ne_two hp2
  have hA : (2 * X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2)).natDegree ≤ 2 * p := by
    have hZ : ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2)).natDegree ≤ p - 1 := by
      calc _ ≤ ((p - 1) / 2) * (X ^ 2 - 1 : (ZMod p)[X]).natDegree := natDegree_pow_le
        _ ≤ ((p - 1) / 2) * 2 := Nat.mul_le_mul_left _ (by compute_degree)
        _ ≤ p - 1 := by omega
    have hX : (2 * (X : (ZMod p)[X]) ^ p).natDegree ≤ p := by
      refine (natDegree_mul_le).trans ?_
      have : (2 : (ZMod p)[X]).natDegree = 0 := by
        rw [← C_ofNat]; exact natDegree_C _
      simp
    calc _ ≤ _ := natDegree_mul_le
      _ ≤ p + (p - 1) := Nat.add_le_add hX hZ
      _ ≤ 2 * p := by omega
  have hB : (2 * X ^ (2 * p) - 1 : (ZMod p)[X]).natDegree ≤ 2 * p := by
    rw [← C_ofNat]
    compute_degree
  have key := congrArg (reflect (2 * p + E)) (cheb_K6 hp2 m)
  rw [reflect_sub, reflect_mul _ _ hA hT, reflect_mul _ _ hB hU, reflect_K6_left hp2,
    reflect_K6_right] at key
  have hdv := reflect_dvd_of_natDegree_le _ (le_refl _ : _ ≤ _) (show
    (Chebyshev.U (ZMod p) (2 * (p : ℤ) - m - 1)).natDegree ≤ 2 * p + E by omega)
  rw [← key] at hdv
  exact (pow_dvd_pow X (show L ≤ 2 * p + E - (Chebyshev.U (ZMod p)
    (2 * (p : ℤ) - m - 1)).natDegree by omega)).trans hdv

/-- Identity K6 for a row combination of a general design. -/
theorem comb_K6 (hp2 : p ≠ 2) {C g n L : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (hLC : L + g = C) (hH2 : n ≤ 4 * p + 2 * g + 1) (c : Fin n → ZMod p) :
    X ^ L ∣ 2 * X * oddPrimeWeight p * uS p C g n c - (2 - X ^ (2 * p)) * uU p C g n c := by
  have : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  have h : 2 * X * oddPrimeWeight p * uS p C g n c - (2 - X ^ (2 * p)) * uU p C g n c =
      ∑ r : Fin n, Polynomial.C (c r) * (2 * X * oddPrimeWeight p * uSv p C g r.val -
        (2 - X ^ (2 * p)) * uUv p C g r.val) := by
    simp only [uU, uS, combLin_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [h]
  refine Finset.dvd_sum fun r _ => Dvd.dvd.mul_left ?_ _
  have hr := r.isLt
  unfold uSv uUv
  have hT : (Chebyshev.T (ZMod p) ((r.val : ℤ) - g)).natDegree ≤ C - 1 := by
    rw [Chebyshev.natDegree_T]; omega
  have hU : (Chebyshev.U (ZMod p) ((r.val : ℤ) - g - 1)).natDegree ≤ C - 1 := by
    rw [Chebyshev.natDegree_U]; omega
  refine row_K6_gen hp2 hT hU ?_
  rw [Chebyshev.natDegree_U]
  have hp2le := hp.out.two_le
  omega

end
end
end CatalanMeasure.GenD
