module
public import Submission.CatalanMeasure.GenD.RankSeq
@[expose] public section
set_option Elab.async false

/-!
# Family A, digit sequences of truncated row combinations

Theorem A (`proof13`) is U6g applied to the row combinations supported on `r < ns`, where
`ns = 4p + 2g + 1`.  Two changes to the U6g digit data:

* truncation replaces (H2): the lowest degree of every used row is `>= A+1`, `A = L - 4p - 1`, and
  identity K6 holds for every used row;
* when `q + h > (p+1)/2` (`e < 0`), `Qh = (1 - X^p) Y2` with `Y2` of degree `<= C + q + h - 1`, so the
  Frobenius relation holds with `e = 0` and no extra functionals are needed.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsA
open Polynomial OAI.InternalCatalan CatalanMeasure.Parametric CatalanMeasure.GenD
noncomputable section

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem uUv_dvd_ns (hp2 : p ≠ 2) {C g r n ns A : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (hns : ns ≤ n) (hs : 2 * g + 1 ≤ ns) (hA : A + ns = C + g) (hr : r < ns) : X ^ (A + 1) ∣ uUv p C g r := by
  have : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  unfold uUv
  by_cases hm : (r : ℤ) - g - 1 = -1
  · rw [hm, Chebyshev.U_neg_one]
    simp
  · have hd : (Chebyshev.U (ZMod p) ((r : ℤ) - g - 1)).natDegree ≤ ns - 2 - g := by
      rw [Chebyshev.natDegree_U]; omega
    have := reflect_dvd_of_natDegree_le _ hd (show ns - 2 - g ≤ C - 1 by omega)
    exact (pow_dvd_pow X (show A + 1 ≤ C - 1 - (ns - 2 - g) by omega)).trans this

theorem uU_dvd_ns (hp2 : p ≠ 2) {C g n ns A : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (hns : ns ≤ n) (hs : 2 * g + 1 ≤ ns) (hA : A + ns = C + g) (c : Fin n → ZMod p)
    (hc : ∀ r : Fin n, ns ≤ r.val → c r = 0) : X ^ (A + 1) ∣ uU p C g n c := by
  simp only [uU, combLin_apply]
  refine Finset.dvd_sum fun r _ => ?_
  by_cases hr : r.val < ns
  · exact Dvd.dvd.mul_left (uUv_dvd_ns hp2 hgn hnC hns hs hA hr) _
  · rw [hc r (by omega)]; simp

/-- Identity K6 for row combinations supported below `ns ≤ 4p + 2g + 1`. -/
theorem comb_K6_ns (hp2 : p ≠ 2) {C g n L ns : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (hLC : L + g = C) (hns : ns ≤ 4 * p + 2 * g + 1) (c : Fin n → ZMod p)
    (hc : ∀ r : Fin n, ns ≤ r.val → c r = 0) :
    X ^ L ∣ 2 * X * oddPrimeWeight p * uS p C g n c - (2 - X ^ (2 * p)) * uU p C g n c := by
  have : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  have h : 2 * X * oddPrimeWeight p * uS p C g n c - (2 - X ^ (2 * p)) * uU p C g n c =
      ∑ r : Fin n, Polynomial.C (c r) * (2 * X * oddPrimeWeight p * uSv p C g r.val -
        (2 - X ^ (2 * p)) * uUv p C g r.val) := by
    simp only [uU, uS, combLin_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [h]
  refine Finset.dvd_sum fun r _ => ?_
  by_cases hr' : r.val < ns
  · refine Dvd.dvd.mul_left ?_ _
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
  · rw [hc r (by omega)]; simp

end

section
variable {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]

/-- The digit data of a truncated row combination, with an arbitrary Frobenius quotient `Y`. -/
theorem digitSeq_core (hp2 : p ≠ 2) (hgn : 2 * P.g N < P.n N) {ns A e' TY : ℕ}
    (hns : ns ≤ P.n N) (hs : 2 * P.g N + 1 ≤ ns) (hnsp : ns ≤ 4 * p + 2 * P.g N + 1)
    (hA : A + ns = P.C N + P.g N)
    (c : Fin (P.n N) → ZMod p) (hc : ∀ r : Fin (P.n N), ns ≤ r.val → c r = 0)
    (Y : (ZMod p)[X]) (hfr : (1 - X) ^ e' * qhP P N p c = (1 - X ^ p) * Y)
    (hYd : Y.natDegree ≤ TY) (hYl : X ^ (A + 1) ∣ Y) :
    DigitSeq p A (P.L N) (P.C N + P.q N + P.h N + p - 1)
      (P.C N + P.q N + P.h N - 1) TY e'
      (fun i => (qhP P N p c).coeff i) (fun i => (dhP P N p c).coeff i)
      (fun i => Y.coeff i) := by
  have hodd := odd_of_ne_two hp2
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  have hnC : P.n N + P.g N ≤ P.C N := by omega
  have hSdeg := uS_natDegree_le hp2 hgn hnC c
  have hUdeg := uU_natDegree_le hp2 hgn hnC c
  have hSdvd : X ^ A ∣ uS p (P.C N) (P.g N) (P.n N) c :=
    uS_dvd hp2 hgn hnC hns hs hA c hc
  have hUdvd := uU_dvd_ns hp2 hgn hnC hns hs hA c hc
  have hWdeg := oddPrimeWeight_natDegree_le (p := p) hp2
  have hXq := natDegree_X_sub_one_pow_le' (p := p) (P.q N)
  have hXh := one_sub_X_pow_natDegree_le (p := p) (P.h N)
  have dq : (qhP P N p c).natDegree ≤ P.C N + P.q N + P.h N + p - 1 := by
    unfold qhP fP
    refine natDegree_mul_le.trans ?_
    have h1 : (X * oddPrimeWeight p * ((1 - X) ^ P.h N * uS p (P.C N) (P.g N) (P.n N) c)).natDegree
        ≤ 1 + (p - 1) + (P.h N + (P.C N - 1)) := by
      refine natDegree_mul_le.trans (Nat.add_le_add ?_ ?_)
      · refine natDegree_mul_le.trans (Nat.add_le_add ?_ hWdeg)
        simp
      · exact natDegree_mul_le.trans (Nat.add_le_add hXh hSdeg)
    have := hp.out.two_le
    omega
  have dd : (dhP P N p c).natDegree ≤ P.C N + P.q N + P.h N - 1 := by
    unfold dhP gP
    refine natDegree_mul_le.trans ?_
    have h1 : ((1 - X) ^ P.h N * uU p (P.C N) (P.g N) (P.n N) c).natDegree ≤
        P.h N + (P.C N - 1) := natDegree_mul_le.trans (Nat.add_le_add hXh hUdeg)
    omega
  obtain ⟨T, hT⟩ := hSdvd
  obtain ⟨T', hT'⟩ := hUdvd
  have lq : X ^ (A + 1) ∣ qhP P N p c :=
    ⟨(X - 1) ^ P.q N * (oddPrimeWeight p * (1 - X) ^ P.h N * T), by
      unfold qhP fP; rw [hT]; ring⟩
  have ld : X ^ (A + 1) ∣ dhP P N p c :=
    ⟨(X - 1) ^ P.q N * ((1 - X) ^ P.h N * T'), by unfold dhP gP; rw [hT']; ring⟩
  obtain ⟨Z, hZ⟩ := comb_K6_ns hp2 hgn hnC (show P.L N + P.g N = P.C N by omega) hnsp c hc
  have hE : C (2 : ZMod p) * qhP P N p c - (C 2 - X ^ (2 * p)) * dhP P N p c =
      X ^ P.L N * ((X - 1) ^ P.q N * (1 - X) ^ P.h N * Z) := by
    unfold qhP fP dhP gP
    have h2 : (C (2 : ZMod p) : (ZMod p)[X]) = 2 := C_ofNat 2
    rw [h2]
    linear_combination ((X - 1) ^ P.q N * (1 - X) ^ P.h N) * hZ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact X_pow_dvd_iff.mp lq i (by omega)
  · intro i hi
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt dq (by omega))
  · intro i hi
    exact X_pow_dvd_iff.mp ld i (by omega)
  · intro i hi
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt dd (by omega))
  · intro i hi
    exact X_pow_dvd_iff.mp hYl i (by omega)
  · intro i hi
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hYd (by omega))
  · intro i hi
    have := congrArg (fun F : (ZMod p)[X] => F.coeff i) hE
    simp only [coeff_sub, coeff_C_mul, sub_mul, coeff_X_pow_mul', if_neg (not_le.mpr hi)] at this
    linear_combination this
  · intro i hi
    have := congrArg (fun F : (ZMod p)[X] => F.coeff i) hfr
    rw [one_sub_X_pow_mul_coeff _ _ _ hi, sub_mul, one_mul, coeff_sub, coeff_X_pow_mul'] at this
    exact this

/-- Case `e ≥ 0`: the Frobenius quotient is `yP`, with `e = (p+1)/2 - q - h`. -/
theorem digitSeq_pos (hp2 : p ≠ 2) (hgn : 2 * P.g N < P.n N)
    (hH1 : P.q N + P.h N ≤ (p + 1) / 2) {ns A : ℕ}
    (hns : ns ≤ P.n N) (hs : 2 * P.g N + 1 ≤ ns) (hnsp : ns ≤ 4 * p + 2 * P.g N + 1)
    (hA : A + ns = P.C N + P.g N)
    (c : Fin (P.n N) → ZMod p) (hc : ∀ r : Fin (P.n N), ns ≤ r.val → c r = 0) :
    DigitSeq p A (P.L N) (P.C N + P.q N + P.h N + p - 1)
      (P.C N + P.q N + P.h N - 1) (P.C N + (p - 1) / 2) ((p + 1) / 2 - P.q N - P.h N)
      (fun i => (qhP P N p c).coeff i) (fun i => (dhP P N p c).coeff i)
      (fun i => (yP P N p c).coeff i) := by
  have hodd := odd_of_ne_two hp2
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  have hnC : P.n N + P.g N ≤ P.C N := by omega
  have hSdeg := uS_natDegree_le hp2 hgn hnC c
  have hSdvd : X ^ A ∣ uS p (P.C N) (P.g N) (P.n N) c :=
    uS_dvd hp2 hgn hnC hns hs hA c hc
  obtain ⟨T, hT⟩ := hSdvd
  refine digitSeq_core hp2 hgn hns hs hnsp hA c hc (yP P N p c) (frob_poly hp2 hH1 c) ?_ ?_
  · unfold yP
    refine (natDegree_C_mul_le _ _).trans ?_
    have h1 : (X * (1 + X) ^ ((p - 1) / 2) * uS p (P.C N) (P.g N) (P.n N) c).natDegree ≤
        1 + (p - 1) / 2 + (P.C N - 1) := by
      refine natDegree_mul_le.trans (Nat.add_le_add ?_ hSdeg)
      refine natDegree_mul_le.trans (Nat.add_le_add ?_ (natDegree_one_add_X_pow_le' _))
      simp
    omega
  · exact ⟨C ((-1 : ZMod p) ^ P.q N) * ((1 + X) ^ ((p - 1) / 2) * T), by
      unfold yP; rw [hT]; ring⟩

/-- Case `e < 0`: `Qh = (1 - X^p) Y2`, so the Frobenius relation holds with `e = 0`. -/
theorem digitSeq_neg (hp2 : p ≠ 2) (hgn : 2 * P.g N < P.n N)
    (hH1 : (p + 1) / 2 < P.q N + P.h N) {ns A : ℕ}
    (hns : ns ≤ P.n N) (hs : 2 * P.g N + 1 ≤ ns) (hnsp : ns ≤ 4 * p + 2 * P.g N + 1)
    (hA : A + ns = P.C N + P.g N)
    (c : Fin (P.n N) → ZMod p) (hc : ∀ r : Fin (P.n N), ns ≤ r.val → c r = 0) :
    DigitSeq p A (P.L N) (P.C N + P.q N + P.h N + p - 1)
      (P.C N + P.q N + P.h N - 1) (P.C N + P.q N + P.h N - 1) 0
      (fun i => (qhP P N p c).coeff i) (fun i => (dhP P N p c).coeff i)
      (fun i => (C ((-1 : ZMod p) ^ P.q N) * (X * (1 - X) ^ (P.q N + P.h N - (p + 1) / 2) *
        (1 + X) ^ ((p - 1) / 2) * uS p (P.C N) (P.g N) (P.n N) c)).coeff i) := by
  have hodd := odd_of_ne_two hp2
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  have hnC : P.n N + P.g N ≤ P.C N := by omega
  have hSdeg := uS_natDegree_le hp2 hgn hnC c
  have hSdvd : X ^ A ∣ uS p (P.C N) (P.g N) (P.n N) c :=
    uS_dvd hp2 hgn hnC hns hs hA c hc
  obtain ⟨T, hT⟩ := hSdvd
  have hpow : (1 - X : (ZMod p)[X]) ^ p = 1 - X ^ p := by rw [sub_pow_char, one_pow]
  have e1 : (X - 1 : (ZMod p)[X]) ^ P.q N = C ((-1 : ZMod p) ^ P.q N) * (1 - X) ^ P.q N := by
    rw [← neg_sub, neg_pow]; simp
  have e2 : oddPrimeWeight p = (1 - X : (ZMod p)[X]) ^ ((p - 1) / 2) * (1 + X) ^ ((p - 1) / 2) := by
    unfold oddPrimeWeight
    rw [← mul_pow]; congr 1; ring
  have hsum : P.q N + (p - 1) / 2 + P.h N = p + (P.q N + P.h N - (p + 1) / 2) := by omega
  refine digitSeq_core hp2 hgn hns hs hnsp hA c hc _ ?_ ?_ ?_
  · rw [pow_zero, one_mul]
    unfold qhP fP
    rw [e1, e2]
    have : (1 - X : (ZMod p)[X]) ^ (P.q N + (p - 1) / 2 + P.h N) =
        (1 - X ^ p) * (1 - X) ^ (P.q N + P.h N - (p + 1) / 2) := by
      rw [hsum, pow_add, hpow]
    calc _ = C ((-1 : ZMod p) ^ P.q N) * (X * (1 - X) ^ (P.q N + (p - 1) / 2 + P.h N) *
          (1 + X) ^ ((p - 1) / 2) * uS p (P.C N) (P.g N) (P.n N) c) := by
          simp only [pow_add]; ring
      _ = _ := by rw [this]; ring
  · refine (natDegree_C_mul_le _ _).trans ?_
    have h1 : (X * (1 - X) ^ (P.q N + P.h N - (p + 1) / 2) * (1 + X) ^ ((p - 1) / 2) *
        uS p (P.C N) (P.g N) (P.n N) c).natDegree ≤
        1 + (P.q N + P.h N - (p + 1) / 2) + (p - 1) / 2 + (P.C N - 1) := by
      refine natDegree_mul_le.trans (Nat.add_le_add ?_ hSdeg)
      refine natDegree_mul_le.trans (Nat.add_le_add ?_ (natDegree_one_add_X_pow_le' _))
      refine natDegree_mul_le.trans (Nat.add_le_add ?_ (one_sub_X_pow_natDegree_le _))
      simp
    omega
  · exact ⟨C ((-1 : ZMod p) ^ P.q N) * ((1 - X) ^ (P.q N + P.h N - (p + 1) / 2) *
      ((1 + X) ^ ((p - 1) / 2) * T)), by rw [hT]; ring⟩

end
end
end CatalanMeasure.GenD.Uniform.W.SlotsA
