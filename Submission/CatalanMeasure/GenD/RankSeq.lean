module
public import Submission.CatalanMeasure.GenD.RankFilt
public import Submission.CatalanMeasure.GenD.RankK6
public import Submission.CatalanMeasure.GenD.RankDigits
@[expose] public section

/-!
# From the row polynomials to the digit sequences (GenD)

For a design `P`, an odd prime `p`, `2g < n`, `q + h ≤ (p+1)/2` (H1) and `n ≤ 4p + 2g + 1` (H2),
the coefficient sequences of `Qh`, `Dh` and the Frobenius quotient `Y` satisfy `DigitSeq`.
-/

namespace CatalanMeasure.GenD
open Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
noncomputable section

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem uUv_dvd (hp2 : p ≠ 2) {C g r n A : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (hA : A + n = C + g) (hr : r < n) : X ^ (A + 1) ∣ uUv p C g r := by
  have : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  unfold uUv
  by_cases hm : (r : ℤ) - g - 1 = -1
  · rw [hm, Chebyshev.U_neg_one]
    simp
  · have hd : (Chebyshev.U (ZMod p) ((r : ℤ) - g - 1)).natDegree ≤ n - 2 - g := by
      rw [Chebyshev.natDegree_U]; omega
    have := reflect_dvd_of_natDegree_le _ hd (show n - 2 - g ≤ C - 1 by omega)
    exact (pow_dvd_pow X (show A + 1 ≤ C - 1 - (n - 2 - g) by omega)).trans this

theorem uU_dvd (hp2 : p ≠ 2) {C g n A : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (hA : A + n = C + g) (c : Fin n → ZMod p) : X ^ (A + 1) ∣ uU p C g n c := by
  simp only [uU, combLin_apply]
  refine Finset.dvd_sum fun r _ => Dvd.dvd.mul_left ?_ _
  exact uUv_dvd hp2 hgn hnC hA r.isLt

theorem natDegree_X_sub_one_pow_le' (n : ℕ) : ((X - 1 : (ZMod p)[X]) ^ n).natDegree ≤ n := by
  calc _ ≤ n * (X - 1 : (ZMod p)[X]).natDegree := natDegree_pow_le
    _ ≤ n * 1 := Nat.mul_le_mul_left _ (by compute_degree)
    _ = n := by ring

theorem natDegree_one_add_X_pow_le' (n : ℕ) : ((1 + X : (ZMod p)[X]) ^ n).natDegree ≤ n := by
  calc _ ≤ n * (1 + X : (ZMod p)[X]).natDegree := natDegree_pow_le
    _ ≤ n * 1 := Nat.mul_le_mul_left _ (by compute_degree)
    _ = n := by ring

theorem oddPrimeWeight_natDegree_le (hp2 : p ≠ 2) : (oddPrimeWeight p).natDegree ≤ p - 1 := by
  unfold oddPrimeWeight
  rw [one_sub_X_sq_natDegree]
  have := odd_of_ne_two hp2
  omega

/-- Coefficient form of `(1-X)^e A`. -/
theorem one_sub_X_pow_mul_coeff {R : Type*} [CommRing R] (A : R[X]) (e i : ℕ) (hei : e ≤ i) :
    ((1 - X) ^ e * A).coeff i =
      ∑ t ∈ Finset.range (e + 1), (-1 : R) ^ t * (e.choose t : R) * A.coeff (i - t) := by
  have h1 : (1 - X : R[X]) ^ e = ∑ t ∈ Finset.range (e + 1),
      C ((-1 : R) ^ t * (e.choose t : R)) * X ^ t := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [one_pow, mul_one, neg_pow, map_mul, map_pow, map_neg, map_one, map_natCast]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [h1, Finset.sum_mul, finsetSum_coeff]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htl := Finset.mem_range.mp ht
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega)]

end

section
variable {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]

/-- The Frobenius quotient `Y = (-1)^q X (1+X)^((p-1)/2) S_c`. -/
def yP (P : Parameters) (N p : ℕ) [Fact p.Prime] (c : Fin (P.n N) → ZMod p) : (ZMod p)[X] :=
  C ((-1 : ZMod p) ^ P.q N) * (X * (1 + X) ^ ((p - 1) / 2) * uS p (P.C N) (P.g N) (P.n N) c)

theorem frob_poly (hp2 : p ≠ 2) (hH1 : P.q N + P.h N ≤ (p + 1) / 2) (c : Fin (P.n N) → ZMod p) :
    (1 - X) ^ ((p + 1) / 2 - P.q N - P.h N) * qhP P N p c = (1 - X ^ p) * yP P N p c := by
  have hodd := odd_of_ne_two hp2
  have hsum : ((p + 1) / 2 - P.q N - P.h N) + P.q N + (p - 1) / 2 + P.h N = p := by omega
  have hpow : (1 - X : (ZMod p)[X]) ^ p = 1 - X ^ p := by rw [sub_pow_char, one_pow]
  have e1 : (X - 1 : (ZMod p)[X]) ^ P.q N = C ((-1 : ZMod p) ^ P.q N) * (1 - X) ^ P.q N := by
    rw [← neg_sub, neg_pow]; simp
  have e2 : oddPrimeWeight p = (1 - X : (ZMod p)[X]) ^ ((p - 1) / 2) * (1 + X) ^ ((p - 1) / 2) := by
    unfold oddPrimeWeight
    rw [← mul_pow]; congr 1; ring
  have key : (1 - X : (ZMod p)[X]) ^ ((p + 1) / 2 - P.q N - P.h N) * qhP P N p c =
      (1 - X : (ZMod p)[X]) ^ (((p + 1) / 2 - P.q N - P.h N) + P.q N + (p - 1) / 2 + P.h N) *
        yP P N p c := by
    unfold qhP yP fP
    rw [e1, e2]
    ring
  rw [key, hsum, hpow]

/-- Support facts and the three identities for the sequences of `Qh`, `Dh`, `Y`. -/
theorem digitSeq_design (hp2 : p ≠ 2) (hgn : 2 * P.g N < P.n N)
    (hH1 : P.q N + P.h N ≤ (p + 1) / 2) (hH2 : P.n N ≤ 4 * p + 2 * P.g N + 1)
    (c : Fin (P.n N) → ZMod p) :
    DigitSeq p (P.b N + P.q N + 2 * P.g N) (P.L N) (P.C N + P.q N + P.h N + p - 1)
      (P.C N + P.q N + P.h N - 1) (P.C N + (p - 1) / 2) ((p + 1) / 2 - P.q N - P.h N)
      (fun i => (qhP P N p c).coeff i) (fun i => (dhP P N p c).coeff i)
      (fun i => (yP P N p c).coeff i) := by
  have hodd := odd_of_ne_two hp2
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  have hnC : P.n N + P.g N ≤ P.C N := by omega
  have hA : (P.b N + P.q N + 2 * P.g N) + P.n N = P.C N + P.g N := by omega
  have hSdeg := uS_natDegree_le hp2 hgn hnC c
  have hUdeg := uU_natDegree_le hp2 hgn hnC c
  have hSdvd : X ^ (P.b N + P.q N + 2 * P.g N) ∣ uS p (P.C N) (P.g N) (P.n N) c :=
    uS_dvd hp2 hgn hnC le_rfl (by omega) hA c (fun r hr => absurd r.isLt (by omega))
  have hUdvd := uU_dvd hp2 hgn hnC hA c
  have hWdeg := oddPrimeWeight_natDegree_le (p := p) hp2
  have hXq := natDegree_X_sub_one_pow_le' (p := p) (P.q N)
  have hXh := one_sub_X_pow_natDegree_le (p := p) (P.h N)
  -- degrees
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
  have dy : (yP P N p c).natDegree ≤ P.C N + (p - 1) / 2 := by
    unfold yP
    refine (natDegree_C_mul_le _ _).trans ?_
    have h1 : (X * (1 + X) ^ ((p - 1) / 2) * uS p (P.C N) (P.g N) (P.n N) c).natDegree ≤
        1 + (p - 1) / 2 + (P.C N - 1) := by
      refine natDegree_mul_le.trans (Nat.add_le_add ?_ hSdeg)
      refine natDegree_mul_le.trans (Nat.add_le_add ?_ (natDegree_one_add_X_pow_le' _))
      simp
    omega
  -- lower supports
  obtain ⟨T, hT⟩ := hSdvd
  obtain ⟨T', hT'⟩ := hUdvd
  have lq : X ^ (P.b N + P.q N + 2 * P.g N + 1) ∣ qhP P N p c :=
    ⟨(X - 1) ^ P.q N * (oddPrimeWeight p * (1 - X) ^ P.h N * T), by
      unfold qhP fP; rw [hT]; ring⟩
  have ld : X ^ (P.b N + P.q N + 2 * P.g N + 1) ∣ dhP P N p c :=
    ⟨(X - 1) ^ P.q N * ((1 - X) ^ P.h N * T'), by unfold dhP gP; rw [hT']; ring⟩
  have ly : X ^ (P.b N + P.q N + 2 * P.g N + 1) ∣ yP P N p c :=
    ⟨C ((-1 : ZMod p) ^ P.q N) * ((1 + X) ^ ((p - 1) / 2) * T), by
      unfold yP; rw [hT]; ring⟩
  -- identity K6
  obtain ⟨Z, hZ⟩ := comb_K6 hp2 hgn hnC (show P.L N + P.g N = P.C N by omega) hH2 c
  have hE : C (2 : ZMod p) * qhP P N p c - (C 2 - X ^ (2 * p)) * dhP P N p c =
      X ^ P.L N * ((X - 1) ^ P.q N * (1 - X) ^ P.h N * Z) := by
    unfold qhP fP dhP gP
    have h2 : (C (2 : ZMod p) : (ZMod p)[X]) = 2 := C_ofNat 2
    rw [h2]
    linear_combination ((X - 1) ^ P.q N * (1 - X) ^ P.h N) * hZ
  have hfr := frob_poly hp2 hH1 c
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
    exact X_pow_dvd_iff.mp ly i (by omega)
  · intro i hi
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt dy (by omega))
  · intro i hi
    have := congrArg (fun F : (ZMod p)[X] => F.coeff i) hE
    simp only [coeff_sub, coeff_C_mul, sub_mul, coeff_X_pow_mul', if_neg (not_le.mpr hi)] at this
    linear_combination this
  · intro i hi
    have := congrArg (fun F : (ZMod p)[X] => F.coeff i) hfr
    rw [one_sub_X_pow_mul_coeff _ _ _ hi, sub_mul, one_mul, coeff_sub, coeff_X_pow_mul'] at this
    exact this

end
end
end CatalanMeasure.GenD
