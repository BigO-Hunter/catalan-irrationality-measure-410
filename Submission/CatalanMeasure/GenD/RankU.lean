module
public import Submission.CatalanMeasure.GenD.RankUCore
public import Submission.CatalanMeasure.Parametric.RawDigitFunctional
public import Submission.CatalanMeasure.Parametric.SecondaryTentFilteredResponse
@[expose] public section

/-!
# Theorem U for a general design (GenD, module 11)

For `P : Parameters`, `N > 0` and an odd prime `p` with `H < p^2` satisfying the linear window
`2h ≤ p+1`, `L ≤ 3p ≤ H`, `n+q+g+h ≤ 3p`, `2p ≤ n+q`, the left kernel of the filtered scaled
residue matrix has dimension at least `min n (2p+2g+1) - g - 2p - 1`.
At the design `(20,3,1,2,1)` and `8N ≤ p ≤ 9N` this is `18N - 2p - 1`.
-/

namespace CatalanMeasure.GenD
open Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
noncomputable section

/-- The linear window of Theorem U. -/
structure UWindow (P : Parameters) (N p : ℕ) : Prop where
  hh : 2 * P.h N ≤ p + 1
  hL : P.n N + P.b N + P.q N ≤ 3 * p
  hH : 3 * p ≤ P.n N + P.b N + P.q N + P.g N + P.h N
  hA : P.n N + P.q N + P.g N + P.h N ≤ 3 * p
  hB : 2 * p ≤ P.n N + P.q N

/-- The number of rows used by Theorem U. -/
def uStar (P : Parameters) (N p : ℕ) : ℕ := min (P.n N) (2 * p + 2 * P.g N + 1)

theorem reversedRow_eq_reflect (E : ℕ) (F : ℤ[X]) (hF : F.natDegree < E) :
    reversedRow E F = reflect (E - 1) F := by
  ext i
  rw [reversedRow_coeff, coeff_reflect]
  by_cases hi : i < E
  · simp only [hi, ite_true, revAt_le (show i ≤ E - 1 by omega)]
  · simp only [hi, ite_false, revAt_eq_self_of_lt (show E - 1 < i by omega)]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem primeDigitSample_comb {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (H p ell : ℕ) (f : ℕ → R) (Q : ι → R[X]) (c : ι → R) :
    primeDigitSample H p ell f (∑ i, Polynomial.C (c i) * Q i) =
      ∑ i, c i * primeDigitSample H p ell f (Q i) := by
  unfold primeDigitSample
  simp only [finsetSum_coeff, coeff_C_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => ?_
  ring

theorem primeDigitPair_comb {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] (H j : ℕ)
    (F G : ι → (ZMod p)[X]) (c : ι → ZMod p) :
    primeDigitPair H p j (∑ i, Polynomial.C (c i) * F i) (∑ i, Polynomial.C (c i) * G i) =
      ∑ i, c i * primeDigitPair H p j (F i) (G i) := by
  unfold primeDigitPair
  have e : (X : (ZMod p)[X]) * oddPrimeWeight p * (∑ i, Polynomial.C (c i) * F i) =
      ∑ i, Polynomial.C (c i) * (X * oddPrimeWeight p * F i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e, primeDigitSample_comb, primeDigitSample_comb, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

section
variable {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]

/-! ### Row polynomials modulo `p` -/

theorem rowP_map_gen (hP : Admissible P) (hN : 0 < N) {r : ℕ} (hr : r < P.n N) :
    (rowP P N r).map (Int.castRingHom (ZMod p)) =
      (1 - X) ^ P.h N * uSv p (P.C N) (P.g N) r := by
  have hdeg : (Chebyshev.T ℤ (rowDistance P N r : ℤ)).natDegree < P.C N := by
    rw [Chebyshev.natDegree_T, Int.natAbs_natCast]; exact rowDistance_lt_C hP hN hr
  have hd : rowDistance P N r = ((r : ℤ) - P.g N).natAbs := rfl
  unfold CatalanMeasure.Parametric.rowP uSv
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, reversedRow_eq_reflect _ _ hdeg, ← reflect_map, Chebyshev.map_T, hd,
    Chebyshev.T_natAbs]

theorem rowD_map_gen (hP : Admissible P) (hN : 0 < N) {r : ℕ} (hr : r < P.n N) :
    (rowD P N r).map (Int.castRingHom (ZMod p)) =
      (1 - X) ^ P.h N * uUv p (P.C N) (P.g N) r := by
  have hd : rowDistance P N r = (rowOffset P N r).natAbs := rfl
  have h1 := rowDistance_lt_C hP hN hr
  have hdeg : (Chebyshev.U ℤ ((rowDistance P N r : ℤ) - 1)).natDegree < P.C N := by
    rw [Chebyshev.natDegree_U]; omega
  unfold CatalanMeasure.Parametric.rowD uUv
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_C,
    reversedRow_eq_reflect _ _ hdeg, ← reflect_map, Chebyshev.map_U]
  have e : ((r : ℤ) - P.g N) = rowOffset P N r := rfl
  rw [e, hd]
  generalize rowOffset P N r = m
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have hs : Int.sign m = -1 := Int.sign_eq_neg_one_of_neg hm
    have ha : ((m.natAbs : ℕ) : ℤ) = -m := by omega
    have e : Chebyshev.U (ZMod p) (m - 1) = -Chebyshev.U (ZMod p) (-m - 1) := by
      simpa using Chebyshev.U_neg_sub_one (ZMod p) (-m)
    rw [hs, ha, e, reflect_neg]
    simp only [map_neg, map_one]
    ring
  · subst hm
    simp [Chebyshev.U_neg_one]
  · have hs : Int.sign m = 1 := Int.sign_eq_one_of_pos hm
    have ha : ((m.natAbs : ℕ) : ℤ) = m := by omega
    rw [hs, ha]
    simp

/-! ### Raw residue response -/

/-- Raw residue response of a row combination at column `j`. -/
def uResp (P : Parameters) (N p j : ℕ) [Fact p.Prime] :
    (Fin (P.n N) → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun c := ∑ r : Fin (P.n N),
    palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat P 0 N r.val j) * c r
  map_add' c d := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.mul_sum, mul_left_comm]

theorem uResp_eq (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {j : ℕ} (hj : j < P.H N) (c : Fin (P.n N) → ZMod p) :
    uResp P N p j c = primeDigitPair (P.H N) p j
      ((1 - X) ^ P.h N * uS p (P.C N) (P.g N) (P.n N) c)
      ((1 - X) ^ P.h N * uU p (P.C N) (P.g N) (P.n N) c) := by
  have h1 : (1 - X : (ZMod p)[X]) ^ P.h N * uS p (P.C N) (P.g N) (P.n N) c =
      ∑ r : Fin (P.n N), Polynomial.C (c r) *
        (rowP P N r.val).map (Int.castRingHom (ZMod p)) := by
    show (1 - X : (ZMod p)[X]) ^ P.h N * combLin (fun r : Fin (P.n N) => uSv p (P.C N) (P.g N) r.val) c = _
    rw [combLin_mul_left, combLin_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [rowP_map_gen hP hN r.isLt]
  have h2 : (1 - X : (ZMod p)[X]) ^ P.h N * uU p (P.C N) (P.g N) (P.n N) c =
      ∑ r : Fin (P.n N), Polynomial.C (c r) *
        (rowD P N r.val).map (Int.castRingHom (ZMod p)) := by
    show (1 - X : (ZMod p)[X]) ^ P.h N * combLin (fun r : Fin (P.n N) => uUv p (P.C N) (P.g N) r.val) c = _
    rw [combLin_mul_left, combLin_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [rowD_map_gen hP hN r.isLt]
  rw [h1, h2, primeDigitPair_comb]
  unfold uResp
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hz : (((p : ℚ) * 0).den : ZMod p) ≠ 0 := by simp
  rw [rawEntry_primeDigitPair hP hN hp2 hH hj 0 hz, mul_comm]

/-! ### Constraints -/

def uCost (P : Parameters) (N p ns : ℕ) : Fin 6 → ℕ
  | 0 => (p + 1) / 2 - P.h N
  | 1 => (p + 1) / 2
  | 2 => 2 * (P.H N - 3 * p)
  | 3 => (P.L N - 2 * p) - (P.H N - 3 * p)
  | 4 => 2 * (p - (P.L N - 2 * p))
  | 5 => P.n N - ns

/-- Taylor coefficient functionals at `1`. -/
def uFlagUp (P : Parameters) (N p : ℕ) [Fact p.Prime] : (Fin (P.n N) → ZMod p) →ₗ[ZMod p]
    (Fin ((p + 1) / 2 - P.h N) → ZMod p) :=
  LinearMap.pi fun i => (lcoeff (ZMod p) (i : ℕ)).comp
    ((taylor (1 : ZMod p)).comp (uS p (P.C N) (P.g N) (P.n N)))

/-- Taylor coefficient functionals at `-1`. -/
def uFlagDown (P : Parameters) (N p : ℕ) [Fact p.Prime] : (Fin (P.n N) → ZMod p) →ₗ[ZMod p]
    (Fin ((p + 1) / 2) → ZMod p) :=
  LinearMap.pi fun i => (lcoeff (ZMod p) (i : ℕ)).comp
    ((taylor (-1 : ZMod p)).comp (uS p (P.C N) (P.g N) (P.n N)))

def uConstraint (P : Parameters) (N p ns : ℕ) [Fact p.Prime] :
    ∀ i : Fin 6, (Fin (P.n N) → ZMod p) →ₗ[ZMod p] (Fin (uCost P N p ns i) → ZMod p)
  | 0 => uFlagUp P N p
  | 1 => uFlagDown P N p
  | 2 => LinearMap.pi fun a : Fin (2 * (P.H N - 3 * p)) =>
      uResp P N p (((a.val % 2) + 1) * p + a.val / 2)
  | 3 => LinearMap.pi fun a : Fin ((P.L N - 2 * p) - (P.H N - 3 * p)) =>
      (lcoeff (ZMod p) (p + (P.H N - 3 * p) + a.val)).comp
        ((LinearMap.mulLeft (ZMod p) ((1 - X : (ZMod p)[X]) ^ P.h N)).comp
          (uU p (P.C N) (P.g N) (P.n N)))
  | 4 => LinearMap.pi fun a : Fin (2 * (p - (P.L N - 2 * p))) =>
      uResp P N p ((a.val % 2) * p + (P.L N - 2 * p) + a.val / 2)
  | 5 => LinearMap.pi fun a : Fin (P.n N - ns) =>
      LinearMap.proj (R := ZMod p) (⟨ns + a.val, by have := a.isLt; omega⟩ : Fin (P.n N))

theorem uCost_sum (hW : UWindow P N p) (hodd : p % 2 = 1) {ns : ℕ} (hns : ns ≤ P.n N) :
    ∑ i, uCost P N p ns i = 2 * p + 1 + P.g N + (P.n N - ns) := by
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  have hHd : P.H N = P.C N + P.h N := rfl
  have h1 := hW.hh
  have h2 := hW.hL
  have h3 := hW.hH
  have h4 := hW.hA
  have h5 := hW.hB
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, uCost, Fin.isValue,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  norm_num
  omega

/-! ### Kernel response and rank -/

theorem u_kernel_response (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hW : UWindow P N p) {ns : ℕ} (hns : ns ≤ P.n N) (hs : 2 * P.g N + 1 ≤ ns)
    (hns2 : ns ≤ 2 * p + 2 * P.g N + 1)
    (c : Fin (P.n N) → ZMod p) (hc : ∀ i, uConstraint P N p ns i c = 0)
    {j : ℕ} (hj1 : P.b N ≤ j) (hj2 : j < P.L N) : uResp P N p j c = 0 := by
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  have hHd : P.H N = P.C N + P.h N := rfl
  have hgn := two_g_lt_n hP hN
  obtain ⟨wh, wL, wH, wA, wB⟩ := hW
  have hodd := odd_of_ne_two hp2
  have hp2' := hp.out.two_le
  have hcs : ∀ r : Fin (P.n N), ns ≤ r.val → c r = 0 := by
    intro r hr
    have h5 : c ⟨ns + (r.val - ns), by have := r.isLt; omega⟩ = 0 :=
      congrFun (hc 5) ⟨r.val - ns, by have := r.isLt; simp only [uCost]; omega⟩
    have e : (⟨ns + (r.val - ns), by have := r.isLt; omega⟩ : Fin (P.n N)) = r :=
      Fin.ext (by simp only; omega)
    rwa [e] at h5
  have f0 : uFlagUp P N p c = 0 := hc 0
  have f1 : uFlagDown P N p c = 0 := hc 1
  obtain ⟨Y, hY⟩ := flag_dvd hp2 (by omega : P.h N ≤ (p + 1) / 2)
    (uS p (P.C N) (P.g N) (P.n N) c)
    (fun i hi => by have := congrFun f0 ⟨i, hi⟩; simpa [uFlagUp] using this)
    (fun i hi => by have := congrFun f1 ⟨i, hi⟩; simpa [uFlagDown] using this)
  obtain ⟨hS1, hS2, hK, hQ⟩ := uQt_props hp2 (C := P.C N) (g := P.g N) (h := P.h N)
    (n := P.n N) (ns := ns) (L := P.L N) (H := P.H N) (A := P.C N + P.g N - ns)
    hgn (by omega) hns hs hns2 (by omega) (by omega) (by omega) (by omega) c hcs Y hY
  have hGH : ∀ i, P.H N ≤ i →
      ((1 - X : (ZMod p)[X]) ^ P.h N * uU p (P.C N) (P.g N) (P.n N) c).coeff i = 0 := by
    intro i hi
    apply coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt natDegree_mul_le ?_
    have h1 := one_sub_X_pow_natDegree_le (p := p) (P.h N)
    have := uU_natDegree_le hp2 hgn (by omega : P.n N + P.g N ≤ P.C N) c
    omega
  have hjd := Nat.div_add_mod j p
  have hℓp : j % p < p := Nat.mod_lt _ hp.out.pos
  generalize hJ : j / p = J at hjd
  generalize hL : j % p = ℓ at hjd hℓp
  have hJ3 : J < 3 := by
    by_contra h
    have := Nat.mul_le_mul_left p (show 3 ≤ J by omega)
    omega
  by_cases hA : ℓ < P.H N - 3 * p
  · have hJ0 : J ≠ 0 := by rintro rfl; omega
    have hJ' : J = 1 ∨ J = 2 := by omega
    rcases hJ' with rfl | rfl
    · have key : uResp P N p (((2 * ℓ + 0) % 2 + 1) * p + (2 * ℓ + 0) / 2) c = 0 :=
        congrFun (hc 2) ⟨2 * ℓ + 0, by simp only [uCost]; omega⟩
      have h1 : (2 * ℓ + 0) % 2 = 0 := by omega
      have h2 : (2 * ℓ + 0) / 2 = ℓ := by omega
      rw [h1, h2] at key
      rwa [show j = (0 + 1) * p + ℓ by omega]
    · have key : uResp P N p (((2 * ℓ + 1) % 2 + 1) * p + (2 * ℓ + 1) / 2) c = 0 :=
        congrFun (hc 2) ⟨2 * ℓ + 1, by simp only [uCost]; omega⟩
      have h1 : (2 * ℓ + 1) % 2 = 1 := by omega
      have h2 : (2 * ℓ + 1) / 2 = ℓ := by omega
      rw [h1, h2] at key
      rwa [show j = (1 + 1) * p + ℓ by omega]
  by_cases hB : ℓ < P.L N - 2 * p
  · have hw : uResp P N p j c = ((1 - X : (ZMod p)[X]) ^ P.h N *
        uU p (P.C N) (P.g N) (P.n N) c).coeff (p + j % p) * uKappa p (j / p) := by
      rw [uResp_eq hP hN hp2 hH (by omega) c]
      exact digit_window (H := P.H N) (L := P.L N) (A := P.C N + P.g N - ns) (j := j) _ _ Y
        (by omega) hS1 hS2 hK hGH hQ (by omega) (by rw [hL]; omega) (by rw [hL]; omega)
    rw [hw, hL]
    have key : ((1 - X : (ZMod p)[X]) ^ P.h N * uU p (P.C N) (P.g N) (P.n N) c).coeff
        (p + (P.H N - 3 * p) + (ℓ - (P.H N - 3 * p))) = 0 :=
      congrFun (hc 3) ⟨ℓ - (P.H N - 3 * p), by simp only [uCost]; omega⟩
    rw [show p + ℓ = p + (P.H N - 3 * p) + (ℓ - (P.H N - 3 * p)) by omega, key, zero_mul]
  · have hJ' : J = 0 ∨ J = 1 := by
      by_contra h
      have := Nat.mul_le_mul_left p (show 2 ≤ J by omega)
      omega
    rcases hJ' with rfl | rfl
    · have key : uResp P N p (((2 * (ℓ - (P.L N - 2 * p)) + 0) % 2) * p + (P.L N - 2 * p) +
          (2 * (ℓ - (P.L N - 2 * p)) + 0) / 2) c = 0 :=
        congrFun (hc 4) ⟨2 * (ℓ - (P.L N - 2 * p)) + 0, by simp only [uCost]; omega⟩
      have h1 : (2 * (ℓ - (P.L N - 2 * p)) + 0) % 2 = 0 := by omega
      have h2 : (2 * (ℓ - (P.L N - 2 * p)) + 0) / 2 = ℓ - (P.L N - 2 * p) := by omega
      rw [h1, h2] at key
      rwa [show j = 0 * p + (P.L N - 2 * p) + (ℓ - (P.L N - 2 * p)) by omega]
    · have key : uResp P N p (((2 * (ℓ - (P.L N - 2 * p)) + 1) % 2) * p + (P.L N - 2 * p) +
          (2 * (ℓ - (P.L N - 2 * p)) + 1) / 2) c = 0 :=
        congrFun (hc 4) ⟨2 * (ℓ - (P.L N - 2 * p)) + 1, by simp only [uCost]; omega⟩
      have h1 : (2 * (ℓ - (P.L N - 2 * p)) + 1) % 2 = 1 := by omega
      have h2 : (2 * (ℓ - (P.L N - 2 * p)) + 1) / 2 = ℓ - (P.L N - 2 * p) := by omega
      rw [h1, h2] at key
      rwa [show j = 1 * p + (P.L N - 2 * p) + (ℓ - (P.L N - 2 * p)) by omega]

/-- **Theorem U (general design).** With `ns = min n (2p+2g+1)`, the filtered scaled residue
matrix has rank at most `n - (ns - g - 2p - 1)`; equivalently its left nullity is at least
`ns - g - 2p - 1`. -/
theorem u_rank (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hW : UWindow P N p) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val)).rank +
        (uStar P N p - P.g N - 2 * p - 1) ≤ P.n N := by
  have hodd := odd_of_ne_two hp2
  have hgn := two_g_lt_n hP hN
  have hns : uStar P N p ≤ P.n N := min_le_left _ _
  have hs : 2 * P.g N + 1 ≤ uStar P N p := by unfold uStar; omega
  have hns2 : uStar P N p ≤ 2 * p + 2 * P.g N + 1 := min_le_right _ _
  have hzp : (((p : ℚ) * 0).den : ZMod p) ≠ 0 := by simp
  have hq : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
  let J : LinearMap.ker (secondaryTentConstraintMap (uCost P N p (uStar P N p))
      (uConstraint P N p (uStar P N p))) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
    Submodule.subtype _
  have hr := secondaryTent_rank_of_raw_polynomial_responses (P := P) (p := p) (N := N)
    (V := Fin (P.n N) → ZMod p) hp2 hH 0 hzp (uCost P N p (uStar P N p))
    (uConstraint P N p (uStar P N p)) J Subtype.val_injective (by
      intro v
      refine ⟨0, by rw [natDegree_zero]; exact hq, ?_⟩
      intro j hj1 hj2
      have hv := (secondaryTentConstraintMap_eq_zero_iff _ _ v.1).mp v.2
      have := u_kernel_response hP hN hp2 hH hW hns hs hns2 v.1 hv hj1 hj2
      rw [eval_zero]
      exact this)
  rw [uCost_sum hW hodd hns, Module.finrank_fin_fun] at hr
  have e : P.n N - (2 * p + 1 + P.g N + (P.n N - uStar P N p)) =
      uStar P N p - P.g N - 2 * p - 1 := by omega
  rw [e] at hr
  exact hr

/-- Nullity form of Theorem U. -/
theorem u_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hW : UWindow P N p) :
    uStar P N p - P.g N - 2 * p - 1 ≤ P.n N -
      (scaledResidueMatrix (p := p)
        (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val)).rank := by
  have := u_rank hP hN hp2 hH hW
  omega

end

end
end CatalanMeasure.GenD
