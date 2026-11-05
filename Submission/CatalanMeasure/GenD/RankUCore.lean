module
public import Submission.CatalanMeasure.GenD.RankCommon
public import Submission.CatalanMeasure.Parametric.PrimeDigitSampling
public import Submission.OAI.NumberTheory.Catalan.Arithmetic.OddPrimeWeight
@[expose] public section

/-!
# Theorem U, polynomial core (GenD, module 11a)

Everything here is over `ZMod p[X]` and natural numbers with linear hypotheses.
`C` is the reversal length, `g` the central row, `n` the number of rows, `ns` the number
of rows used, `L` the number of raw coordinates plus offset, `H` the degree bound, `h` the
power of `1-X`, `A` the lowest-degree bound.  No design appears.
-/

namespace CatalanMeasure.GenD
open Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
noncomputable section

section
variable {p : ℕ} [hp : Fact p.Prime]

/-- Reflected Chebyshev `T` of row `r`. -/
def uSv (p C g r : ℕ) : (ZMod p)[X] :=
  reflect (C - 1) (Chebyshev.T (ZMod p) ((r : ℤ) - g))

/-- Reflected Chebyshev `U` of row `r`. -/
def uUv (p C g r : ℕ) : (ZMod p)[X] :=
  reflect (C - 1) (Chebyshev.U (ZMod p) ((r : ℤ) - g - 1))

def uS (p C g n : ℕ) : (Fin n → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  combLin fun r : Fin n => uSv p C g r.val

def uU (p C g n : ℕ) : (Fin n → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  combLin fun r : Fin n => uUv p C g r.val

theorem uSv_natDegree_le (hp2 : p ≠ 2) {C g r n : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (hr : r < n) : (uSv p C g r).natDegree ≤ C - 1 := by
  have : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  unfold uSv
  refine natDegree_reflect_le.trans (max_le le_rfl ?_)
  rw [Chebyshev.natDegree_T]; omega

theorem uUv_natDegree_le (hp2 : p ≠ 2) {C g r n : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (hr : r < n) : (uUv p C g r).natDegree ≤ C - 1 := by
  have : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  unfold uUv
  refine natDegree_reflect_le.trans (max_le le_rfl ?_)
  rw [Chebyshev.natDegree_U]; omega

theorem uS_natDegree_le (hp2 : p ≠ 2) {C g n : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (c : Fin n → ZMod p) : (uS p C g n c).natDegree ≤ C - 1 := by
  simp only [uS, combLin_apply]
  apply natDegree_sum_le_of_forall_le
  intro r _
  exact (natDegree_C_mul_le _ _).trans (uSv_natDegree_le hp2 hgn hnC r.isLt)

theorem uU_natDegree_le (hp2 : p ≠ 2) {C g n : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (c : Fin n → ZMod p) : (uU p C g n c).natDegree ≤ C - 1 := by
  simp only [uU, combLin_apply]
  apply natDegree_sum_le_of_forall_le
  intro r _
  exact (natDegree_C_mul_le _ _).trans (uUv_natDegree_le hp2 hgn hnC r.isLt)

theorem uSv_dvd (hp2 : p ≠ 2) {C g r n ns A : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (hns : ns ≤ n) (hs : 2 * g + 1 ≤ ns) (hA : A + ns = C + g) (hr : r < ns) :
    X ^ A ∣ uSv p C g r := by
  have : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  have hd : (Chebyshev.T (ZMod p) ((r : ℤ) - g)).natDegree ≤ ns - 1 - g := by
    rw [Chebyshev.natDegree_T]; omega
  have := reflect_dvd_of_natDegree_le _ hd (show ns - 1 - g ≤ C - 1 by omega)
  exact (pow_dvd_pow X (show A ≤ C - 1 - (ns - 1 - g) by omega)).trans this

theorem uS_dvd (hp2 : p ≠ 2) {C g n ns A : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (hns : ns ≤ n) (hs : 2 * g + 1 ≤ ns) (hA : A + ns = C + g)
    (c : Fin n → ZMod p) (hc : ∀ r : Fin n, ns ≤ r.val → c r = 0) :
    X ^ A ∣ uS p C g n c := by
  simp only [uS, combLin_apply]
  refine Finset.dvd_sum fun r _ => ?_
  by_cases hr : r.val < ns
  · exact Dvd.dvd.mul_left (uSv_dvd hp2 hgn hnC hns hs hA hr) _
  · rw [hc r (by omega)]; simp

/-- Identity K for any row combination supported on the first `ns` rows. -/
theorem uComb_identity_K (hp2 : p ≠ 2) {C g n ns L : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (hns2 : ns ≤ 2 * p + 2 * g + 1) (hLC : L + g = C) (hpC : p + g < C)
    (c : Fin n → ZMod p) (hc : ∀ r : Fin n, ns ≤ r.val → c r = 0) :
    X ^ L ∣ (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * uU p C g n c -
      X * uS p C g n c := by
  have h : (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * uU p C g n c - X * uS p C g n c =
      ∑ r : Fin n, Polynomial.C (c r) * ((1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) *
        uUv p C g r.val - X * uSv p C g r.val) := by
    simp only [uU, uS, combLin_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [h]
  refine Finset.dvd_sum fun r _ => ?_
  by_cases hr : r.val < ns
  · have hr' := r.isLt
    refine Dvd.dvd.mul_left ?_ _
    exact row_identity_gen (m := (r.val : ℤ) - g) (E := C - 1) hp2 (by omega) (by omega) (by omega)
  · rw [hc r (by omega)]; simp

/-! ### Flag subspace and support -/

/-- Support, identity K and the Frobenius relation for `Q~ = X * Y` on the flag subspace. -/
theorem uQt_props (hp2 : p ≠ 2) {C g h n ns L H A : ℕ} (hgn : 2 * g < n) (hnC : n + g ≤ C)
    (hns : ns ≤ n) (hs : 2 * g + 1 ≤ ns) (hns2 : ns ≤ 2 * p + 2 * g + 1)
    (hLC : L + g = C) (hpC : p + g < C) (hHd : C + h = H) (hA : A + ns = C + g)
    (c : Fin n → ZMod p) (hc : ∀ r : Fin n, ns ≤ r.val → c r = 0) (Y : (ZMod p)[X])
    (hY : (1 - X) ^ h * uS p C g n c = (1 - X ^ 2) ^ ((p + 1) / 2) * Y) :
    (∀ i, i ≤ A → (X * Y).coeff i = 0) ∧
    (∀ i, H - p ≤ i → (X * Y).coeff i = 0) ∧
    (∀ k, k < L → ((1 - X) ^ h * uU p C g n c).coeff k = (X * Y).coeff k) ∧
    X * oddPrimeWeight p * ((1 - X) ^ h * uS p C g n c) = (1 - X ^ (2 * p)) * (X * Y) := by
  have hodd := odd_of_ne_two hp2
  have hcopA := isCoprime_X_pow_one_sub_X_sq (p := p) A ((p + 1) / 2)
  have hcopL := isCoprime_X_pow_one_sub_X_sq (p := p) L ((p + 1) / 2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hd : X ^ A ∣ (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * Y := by
      rw [← hY]
      exact Dvd.dvd.mul_left (uS_dvd hp2 hgn hnC hns hs hA c hc) _
    have hYA := X_pow_dvd_iff.mp (hcopA.dvd_of_dvd_mul_left hd)
    rcases i with _ | i
    · simp
    · rw [coeff_X_mul]; exact hYA i (by omega)
  · intro i hi
    by_cases hY0 : Y = 0
    · simp [hY0]
    have hA0 : ((1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2)) ≠ 0 := by
      intro h0
      have := congrArg natDegree h0
      rw [one_sub_X_sq_natDegree] at this
      simp at this
      omega
    have hdeg : ((1 - X) ^ h * uS p C g n c).natDegree ≤ H - 1 := by
      refine natDegree_mul_le.trans ?_
      have h1 := one_sub_X_pow_natDegree_le (p := p) h
      have := uS_natDegree_le hp2 hgn hnC c
      omega
    rw [hY, natDegree_mul hA0 hY0, one_sub_X_sq_natDegree] at hdeg
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_X_mul hY0]
    have : (p + 1) / 2 * 2 = p + 1 := by omega
    omega
  · intro k hk
    have hK := uComb_identity_K hp2 hgn hnC hns2 hLC hpC c hc
    have hK' : X ^ L ∣ (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) *
        ((1 - X) ^ h * uU p C g n c) - X * ((1 - X) ^ h * uS p C g n c) := by
      have : (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * ((1 - X) ^ h * uU p C g n c) -
          X * ((1 - X) ^ h * uS p C g n c) = (1 - X) ^ h *
          ((1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * uU p C g n c -
            X * uS p C g n c) := by ring
      rw [this]
      exact Dvd.dvd.mul_left hK _
    rw [hY] at hK'
    have : (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * ((1 - X) ^ h * uU p C g n c) -
        X * ((1 - X ^ 2) ^ ((p + 1) / 2) * Y) =
        (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) *
          ((1 - X) ^ h * uU p C g n c - X * Y) := by ring
    rw [this] at hK'
    have h24 := X_pow_dvd_iff.mp (hcopL.dvd_of_dvd_mul_left hK') k hk
    rw [coeff_sub] at h24
    exact sub_eq_zero.mp h24
  · rw [hY, oddPrimeWeight]
    have e : (X : (ZMod p)[X]) * (1 - X ^ 2) ^ ((p - 1) / 2) *
        ((1 - X ^ 2) ^ ((p + 1) / 2) * Y) =
        X * ((1 - X ^ 2) ^ ((p - 1) / 2 + (p + 1) / 2) * Y) := by
      rw [pow_add]; ring
    rw [e, show (p - 1) / 2 + (p + 1) / 2 = p by omega, one_sub_X_sq_pow_prime]
    ring

/-! ### The rank-one digit window -/

/-- The constant multiplying the single digit in the rank-one window. -/
def uKappa (p J : ℕ) [Fact p.Prime] : ZMod p :=
  palindromicRatResidue p (momentRatSigned (((1 : ℕ) : ℤ) - 1) J) -
    palindromicRatResidue p (momentRatSigned (((3 : ℕ) : ℤ) - 1) J) -
    (3 / 2 : ZMod p) * palindromicRatResidue p (zetaRat 1 J)

theorem digit_window {H L A j : ℕ} (F G Y : (ZMod p)[X]) (hH3 : 3 * p ≤ H)
    (hS1 : ∀ i, i ≤ A → (X * Y).coeff i = 0)
    (hS2 : ∀ i, H - p ≤ i → (X * Y).coeff i = 0)
    (hK : ∀ k, k < L → G.coeff k = (X * Y).coeff k)
    (hGH : ∀ i, H ≤ i → G.coeff i = 0)
    (hQ : X * oddPrimeWeight p * F = (1 - X ^ (2 * p)) * (X * Y))
    (hLA : L ≤ A + 1 + 2 * p) (hl1 : H ≤ 3 * p + j % p) (hl2 : j % p + 2 * p < L) :
    primeDigitPair H p j F G = G.coeff (p + j % p) * uKappa p (j / p) := by
  have hp2' := hp.out.two_le
  have hℓp : j % p < p := Nat.mod_lt _ hp.out.pos
  unfold primeDigitPair primeDigitSample
  rw [hQ]
  beta_reduce
  generalize j % p = ℓ at *
  generalize hq : (X * Y).coeff (p + ℓ) = q
  have hmul2 : ∀ v, 2 ≤ v → 2 * p ≤ v * p := fun v hv => Nat.mul_le_mul_right p hv
  have ha : ∀ v, 2 ≤ v → (X * Y).coeff (v * p + ℓ) = 0 := fun v hv =>
    hS2 _ (by have := hmul2 v hv; omega)
  have ha0 : (X * Y).coeff ℓ = 0 := hS1 _ (by omega)
  have hD1 : G.coeff (p + ℓ) = q := by
    rw [hK _ (by omega), hq]
  have hb : ∀ v, ((1 - X ^ (2 * p)) * (X * Y)).coeff (v * p + ℓ) =
      if v = 1 then q else if v = 3 then -q else 0 := by
    intro v
    rw [sub_mul, one_mul, coeff_sub, coeff_X_pow_mul']
    rcases Nat.lt_or_ge v 2 with hv | hv
    · have : ¬ 2 * p ≤ v * p + ℓ := by
        have : v * p ≤ 1 * p := Nat.mul_le_mul_right p (by omega)
        omega
      rw [if_neg this]
      interval_cases v
      · simp [ha0]
      · simp [hq]
    · have h2 : 2 * p ≤ v * p + ℓ := by have := hmul2 v hv; omega
      rw [if_pos h2, ha v hv]
      have e : v * p + ℓ - 2 * p = (v - 2) * p + ℓ := by
        rw [Nat.sub_mul]; have := hmul2 v hv; omega
      rw [e]
      by_cases h3 : v = 3
      · subst h3
        have : (3 - 2) * p + ℓ = p + ℓ := by omega
        rw [this, hq]; simp
      · by_cases h2' : v = 2
        · subst h2'; simp [ha0]
        · rw [ha (v - 2) (by omega)]
          simp [h2', h3]; omega
  have hs1 : ∑ v ∈ Finset.range (H + 1), ((1 - X ^ (2 * p)) * (X * Y)).coeff (v * p + ℓ) *
      palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) (j / p)) =
      q * palindromicRatResidue p (momentRatSigned (((1 : ℕ) : ℤ) - 1) (j / p)) -
      q * palindromicRatResidue p (momentRatSigned (((3 : ℕ) : ℤ) - 1) (j / p)) := by
    rw [Finset.sum_eq_add 1 3 (by norm_num)]
    · simp only [hb]; simp; ring
    · intro v _ hv
      rw [hb, if_neg hv.1, if_neg hv.2]; simp
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hs2 : ∑ v ∈ Finset.range H, G.coeff (v * p + ℓ) *
      palindromicRatResidue p (zetaRat v (j / p)) =
      q * palindromicRatResidue p (zetaRat 1 (j / p)) := by
    rw [Finset.sum_eq_single 1]
    · simp [hD1]
    · intro v _ hv
      have : G.coeff (v * p + ℓ) = 0 := by
        rcases Nat.lt_or_ge v 3 with h3 | h3
        · interval_cases v
          · rw [hK _ (by omega)]; simpa using ha0
          · exact absurd rfl hv
          · rw [hK _ (by have := hmul2 2 le_rfl; omega)]; exact ha 2 le_rfl
        · apply hGH
          have := Nat.mul_le_mul_right p h3
          omega
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [hs1, hs2, hD1]
  unfold uKappa
  ring

end

end
end CatalanMeasure.GenD
