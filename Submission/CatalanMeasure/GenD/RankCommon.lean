module
public import Submission.CatalanMeasure.Parametric.ChebyshevPrime
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Polynomial.Chebyshev
@[expose] public section

/-!
# Design-free layer for the rank-deficiency theorems (GenD, module 9)

Statements are over `ZMod p[X]` and natural numbers only.  No design appears.

* reflection of `Polynomial.reflect` against products and `(X^2-1)^h`;
* the Chebyshev reflection `T_{p-m} = X^p T_m - (X^2-1)^((p+1)/2) U_{m-1}` in characteristic `p`;
* the row identity `X^L ∣ (1-X^2)^ν reflect E U_{m-1} - X reflect E T_m`;
* flag conditions (Taylor coefficients at `±1`) and divisibility by `(1-X^2)^ν`;
* Frobenius `(1-X^2)^p = 1-X^(2p)` and degree facts.
-/

namespace CatalanMeasure.GenD
open Polynomial
noncomputable section

/-! ### Reflection -/

theorem reflect_shift {R : Type*} [Semiring R] (f : R[X]) {n : ℕ} (hf : f.natDegree ≤ n)
    (k : ℕ) : reflect (n + k) f = X ^ k * reflect n f := by
  have h := reflect_mul f (1 : R[X]) (F := n) (G := k) hf (by simp)
  rw [mul_one, reflect_one] at h
  rw [h, X_pow_mul]

theorem reflect_pow_two {R : Type*} [CommRing R] (h : ℕ) :
    reflect (2 * h) ((X ^ 2 - 1 : R[X]) ^ h) = (1 - X ^ 2) ^ h := by
  induction h with
  | zero => simp [reflect_one]
  | succ h ih =>
    have hd : ((X ^ 2 - 1 : R[X]) ^ h).natDegree ≤ 2 * h := by
      calc _ ≤ h * (X ^ 2 - 1 : R[X]).natDegree := natDegree_pow_le
        _ ≤ h * 2 := Nat.mul_le_mul_left _ (by compute_degree)
        _ = 2 * h := by ring
    have hd2 : (X ^ 2 - 1 : R[X]).natDegree ≤ 2 := by compute_degree
    have := reflect_mul ((X ^ 2 - 1 : R[X]) ^ h) (X ^ 2 - 1 : R[X]) hd hd2
    have hr2 : reflect 2 (X ^ 2 - 1 : R[X]) = 1 - X ^ 2 := by
      rw [reflect_sub, reflect_monomial, reflect_one]
      simp [revAt_le]
    rw [← pow_succ, show 2 * h + 2 = 2 * (h + 1) by ring] at this
    rw [this, ih, hr2]
    exact (pow_succ _ _).symm

theorem reflect_dvd_of_natDegree_le {R : Type*} [Semiring R] (f : R[X]) {d E : ℕ}
    (hf : f.natDegree ≤ d) (hd : d ≤ E) : X ^ (E - d) ∣ reflect E f := by
  have := reflect_shift f hf (E - d)
  rw [show d + (E - d) = E by omega] at this
  rw [this]
  exact dvd_mul_right _ _

/-! ### Chebyshev reflection in characteristic p -/

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2p : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2p)

theorem odd_of_ne_two (hp2 : p ≠ 2) : p % 2 = 1 := by
  rcases hp.out.eq_two_or_odd with h | h
  · exact absurd h hp2
  · exact h

/-- `T_{p-m} = X^p T_m - (X^2-1)^((p+1)/2) U_{m-1}` in characteristic `p`. -/
theorem chebyshev_reflect (hp2 : p ≠ 2) (m : ℤ) :
    Chebyshev.T (ZMod p) ((p : ℤ) - m) =
      X ^ p * Chebyshev.T (ZMod p) m - (X ^ 2 - 1) ^ ((p + 1) / 2) *
        Chebyshev.U (ZMod p) (m - 1) := by
  have hT := CatalanMeasure.Parametric.chebyshev_T_prime (p := p) hp2
  have hU := CatalanMeasure.Parametric.chebyshev_U_prime (p := p) hp2
  have hodd := odd_of_ne_two hp2
  have hh : (p + 1) / 2 = (p - 1) / 2 + 1 := by omega
  set G : ℤ → (ZMod p)[X] := fun m =>
    X ^ p * Chebyshev.T (ZMod p) m - (X ^ 2 - 1) ^ ((p + 1) / 2) *
        Chebyshev.U (ZMod p) (m - 1) - Chebyshev.T (ZMod p) ((p : ℤ) - m) with hG
  have hrec : ∀ m : ℤ, G (m + 2) = 2 * X * G (m + 1) - G m := by
    intro m
    have t1 := Chebyshev.T_add_two (ZMod p) m
    have u1 := Chebyshev.U_add_two (ZMod p) (m - 1)
    have t3 := Chebyshev.T_sub_two (ZMod p) ((p : ℤ) - m)
    rw [show m - 1 + 2 = m + 1 by ring, show m - 1 + 1 = m by ring] at u1
    have e1 : (p : ℤ) - (m + 2) = (p : ℤ) - m - 2 := by ring
    have e2 : (p : ℤ) - (m + 1) = (p : ℤ) - m - 1 := by ring
    have e3 : m + 1 - 1 = m := by ring
    have e4 : m + 2 - 1 = m + 1 := by ring
    simp only [hG, e1, e2, e3, e4]
    linear_combination (X ^ p : (ZMod p)[X]) * t1 - (X ^ 2 - 1) ^ ((p + 1) / 2) * u1 - t3
  have h0 : G 0 = 0 := by
    simp [hG, hT, Chebyshev.T_zero, Chebyshev.U_neg_one]
  have h1 : G 1 = 0 := by
    have a1 := Chebyshev.T_eq_X_mul_T_sub_pol_U (ZMod p) ((p : ℤ) - 1)
    have a2 := Chebyshev.T_sub_one (ZMod p) (p : ℤ)
    rw [show (p : ℤ) - 1 + 2 = (p : ℤ) + 1 by ring,
      show (p : ℤ) - 1 + 1 = (p : ℤ) by ring] at a1
    rw [hT] at a1 a2
    rw [hU] at a1
    simp only [hG, Chebyshev.T_one, Chebyshev.U_zero, sub_self, hh, pow_succ]
    linear_combination (-1 : (ZMod p)[X]) * a2 + a1
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
  have := key m
  simp only [hG] at this
  linear_combination -this

/-- Reflected form of the Chebyshev reflection (identity K for one row). -/
theorem chebyshev_reflect_row (hp2 : p ≠ 2) (E : ℕ) (m : ℤ)
    (hU : (Chebyshev.U (ZMod p) (m - 1)).natDegree ≤ E)
    (hT : (Chebyshev.T (ZMod p) m).natDegree ≤ E)
    (hTp : (Chebyshev.T (ZMod p) ((p : ℤ) - m)).natDegree ≤ E) :
    (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * reflect E (Chebyshev.U (ZMod p) (m - 1)) -
        X * reflect E (Chebyshev.T (ZMod p) m) =
      -(X ^ (p + 1) * reflect E (Chebyshev.T (ZMod p) ((p : ℤ) - m))) := by
  have hodd := odd_of_ne_two hp2
  have h2h : 2 * ((p + 1) / 2) = p + 1 := by omega
  have e : (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2) * Chebyshev.U (ZMod p) (m - 1) +
      Chebyshev.T (ZMod p) ((p : ℤ) - m) = X ^ p * Chebyshev.T (ZMod p) m := by
    linear_combination chebyshev_reflect hp2 m
  have hdeg1 : ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2)).natDegree ≤ p + 1 := by
    calc _ ≤ ((p + 1) / 2) * (X ^ 2 - 1 : (ZMod p)[X]).natDegree := natDegree_pow_le
      _ ≤ ((p + 1) / 2) * 2 := Nat.mul_le_mul_left _ (by compute_degree)
      _ = p + 1 := by omega
  have hx : ((X : (ZMod p)[X]) ^ p).natDegree ≤ p := by simp
  have r := congrArg (reflect (p + 1 + E)) e
  rw [reflect_add] at r
  have a1 := reflect_mul ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2))
    (Chebyshev.U (ZMod p) (m - 1)) hdeg1 hU
  have a2 : reflect (p + 1 + E) (Chebyshev.T (ZMod p) ((p : ℤ) - m)) =
      X ^ (p + 1) * reflect E (Chebyshev.T (ZMod p) ((p : ℤ) - m)) := by
    rw [add_comm (p + 1) E]
    exact reflect_shift _ hTp (p + 1)
  have a3 : reflect (p + 1 + E) (X ^ p * Chebyshev.T (ZMod p) m) =
      X * reflect E (Chebyshev.T (ZMod p) m) := by
    rw [Nat.add_assoc, reflect_mul ((X : (ZMod p)[X]) ^ p) (Chebyshev.T (ZMod p) m) hx
      (show (Chebyshev.T (ZMod p) m).natDegree ≤ 1 + E by omega), reflect_monomial,
      revAt_le le_rfl, Nat.sub_self, pow_zero, one_mul, add_comm 1 E,
      reflect_shift _ hT 1, pow_one]
  have a5 : reflect (2 * ((p + 1) / 2)) ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2)) =
      (1 - X ^ 2) ^ ((p + 1) / 2) := reflect_pow_two _
  rw [h2h] at a5
  rw [a1, a5, a2, a3] at r
  linear_combination r

/-- Generic row identity: with `|m| ≤ E`, `|p-m| ≤ E` and `L + |p-m| ≤ p + 1 + E`,
`X^L` divides `(1-X^2)^ν reflect E U_{m-1} - X reflect E T_m`. -/
theorem row_identity_gen (hp2 : p ≠ 2) {E L : ℕ} {m : ℤ}
    (hm : m.natAbs ≤ E) (hpm : ((p : ℤ) - m).natAbs ≤ E)
    (hL : L + ((p : ℤ) - m).natAbs ≤ p + 1 + E) :
    X ^ L ∣ (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) *
        reflect E (Chebyshev.U (ZMod p) (m - 1)) -
      X * reflect E (Chebyshev.T (ZMod p) m) := by
  have : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  have hU : (Chebyshev.U (ZMod p) (m - 1)).natDegree ≤ E := by
    rw [Chebyshev.natDegree_U]; omega
  have hT : (Chebyshev.T (ZMod p) m).natDegree ≤ E := by
    rw [Chebyshev.natDegree_T]; omega
  have hTp : (Chebyshev.T (ZMod p) ((p : ℤ) - m)).natDegree ≤ E := by
    rw [Chebyshev.natDegree_T]; omega
  rw [chebyshev_reflect_row hp2 E m hU hT hTp, dvd_neg]
  have hd : (Chebyshev.T (ZMod p) ((p : ℤ) - m)).natDegree ≤ ((p : ℤ) - m).natAbs := by
    rw [Chebyshev.natDegree_T]
  have hdv := reflect_dvd_of_natDegree_le _ hd hpm
  refine (pow_dvd_pow X (show L ≤ p + 1 + (E - ((p : ℤ) - m).natAbs) by omega)).trans ?_
  rw [pow_add]
  exact mul_dvd_mul (dvd_refl _) hdv

/-! ### Flags and Frobenius -/

theorem dvd_of_taylor_coeff_zero {R : Type*} [CommRing R] (a : R) (k : ℕ) (f : R[X])
    (h : ∀ i < k, (taylor a f).coeff i = 0) : (X - C a) ^ k ∣ f := by
  obtain ⟨g, hg⟩ := X_pow_dvd_iff.mpr h
  refine ⟨g.comp (X - C a), ?_⟩
  have h1 : f = (taylor a f).comp (X - C a) := by
    rw [taylor_apply, comp_assoc]
    simp
  conv_lhs => rw [h1, hg]
  rw [mul_comp, pow_comp, X_comp]

/-- Flags: vanishing of `ν - h` Taylor coefficients at `1` and `ν = (p+1)/2` at `-1`
give `(1-X)^h S = (1-X^2)^ν Y`. -/
theorem flag_dvd (hp2 : p ≠ 2) {h : ℕ} (hh : h ≤ (p + 1) / 2) (S : (ZMod p)[X])
    (h1 : ∀ i < (p + 1) / 2 - h, (taylor (1 : ZMod p) S).coeff i = 0)
    (h2 : ∀ i < (p + 1) / 2, (taylor (-1 : ZMod p) S).coeff i = 0) :
    ∃ Y : (ZMod p)[X], (1 - X) ^ h * S = (1 - X ^ 2) ^ ((p + 1) / 2) * Y := by
  have hu : (X - C (1 : ZMod p)) ^ ((p + 1) / 2 - h) ∣ S :=
    dvd_of_taylor_coeff_zero _ _ _ h1
  have hd : (X - C (-1 : ZMod p)) ^ ((p + 1) / 2) ∣ S :=
    dvd_of_taylor_coeff_zero _ _ _ h2
  have hcop : IsCoprime ((X - C (1 : ZMod p)) ^ ((p + 1) / 2 - h))
      ((X - C (-1 : ZMod p)) ^ ((p + 1) / 2)) := by
    apply IsCoprime.pow
    have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
    refine ⟨-C (2 : ZMod p)⁻¹, C (2 : ZMod p)⁻¹, ?_⟩
    have : (C (2 : ZMod p)⁻¹ * C 2 : (ZMod p)[X]) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ h2, C_1]
    have h2c : (2 : (ZMod p)[X]) = C 2 := (C_ofNat (R := ZMod p) 2).symm
    simp only [map_neg, map_one]
    linear_combination this + (C (2 : ZMod p)⁻¹) * h2c
  obtain ⟨Z, hZ⟩ := hcop.mul_dvd hu hd
  generalize hk : (p + 1) / 2 - h = k at hZ
  have hk2 : (p + 1) / 2 = h + k := by omega
  refine ⟨(-1) ^ k * Z, ?_⟩
  have e1 : (X - C (1 : ZMod p)) = -(1 - X) := by simp
  have e2 : (X - C (-1 : ZMod p)) = 1 + X := by
    rw [map_neg, map_one]; ring
  have e3 : (1 - X ^ 2 : (ZMod p)[X]) = (1 - X) * (1 + X) := by ring
  rw [hZ, e1, e2, e3, hk2, mul_pow, neg_pow]
  ring

theorem isCoprime_X_pow_one_sub_X_sq (m h : ℕ) :
    IsCoprime ((X : (ZMod p)[X]) ^ m) ((1 - X ^ 2 : (ZMod p)[X]) ^ h) := by
  apply IsCoprime.pow
  exact ⟨X, 1, by ring⟩

theorem one_sub_X_sq_pow_prime : (1 - X ^ 2 : (ZMod p)[X]) ^ p = 1 - X ^ (2 * p) := by
  rw [sub_pow_char, one_pow, ← pow_mul]

theorem one_sub_X_sq_natDegree (h : ℕ) :
    ((1 - X ^ 2 : (ZMod p)[X]) ^ h).natDegree = 2 * h := by
  have h1 : (1 - X ^ 2 : (ZMod p)[X]).natDegree = 2 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt] <;> simp
  rw [natDegree_pow, h1]; ring

theorem one_sub_X_pow_natDegree_le (h : ℕ) :
    ((1 - X : (ZMod p)[X]) ^ h).natDegree ≤ h := by
  calc _ ≤ h * (1 - X : (ZMod p)[X]).natDegree := natDegree_pow_le
    _ ≤ h * 1 := Nat.mul_le_mul_left _ (by compute_degree)
    _ = h := by ring

end

/-! ### Polynomial combinations -/

/-- The polynomial combination `∑ c_i • v_i`. -/
def combLin {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (v : ι → R[X]) :
    (ι → R) →ₗ[R] R[X] where
  toFun c := ∑ i, C (c i) * v i
  map_add' c d := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.mul_sum, mul_assoc, smul_eq_C_mul]

theorem combLin_apply {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (v : ι → R[X])
    (c : ι → R) : combLin v c = ∑ i, C (c i) * v i := rfl

theorem combLin_mul_left {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (v : ι → R[X])
    (f : R[X]) (c : ι → R) : f * combLin v c = combLin (fun i => f * v i) c := by
  simp only [combLin_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring


/-! ### Triangular count -/

/-- A sequence obeying the order-`e` alternating binomial recurrence on `[m0+e, m1)` that
vanishes on the first `e` terms vanishes on `[m0, m1)`. -/
theorem alt_binom_vanish {K : Type*} [Field K] (a : ℕ → K) (e m0 m1 : ℕ)
    (hrec : ∀ mu, m0 + e ≤ mu → mu < m1 →
      ∑ t ∈ Finset.range (e + 1), (-1 : K) ^ t * (e.choose t : K) * a (mu - t) = 0)
    (hinit : ∀ mu, m0 ≤ mu → mu < m0 + e → a mu = 0) :
    ∀ mu, m0 ≤ mu → mu < m1 → a mu = 0 := by
  intro mu
  induction mu using Nat.strong_induction_on with
  | _ mu ih =>
    intro h0 h1
    by_cases hmu : mu < m0 + e
    · exact hinit mu h0 hmu
    · have hr := hrec mu (by omega) h1
      rw [Finset.sum_eq_single 0] at hr
      · simpa using hr
      · intro t ht ht0
        have htl := Finset.mem_range.mp ht
        rw [ih (mu - t) (by omega) (by omega) (by omega), mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- Triangular families with nonzero diagonal are linearly independent. -/
theorem triangular_linearIndependent {K : Type*} [Field K] {k : ℕ} (w : Fin k → Fin k → K)
    (hlow : ∀ i j : Fin k, i < j → w i j = 0) (hdiag : ∀ i, w i i ≠ 0) :
    LinearIndependent K w := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ m : ℕ, ∀ i : Fin k, k - m ≤ i.val → c i = 0 := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd i.isLt (by omega)
    | succ m ih =>
      intro i hi
      have hz := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
      rw [Finset.sum_eq_single i] at hz
      · exact (mul_eq_zero.mp hz).resolve_right (hdiag i)
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with h | h
        · rw [hlow j i h, mul_zero]
        · rw [ih j (by have := Fin.lt_def.mp h; omega), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
  intro i
  exact key k i (by omega)

end
end CatalanMeasure.GenD
