module
public import Submission.CatalanMeasure.GenD.RankU
@[expose] public section

/-!
# Theorem T (tent) for a general design (GenD, module 10)
-/

namespace CatalanMeasure.GenD
open Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
noncomputable section

section
variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Chebyshev differences at the multiples `0, p, 2p` in characteristic `p` -/

theorem tent_T0 (d : ℕ) :
    Chebyshev.T (ZMod p) ((d : ℤ)) - Chebyshev.T (ZMod p) (-(d : ℤ)) = 0 := by
  rw [Chebyshev.T_neg, sub_self]

theorem tent_U0 (d : ℕ) :
    Chebyshev.U (ZMod p) ((d : ℤ) - 1) - Chebyshev.U (ZMod p) (-(d : ℤ) - 1) =
      2 * Chebyshev.U (ZMod p) ((d : ℤ) - 1) := by
  have h := chebyshev_U_difference (ZMod p) 0 d
  rw [Chebyshev.T_zero] at h
  simpa using h

theorem tent_T1 (hp2 : p ≠ 2) (d : ℕ) :
    Chebyshev.T (ZMod p) ((p : ℤ) + d) - Chebyshev.T (ZMod p) ((p : ℤ) - d) =
      (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2) * (2 * Chebyshev.U (ZMod p) ((d : ℤ) - 1)) := by
  have hodd := odd_of_ne_two hp2
  have h := chebyshev_T_difference (ZMod p) (p : ℤ) d
  rw [chebyshev_U_prime hp2] at h
  have hh : (p + 1) / 2 = (p - 1) / 2 + 1 := by omega
  rw [h, hh, pow_succ]
  ring

theorem tent_U1 (hp2 : p ≠ 2) (d : ℕ) :
    Chebyshev.U (ZMod p) ((p : ℤ) + d - 1) - Chebyshev.U (ZMod p) ((p : ℤ) - d - 1) =
      X ^ p * (2 * Chebyshev.U (ZMod p) ((d : ℤ) - 1)) := by
  rw [chebyshev_U_difference (ZMod p) (p : ℤ) d, chebyshev_T_prime hp2]
  ring

theorem tent_U_two_p (hp2 : p ≠ 2) :
    Chebyshev.U (ZMod p) (2 * (p : ℤ) - 1) =
      2 * X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) := by
  have h := chebyshev_U_difference (ZMod p) (p : ℤ) p
  rw [show (p : ℤ) + p - 1 = 2 * p - 1 by ring, show (p : ℤ) - p - 1 = -1 by ring,
    Chebyshev.U_neg_one, chebyshev_T_prime hp2, chebyshev_U_prime hp2] at h
  rw [sub_zero] at h
  exact h

theorem tent_T_two_p (hp2 : p ≠ 2) :
    Chebyshev.T (ZMod p) (2 * (p : ℤ)) = 2 * X ^ (2 * p) - 1 := by
  have hodd := odd_of_ne_two hp2
  have h := chebyshev_T_difference (ZMod p) (p : ℤ) p
  rw [show (p : ℤ) + p = 2 * p by ring, show (p : ℤ) - p = 0 by ring, Chebyshev.T_zero,
    chebyshev_U_prime hp2] at h
  have e : (X ^ 2 - 1 : (ZMod p)[X]) ^ p = X ^ (2 * p) - 1 := by
    rw [sub_pow_char, one_pow, ← pow_mul]
  have e2 : (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) * (X ^ 2 - 1) ^ ((p - 1) / 2) *
      (X ^ 2 - 1) = (X ^ 2 - 1) ^ p := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have : Chebyshev.T (ZMod p) (2 * (p : ℤ)) = 1 + 2 * (X ^ 2 - 1 : (ZMod p)[X]) ^ p := by
    rw [← e2]
    linear_combination h
  rw [this, e]
  ring

theorem tent_T2 (hp2 : p ≠ 2) (d : ℕ) :
    Chebyshev.T (ZMod p) (2 * (p : ℤ) + d) - Chebyshev.T (ZMod p) (2 * (p : ℤ) - d) =
      2 * (X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2) *
        (2 * Chebyshev.U (ZMod p) ((d : ℤ) - 1))) := by
  have hodd := odd_of_ne_two hp2
  have h := chebyshev_T_difference (ZMod p) (2 * (p : ℤ)) d
  rw [show 2 * (p : ℤ) - 1 = 2 * p - 1 by ring, tent_U_two_p hp2] at h
  have hh : (p + 1) / 2 = (p - 1) / 2 + 1 := by omega
  rw [h, hh, pow_succ]
  ring

theorem tent_U2 (hp2 : p ≠ 2) (d : ℕ) :
    Chebyshev.U (ZMod p) (2 * (p : ℤ) + d - 1) - Chebyshev.U (ZMod p) (2 * (p : ℤ) - d - 1) =
      (2 * X ^ (2 * p) - 1) * (2 * Chebyshev.U (ZMod p) ((d : ℤ) - 1)) := by
  rw [chebyshev_U_difference (ZMod p) (2 * (p : ℤ)) d, tent_T_two_p hp2]
  ring


/-! ### Reflection of the row differences -/

theorem reflect_two_mul' {R : Type*} [CommRing R] (N : ℕ) (f : R[X]) :
    reflect N (2 * f) = 2 * reflect N f := by
  rw [two_mul, reflect_add, two_mul]

theorem reflect_row_mul {R : Type*} [Semiring R] {A B e : ℕ} {a u : R[X]}
    (ha : a.natDegree ≤ A) (hu : u.natDegree ≤ B) :
    reflect (A + (B + e)) (a * u) = reflect A a * (X ^ e * reflect B u) := by
  rw [reflect_mul a u ha (hu.trans (Nat.le_add_right B e)), reflect_shift u hu e]

theorem reflect_X_pow_self {R : Type*} [Semiring R] (n : ℕ) :
    reflect n ((X : R[X]) ^ n) = 1 := by
  rw [reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero]

theorem X_sq_sub_one_pow_natDegree_le {R : Type*} [CommRing R] (m : ℕ) :
    ((X ^ 2 - 1 : R[X]) ^ m).natDegree ≤ 2 * m := by
  calc _ ≤ m * (X ^ 2 - 1 : R[X]).natDegree := natDegree_pow_le
    _ ≤ m * 2 := Nat.mul_le_mul_left _ (by compute_degree)
    _ = 2 * m := by ring

theorem refl_G0 {B w E : ℕ} {u : (ZMod p)[X]} (hu : u.natDegree ≤ B) (hE : E = B + w) :
    reflect E u = X ^ w * reflect B u := by
  rw [hE, reflect_shift u hu]

theorem refl_S1 (hodd : p % 2 = 1) {B e E : ℕ} {u : (ZMod p)[X]} (hu : u.natDegree ≤ B)
    (hE : E = (p + 1) + (B + e)) :
    reflect E ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2) * u) =
      (1 - X ^ 2) ^ ((p + 1) / 2) * (X ^ e * reflect B u) := by
  have h2 : 2 * ((p + 1) / 2) = p + 1 := by omega
  have hd := X_sq_sub_one_pow_natDegree_le (R := ZMod p) ((p + 1) / 2)
  rw [h2] at hd
  have hr : reflect (p + 1) ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2)) =
      (1 - X ^ 2) ^ ((p + 1) / 2) := by
    have := reflect_pow_two (R := ZMod p) ((p + 1) / 2)
    rwa [h2] at this
  rw [hE, reflect_row_mul hd hu, hr]

theorem refl_G1 {B e E : ℕ} {u : (ZMod p)[X]} (hu : u.natDegree ≤ B)
    (hE : E = p + (B + e)) :
    reflect E ((X : (ZMod p)[X]) ^ p * u) = X ^ e * reflect B u := by
  rw [hE, reflect_row_mul (a := (X : (ZMod p)[X]) ^ p) (by simp) hu, reflect_X_pow_self, one_mul]

theorem refl_S2 (hodd : p % 2 = 1) {B e E : ℕ} {u : (ZMod p)[X]} (hu : u.natDegree ≤ B)
    (hE : E = (p + (p + 1)) + (B + e)) :
    reflect E (2 * ((X : (ZMod p)[X]) ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2) * u)) =
      2 * ((1 - X ^ 2) ^ ((p + 1) / 2) * (X ^ e * reflect B u)) := by
  have h2 : 2 * ((p + 1) / 2) = p + 1 := by omega
  have hd := X_sq_sub_one_pow_natDegree_le (R := ZMod p) ((p + 1) / 2)
  rw [h2] at hd
  have hr : reflect (p + 1) ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2)) =
      (1 - X ^ 2) ^ ((p + 1) / 2) := by
    have := reflect_pow_two (R := ZMod p) ((p + 1) / 2)
    rwa [h2] at this
  have ha : ((X : (ZMod p)[X]) ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2)).natDegree ≤
      p + (p + 1) :=
    natDegree_mul_le.trans (add_le_add (by simp) hd)
  rw [reflect_two_mul', hE, reflect_row_mul ha hu,
    reflect_mul ((X : (ZMod p)[X]) ^ p) _ (by simp) hd, reflect_X_pow_self, hr, one_mul]

theorem refl_G2 {B e E : ℕ} {u : (ZMod p)[X]} (hu : u.natDegree ≤ B)
    (hE : E = 2 * p + (B + e)) :
    reflect E ((2 * (X : (ZMod p)[X]) ^ (2 * p) - 1) * u) =
      (2 - X ^ (2 * p)) * (X ^ e * reflect B u) := by
  have ha : (2 * (X : (ZMod p)[X]) ^ (2 * p) - 1).natDegree ≤ 2 * p := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    refine natDegree_mul_le.trans ?_
    simp
  have hr : reflect (2 * p) (2 * (X : (ZMod p)[X]) ^ (2 * p) - 1) = 2 - X ^ (2 * p) := by
    rw [reflect_sub, reflect_two_mul', reflect_X_pow_self, reflect_one]
    ring
  rw [hE, reflect_row_mul ha hu, hr]

/-! ### Per-row-pair facts -/

/-- `2 U_{B}`. -/
def tU2 (p B : ℕ) : (ZMod p)[X] := 2 * Chebyshev.U (ZMod p) (B : ℤ)

/-- `(1-X)^h` times the reflection of `tU2`. -/
def tz (p h B : ℕ) : (ZMod p)[X] := (1 - X) ^ h * reflect B (tU2 p B)

theorem tU2_natDegree_le (hp2 : p ≠ 2) (B : ℕ) : (tU2 p B).natDegree ≤ B := by
  have : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  unfold tU2
  rw [two_mul]
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_) <;>
    simp [Chebyshev.natDegree_U_natCast]

theorem uSv_sub {C g a b : ℕ} (m d : ℤ) (ha : (a : ℤ) - g = m + d) (hb : (b : ℤ) - g = m - d) :
    uSv p C g a - uSv p C g b =
      reflect (C - 1) (Chebyshev.T (ZMod p) (m + d) - Chebyshev.T (ZMod p) (m - d)) := by
  unfold uSv
  rw [ha, hb, reflect_sub]

theorem uUv_sub {C g a b : ℕ} (m d : ℤ) (ha : (a : ℤ) - g - 1 = m + d - 1)
    (hb : (b : ℤ) - g - 1 = m - d - 1) :
    uUv p C g a - uUv p C g b =
      reflect (C - 1) (Chebyshev.U (ZMod p) (m + d - 1) - Chebyshev.U (ZMod p) (m - d - 1)) := by
  unfold uUv
  rw [ha, hb, reflect_sub]

theorem cast_B (B : ℕ) : (((B + 1 : ℕ) : ℤ) - 1) = (B : ℤ) := by push_cast; ring

theorem pow_pair (hodd : p % 2 = 1) :
    (1 - X ^ 2 : (ZMod p)[X]) ^ ((p - 1) / 2) * (1 - X ^ 2) ^ ((p + 1) / 2) = 1 - X ^ (2 * p) := by
  rw [← pow_add, show (p - 1) / 2 + (p + 1) / 2 = p by omega, one_sub_X_sq_pow_prime]

theorem tent_fact_S0 (hp2 : p ≠ 2) {h C g B : ℕ} (hdg : B + 1 ≤ g) :
    (1 - X) ^ h * (uSv p C g (g + (B + 1)) - uSv p C g (g - (B + 1))) = 0 := by
  rw [uSv_sub (0 : ℤ) ((B + 1 : ℕ) : ℤ) (by omega) (by omega)]
  have := tent_T0 (p := p) (B + 1)
  rw [zero_add, zero_sub, this]
  simp

theorem tent_fact_U0 (hp2 : p ≠ 2) {h C g B t : ℕ} (hdg : B + 1 ≤ g)
    (hC : C = 3 * p + (B + 1) + t) :
    (1 - X) ^ h * (uUv p C g (g + (B + 1)) - uUv p C g (g - (B + 1))) =
      X ^ (3 * p + t) * tz p h B := by
  rw [uUv_sub (0 : ℤ) ((B + 1 : ℕ) : ℤ) (by omega) (by omega)]
  have := tent_U0 (p := p) (B + 1)
  rw [zero_add, zero_sub, this, cast_B]
  have hu := tU2_natDegree_le hp2 B
  change (1 - X : (ZMod p)[X]) ^ h * reflect (C - 1) (tU2 p B) = _
  rw [refl_G0 hu (w := 3 * p + t) (by omega)]
  unfold tz
  ring

theorem tU2_def (B : ℕ) : tU2 p B = 2 * Chebyshev.U (ZMod p) (B : ℤ) := rfl

theorem tent_fact_S1 (hp2 : p ≠ 2) {h C g B t : ℕ} (hdg : B + 1 ≤ g)
    (hC : C = 3 * p + (B + 1) + t) :
    X * (1 - X ^ 2 : (ZMod p)[X]) ^ ((p - 1) / 2) *
        ((1 - X) ^ h * (uSv p C g (g + p + (B + 1)) - uSv p C g (g + p - (B + 1)))) =
      X ^ (2 * p + t) * tz p h B - X ^ p * (X ^ (3 * p + t) * tz p h B) := by
  have hodd := odd_of_ne_two hp2
  have hu := tU2_natDegree_le hp2 B
  rw [uSv_sub (p : ℤ) ((B + 1 : ℕ) : ℤ) (by omega) (by omega), tent_T1 hp2 (B + 1), cast_B,
    ← tU2_def]
  obtain ⟨e, he⟩ : ∃ e, 2 * p + t = e + 1 := ⟨2 * p + t - 1, by have := hp.out.two_le; omega⟩
  rw [refl_S1 hodd hu (e := e) (E := C - 1) (by omega)]
  have h3 : 3 * p + t = e + 1 + p := by omega
  rw [h3, he]
  unfold tz
  linear_combination (X ^ (e + 1) * ((1 - X) ^ h * reflect B (tU2 p B))) * pow_pair hodd

theorem tent_fact_U1 (hp2 : p ≠ 2) {h C g B t : ℕ} (hdg : B + 1 ≤ g)
    (hC : C = 3 * p + (B + 1) + t) :
    (1 - X) ^ h * (uUv p C g (g + p + (B + 1)) - uUv p C g (g + p - (B + 1))) =
      X ^ (2 * p + t) * tz p h B := by
  have hu := tU2_natDegree_le hp2 B
  rw [uUv_sub (p : ℤ) ((B + 1 : ℕ) : ℤ) (by omega) (by omega), tent_U1 hp2 (B + 1), cast_B,
    ← tU2_def]
  rw [refl_G1 hu (e := 2 * p + t) (E := C - 1) (by omega)]
  unfold tz
  ring

theorem tent_fact_S2 (hp2 : p ≠ 2) {h C g B t : ℕ} (hdg : B + 1 ≤ g)
    (hC : C = 3 * p + (B + 1) + t) :
    X * (1 - X ^ 2 : (ZMod p)[X]) ^ ((p - 1) / 2) *
        ((1 - X) ^ h * (uSv p C g (g + 2 * p + (B + 1)) - uSv p C g (g + 2 * p - (B + 1)))) =
      2 * (X ^ (p + t) * tz p h B - X ^ (3 * p + t) * tz p h B) := by
  have hodd := odd_of_ne_two hp2
  have hu := tU2_natDegree_le hp2 B
  rw [uSv_sub (2 * (p : ℤ)) ((B + 1 : ℕ) : ℤ) (by omega) (by omega), tent_T2 hp2 (B + 1), cast_B,
    ← tU2_def]
  obtain ⟨e, he⟩ : ∃ e, p + t = e + 1 := ⟨p + t - 1, by have := hp.out.two_le; omega⟩
  rw [refl_S2 hodd hu (e := e) (E := C - 1) (by omega)]
  have h3 : 3 * p + t = e + 1 + 2 * p := by omega
  rw [h3, he]
  unfold tz
  linear_combination (2 * X ^ (e + 1) * ((1 - X) ^ h * reflect B (tU2 p B))) * pow_pair hodd

theorem tent_fact_U2 (hp2 : p ≠ 2) {h C g B t : ℕ} (hdg : B + 1 ≤ g)
    (hC : C = 3 * p + (B + 1) + t) :
    (1 - X) ^ h * (uUv p C g (g + 2 * p + (B + 1)) - uUv p C g (g + 2 * p - (B + 1))) =
      2 * (X ^ (p + t) * tz p h B) - X ^ (3 * p + t) * tz p h B := by
  have hu := tU2_natDegree_le hp2 B
  rw [uUv_sub (2 * (p : ℤ)) ((B + 1 : ℕ) : ℤ) (by omega) (by omega), tent_U2 hp2 (B + 1), cast_B,
    ← tU2_def]
  rw [refl_G2 hu (e := p + t) (E := C - 1) (by omega)]
  unfold tz
  ring


/-! ### The digit window of the tent vectors -/

/-- Moment weight at digit `v`. -/
def tentA (p J v : ℕ) [Fact p.Prime] : ZMod p :=
  palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) J)

/-- Zeta weight at digit `v`. -/
def tentB (p J v : ℕ) [Fact p.Prime] : ZMod p :=
  palindromicRatResidue p (zetaRat v J)

/-- The linear form `f_J(x)` of the proof of Theorem T. -/
def tentForm (p J : ℕ) [Fact p.Prime] (x0 x1 x2 : ZMod p) : ZMod p :=
  x1 * (tentA p J 2 - tentA p J 4) + 2 * x2 * (tentA p J 1 - tentA p J 3) -
    (3 / 2 : ZMod p) * (x0 * tentB p J 3 + x1 * tentB p J 2 +
      x2 * (2 * tentB p J 1 - tentB p J 3))

theorem tent_digit {H j : ℕ} (hH : 4 ≤ H) (F G R R1 R2 : (ZMod p)[X]) (x0 x1 x2 : ZMod p)
    (hR1 : R = X ^ p * R1) (hR2 : R = X ^ (2 * p) * R2)
    (hsup : ∀ i, i < 3 * p ∨ 4 * p ≤ i → R.coeff i = 0)
    (hQ : X * oddPrimeWeight p * F = C x1 * (R1 - X ^ p * R) + C (2 * x2) * (R2 - R))
    (hG : G = C x0 * R + C x1 * R1 + C x2 * (2 * R2 - R)) :
    primeDigitPair H p j F G = R.coeff (3 * p + j % p) * tentForm p (j / p) x0 x1 x2 := by
  have hℓ : j % p < p := Nat.mod_lt _ hp.out.pos
  unfold primeDigitPair primeDigitSample
  rw [hQ, hG]
  have hdef : tentForm p (j / p) x0 x1 x2 = tentForm p (j / p) x0 x1 x2 := rfl
  generalize j % p = ℓ at *
  unfold tentForm tentA tentB
  generalize j / p = J
  generalize hρ : R.coeff (3 * p + ℓ) = ρ
  have cR : ∀ v, R.coeff (v * p + ℓ) = if v = 3 then ρ else 0 := by
    intro v
    by_cases h3 : v = 3
    · subst h3; simp [hρ]
    · rw [if_neg h3]
      apply hsup
      rcases lt_or_gt_of_ne h3 with h | h
      · left
        have := Nat.mul_le_mul_right p (show v + 1 ≤ 3 by omega)
        rw [Nat.add_mul, one_mul] at this
        omega
      · right
        have := Nat.mul_le_mul_right p (show 4 ≤ v by omega)
        omega
  have cR1 : ∀ v, R1.coeff (v * p + ℓ) = if v = 2 then ρ else 0 := by
    intro v
    have e : R.coeff (v * p + ℓ + p) = R1.coeff (v * p + ℓ) := by
      rw [hR1]; exact coeff_X_pow_mul R1 p _
    rw [← e, show v * p + ℓ + p = (v + 1) * p + ℓ by ring, cR (v + 1)]
    have : (v + 1 = 3) ↔ (v = 2) := by omega
    simp only [this]
  have cR2 : ∀ v, R2.coeff (v * p + ℓ) = if v = 1 then ρ else 0 := by
    intro v
    have e : R.coeff (v * p + ℓ + 2 * p) = R2.coeff (v * p + ℓ) := by
      rw [hR2]; exact coeff_X_pow_mul R2 (2 * p) _
    rw [← e, show v * p + ℓ + 2 * p = (v + 2) * p + ℓ by ring, cR (v + 2)]
    have : (v + 2 = 3) ↔ (v = 1) := by omega
    simp only [this]
  have cXR : ∀ v, (X ^ p * R).coeff (v * p + ℓ) = if v = 4 then ρ else 0 := by
    intro v
    rw [coeff_X_pow_mul']
    rcases v with _ | v
    · rw [if_neg (by omega)]; simp
    · rw [if_pos (by rw [Nat.add_mul, one_mul]; omega),
        show (v + 1) * p + ℓ - p = v * p + ℓ by rw [Nat.add_mul, one_mul]; omega, cR v]
      have : (v = 3) ↔ (v + 1 = 4) := by omega
      simp only [this]
  have cQ : ∀ v, (C x1 * (R1 - X ^ p * R) + C (2 * x2) * (R2 - R)).coeff (v * p + ℓ) =
      x1 * ((if v = 2 then ρ else 0) - (if v = 4 then ρ else 0)) +
        2 * x2 * ((if v = 1 then ρ else 0) - (if v = 3 then ρ else 0)) := by
    intro v
    simp only [coeff_add, coeff_C_mul, coeff_sub, cR1, cR2, cXR, cR]
  have cG : ∀ v, (C x0 * R + C x1 * R1 + C x2 * (2 * R2 - R)).coeff (v * p + ℓ) =
      x0 * (if v = 3 then ρ else 0) + x1 * (if v = 2 then ρ else 0) +
        x2 * (2 * (if v = 1 then ρ else 0) - (if v = 3 then ρ else 0)) := by
    intro v
    simp only [coeff_add, coeff_C_mul, coeff_sub, coeff_ofNat_mul, cR1, cR2, cR]
  simp only [cQ, cG]
  have hsQ : ({1, 2, 3, 4} : Finset ℕ) ⊆ Finset.range (H + 1) := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hv ⊢; omega
  have hsG : ({1, 2, 3} : Finset ℕ) ⊆ Finset.range H := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hv ⊢; omega
  rw [← Finset.sum_subset hsQ (fun v hv hn => ?_), ← Finset.sum_subset hsG (fun v hv hn => ?_)]
  · simp [Finset.sum_insert]
    ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [hn.1, hn.2.1, hn.2.2]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2]


/-! ### The vectors `delta_k(d)` and their parametrisation -/

/-- `e_{g+m+d} - e_{g+m-d}` on `Fin n`. -/
def tVec (p g n m d : ℕ) : Fin n → ZMod p := fun r =>
  (if r.val = g + m + d then 1 else 0) - (if r.val = g + m - d then 1 else 0)

/-- `x0 delta_0(B+1) + x1 delta_1(B+1) + x2 delta_2(B+1)`. -/
def tW (p g n : ℕ) (x0 x1 x2 : ZMod p) (B : ℕ) : Fin n → ZMod p :=
  x0 • tVec p g n 0 (B + 1) + x1 • tVec p g n p (B + 1) + x2 • tVec p g n (2 * p) (B + 1)

def tJ (p g n D : ℕ) (x0 x1 x2 : ZMod p) : (Fin D → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) where
  toFun s := ∑ B : Fin D, s B • tW p g n x0 x1 x2 B.val
  map_add' s s' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a s := by simp [Finset.smul_sum, mul_smul]

theorem tVec_eval {g n m m' B B' : ℕ} (hm : m = 0 ∨ m = p ∨ m = 2 * p)
    (hm' : m' = 0 ∨ m' = p ∨ m' = 2 * p) (hB : B + 1 ≤ g) (hB' : B' + 1 ≤ g) (hgp : 2 * g < p)
    (hr : g + m + (B + 1) < n) :
    tVec p g n m' (B' + 1) ⟨g + m + (B + 1), hr⟩ = if m = m' ∧ B = B' then 1 else 0 := by
  simp only [tVec]
  by_cases h : m = m' ∧ B = B'
  · have h1 : g + m + (B + 1) = g + m' + (B' + 1) := by omega
    have h2 : ¬ (g + m + (B + 1) = g + m' - (B' + 1)) := by omega
    rw [if_pos h1, if_neg h2, if_pos h]; simp
  · have h1 : ¬ (g + m + (B + 1) = g + m' + (B' + 1)) := by omega
    have h2 : ¬ (g + m + (B + 1) = g + m' - (B' + 1)) := by omega
    rw [if_neg h1, if_neg h2, if_neg h]; simp

theorem tJ_coord {g n D : ℕ} (x0 x1 x2 : ZMod p) (s : Fin D → ZMod p) {m B : ℕ}
    (hm : m = 0 ∨ m = p ∨ m = 2 * p) (hBD : B < D) (hbd : ∀ B' < D, B' + 1 ≤ g)
    (hgp : 2 * g < p) (hr : g + m + (B + 1) < n) :
    tJ p g n D x0 x1 x2 s ⟨g + m + (B + 1), hr⟩ =
      s ⟨B, hBD⟩ * (x0 * (if m = 0 then 1 else 0) + x1 * (if m = p then 1 else 0) +
        x2 * (if m = 2 * p then 1 else 0)) := by
  have hB := hbd B hBD
  simp only [tJ, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    tW, Pi.add_apply]
  rw [Finset.sum_eq_single (⟨B, hBD⟩ : Fin D)]
  · rw [tVec_eval (m' := 0) hm (Or.inl rfl) hB hB hgp, tVec_eval (m' := p) hm (Or.inr (Or.inl rfl)) hB hB hgp,
      tVec_eval (m' := 2 * p) hm (Or.inr (Or.inr rfl)) hB hB hgp]
    simp only [and_true, smul_eq_mul]
  · intro B' _ hne
    have hne' : B ≠ B'.val := fun h => hne (Fin.ext h.symm)
    have hB' := hbd B'.val B'.isLt
    rw [tVec_eval (m' := 0) hm (Or.inl rfl) hB hB' hgp, tVec_eval (m' := p) hm (Or.inr (Or.inl rfl)) hB hB' hgp,
      tVec_eval (m' := 2 * p) hm (Or.inr (Or.inr rfl)) hB hB' hgp]
    simp [hne']
  · intro h; exact absurd (Finset.mem_univ _) h


theorem tJ_injective {g n D : ℕ} (x0 x1 x2 : ZMod p) (hx : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0)
    (hbd : ∀ B' < D, B' + 1 ≤ g) (hbn : ∀ B' < D, g + 2 * p + (B' + 1) < n) (hgp : 2 * g < p) :
    Function.Injective (tJ p g n D x0 x1 x2) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  funext ⟨B, hBD⟩
  have hn := hbn B hBD
  have hp0 : p ≠ 0 := by omega
  have hq1 : 2 * p ≠ p := by omega
  have hq2 : p ≠ 2 * p := by omega
  have hq3 : 0 ≠ p := by omega
  have hq4 : 0 ≠ 2 * p := by omega
  have hq5 : 2 * p ≠ 0 := by omega
  rcases hx with h0 | h1 | h2
  · have := congrFun hs ⟨g + 0 + (B + 1), by omega⟩
    rw [tJ_coord x0 x1 x2 s (Or.inl rfl) hBD hbd hgp] at this
    simpa [hp0, hq3, hq4, h0] using this
  · have := congrFun hs ⟨g + p + (B + 1), by omega⟩
    rw [tJ_coord x0 x1 x2 s (Or.inr (Or.inl rfl)) hBD hbd hgp] at this
    simpa [hp0, hq1, hq2, h1] using this
  · have := congrFun hs ⟨g + 2 * p + (B + 1), by omega⟩
    rw [tJ_coord x0 x1 x2 s (Or.inr (Or.inr rfl)) hBD hbd hgp] at this
    simpa [hp0, hq1, hq5, h2] using this


/-! ### Two linear forms on `K^3` have a common nonzero zero -/

theorem two_forms_common_zero {K : Type*} [Field K] (a0 a1 a2 b0 b1 b2 : K) :
    ∃ x0 x1 x2 : K, (x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0) ∧ a0 * x0 + a1 * x1 + a2 * x2 = 0 ∧
      b0 * x0 + b1 * x1 + b2 * x2 = 0 := by
  let M : Matrix (Fin 2) (Fin 3) K := !![a0, a1, a2; b0, b1, b2]
  have hker : LinearMap.ker M.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hx' : M.mulVec x = 0 := hx
  have h0 := congrFun hx' 0
  have h1 := congrFun hx' 1
  simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
  refine ⟨x 0, x 1, x 2, ?_, h0, h1⟩
  by_contra hcon
  push_neg at hcon
  exact hne (funext fun i => by fin_cases i <;> simp [hcon.1, hcon.2.1, hcon.2.2])

theorem tentForm_eq (p J : ℕ) [Fact p.Prime] (x0 x1 x2 : ZMod p) :
    tentForm p J x0 x1 x2 =
      (-(3 / 2 : ZMod p) * tentB p J 3) * x0 +
      ((tentA p J 2 - tentA p J 4) - (3 / 2 : ZMod p) * tentB p J 2) * x1 +
      (2 * (tentA p J 1 - tentA p J 3) - (3 / 2 : ZMod p) * (2 * tentB p J 1 - tentB p J 3)) *
        x2 := by
  unfold tentForm
  ring

theorem tent_exists_x (p : ℕ) [Fact p.Prime] :
    ∃ x0 x1 x2 : ZMod p, (x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0) ∧ tentForm p 1 x0 x1 x2 = 0 ∧
      tentForm p 2 x0 x1 x2 = 0 := by
  obtain ⟨x0, x1, x2, hx, h1, h2⟩ := two_forms_common_zero
    (-(3 / 2 : ZMod p) * tentB p 1 3)
    ((tentA p 1 2 - tentA p 1 4) - (3 / 2 : ZMod p) * tentB p 1 2)
    (2 * (tentA p 1 1 - tentA p 1 3) - (3 / 2 : ZMod p) * (2 * tentB p 1 1 - tentB p 1 3))
    (-(3 / 2 : ZMod p) * tentB p 2 3)
    ((tentA p 2 2 - tentA p 2 4) - (3 / 2 : ZMod p) * tentB p 2 2)
    (2 * (tentA p 2 1 - tentA p 2 3) - (3 / 2 : ZMod p) * (2 * tentB p 2 1 - tentB p 2 3))
  exact ⟨x0, x1, x2, hx, by rw [tentForm_eq]; exact h1, by rw [tentForm_eq]; exact h2⟩

/-! ### Row combinations of the tent vectors -/

theorem sum_C_ite {n a : ℕ} (ha : a < n) (f : ℕ → (ZMod p)[X]) :
    ∑ r : Fin n, C (if r.val = a then (1 : ZMod p) else 0) * f r.val = f a := by
  rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin n)]
  · simp
  · intro r _ hr
    have : r.val ≠ a := fun h => hr (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem uS_tVec {C g n m d : ℕ} (h1 : g + m + d < n) (h2 : g + m - d < n) :
    uS p C g n (tVec p g n m d) = uSv p C g (g + m + d) - uSv p C g (g + m - d) := by
  simp only [uS, combLin_apply, tVec, map_sub, sub_mul, Finset.sum_sub_distrib]
  rw [sum_C_ite h1 (uSv p C g), sum_C_ite h2 (uSv p C g)]

theorem uU_tVec {C g n m d : ℕ} (h1 : g + m + d < n) (h2 : g + m - d < n) :
    uU p C g n (tVec p g n m d) = uUv p C g (g + m + d) - uUv p C g (g + m - d) := by
  simp only [uU, combLin_apply, tVec, map_sub, sub_mul, Finset.sum_sub_distrib]
  rw [sum_C_ite h1 (uUv p C g), sum_C_ite h2 (uUv p C g)]

/-- The three shifted copies `X^e * tz`. -/
def trr (p h C e B : ℕ) : (ZMod p)[X] := X ^ (e + (C - (3 * p + (B + 1)))) * tz p h B

theorem tent_B_facts (hp2 : p ≠ 2) {h C g n B : ℕ} (x0 x1 x2 : ZMod p) (hdg : B + 1 ≤ g)
    (hCB : 3 * p + (B + 1) ≤ C) (hn : g + 2 * p + (B + 1) < n) :
    X * oddPrimeWeight p * ((1 - X) ^ h * uS p C g n (tW p g n x0 x1 x2 B)) =
        Polynomial.C x1 * (trr p h C (2 * p) B - X ^ p * trr p h C (3 * p) B) +
        Polynomial.C (2 * x2) * (trr p h C p B - trr p h C (3 * p) B) ∧
      (1 - X) ^ h * uU p C g n (tW p g n x0 x1 x2 B) =
        Polynomial.C x0 * trr p h C (3 * p) B + Polynomial.C x1 * trr p h C (2 * p) B +
        Polynomial.C x2 * (2 * trr p h C p B - trr p h C (3 * p) B) := by
  have hC : C = 3 * p + (B + 1) + (C - (3 * p + (B + 1))) := by omega
  have f0 := tent_fact_S0 (p := p) hp2 (h := h) (C := C) hdg
  have f1 := tent_fact_S1 hp2 (h := h) hdg hC
  have f2 := tent_fact_S2 hp2 (h := h) hdg hC
  have u0 := tent_fact_U0 hp2 (h := h) hdg hC
  have u1 := tent_fact_U1 hp2 (h := h) hdg hC
  have u2 := tent_fact_U2 hp2 (h := h) hdg hC
  have e2 : (Polynomial.C (2 * x2) : (ZMod p)[X]) = 2 * Polynomial.C x2 := by
    rw [C_mul]; rfl
  unfold tW
  rw [map_add, map_add, map_smul, map_smul, map_smul, uS_tVec (by omega) (by omega),
    uS_tVec (by omega) (by omega), uS_tVec (by omega) (by omega)]
  rw [map_add, map_add, map_smul, map_smul, map_smul, uU_tVec (by omega) (by omega),
    uU_tVec (by omega) (by omega), uU_tVec (by omega) (by omega)]
  simp only [Nat.add_zero, smul_eq_C_mul]
  unfold trr
  rw [e2]
  refine ⟨?_, ?_⟩
  · unfold oddPrimeWeight
    linear_combination (X * (1 - X ^ 2 : (ZMod p)[X]) ^ ((p - 1) / 2) * Polynomial.C x0) * f0 +
      Polynomial.C x1 * f1 + Polynomial.C x2 * f2
  · linear_combination Polynomial.C x0 * u0 + Polynomial.C x1 * u1 + Polynomial.C x2 * u2


/-! ### Sums over the parameter `s` and supports -/

theorem tent_sums {ι : Type*} [Fintype ι] (c : ι → ZMod p) (Φ r0 r1 r2 : ι → (ZMod p)[X])
    (K : (ZMod p)[X]) (x1 x2 : ZMod p)
    (hQ : ∀ i, K * Φ i =
      Polynomial.C x1 * (r1 i - X ^ p * r0 i) + Polynomial.C (2 * x2) * (r2 i - r0 i)) :
    K * ∑ i, Polynomial.C (c i) * Φ i =
      Polynomial.C x1 * (∑ i, Polynomial.C (c i) * r1 i -
        X ^ p * ∑ i, Polynomial.C (c i) * r0 i) +
      Polynomial.C (2 * x2) * (∑ i, Polynomial.C (c i) * r2 i -
        ∑ i, Polynomial.C (c i) * r0 i) := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (Polynomial.C (c i)) * hQ i

theorem tent_sums_G {ι : Type*} [Fintype ι] (c : ι → ZMod p) (Ψ r0 r1 r2 : ι → (ZMod p)[X])
    (x0 x1 x2 : ZMod p)
    (hG : ∀ i, Ψ i = Polynomial.C x0 * r0 i + Polynomial.C x1 * r1 i +
      Polynomial.C x2 * (2 * r2 i - r0 i)) :
    ∑ i, Polynomial.C (c i) * Ψ i =
      Polynomial.C x0 * ∑ i, Polynomial.C (c i) * r0 i +
      Polynomial.C x1 * ∑ i, Polynomial.C (c i) * r1 i +
      Polynomial.C x2 * (2 * ∑ i, Polynomial.C (c i) * r2 i -
        ∑ i, Polynomial.C (c i) * r0 i) := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hG i]
  ring

theorem tz_natDegree_le (hp2 : p ≠ 2) (h B : ℕ) : (tz p h B).natDegree ≤ h + B := by
  unfold tz
  refine natDegree_mul_le.trans (add_le_add (one_sub_X_pow_natDegree_le h) ?_)
  exact natDegree_reflect_le.trans (max_le le_rfl (tU2_natDegree_le hp2 B))

theorem trr3_coeff_zero (hp2 : p ≠ 2) {h C B i : ℕ} (hBC : 3 * p + (B + 1) ≤ C)
    (hi : i < C - (B + 1) ∨ C + h ≤ i) : (trr p h C (3 * p) B).coeff i = 0 := by
  unfold trr
  rw [coeff_X_pow_mul']
  split_ifs with hle
  · apply coeff_eq_zero_of_natDegree_lt
    have := tz_natDegree_le hp2 h B
    omega
  · rfl

/-- The number `D = min g (n-1-g-2p) (C-3p)` of independent tent directions. -/
def tentD (P : Parameters) (N p : ℕ) : ℕ :=
  min (P.g N) (min (P.n N - 1 - P.g N - 2 * p) (P.C N - 3 * p))

variable {P : Parameters} {N : ℕ}

/-- The constraint functionals on the parameter `s`: coefficients of `∑ s_B X^{C-B-1} tz_B`
in degrees `3p + b + a`. -/
def tCon (P : Parameters) (N p : ℕ) [Fact p.Prime] :
    (Fin (tentD P N p) → ZMod p) →ₗ[ZMod p] (Fin (P.H N - 3 * p - P.b N) → ZMod p) :=
  (Matrix.of fun (a : Fin (P.H N - 3 * p - P.b N)) (B : Fin (tentD P N p)) =>
    (trr p (P.h N) (P.C N) (3 * p) B.val).coeff (3 * p + P.b N + a.val)).mulVecLin

theorem tCon_apply (s : Fin (tentD P N p) → ZMod p) (a : Fin (P.H N - 3 * p - P.b N)) :
    tCon P N p s a = ∑ B : Fin (tentD P N p),
      s B * (trr p (P.h N) (P.C N) (3 * p) B.val).coeff (3 * p + P.b N + a.val) := by
  simp only [tCon, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun B _ => mul_comm _ _


/-! ### Kernel response and rank -/

theorem t_response (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (h2g : 2 * P.g N < p) (hH4 : P.H N ≤ 4 * p) (hD : 1 ≤ tentD P N p)
    (x0 x1 x2 : ZMod p) (hx1 : tentForm p 1 x0 x1 x2 = 0) (hx2 : tentForm p 2 x0 x1 x2 = 0)
    (s : Fin (tentD P N p) → ZMod p)
    (hcon : ∀ a, a < P.H N - 3 * p - P.b N →
      ∑ B : Fin (tentD P N p), s B *
        (trr p (P.h N) (P.C N) (3 * p) B.val).coeff (3 * p + P.b N + a) = 0)
    {j : ℕ} (hj1 : P.b N ≤ j) (hj2 : j < P.L N) :
    uResp P N p j (tJ p (P.g N) (P.n N) (tentD P N p) x0 x1 x2 s) = 0 := by
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  have hHd : P.H N = P.C N + P.h N := rfl
  have hodd := odd_of_ne_two hp2
  have hp2' := hp.out.two_le
  have hD1 : tentD P N p ≤ P.g N := min_le_left _ _
  have hD2 : tentD P N p ≤ P.n N - 1 - P.g N - 2 * p :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hD3 : tentD P N p ≤ P.C N - 3 * p := (min_le_right _ _).trans (min_le_right _ _)
  have hbd : ∀ B < tentD P N p, B + 1 ≤ P.g N := fun B hB => by omega
  have hBC : ∀ B < tentD P N p, 3 * p + (B + 1) ≤ P.C N := fun B hB => by omega
  have hBn : ∀ B < tentD P N p, P.g N + 2 * p + (B + 1) < P.n N := fun B hB => by omega
  have hFB := fun B : Fin (tentD P N p) =>
    tent_B_facts hp2 (h := P.h N) (C := P.C N) (g := P.g N) (n := P.n N) (B := B.val) x0 x1 x2
      (hbd B.val B.isLt) (hBC B.val B.isLt) (hBn B.val B.isLt)
  set c := tJ p (P.g N) (P.n N) (tentD P N p) x0 x1 x2 s with hc
  set R0 : (ZMod p)[X] := ∑ B : Fin (tentD P N p),
    Polynomial.C (s B) * trr p (P.h N) (P.C N) (3 * p) B.val with hR0
  set R1 : (ZMod p)[X] := ∑ B : Fin (tentD P N p),
    Polynomial.C (s B) * trr p (P.h N) (P.C N) (2 * p) B.val with hR1
  set R2 : (ZMod p)[X] := ∑ B : Fin (tentD P N p),
    Polynomial.C (s B) * trr p (P.h N) (P.C N) p B.val with hR2
  have hFsum : (1 - X : (ZMod p)[X]) ^ P.h N * uS p (P.C N) (P.g N) (P.n N) c =
      ∑ B : Fin (tentD P N p), Polynomial.C (s B) * ((1 - X) ^ P.h N *
        uS p (P.C N) (P.g N) (P.n N) (tW p (P.g N) (P.n N) x0 x1 x2 B.val)) := by
    simp only [hc, tJ, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, Finset.mul_sum,
      smul_eq_C_mul]
    exact Finset.sum_congr rfl fun B _ => by ring
  have hGsum : (1 - X : (ZMod p)[X]) ^ P.h N * uU p (P.C N) (P.g N) (P.n N) c =
      ∑ B : Fin (tentD P N p), Polynomial.C (s B) * ((1 - X) ^ P.h N *
        uU p (P.C N) (P.g N) (P.n N) (tW p (P.g N) (P.n N) x0 x1 x2 B.val)) := by
    simp only [hc, tJ, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, Finset.mul_sum,
      smul_eq_C_mul]
    exact Finset.sum_congr rfl fun B _ => by ring
  have hQ : X * oddPrimeWeight p * ((1 - X : (ZMod p)[X]) ^ P.h N *
      uS p (P.C N) (P.g N) (P.n N) c) =
      Polynomial.C x1 * (R1 - X ^ p * R0) + Polynomial.C (2 * x2) * (R2 - R0) := by
    rw [hFsum]
    exact tent_sums (fun B : Fin (tentD P N p) => s B)
      (fun B => (1 - X : (ZMod p)[X]) ^ P.h N *
        uS p (P.C N) (P.g N) (P.n N) (tW p (P.g N) (P.n N) x0 x1 x2 B.val))
      (fun B => trr p (P.h N) (P.C N) (3 * p) B.val)
      (fun B => trr p (P.h N) (P.C N) (2 * p) B.val)
      (fun B => trr p (P.h N) (P.C N) p B.val) (X * oddPrimeWeight p) x1 x2
      (fun B => (hFB B).1)
  have hG : (1 - X : (ZMod p)[X]) ^ P.h N * uU p (P.C N) (P.g N) (P.n N) c =
      Polynomial.C x0 * R0 + Polynomial.C x1 * R1 + Polynomial.C x2 * (2 * R2 - R0) := by
    rw [hGsum]
    exact tent_sums_G (fun B : Fin (tentD P N p) => s B) _
      (fun B => trr p (P.h N) (P.C N) (3 * p) B.val)
      (fun B => trr p (P.h N) (P.C N) (2 * p) B.val)
      (fun B => trr p (P.h N) (P.C N) p B.val) x0 x1 x2 (fun B => (hFB B).2)
  have hR1' : R0 = X ^ p * R1 := by
    simp only [hR0, hR1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    unfold trr
    ring
  have hR2' : R0 = X ^ (2 * p) * R2 := by
    simp only [hR0, hR2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    unfold trr
    ring
  have hcoef : ∀ i, R0.coeff i = ∑ B : Fin (tentD P N p),
      s B * (trr p (P.h N) (P.C N) (3 * p) B.val).coeff i := by
    intro i
    simp [hR0, finset_sum_coeff, coeff_C_mul]
  have hz : ∀ i, (∀ B < tentD P N p, i < P.C N - (B + 1) ∨ P.C N + P.h N ≤ i) →
      R0.coeff i = 0 := by
    intro i hi
    rw [hcoef]
    exact Finset.sum_eq_zero fun B _ => by
      rw [trr3_coeff_zero hp2 (hBC B.val B.isLt) (hi B.val B.isLt), mul_zero]
  have hsup : ∀ i, i < 3 * p ∨ 4 * p ≤ i → R0.coeff i = 0 := by
    intro i hi
    exact hz i fun B hB => by have := hBC B hB; omega
  have hlow : ∀ i, i < P.L N → R0.coeff i = 0 := by
    intro i hi
    exact hz i fun B hB => by have := hbd B hB; omega
  have hhigh : ∀ i, P.H N ≤ i → R0.coeff i = 0 := by
    intro i hi
    exact hz i fun B hB => by omega
  rw [uResp_eq hP hN hp2 hH (by omega : j < P.H N) c,
    tent_digit (by omega) _ _ R0 R1 R2 x0 x1 x2 hR1' hR2' hsup hQ hG]
  have hjd := Nat.div_add_mod j p
  have hℓ : j % p < p := Nat.mod_lt _ hp.out.pos
  have hJ4 : j / p < 4 := Nat.div_lt_of_lt_mul (by omega)
  generalize j / p = J at *
  generalize j % p = ℓ at *
  interval_cases J
  · rcases lt_or_ge (3 * p + ℓ) (P.H N) with hlt | hge
    · have := hcon (ℓ - P.b N) (by omega)
      rw [show 3 * p + P.b N + (ℓ - P.b N) = 3 * p + ℓ by omega, ← hcoef] at this
      rw [this, zero_mul]
    · rw [hhigh _ hge, zero_mul]
  · rw [hx1, mul_zero]
  · rw [hx2, mul_zero]
  · rw [hlow _ (by omega), zero_mul]

/-- **Theorem T (general design).** For `2g < p`, `H ≤ 4p`, `D ≥ 1`, the filtered scaled residue
matrix has rank at most `n - (D - (n+q+g+h-3p)_+)`; equivalently its left nullity is at least
`D - (n+q+g+h-3p)_+`, where `D = min g (n-1-g-2p) (C-3p)`. -/
theorem t_rank (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (h2g : 2 * P.g N < p) (hH4 : P.H N ≤ 4 * p) (hD : 1 ≤ tentD P N p) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val)).rank +
        (tentD P N p - (P.n N + P.q N + P.g N + P.h N - 3 * p)) ≤ P.n N := by
  obtain ⟨x0, x1, x2, hx, hx1, hx2⟩ := tent_exists_x p
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  have hHd : P.H N = P.C N + P.h N := rfl
  have hD1 : tentD P N p ≤ P.g N := min_le_left _ _
  have hD2 : tentD P N p ≤ P.n N - 1 - P.g N - 2 * p :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hbd : ∀ B < tentD P N p, B + 1 ≤ P.g N := fun B hB => by omega
  have hbn : ∀ B < tentD P N p, P.g N + 2 * p + (B + 1) < P.n N := fun B hB => by omega
  have hzp : (((p : ℚ) * 0).den : ZMod p) ≠ 0 := by simp
  have hq : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
  have hinj := tJ_injective x0 x1 x2 hx hbd hbn h2g
  let J : LinearMap.ker (secondaryTentConstraintMap (fun _ : Unit => P.H N - 3 * p - P.b N)
      (fun _ => tCon P N p)) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
    (tJ p (P.g N) (P.n N) (tentD P N p) x0 x1 x2).comp (Submodule.subtype _)
  have hr := secondaryTent_rank_of_raw_polynomial_responses (P := P) (p := p) (N := N)
    (V := Fin (tentD P N p) → ZMod p) hp2 hH 0 hzp (fun _ : Unit => P.H N - 3 * p - P.b N)
    (fun _ => tCon P N p) J (hinj.comp Subtype.val_injective) (by
      intro v
      refine ⟨0, by rw [natDegree_zero]; exact hq, ?_⟩
      intro j hj1 hj2
      have hv := (secondaryTentConstraintMap_eq_zero_iff _ _ v.1).mp v.2 ()
      rw [eval_zero]
      exact t_response hP hN hp2 hH h2g hH4 hD x0 x1 x2 hx1 hx2 v.1
        (fun a ha => by
          have := congrFun hv ⟨a, ha⟩
          rw [tCon_apply] at this
          exact this) hj1 hj2)
  simp only [Finset.univ_unique, Finset.sum_singleton, Module.finrank_fin_fun] at hr
  have e : tentD P N p - (P.H N - 3 * p - P.b N) =
      tentD P N p - (P.n N + P.q N + P.g N + P.h N - 3 * p) := by omega
  rw [e] at hr
  exact hr

end

end
end CatalanMeasure.GenD
