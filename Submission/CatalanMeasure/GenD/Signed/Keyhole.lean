module

public import Submission.CatalanMeasure.Parametric.PolynomialFunctional
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Keyhole bound for the weight of a column (PROOF-RHO Lemma KH) and Theorem K

Generic statements, no data.

* `keyhole_bound` (Lemma KH): for a real polynomial `P` and `F(t) = t^{-I} P(t)` (a Laurent
  polynomial with pole of order `≤ J` at `0`), the functional
  `λ = 4 [t^0] F(t) (1 - t^{-2})^{-1/2} = 4 Σ_l c_l [t^{I+2l}] P`, `c_l = C(2l,l)/4^l`, satisfies
  `|λ| ≤ 4 (1+J) max (M, B)` whenever `|F| ≤ M` on `|t| = r` and `|F| ≤ B` on the real
  segments `r ≤ |x| ≤ 1`, `0 < r ≤ 1`.
* `polynomialFunctional_keyhole_le`: the same for `polynomialFunctional` on a row common factor.
* `keyholePhi_circle`: Theorem K, on `|z| = r` the dependence of
  `Φ_κ = (a - bκ) log|z| + G(z)` on `κ` is the constant `(a - bκ) log r`.

The proof of the central step uses the finite Gauss–Chebyshev identity
`(1/M) Σ_{j<M} cos^{2l}((2j+1)π/(2M)) = C(2l,l)/4^l` (`l < M`) and the finite Cauchy formula
at `K`-th roots of unity, so no integrals appear.
-/

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Keyhole

open Polynomial Finset
open CatalanMeasure.Parametric

noncomputable section

/-! ### Roots of unity -/

/-- The primitive `K`-th root of unity `exp (2πi/K)`. -/
def rootK (K : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / K)

theorem rootK_prim {K : ℕ} (hK : 0 < K) : IsPrimitiveRoot (rootK K) K :=
  Complex.isPrimitiveRoot_exp K hK.ne'

theorem sum_zpow_geom {K : ℕ} (hK : 0 < K) {ζ : ℂ} (hp : IsPrimitiveRoot ζ K) (t : ℤ) :
    ∑ j ∈ range K, (ζ ^ t) ^ j = if (K : ℤ) ∣ t then (K : ℂ) else 0 := by
  split_ifs with h
  · have h1 : ζ ^ t = 1 := (hp.zpow_eq_one_iff_dvd t).2 h
    simp [h1]
  · have h1 : ζ ^ t ≠ 1 := fun h' => h ((hp.zpow_eq_one_iff_dvd t).1 h')
    rw [geom_sum_eq h1]
    have h2 : (ζ ^ t) ^ K = 1 := by
      rw [← zpow_natCast (ζ ^ t) K, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp.pow_eq_one,
        one_zpow]
    rw [h2]
    simp

/-! ### The finite Gauss–Chebyshev identity -/

/-- The Chebyshev angle `(2j+1)π/(2M)`. -/
def gcAngle (M j : ℕ) : ℝ := (2 * j + 1) * Real.pi / (2 * M)

/-- The central binomial weight `c_l = C(2l,l)/4^l`. -/
def centralR (l : ℕ) : ℝ := ((2 * l).choose l : ℝ) / 4 ^ l

theorem gc_v_zpow {M : ℕ} (hM : 0 < M) (j : ℕ) (t : ℤ) :
    (Complex.exp (2 * (gcAngle M j : ℂ) * Complex.I)) ^ t
      = Complex.exp (t * Real.pi * Complex.I / M) * ((rootK M) ^ t) ^ j := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have e1 : (Complex.exp (2 * (gcAngle M j : ℂ) * Complex.I)) ^ t
      = Complex.exp (t * (2 * (gcAngle M j : ℂ) * Complex.I)) := (Complex.exp_int_mul _ _).symm
  have e2 : (rootK M) ^ t = Complex.exp (t * (2 * Real.pi * Complex.I / M)) := by
    unfold rootK; exact (Complex.exp_int_mul _ _).symm
  have e3 : ((rootK M) ^ t) ^ j = Complex.exp (j * (t * (2 * Real.pi * Complex.I / M))) := by
    rw [e2, ← Complex.exp_nat_mul]
  rw [e1, e3, ← Complex.exp_add]
  congr 1
  unfold gcAngle
  push_cast
  field_simp
  ring

theorem two_cos_sq (θ : ℝ) :
    ((2 * Real.cos θ : ℝ) : ℂ) ^ 2
      = (Complex.exp (2 * (θ : ℂ) * Complex.I))⁻¹ * (1 + Complex.exp (2 * (θ : ℂ) * Complex.I)) ^ 2 := by
  have h1 : ((2 * Real.cos θ : ℝ) : ℂ) = Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹ := by
    push_cast
    rw [Complex.two_cos, neg_mul, Complex.exp_neg]
  have h2 : Complex.exp (2 * (θ : ℂ) * Complex.I) = (Complex.exp (θ * Complex.I)) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [h1, h2]
  have hu : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring

theorem gc_sum_two_cos_pow {M : ℕ} (hM : 0 < M) {l : ℕ} (hl : l < M) :
    ∑ j ∈ range M, (2 * Real.cos (gcAngle M j)) ^ (2 * l) = ((2 * l).choose l : ℝ) * M := by
  have hp := rootK_prim hM
  have key : ∑ j ∈ range M, ((2 * Real.cos (gcAngle M j) : ℝ) : ℂ) ^ (2 * l)
      = (((2 * l).choose l : ℝ) * M : ℝ) := by
    have hterm : ∀ j ∈ range M, ((2 * Real.cos (gcAngle M j) : ℝ) : ℂ) ^ (2 * l)
        = ∑ m ∈ range (2 * l + 1), (((2 * l).choose m : ℂ)) *
            (Complex.exp (2 * (gcAngle M j : ℂ) * Complex.I)) ^ ((m : ℤ) - l) := by
      intro j _
      have hv : Complex.exp (2 * (gcAngle M j : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      rw [pow_mul, two_cos_sq, mul_pow, ← pow_mul, add_comm (1 : ℂ), add_pow, mul_sum]
      apply sum_congr rfl
      intro m _
      rw [zpow_sub₀ hv, zpow_natCast, zpow_natCast, inv_pow, one_pow]
      field_simp
    rw [sum_congr rfl hterm, sum_comm]
    have hinner : ∀ m ∈ range (2 * l + 1),
        ∑ j ∈ range M, (((2 * l).choose m : ℂ)) *
            (Complex.exp (2 * (gcAngle M j : ℂ) * Complex.I)) ^ ((m : ℤ) - l)
          = (((2 * l).choose m : ℂ)) * (Complex.exp (((m : ℤ) - l : ℤ) * Real.pi * Complex.I / M) *
              (if (M : ℤ) ∣ ((m : ℤ) - l) then (M : ℂ) else 0)) := by
      intro m _
      rw [← mul_sum]
      congr 1
      simp_rw [gc_v_zpow hM]
      rw [← mul_sum, sum_zpow_geom hM hp]
    rw [sum_congr rfl hinner, sum_eq_single l]
    · simp
    · intro m hm hml
      rw [mem_range] at hm
      have hnd : ¬ (M : ℤ) ∣ ((m : ℤ) - l) := by
        intro hd
        have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
        omega
      rw [if_neg hnd]
      simp
    · intro h
      exfalso; apply h
      rw [mem_range]; omega
  exact_mod_cast key

theorem gc_sum_cos_pow_even {M : ℕ} (hM : 0 < M) {l : ℕ} (hl : l < M) :
    ∑ j ∈ range M, (Real.cos (gcAngle M j)) ^ (2 * l) = M * centralR l := by
  have h := gc_sum_two_cos_pow hM hl
  have h4 : ∀ j, (2 * Real.cos (gcAngle M j)) ^ (2 * l)
      = 4 ^ l * (Real.cos (gcAngle M j)) ^ (2 * l) := by
    intro j
    rw [mul_pow, pow_mul]
    norm_num
  simp_rw [h4, ← mul_sum] at h
  unfold centralR
  have h5 : (4 : ℝ) ^ l ≠ 0 := by positivity
  field_simp
  linarith

theorem gc_sum_cos_pow_odd {M : ℕ} (hM : 0 < M) (n : ℕ) (hn : Odd n) :
    ∑ j ∈ range M, (Real.cos (gcAngle M j)) ^ n = 0 := by
  have h := Finset.sum_range_reflect (fun j => (Real.cos (gcAngle M j)) ^ n) M
  have h2 : ∀ j ∈ range M, (fun j => (Real.cos (gcAngle M j)) ^ n) (M - 1 - j)
      = - (Real.cos (gcAngle M j)) ^ n := by
    intro j hj
    rw [mem_range] at hj
    have hc : Real.cos (gcAngle M (M - 1 - j)) = - Real.cos (gcAngle M j) := by
      have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      have : gcAngle M (M - 1 - j) = Real.pi - gcAngle M j := by
        unfold gcAngle
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        field_simp
        push_cast
        ring
      rw [this, Real.cos_pi_sub]
    simp only [hc]
    exact hn.neg_pow _
  rw [sum_congr rfl h2, sum_neg_distrib] at h
  linarith

theorem sum_range_two_mul {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ l ∈ range n, (f (2 * l) + f (2 * l + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ f (2 * n + 1),
      sum_range_succ f (2 * n), ih, sum_range_succ _ n, add_assoc]

/-- The finite Gauss–Chebyshev identity for polynomials of degree `< 2M`. -/
theorem gc_average (Q : ℝ[X]) {M : ℕ} (hM : 0 < M) (hdeg : Q.natDegree < 2 * M) :
    ∑ l ∈ range M, centralR l * Q.coeff (2 * l)
      = (1 / M) * ∑ j ∈ range M, Q.eval (Real.cos (gcAngle M j)) := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have h1 : ∀ j, Q.eval (Real.cos (gcAngle M j))
      = ∑ i ∈ range (2 * M), Q.coeff i * (Real.cos (gcAngle M j)) ^ i :=
    fun j => eval_eq_sum_range' hdeg _
  simp_rw [h1]
  rw [sum_comm]
  simp_rw [← mul_sum]
  rw [sum_range_two_mul, mul_sum]
  apply sum_congr rfl
  intro l hl
  rw [mem_range] at hl
  rw [gc_sum_cos_pow_even hM hl, gc_sum_cos_pow_odd hM (2 * l + 1) ⟨l, rfl⟩, mul_zero, add_zero]
  field_simp

/-- `|Σ c_l q_{2l}| ≤ B` when `|Q| ≤ B` on `[-1,1]`. -/
theorem gc_abs_le (Q : ℝ[X]) {M : ℕ} (hM : 0 < M) (hdeg : Q.natDegree < 2 * M) {B : ℝ}
    (hB : ∀ x : ℝ, |x| ≤ 1 → |Q.eval x| ≤ B) :
    |∑ l ∈ range M, centralR l * Q.coeff (2 * l)| ≤ B := by
  rw [gc_average Q hM hdeg]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 (by simp))
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / M)]
  have : |∑ j ∈ range M, Q.eval (Real.cos (gcAngle M j))| ≤ M * B := by
    calc _ ≤ ∑ j ∈ range M, |Q.eval (Real.cos (gcAngle M j))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range M, B := by
        apply sum_le_sum
        intro j _
        exact hB _ (Real.abs_cos_le_one _)
      _ = M * B := by simp
  calc 1 / (M : ℝ) * _ ≤ 1 / (M : ℝ) * (M * B) := by gcongr
    _ = B := by field_simp

/-! ### Finite Cauchy formula -/

theorem eval_map_eq_sum (P : ℝ[X]) {n : ℕ} (hn : P.natDegree < n) (z : ℂ) :
    (P.map (algebraMap ℝ ℂ)).eval z = ∑ i ∈ range n, (P.coeff i : ℂ) * z ^ i := by
  rw [Polynomial.eval_map, eval₂_eq_sum_range' _ hn]
  simp

theorem norm_eval_map_real (Q : ℝ[X]) (x : ℝ) :
    ‖(Q.map (algebraMap ℝ ℂ)).eval (x : ℂ)‖ = |Q.eval x| := by
  have : (Q.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((Q.eval x : ℝ) : ℂ) := by
    rw [Polynomial.eval_map]; exact eval₂_at_apply (algebraMap ℝ ℂ) x
  rw [this, Complex.norm_real, Real.norm_eq_abs]

theorem zpow_aux {ζ : ℂ} (hζ : ζ ≠ 0) (j n m : ℕ) :
    (ζ ^ j) ^ n * (ζ ^ (-(m : ℤ))) ^ j = (ζ ^ ((n : ℤ) - m)) ^ j := by
  rw [← zpow_natCast ζ j, ← zpow_natCast (ζ ^ (j : ℤ)) n, ← zpow_natCast (ζ ^ (-(m : ℤ))) j,
    ← zpow_natCast (ζ ^ ((n : ℤ) - m)) j, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ]
  congr 1
  ring

/-- Cauchy's coefficient estimate for a polynomial bounded on a circle (finite form). -/
theorem coeff_abs_mul_pow_le (P : ℝ[X]) {r B : ℝ} (hr : 0 < r)
    (h : ∀ z : ℂ, ‖z‖ = r → ‖(P.map (algebraMap ℝ ℂ)).eval z‖ ≤ B) (m : ℕ) :
    |P.coeff m| * r ^ m ≤ B := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (h r (by simp [abs_of_pos hr]))
  by_cases hm : P.natDegree < m
  · rw [coeff_eq_zero_of_natDegree_lt hm]; simpa using hB
  push_neg at hm
  have hK0 : 0 < P.natDegree + 1 := Nat.succ_pos _
  obtain ⟨K, hK⟩ : ∃ K, K = P.natDegree + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by omega
  have hdeg : P.natDegree < K := by omega
  have hmK : m < K := by omega
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = rootK K := ⟨_, rfl⟩
  have hp : IsPrimitiveRoot ζ K := hζ ▸ rootK_prim hK0
  have hζ0 : ζ ≠ 0 := hp.ne_zero hK0.ne'
  have hζ1 : ‖ζ‖ = 1 := hp.norm'_eq_one hK0.ne'
  have key : (K : ℂ) * ((P.coeff m : ℂ) * (r : ℂ) ^ m)
      = ∑ j ∈ range K, (P.map (algebraMap ℝ ℂ)).eval ((r : ℂ) * ζ ^ j) * (ζ ^ (-(m : ℤ))) ^ j := by
    have e1 : ∀ j, (P.map (algebraMap ℝ ℂ)).eval ((r : ℂ) * ζ ^ j) * (ζ ^ (-(m : ℤ))) ^ j
        = ∑ n ∈ range K, (P.coeff n : ℂ) * (r : ℂ) ^ n * (ζ ^ ((n : ℤ) - m)) ^ j := by
      intro j
      rw [eval_map_eq_sum P hdeg, sum_mul]
      apply sum_congr rfl
      intro n _
      rw [mul_pow, ← zpow_aux hζ0 j n m]
      ring
    rw [sum_congr rfl (fun j _ => e1 j), sum_comm]
    have e2 : ∀ n ∈ range K, ∑ j ∈ range K, (P.coeff n : ℂ) * (r : ℂ) ^ n * (ζ ^ ((n : ℤ) - m)) ^ j
        = (P.coeff n : ℂ) * (r : ℂ) ^ n * (if (K : ℤ) ∣ ((n : ℤ) - m) then (K : ℂ) else 0) := by
      intro n _
      rw [← mul_sum, sum_zpow_geom hK0 hp]
    rw [sum_congr rfl e2, sum_eq_single m]
    · simp [mul_comm]
    · intro n hn hnm
      rw [mem_range] at hn
      have hnd : ¬ (K : ℤ) ∣ ((n : ℤ) - m) := by
        intro hd
        have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
        omega
      rw [if_neg hnd]; simp
    · intro h; exact absurd (mem_range.2 hmK) h
  have hnorm := congrArg norm key
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr] at hnorm
  have hle : ‖∑ j ∈ range K, (P.map (algebraMap ℝ ℂ)).eval ((r : ℂ) * ζ ^ j) * (ζ ^ (-(m : ℤ))) ^ j‖
      ≤ K * B := by
    calc _ ≤ ∑ j ∈ range K, ‖(P.map (algebraMap ℝ ℂ)).eval ((r : ℂ) * ζ ^ j) * (ζ ^ (-(m : ℤ))) ^ j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ range K, B := by
        apply sum_le_sum
        intro j _
        rw [norm_mul, norm_pow, norm_zpow, hζ1, one_zpow, one_pow, mul_one]
        apply h
        rw [norm_mul, norm_pow, hζ1, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr]
      _ = K * B := by simp
  rw [← hnorm] at hle
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  nlinarith

/-! ### Lemma KH -/

/-- The functional `λ = 4 [t^0] t^{-I} P(t) (1 - t^{-2})^{-1/2} = 4 Σ_l c_l [t^{I+2l}] P`. -/
def keyholeFunctional (I : ℕ) (P : ℝ[X]) : ℝ :=
  4 * ∑ l ∈ range (P.natDegree + 1), centralR l * P.coeff (I + 2 * l)

/-- The polynomial part `Π(x) = Σ_{j ≥ 0} [t^{I+j}]P · x^j` of `t^{-I} P(t)`. -/
def polyPart (P : ℝ[X]) (I : ℕ) : ℝ[X] :=
  ∑ j ∈ range (P.natDegree + 1), C (P.coeff (I + j)) * X ^ j

theorem polyPart_coeff (P : ℝ[X]) (I j : ℕ) : (polyPart P I).coeff j = P.coeff (I + j) := by
  unfold polyPart
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range] at h
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]

theorem polyPart_natDegree_lt (P : ℝ[X]) (I : ℕ) : (polyPart P I).natDegree < P.natDegree + 1 := by
  have : (polyPart P I).natDegree ≤ P.natDegree := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [polyPart_coeff]
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  omega

theorem eval_split (P : ℝ[X]) (I : ℕ) (z : ℂ) :
    (P.map (algebraMap ℝ ℂ)).eval z =
      ∑ m ∈ range I, (P.coeff m : ℂ) * z ^ m
        + z ^ I * ((polyPart P I).map (algebraMap ℝ ℂ)).eval z := by
  have hlt : P.natDegree < I + (P.natDegree + 1) := by omega
  rw [eval_map_eq_sum P hlt, sum_range_add, eval_map_eq_sum _ (polyPart_natDegree_lt P I), mul_sum]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [polyPart_coeff, pow_add]
  ring

/-- The principal part is at most `J M` in size, relative to `|z|^I`, outside the circle `|z| = r`. -/
theorem principal_norm_le (P : ℝ[X]) (I J : ℕ) (hpole : ∀ m, m < I - J → P.coeff m = 0)
    {r M : ℝ} (hr : 0 < r)
    (hcirc : ∀ z : ℂ, ‖z‖ = r → ‖(P.map (algebraMap ℝ ℂ)).eval z‖ ≤ M * r ^ I)
    {z : ℂ} (hz : r ≤ ‖z‖) :
    ‖∑ m ∈ range I, (P.coeff m : ℂ) * z ^ m‖ ≤ J * (M * ‖z‖ ^ I) := by
  have hM : 0 ≤ M := by
    have h0 := le_trans (norm_nonneg _) (hcirc r (by simp [abs_of_pos hr]))
    have hrI : 0 < r ^ I := by positivity
    exact nonneg_of_mul_nonneg_left h0 hrI
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hterm : ∀ m ∈ range I, ‖(P.coeff m : ℂ) * z ^ m‖
      ≤ if I - J ≤ m then M * ‖z‖ ^ I else 0 := by
    intro m hm
    rw [mem_range] at hm
    split_ifs with h
    · have hc := coeff_abs_mul_pow_le P hr hcirc m
      have hrm : 0 < r ^ m := by positivity
      have h1 : |P.coeff m| ≤ M * r ^ (I - m) := by
        have : |P.coeff m| * r ^ m ≤ (M * r ^ (I - m)) * r ^ m := by
          calc _ ≤ M * r ^ I := hc
            _ = (M * r ^ (I - m)) * r ^ m := by
              rw [mul_assoc, ← pow_add]; congr 2; omega
        exact le_of_mul_le_mul_right this hrm
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      calc |P.coeff m| * ‖z‖ ^ m ≤ (M * r ^ (I - m)) * ‖z‖ ^ m := by gcongr
        _ ≤ (M * ‖z‖ ^ (I - m)) * ‖z‖ ^ m := by gcongr
        _ = M * ‖z‖ ^ I := by
          rw [mul_assoc, ← pow_add]; congr 2; omega
    · rw [hpole m (by omega)]; simp
  calc ‖∑ m ∈ range I, (P.coeff m : ℂ) * z ^ m‖
      ≤ ∑ m ∈ range I, ‖(P.coeff m : ℂ) * z ^ m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ range I, (if I - J ≤ m then M * ‖z‖ ^ I else 0) := sum_le_sum hterm
    _ = ∑ m ∈ (range I).filter (fun m => I - J ≤ m), M * ‖z‖ ^ I := by
        rw [sum_filter]
    _ = ((range I).filter (fun m => I - J ≤ m)).card * (M * ‖z‖ ^ I) := by simp
    _ ≤ J * (M * ‖z‖ ^ I) := by
        have hcard : ((range I).filter (fun m => I - J ≤ m)).card ≤ J := by
          calc _ ≤ (Ico (I - J) I).card := by
                apply card_le_card
                intro m hm
                simp only [mem_filter, mem_range] at hm
                simp only [mem_Ico]; omega
            _ ≤ J := by rw [Nat.card_Ico]; omega
        have : (0 : ℝ) ≤ M * ‖z‖ ^ I := by positivity
        have hc' : (((range I).filter (fun m => I - J ≤ m)).card : ℝ) ≤ J := by exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right hc' this

theorem polyPart_norm_mul_le (P : ℝ[X]) (I J : ℕ) (hpole : ∀ m, m < I - J → P.coeff m = 0)
    {r M : ℝ} (hr : 0 < r)
    (hcirc : ∀ z : ℂ, ‖z‖ = r → ‖(P.map (algebraMap ℝ ℂ)).eval z‖ ≤ M * r ^ I)
    {z : ℂ} (hz : r ≤ ‖z‖) :
    ‖((polyPart P I).map (algebraMap ℝ ℂ)).eval z‖ * ‖z‖ ^ I
      ≤ ‖(P.map (algebraMap ℝ ℂ)).eval z‖ + J * (M * ‖z‖ ^ I) := by
  have h1 := principal_norm_le P I J hpole hr hcirc hz
  have h2 : z ^ I * ((polyPart P I).map (algebraMap ℝ ℂ)).eval z
      = (P.map (algebraMap ℝ ℂ)).eval z - ∑ m ∈ range I, (P.coeff m : ℂ) * z ^ m := by
    rw [eval_split P I z]; ring
  have h3 : ‖z ^ I * ((polyPart P I).map (algebraMap ℝ ℂ)).eval z‖
      ≤ ‖(P.map (algebraMap ℝ ℂ)).eval z‖ + ‖∑ m ∈ range I, (P.coeff m : ℂ) * z ^ m‖ := by
    rw [h2]; exact norm_sub_le _ _
  rw [norm_mul, norm_pow] at h3
  linarith

/-- **Lemma KH** (keyhole bound). -/
theorem keyhole_bound (P : ℝ[X]) (I J : ℕ) (hpole : ∀ m, m < I - J → P.coeff m = 0)
    {r M B : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hcirc : ∀ z : ℂ, ‖z‖ = r → ‖(P.map (algebraMap ℝ ℂ)).eval z‖ ≤ M * r ^ I)
    (hseg : ∀ x : ℝ, r ≤ |x| → |x| ≤ 1 → |P.eval x| ≤ B * |x| ^ I) :
    |keyholeFunctional I P| ≤ 4 * (1 + J) * max M B := by
  have hM : 0 ≤ M := by
    have h0 := le_trans (norm_nonneg _) (hcirc r (by simp [abs_of_pos hr0]))
    have hrI : 0 < r ^ I := by positivity
    exact nonneg_of_mul_nonneg_left h0 hrI
  have hsphere : ∀ z : ℂ, ‖z‖ = r → ‖((polyPart P I).map (algebraMap ℝ ℂ)).eval z‖ ≤ (1 + J) * M := by
    intro z hz
    have hb := polyPart_norm_mul_le P I J hpole hr0 hcirc (le_of_eq hz.symm)
    have hc := hcirc z hz
    rw [hz] at hb
    have hrI : 0 < r ^ I := by positivity
    have : ‖((polyPart P I).map (algebraMap ℝ ℂ)).eval z‖ * r ^ I ≤ ((1 + J) * M) * r ^ I := by
      calc _ ≤ _ := hb
        _ ≤ M * r ^ I + J * (M * r ^ I) := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hrI
  have hball : ∀ z : ℂ, ‖z‖ ≤ r → ‖((polyPart P I).map (algebraMap ℝ ℂ)).eval z‖ ≤ (1 + J) * M := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le
      (f := fun w : ℂ => ((polyPart P I).map (algebraMap ℝ ℂ)).eval w)
      (U := Metric.ball (0 : ℂ) r) (Metric.isBounded_ball) ?_ ?_ ?_
    · exact (Polynomial.differentiable _).diffContOnCl
    · intro w hw
      rw [frontier_ball _ hr0.ne'] at hw
      exact hsphere w (by simpa using hw)
    · rw [closure_ball _ hr0.ne']
      simpa using hz
  have hPi : ∀ x : ℝ, |x| ≤ 1 → |(polyPart P I).eval x| ≤ (1 + J) * max M B := by
    intro x hx
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have hMB : M ≤ max M B := le_max_left _ _
    have hBM : B ≤ max M B := le_max_right _ _
    by_cases hxr : |x| ≤ r
    · have := hball (x : ℂ) (by simpa using hxr)
      rw [norm_eval_map_real] at this
      calc _ ≤ (1 + J) * M := this
        _ ≤ _ := by gcongr
    · push_neg at hxr
      have hn : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
      have hxz : r ≤ ‖(x : ℂ)‖ := by rw [hn]; exact hxr.le
      have hb := polyPart_norm_mul_le P I J hpole hr0 hcirc hxz
      rw [norm_eval_map_real (polyPart P I) x, norm_eval_map_real P x, hn] at hb
      have hxpos : 0 < |x| ^ I := by
        have : 0 < |x| := lt_trans hr0 hxr
        positivity
      have h2 := hseg x hxr.le hx
      have : |(polyPart P I).eval x| * |x| ^ I ≤ ((1 + J) * max M B) * |x| ^ I := by
        calc _ ≤ _ := hb
          _ ≤ B * |x| ^ I + J * (M * |x| ^ I) := by linarith
          _ ≤ max M B * |x| ^ I + J * (max M B * |x| ^ I) := by gcongr
          _ = _ := by ring
      exact le_of_mul_le_mul_right this hxpos
  -- Gauss–Chebyshev
  set D := P.natDegree + 1 with hD
  have hD0 : 0 < D := Nat.succ_pos _
  have hdeg : (polyPart P I).natDegree < 2 * D := by
    have := polyPart_natDegree_lt P I; omega
  have hgc := gc_abs_le (polyPart P I) hD0 hdeg hPi
  have hsum : ∑ l ∈ range D, centralR l * (polyPart P I).coeff (2 * l)
      = ∑ l ∈ range D, centralR l * P.coeff (I + 2 * l) := by
    apply sum_congr rfl; intro l _; rw [polyPart_coeff]
  rw [hsum] at hgc
  unfold keyholeFunctional
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc 4 * |∑ l ∈ range D, centralR l * P.coeff (I + 2 * l)|
      ≤ 4 * ((1 + J) * max M B) := by gcongr
    _ = _ := by ring

/-! ### Application to the Catalan functional -/

theorem kernel_even (l : ℕ) :
    (OAI.InternalCatalan.centralCoeffKernel ((2 * l : ℕ) : ℤ) : ℝ) = centralR l := by
  unfold OAI.InternalCatalan.centralCoeffKernel
  have h1 : (0 : ℤ) ≤ ((2 * l : ℕ) : ℤ) ∧ ((2 * l : ℕ) : ℤ) % 2 = 0 := ⟨by positivity, by omega⟩
  rw [if_pos h1]
  have h2 : ((2 * l : ℕ) : ℤ).toNat / 2 = l := by omega
  rw [h2]
  unfold OAI.InternalCatalan.centralCoeff centralR
  push_cast
  rfl

theorem kernel_odd (l : ℕ) :
    (OAI.InternalCatalan.centralCoeffKernel ((2 * l + 1 : ℕ) : ℤ) : ℝ) = 0 := by
  unfold OAI.InternalCatalan.centralCoeffKernel
  have h1 : ¬ ((0 : ℤ) ≤ ((2 * l + 1 : ℕ) : ℤ) ∧ ((2 * l + 1 : ℕ) : ℤ) % 2 = 0) := by
    rintro ⟨_, h⟩; omega
  rw [if_neg h1]
  simp

theorem polynomialFunctional_eq_keyhole (P : Parameters) (N k : ℕ) (Q : ℝ[X])
    (hdeg : ∀ i, P.H N ≤ i → Q.coeff i = 0) :
    polynomialFunctional P N k Q
      = keyholeFunctional (P.b N + k + P.q N) (Q * (X - 1) ^ (P.q N)) := by
  rw [polynomialFunctional_eq_coeff P N k Q hdeg]
  unfold keyholeFunctional
  congr 1
  set S := Q * (X - 1) ^ (P.q N) with hS
  set I := P.b N + k + P.q N with hI
  -- vanishing of high coefficients
  have hvan : ∀ e, P.H N ≤ e → S.coeff (I + e) = 0 := by
    intro e he
    rcases Nat.eq_zero_or_pos (P.H N) with h0 | hpos
    · have : Q = 0 := by
        ext i; simpa using hdeg i (by omega)
      simp [hS, this]
    · apply coeff_eq_zero_of_natDegree_lt
      have h1 : Q.natDegree ≤ P.H N - 1 := by
        rw [natDegree_le_iff_coeff_eq_zero]
        intro n hn; exact hdeg n (by omega)
      have h2 : ((X - 1 : ℝ[X]) ^ (P.q N)).natDegree ≤ P.q N := by
        refine (natDegree_pow_le).trans ?_
        have : (X - 1 : ℝ[X]).natDegree ≤ 1 := by compute_degree
        calc _ ≤ P.q N * 1 := by gcongr
          _ = _ := by ring
      have h3 : S.natDegree ≤ Q.natDegree + ((X - 1 : ℝ[X]) ^ (P.q N)).natDegree :=
        natDegree_mul_le
      omega
  set D := S.natDegree + 1 with hD
  have hvan2 : ∀ l, D ≤ l → S.coeff (I + 2 * l) = 0 := by
    intro l hl
    apply coeff_eq_zero_of_natDegree_lt; omega
  have hidx : ∀ d, P.b N + k + d + P.q N = I + d := by intro d; rw [hI]; ring
  simp_rw [hidx]
  -- extend to range (2 * L)
  set L := P.H N + D with hL
  have step1 : ∑ d ∈ range (P.H N),
        (OAI.InternalCatalan.centralCoeffKernel (d : ℤ) : ℝ) * S.coeff (I + d)
      = ∑ d ∈ range (2 * L),
        (OAI.InternalCatalan.centralCoeffKernel (d : ℤ) : ℝ) * S.coeff (I + d) := by
    apply sum_subset
    · intro d hd; rw [mem_range] at *; omega
    · intro d _ hd
      rw [mem_range] at hd
      rw [hvan d (by omega), mul_zero]
  have step2 : ∑ d ∈ range (2 * L),
        (OAI.InternalCatalan.centralCoeffKernel (d : ℤ) : ℝ) * S.coeff (I + d)
      = ∑ l ∈ range L, centralR l * S.coeff (I + 2 * l) := by
    rw [sum_range_two_mul]
    apply sum_congr rfl
    intro l _
    rw [kernel_even, kernel_odd]; simp
  have step3 : ∑ l ∈ range L, centralR l * S.coeff (I + 2 * l)
      = ∑ l ∈ range D, centralR l * S.coeff (I + 2 * l) := by
    symm
    apply sum_subset
    · intro l hl; rw [mem_range] at *; omega
    · intro l _ hl
      rw [mem_range] at hl
      rw [hvan2 l (by omega), mul_zero]
  rw [step1, step2, step3]

/-- **Lemma KH for the Catalan functional.**  With `S = X^A (1-X)^h R (X-1)^q` and
`I = b + k + q`, the weight `|polynomialFunctional P N k (rowCommonFactor P N * R)|` of column
`k` is at most `4 (1 + J) max(M, B)`, `J = I - A`, where `M` bounds
`|S(t)| / |t|^I` on `|t| = r` and `B` bounds it on `r ≤ |x| ≤ 1`. -/
theorem polynomialFunctional_keyhole_le (P : Parameters) (N k : ℕ) (R : ℝ[X])
    (hdeg : ∀ i, P.H N ≤ i → (rowCommonFactor P N * R).coeff i = 0)
    {r M B : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hcirc : ∀ z : ℂ, ‖z‖ = r →
      ‖(((rowCommonFactor P N * R) * (X - 1) ^ (P.q N)).map (algebraMap ℝ ℂ)).eval z‖
        ≤ M * r ^ (P.b N + k + P.q N))
    (hseg : ∀ x : ℝ, r ≤ |x| → |x| ≤ 1 →
      |((rowCommonFactor P N * R) * (X - 1) ^ (P.q N)).eval x|
        ≤ B * |x| ^ (P.b N + k + P.q N)) :
    |polynomialFunctional P N k (rowCommonFactor P N * R)|
      ≤ 4 * (1 + ((P.b N + k + P.q N - P.A N : ℕ) : ℝ)) * max M B := by
  rw [polynomialFunctional_eq_keyhole P N k _ hdeg]
  apply keyhole_bound _ (P.b N + k + P.q N) (P.b N + k + P.q N - P.A N) _ hr0 hr1 hcirc hseg
  intro m hm
  have hS : (rowCommonFactor P N * R) * (X - 1) ^ (P.q N)
      = X ^ (P.A N) * ((1 - X) ^ (P.h N) * R * (X - 1) ^ (P.q N)) := by
    unfold rowCommonFactor; ring
  rw [hS, coeff_X_pow_mul', if_neg (by omega)]

/-! ### Theorem K -/

/-- `Φ_κ(z) = (a - bκ) log |z| + G(z)` (PROOF-RHO: `a = 10`, `b = 58`,
`G = 6 log|1-z| + 53 g_S`). -/
def keyholePhi (a b : ℝ) (G : ℂ → ℝ) (κ : ℝ) (z : ℂ) : ℝ :=
  (a - b * κ) * Real.log ‖z‖ + G z

/-- **Theorem K.** On `|z| = r` the `κ`-dependence of `Φ_κ` is the constant `(a - bκ) log r`. -/
theorem keyholePhi_circle (a b : ℝ) (G : ℂ → ℝ) (κ : ℝ) {r : ℝ} {z : ℂ} (hz : ‖z‖ = r) :
    keyholePhi a b G κ z = (a - b * κ) * Real.log r + G z := by
  unfold keyholePhi; rw [hz]

/-- One 1-D bound on the circle serves every `κ`. -/
theorem keyholePhi_circle_le (a b : ℝ) (G : ℂ → ℝ) {r Gmax : ℝ}
    (hG : ∀ z : ℂ, ‖z‖ = r → G z ≤ Gmax) (κ : ℝ) :
    ∀ z : ℂ, ‖z‖ = r → keyholePhi a b G κ z ≤ (a - b * κ) * Real.log r + Gmax := by
  intro z hz
  rw [keyholePhi_circle a b G κ hz]
  linarith [hG z hz]

/-- Conversely, the `κ`-bound on the circle gives the `G`-bound. -/
theorem keyholePhi_circle_iff (a b : ℝ) (G : ℂ → ℝ) {r Gmax : ℝ} (κ : ℝ) :
    (∀ z : ℂ, ‖z‖ = r → keyholePhi a b G κ z ≤ (a - b * κ) * Real.log r + Gmax)
      ↔ ∀ z : ℂ, ‖z‖ = r → G z ≤ Gmax := by
  constructor
  · intro h z hz
    have := h z hz
    rw [keyholePhi_circle a b G κ hz] at this
    linarith
  · intro h; exact keyholePhi_circle_le a b G h κ

/-- The circle values are an affine function of `κ` plus a `κ`-free term; the supremum over a
range of `κ` is attained at an endpoint. -/
theorem keyholePhi_circle_affine (a b : ℝ) (G : ℂ → ℝ) {r : ℝ} {z : ℂ} (hz : ‖z‖ = r)
    {κ₀ κ₁ : ℝ} (hκ : κ₀ ≤ κ₁) {κ : ℝ} (h0 : κ₀ ≤ κ) (h1 : κ ≤ κ₁) :
    keyholePhi a b G κ z ≤ max (keyholePhi a b G κ₀ z) (keyholePhi a b G κ₁ z) := by
  rw [keyholePhi_circle a b G κ hz, keyholePhi_circle a b G κ₀ hz,
    keyholePhi_circle a b G κ₁ hz]
  rcases le_total 0 (b * Real.log r) with hb | hb
  · apply le_max_of_le_left
    nlinarith [mul_nonneg hb (sub_nonneg.2 h0)]
  · apply le_max_of_le_right
    nlinarith [mul_nonneg (neg_nonneg.2 hb) (sub_nonneg.2 h1)]

end

end CatalanMeasure.GenD.Signed.Keyhole

/-! ### Audit -/
#print axioms CatalanMeasure.GenD.Signed.Keyhole.gc_average
#print axioms CatalanMeasure.GenD.Signed.Keyhole.coeff_abs_mul_pow_le
#print axioms CatalanMeasure.GenD.Signed.Keyhole.keyhole_bound
#print axioms CatalanMeasure.GenD.Signed.Keyhole.polynomialFunctional_keyhole_le
#print axioms CatalanMeasure.GenD.Signed.Keyhole.keyholePhi_circle
#print axioms CatalanMeasure.GenD.Signed.Keyhole.keyholePhi_circle_affine
