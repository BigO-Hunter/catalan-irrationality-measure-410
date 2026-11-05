module

public import Submission.CatalanMeasure.Quadrature
public import Submission.CatalanMeasure.ChebyshevNodes
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section

/-!
# Quadrature weights bounded on the unit circle

The quadrature weights are `β_{a,k} = 4 Σ_d c_d g_{b+k+q+d}` with `g = ℓ_a · (X - 1)^q`,
where `ℓ_a` is the Lagrange basis polynomial at the Chebyshev nodes on `[-1, 0]` and `c_d ≤ 1`.
Each coefficient of `g` is at most `max_{|t| = 1} |g(t)|` (an average over roots of unity), and
on the unit circle `|ℓ_a(t)| ≤ |T_J(2t + 1)| / (2J |t - τ_a|)`.  With
`|T_J(ζ)| ≤ (S + √(S² - 1))^J`, `S = (|ζ - 1| + |ζ + 1|) / 2`, this replaces the factor
`2^q (3 + 2√2)^J` of the coefficient bound by about `exp(110.45 N)`.
-/

open Polynomial Finset Complex

namespace CatalanMeasure

/-! ### Coefficients from values on the unit circle -/

theorem sum_rootsOfUnity_pow {M : ℕ} (hM : 0 < M) (s : ℕ) :
    ∑ j ∈ range M, (Complex.exp (2 * Real.pi * I / M)) ^ (j * s) =
      if M ∣ s then (M : ℂ) else 0 := by
  set ω := Complex.exp (2 * Real.pi * I / M)
  have hω : IsPrimitiveRoot ω M := Complex.isPrimitiveRoot_exp M hM.ne'
  have hpow : ∀ j, ω ^ (j * s) = (ω ^ s) ^ j := fun j => by rw [← pow_mul, mul_comm]
  simp_rw [hpow]
  split_ifs with hd
  · obtain ⟨c, rfl⟩ := hd
    have : ω ^ (M * c) = 1 := by rw [pow_mul, hω.pow_eq_one, one_pow]
    simp [this]
  · have hne : ω ^ s ≠ 1 := by
      intro h
      exact hd (hω.dvd_of_pow_eq_one s h)
    rw [geom_sum_eq hne]
    have : (ω ^ s) ^ M = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    simp [this]

/-- A coefficient of a polynomial is bounded by its maximum modulus on the unit circle. -/
theorem abs_coeff_le_of_circle (p : ℝ[X]) {C : ℝ}
    (hC : ∀ t : ℂ, ‖t‖ = 1 → ‖(p.map (algebraMap ℝ ℂ)).eval t‖ ≤ C) (m : ℕ) :
    |p.coeff m| ≤ C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 (by simp))
  set M := max p.natDegree m + 1 with hM
  have hMpos : 0 < M := by omega
  set ω := Complex.exp (2 * Real.pi * I / M)
  have hω : IsPrimitiveRoot ω M := Complex.isPrimitiveRoot_exp M hMpos.ne'
  have hω1 : ‖ω‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.div_re]
  have hωn : ∀ j, ‖ω ^ j‖ = 1 := fun j => by
    rw [norm_pow, hω1, one_pow]
  -- the averaging identity
  have key : ∑ j ∈ range M, (p.map (algebraMap ℝ ℂ)).eval (ω ^ j) * (ω ^ j) ^ (M - m) =
      (M : ℂ) * (p.coeff m : ℂ) := by
    have hdeg : p.natDegree < M := by omega
    simp_rw [eval_eq_sum_range' (n := M) (lt_of_le_of_lt natDegree_map_le hdeg), sum_mul]
    rw [sum_comm]
    have hterm : ∀ i ∈ range M, ∑ j ∈ range M, (p.map (algebraMap ℝ ℂ)).coeff i * (ω ^ j) ^ i *
        (ω ^ j) ^ (M - m) = if i = m then (M : ℂ) * (p.coeff m : ℂ) else 0 := by
      intro i hi
      have hi' : i < M := mem_range.mp hi
      have hrw : ∀ j, (p.map (algebraMap ℝ ℂ)).coeff i * (ω ^ j) ^ i * (ω ^ j) ^ (M - m) =
          (p.coeff i : ℂ) * ω ^ (j * (i + (M - m))) := by
        intro j
        rw [coeff_map, mul_assoc, ← pow_add, ← pow_mul, mul_add]
        rfl
      rw [Finset.sum_congr rfl (fun j _ => hrw j), ← mul_sum, sum_rootsOfUnity_pow hMpos]
      split_ifs with h1 h2 h2
      · subst h2; ring
      · exfalso
        obtain ⟨c, hc⟩ := h1
        have hm : m < M := by omega
        rcases c with _ | _ | c
        · omega
        · omega
        · have : M * (c + 1 + 1) ≥ 2 * M := by nlinarith
          omega
      · exfalso; apply h1; subst h2; exact ⟨1, by omega⟩
      · simp
    rw [sum_congr rfl hterm, sum_ite_eq']
    simp only [mem_range]
    rw [if_pos (by omega)]
  have hbound : ‖(M : ℂ) * (p.coeff m : ℂ)‖ ≤ M * C := by
    rw [← key]
    calc ‖∑ j ∈ range M, (p.map (algebraMap ℝ ℂ)).eval (ω ^ j) * (ω ^ j) ^ (M - m)‖
        ≤ ∑ j ∈ range M, ‖(p.map (algebraMap ℝ ℂ)).eval (ω ^ j) * (ω ^ j) ^ (M - m)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j ∈ range M, C := by
          apply sum_le_sum
          intro j _
          rw [norm_mul, norm_pow, hωn, one_pow, mul_one]
          exact hC _ (hωn j)
      _ = M * C := by simp
  rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs] at hbound
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  nlinarith

/-! ### Chebyshev polynomials off the real line -/

theorem cosh_re_im (x y : ℝ) : Complex.cosh ((x : ℂ) + (y : ℂ) * I) =
    ((Real.cosh x * Real.cos y : ℝ) : ℂ) + ((Real.sinh x * Real.sin y : ℝ) : ℂ) * I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

theorem sinh_re_im (x y : ℝ) : Complex.sinh ((x : ℂ) + (y : ℂ) * I) =
    ((Real.sinh x * Real.cos y : ℝ) : ℂ) + ((Real.cosh x * Real.sin y : ℝ) : ℂ) * I := by
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

theorem normSq_re_im (a b : ℝ) : ‖((a : ℂ) + (b : ℂ) * I)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

theorem norm_sinh_sq_add_norm_cosh_sq (u : ℂ) :
    ‖Complex.sinh u‖ ^ 2 + ‖Complex.cosh u‖ ^ 2 = Real.cosh (2 * u.re) := by
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, u = (x : ℂ) + (y : ℂ) * I := ⟨u.re, u.im, (Complex.re_add_im u).symm⟩
  rw [sinh_re_im, cosh_re_im, normSq_re_im, normSq_re_im]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [Real.cosh_two_mul]
  have h1 := Real.sin_sq_add_cos_sq y
  linear_combination (Real.sinh x ^ 2 + Real.cosh x ^ 2) * h1

theorem norm_cosh_sub_one_add (w : ℂ) :
    ‖Complex.cosh w - 1‖ + ‖Complex.cosh w + 1‖ = 2 * Real.cosh w.re := by
  have h1 : Complex.cosh w - 1 = 2 * Complex.sinh (w / 2) ^ 2 := by
    have := Complex.cosh_two_mul (w / 2)
    rw [show 2 * (w / 2) = w by ring] at this
    rw [this, Complex.cosh_sq]; ring
  have h2 : Complex.cosh w + 1 = 2 * Complex.cosh (w / 2) ^ 2 := by
    have := Complex.cosh_two_mul (w / 2)
    rw [show 2 * (w / 2) = w by ring] at this
    rw [this, Complex.cosh_sq]; ring
  rw [h1, h2, norm_mul, norm_mul, norm_pow, norm_pow]
  have := norm_sinh_sq_add_norm_cosh_sq (w / 2)
  rw [show 2 * (w / 2).re = w.re by simp; ring] at this
  simp only [Complex.norm_ofNat]
  linarith

theorem norm_cosh_le (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, z = (x : ℂ) + (y : ℂ) * I := ⟨z.re, z.im, (Complex.re_add_im z).symm⟩
  have hs : ‖Complex.cosh ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤ Real.cosh x ^ 2 := by
    rw [cosh_re_im, normSq_re_im]
    have h1 := Real.sin_sq_add_cos_sq y
    have h2 := Real.cosh_sq x
    nlinarith [sq_nonneg (Real.sinh x * Real.sin y), sq_nonneg (Real.cosh x * Real.sin y)]
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  rw [hre]
  have hc : 0 ≤ Real.cosh x := (Real.cosh_pos _).le
  nlinarith [norm_nonneg (Complex.cosh ((x : ℂ) + (y : ℂ) * I))]

/-- `|T_J(ζ)| ≤ (S + √(S² - 1))^J` with `S = (|ζ - 1| + |ζ + 1|) / 2`. -/
theorem norm_T_eval_le (J : ℕ) (ζ : ℂ) :
    ‖(Chebyshev.T ℂ (J : ℤ)).eval ζ‖ ≤
      ((‖ζ - 1‖ + ‖ζ + 1‖) / 2 + √(((‖ζ - 1‖ + ‖ζ + 1‖) / 2) ^ 2 - 1)) ^ J := by
  obtain ⟨θ, rfl⟩ := Complex.cos_surjective ζ
  set w := θ * I with hw
  have hcw : Complex.cos θ = Complex.cosh w := by rw [hw, Complex.cosh_mul_I]
  rw [Chebyshev.T_complex_cos, hcw, norm_cosh_sub_one_add]
  have hJ : Complex.cos (((J : ℤ) : ℂ) * θ) = Complex.cosh (((J : ℤ) : ℂ) * w) := by
    rw [hw, ← mul_assoc, Complex.cosh_mul_I]
  rw [hJ]
  have hS : 2 * Real.cosh w.re / 2 = Real.cosh w.re := by ring
  rw [hS]
  have hsq : √(Real.cosh w.re ^ 2 - 1) = |Real.sinh w.re| := by
    rw [Real.cosh_sq]; ring_nf; rw [Real.sqrt_sq_eq_abs]
  rw [hsq]
  have he : Real.cosh w.re + |Real.sinh w.re| = Real.exp |w.re| := by
    rcases le_total 0 w.re with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr h), Real.cosh_add_sinh]
    · rw [abs_of_nonpos h, abs_of_nonpos (Real.sinh_nonpos_iff.mpr h), ← Real.cosh_neg,
        ← Real.sinh_neg, Real.cosh_add_sinh]
  rw [he, ← Real.exp_nat_mul]
  calc ‖Complex.cosh ((J : ℤ) * w)‖ ≤ Real.cosh (((J : ℤ) : ℂ) * w).re := norm_cosh_le _
    _ ≤ Real.exp |(((J : ℤ) : ℂ) * w).re| := by
        rw [Real.cosh_eq]
        have h1 := Real.exp_le_exp.mpr (le_abs_self ((((J : ℤ) : ℂ) * w).re))
        have h2 := Real.exp_le_exp.mpr (neg_le_abs ((((J : ℤ) : ℂ) * w).re))
        linarith
    _ = Real.exp (J * |w.re|) := by
        congr 1
        simp [abs_mul]


/-! ### The one-variable inequality on the unit circle -/

/-- The bound `K` for `(1 + s + √(s² + 2s))^65 (4 - s²)^2` on `[0, 2]`. -/
@[irreducible] def circleK : ℚ := 95 * 10 ^ 46

/-- Pieces `(s₀, s₁, u)` with `u ≥ √(s₁² + 2 s₁)`. -/
def circlePieces : List (ℚ × ℚ × ℚ) := [((0 : ℚ), (17169 / 10000 : ℚ), (1263087 / 500000 : ℚ)),
  ((17169 / 10000 : ℚ), (1823 / 1000 : ℚ), (52799 / 20000 : ℚ)),
  ((1823 / 1000 : ℚ), (18591 / 10000 : ℚ), (1339259 / 500000 : ℚ)),
  ((18591 / 10000 : ℚ), (4693 / 2500 : ℚ), (269783 / 100000 : ℚ)),
  ((4693 / 2500 : ℚ), (18883 / 10000 : ℚ), (541933 / 200000 : ℚ)),
  ((18883 / 10000 : ℚ), (237 / 125 : ℚ), (2717871 / 1000000 : ℚ)),
  ((237 / 125 : ℚ), (9509 / 5000 : ℚ), (2724051 / 1000000 : ℚ)),
  ((9509 / 5000 : ℚ), (3813 / 2000 : ℚ), (2729057 / 1000000 : ℚ)),
  ((3813 / 2000 : ℚ), (3821 / 2000 : ℚ), (683329 / 250000 : ℚ)),
  ((3821 / 2000 : ℚ), (19141 / 10000 : ℚ), (2737149 / 1000000 : ℚ)),
  ((19141 / 10000 : ℚ), (767 / 400 : ℚ), (2740769 / 1000000 : ℚ)),
  ((767 / 400 : ℚ), (2401 / 1250 : ℚ), (2744281 / 1000000 : ℚ)),
  ((2401 / 1250 : ℚ), (9621 / 5000 : ℚ), (27479 / 10000 : ℚ)),
  ((9621 / 5000 : ℚ), (9639 / 5000 : ℚ), (2751731 / 1000000 : ℚ)),
  ((9639 / 5000 : ℚ), (19319 / 10000 : ℚ), (2756093 / 1000000 : ℚ)),
  ((19319 / 10000 : ℚ), (19367 / 10000 : ℚ), (1380599 / 500000 : ℚ)),
  ((19367 / 10000 : ℚ), (4857 / 2500 : ℚ), (553537 / 200000 : ℚ)),
  ((4857 / 2500 : ℚ), (9757 / 5000 : ℚ), (2776827 / 1000000 : ℚ)),
  ((9757 / 5000 : ℚ), (19651 / 10000 : ℚ), (348923 / 125000 : ℚ)),
  ((19651 / 10000 : ℚ), (9967 / 5000 : ℚ), (2821427 / 1000000 : ℚ)),
  ((9967 / 5000 : ℚ), (2 : ℚ), (2828429 / 1000000 : ℚ))]

def circlePieceOK (p : ℚ × ℚ × ℚ) : Bool :=
  decide (0 ≤ p.1) && decide (p.1 ≤ p.2.1) && decide (p.2.1 ≤ 2) && decide (0 ≤ p.2.2) &&
    decide (p.2.1 * p.2.1 + 2 * p.2.1 ≤ p.2.2 * p.2.2) &&
    decide ((1 + p.2.1 + p.2.2) ^ 65 * (4 - p.1 * p.1) ^ 2 ≤ circleK)

def circleCovers : ℚ → List (ℚ × ℚ × ℚ) → Bool
  | c, [] => decide (c = 2)
  | c, p :: l => decide (p.1 = c) && circlePieceOK p && circleCovers p.2.1 l

theorem circleCovers_spec {c : ℚ} {l : List (ℚ × ℚ × ℚ)} (h : circleCovers c l = true)
    {s : ℝ} (hs : (c : ℝ) ≤ s) (hs2 : s ≤ 2) :
    (1 + s + √(s ^ 2 + 2 * s)) ^ 65 * (4 - s ^ 2) ^ 2 ≤ (circleK : ℝ) := by
  induction l generalizing c with
  | nil =>
    simp only [circleCovers, decide_eq_true_eq] at h
    subst h
    have : s = 2 := le_antisymm hs2 (by exact_mod_cast hs)
    subst this
    unfold circleK
    norm_num
  | cons p l ih =>
    simp only [circleCovers, circlePieceOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc, ⟨⟨⟨⟨⟨h0, h01⟩, h12⟩, hu0⟩, hu⟩, hK⟩⟩, hrest⟩ := h
    subst hc
    by_cases hs1 : s ≤ p.2.1
    · have hs0 : (0 : ℝ) ≤ s := le_trans (by exact_mod_cast h0) hs
      have hsq : √(s ^ 2 + 2 * s) ≤ p.2.2 := by
        rw [Real.sqrt_le_left (by exact_mod_cast hu0)]
        have : (p.2.1 : ℝ) * p.2.1 + 2 * p.2.1 ≤ p.2.2 * p.2.2 := by exact_mod_cast hu
        nlinarith
      have hA : 1 + s + √(s ^ 2 + 2 * s) ≤ (1 : ℝ) + p.2.1 + p.2.2 := by linarith
      have hB : (4 - s ^ 2) ^ 2 ≤ (4 - (p.1 : ℝ) * p.1) ^ 2 := by
        have h1 : 0 ≤ 4 - s ^ 2 := by nlinarith
        have h2 : 4 - s ^ 2 ≤ 4 - (p.1 : ℝ) * p.1 := by
          have : (0 : ℝ) ≤ p.1 := by exact_mod_cast h0
          nlinarith
        exact pow_le_pow_left₀ h1 h2 2
      have hK' : ((1 + p.2.1 + p.2.2) ^ 65 * (4 - p.1 * p.1) ^ 2 : ℚ) ≤ circleK := hK
      have hK'' : ((1 : ℝ) + p.2.1 + p.2.2) ^ 65 * (4 - (p.1 : ℝ) * p.1) ^ 2 ≤ circleK := by
        have := (Rat.cast_le (K := ℝ)).mpr hK'
        simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_sub, Rat.cast_one,
          Rat.cast_ofNat] at this
        exact this
      clear hK hK'
      calc (1 + s + √(s ^ 2 + 2 * s)) ^ 65 * (4 - s ^ 2) ^ 2
          ≤ ((1 : ℝ) + p.2.1 + p.2.2) ^ 65 * (4 - (p.1 : ℝ) * p.1) ^ 2 := by
            have hp1 : (0 : ℝ) ≤ p.2.1 := le_trans hs0 hs1
            have hp2 : (0 : ℝ) ≤ p.2.2 := by exact_mod_cast hu0
            have hsq0 := Real.sqrt_nonneg (s ^ 2 + 2 * s)
            have hA0 : (0 : ℝ) ≤ 1 + s + √(s ^ 2 + 2 * s) := by linarith only [hs0, hsq0]
            have hB0 : (0 : ℝ) ≤ (1 : ℝ) + p.2.1 + p.2.2 := by linarith only [hp1, hp2]
            have hfirst := pow_le_pow_left₀ hA0 hA 65
            exact mul_le_mul hfirst hB (sq_nonneg _) (pow_nonneg hB0 65)
        _ ≤ (circleK : ℝ) := hK''
    · exact ih hrest (le_of_lt (not_le.mp hs1))

theorem circleCovers_true : circleCovers 0 circlePieces = true := by decide +kernel

theorem circle_ineq {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    (1 + s + √(s ^ 2 + 2 * s)) ^ 65 * (4 - s ^ 2) ^ 2 ≤ (circleK : ℝ) :=
  circleCovers_spec circleCovers_true (by simpa using hs0) hs2



end CatalanMeasure

namespace OAI.InternalCatalan

open Polynomial Finset

/-! ### The weights as coefficients of `ℓ_a (X - 1)^q` -/

theorem sum_shift_kernel {H m : ℕ} (f : ℕ → ℝ) (hf : ∀ i, H ≤ i → f i = 0) :
    ∑ i ∈ range H, f i * (centralCoeffKernel ((i : ℤ) - (m : ℤ)) : ℝ) =
      ∑ d ∈ range H, f (m + d) * (centralCoeffKernel (d : ℤ) : ℝ) := by
  have h1 : ∑ i ∈ range H, f i * (centralCoeffKernel ((i : ℤ) - (m : ℤ)) : ℝ) =
      ∑ i ∈ range (m + H), f i * (centralCoeffKernel ((i : ℤ) - (m : ℤ)) : ℝ) := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro i hi hni
    simp only [mem_range, not_lt] at hi hni
    rw [hf i hni, zero_mul]
  rw [h1, ← sum_range_add_sum_Ico _ (by omega : m ≤ m + H), sum_Ico_eq_sum_range]
  have h2 : ∑ i ∈ range m, f i * (centralCoeffKernel ((i : ℤ) - (m : ℤ)) : ℝ) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp only [mem_range] at hi
    unfold centralCoeffKernel
    rw [if_neg (by omega)]
    simp
  rw [h2, zero_add, show m + H - m = H by omega]
  apply sum_congr rfl
  intro d _
  congr 3
  push_cast
  ring

theorem coeff_mul_X_sub_one_pow (ℓ : ℝ[X]) (Q j : ℕ) :
    (ℓ * (X - 1) ^ Q).coeff (j + Q) =
      ∑ v ∈ range (Q + 1), (-1 : ℝ) ^ v * (Q.choose v : ℝ) * ℓ.coeff (j + v) := by
  rw [sub_pow, mul_sum, finset_sum_coeff]
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro v hv
  simp only [mem_range] at hv
  have hm : Q + 1 - 1 - v ≤ j + Q := by omega
  rw [one_pow, mul_one, show ℓ * ((-1 : ℝ[X]) ^ (Q + 1 - 1 - v + Q) * X ^ (Q + 1 - 1 - v) *
      ((Q.choose (Q + 1 - 1 - v) : ℕ) : ℝ[X])) =
      C ((-1 : ℝ) ^ (Q + 1 - 1 - v + Q) * (Q.choose (Q + 1 - 1 - v) : ℝ)) * (ℓ * X ^ (Q + 1 - 1 - v)) by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]; ring]
  rw [coeff_C_mul, coeff_mul_X_pow', if_pos hm]
  have he : j + Q - (Q + 1 - 1 - v) = j + v := by omega
  rw [he, show Q + 1 - 1 - v = Q - v by omega, Nat.choose_symm (by omega)]
  congr 1
  have hp : Q - v + Q = 2 * (Q - v) + v := by omega
  rw [hp, pow_add, pow_mul]
  norm_num

/-- The quadrature weight as a combination of coefficients of `ℓ_a (X - 1)^q`. -/
theorem quadWeight_eq_coeff (N : ℕ) (τ : Fin (H N) → ℝ) (a : Fin (H N)) (k : ℕ) :
    quadWeight N τ a k = 4 * ∑ d ∈ range (H N), (centralCoeffKernel (d : ℤ) : ℝ) *
      (quadBasis τ a * (X - 1) ^ q N).coeff (b N + k + d + q N) := by
  have hdeg : ∀ i, H N ≤ i → (quadBasis τ a).coeff i = 0 := by
    intro i hi
    apply coeff_eq_zero_of_natDegree_lt
    rw [quadBasis_eq]
    calc (C (∏ c ∈ univ.erase a, (τ a - τ c)⁻¹) * ∏ c ∈ univ.erase a, (X - C (τ c))).natDegree
        ≤ (∏ c ∈ univ.erase a, (X - C (τ c))).natDegree := natDegree_C_mul_le _ _
      _ ≤ ∑ c ∈ univ.erase a, (X - C (τ c)).natDegree := natDegree_prod_le _ _
      _ = H N - 1 := by
          simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]
          rw [card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin]
      _ < i := by have := a.isLt; omega
  unfold quadWeight
  have hstep : ∀ v ∈ range (q N + 1), (filterCoeffRat N v : ℝ) *
      ∑ i ∈ range (H N), (quadBasis τ a).coeff i *
        (4 * (centralCoeffKernel ((i : ℤ) - ((b N + k + v : ℕ) : ℤ)) : ℝ)) =
      4 * ∑ d ∈ range (H N), (filterCoeffRat N v : ℝ) * (quadBasis τ a).coeff (b N + k + v + d) *
        (centralCoeffKernel (d : ℤ) : ℝ) := by
    intro v _
    have := sum_shift_kernel (H := H N) (m := b N + k + v) (fun i => (quadBasis τ a).coeff i)
      (hdeg)
    simp_rw [mul_left_comm _ (4 : ℝ), ← mul_sum, this, mul_sum]
    ring_nf
  rw [sum_congr rfl hstep, ← mul_sum, sum_comm]
  congr 1
  apply sum_congr rfl
  intro d _
  rw [show b N + k + d + q N = (b N + k + d) + q N by ring, coeff_mul_X_sub_one_pow, mul_sum]
  apply sum_congr rfl
  intro v _
  unfold filterCoeffRat
  push_cast
  rw [show b N + k + d + v = b N + k + v + d by ring]
  ring


end OAI.InternalCatalan

namespace CatalanMeasure

open Polynomial Polynomial.Chebyshev Finset

theorem chebNode_den_ge {J : ℕ} (a : Fin J) :
    (J : ℝ) / (2 ^ (J - 1) * 2 ^ (J - 1)) ≤
      |∏ c ∈ univ.erase a, (chebNode J a - chebNode J c)| := by
  have hJ : 0 < J := by have := a.isLt; omega
  have hTeq := T_eq_nodal hJ
  set ω : ℝ[X] := ∏ c : Fin J, (X - C (chebX J c)) with hω
  have h2pos : (0 : ℝ) < 2 ^ (J - 1) := by positivity
  have hprod : ∏ c ∈ univ.erase a, (chebNode J a - chebNode J c) =
      (∏ c ∈ univ.erase a, (chebX J a - chebX J c)) / 2 ^ (J - 1) := by
    rw [eq_div_iff (by positivity)]
    have hcard : (univ.erase a).card = J - 1 := by simp
    rw [← hcard, ← prod_const (2 : ℝ), ← prod_mul_distrib]
    apply prod_congr rfl
    intro c _
    simp only [chebNode]
    ring
  have hderiv : ∏ c ∈ univ.erase a, (chebX J a - chebX J c) =
      (derivative ω).eval (chebX J a) := by
    have h1 := Lagrange.eval_nodal_derivative_eval_node_eq (s := (univ : Finset (Fin J)))
      (v := chebX J) (mem_univ a)
    rw [Lagrange.eval_nodal] at h1
    rw [← h1, Lagrange.nodal_eq]
  have hTd : (derivative (T ℝ (J : ℤ))).eval (chebX J a) =
      2 ^ (J - 1) * (derivative ω).eval (chebX J a) := by
    rw [hTeq, derivative_C_mul, eval_mul, eval_C]
  have hU : (derivative (T ℝ (J : ℤ))).eval (chebX J a) =
      J * (U ℝ ((J : ℤ) - 1)).eval (chebX J a) := by
    rw [T_derivative_eq_U, eval_mul]
    simp
  have hUabs : 1 ≤ |(U ℝ ((J : ℤ) - 1)).eval (chebX J a)| := by
    have h := U_real_cos (chebAngle J a) ((J : ℤ) - 1)
    have hsin : Real.sin ((((J : ℤ) - 1 : ℤ) + 1) * chebAngle J a) =
        Real.sin ((2 * (a : ℝ) + 1) * (Real.pi / 2)) := by
      congr 1
      have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
      unfold chebAngle
      push_cast
      field_simp
      ring
    have hsin1 : |Real.sin ((2 * (a : ℝ) + 1) * (Real.pi / 2))| = 1 := by
      rw [show (2 * (a : ℝ) + 1) * (Real.pi / 2) = Real.pi / 2 + (a : ℕ) * Real.pi by ring,
        Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one, abs_pow, abs_neg, abs_one, one_pow]
    unfold chebX
    have hprod := congrArg abs h
    rw [abs_mul, hsin, hsin1] at hprod
    have hs : |Real.sin (chebAngle J a)| ≤ 1 := Real.abs_sin_le_one _
    have hU0 : 0 ≤ |(U ℝ ((J : ℤ) - 1)).eval (Real.cos (chebAngle J a))| := abs_nonneg _
    nlinarith
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  rw [hprod, hderiv, abs_div, abs_of_pos h2pos]
  have hω' : (derivative ω).eval (chebX J a) =
      J * (U ℝ ((J : ℤ) - 1)).eval (chebX J a) / 2 ^ (J - 1) := by
    rw [eq_div_iff h2pos.ne', mul_comm, ← hTd, hU]
  have : |(derivative ω).eval (chebX J a)| = J * |(U ℝ ((J : ℤ) - 1)).eval (chebX J a)| /
      2 ^ (J - 1) := by
    rw [hω', abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg J), abs_of_pos h2pos]
  rw [this, div_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

/-- The Chebyshev nodes stay `1 / (4 J²)` away from `-1`. -/
theorem one_add_chebNode_ge {J : ℕ} (a : Fin J) : 1 / (4 * (J : ℝ) ^ 2) ≤ 1 + chebNode J a := by
  have hJ : 0 < J := by have := a.isLt; omega
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have ha : (a : ℝ) + 1 ≤ J := by exact_mod_cast a.isLt
  set θ := chebAngle J a with hθ
  have hcos : 1 + Real.cos θ = 2 * Real.sin (Real.pi / 2 - θ / 2) ^ 2 := by
    rw [Real.sin_pi_div_two_sub, Real.cos_sq (θ / 2), show 2 * (θ / 2) = θ by ring]; ring
  set y := Real.pi / 2 - θ / 2 with hy
  have hy0 : Real.pi / (4 * J) ≤ y := by
    rw [hy, hθ]; unfold chebAngle
    rw [div_le_iff₀ (by positivity)] at *
    field_simp
    nlinarith [Real.pi_pos]
  have hy1 : y ≤ Real.pi / 2 := by
    have : 0 ≤ θ := (chebAngle_mem a.isLt).1.le
    rw [hy]; linarith
  have hsin : 2 / Real.pi * y ≤ Real.sin y :=
    Real.mul_le_sin (le_trans (by positivity) hy0) hy1
  have h1 : 1 / (2 * (J : ℝ)) ≤ Real.sin y := by
    refine le_trans ?_ hsin
    have := mul_le_mul_of_nonneg_left hy0 (by positivity : (0 : ℝ) ≤ 2 / Real.pi)
    refine le_trans (le_of_eq ?_) this
    field_simp
    norm_num
  have h2 : 1 / (2 * (J : ℝ) ^ 2) ≤ 1 + Real.cos θ := by
    rw [hcos]
    have h0 : 0 ≤ 1 / (2 * (J : ℝ)) := by positivity
    have := pow_le_pow_left₀ h0 h1 2
    have e : 1 / (2 * (J : ℝ) ^ 2) = 2 * (1 / (2 * (J : ℝ))) ^ 2 := by field_simp
    rw [e]; linarith
  unfold chebNode chebX
  rw [← hθ]
  have e : 1 + (Real.cos θ - 1) / 2 = (1 + Real.cos θ) / 2 := by ring
  rw [e]
  have e2 : 1 / (4 * (J : ℝ) ^ 2) = (1 / (2 * (J : ℝ) ^ 2)) / 2 := by field_simp; ring
  rw [e2]
  linarith


theorem nodal_eval_complex {J : ℕ} (hJ : 0 < J) (t : ℂ) :
    ∏ c : Fin J, (t - (chebNode J c : ℂ)) =
      (T ℂ (J : ℤ)).eval (2 * t + 1) / (2 ^ J * 2 ^ (J - 1)) := by
  have hT : T ℂ (J : ℤ) = Polynomial.C ((2 : ℂ) ^ (J - 1)) *
      ∏ c : Fin J, (X - Polynomial.C ((chebX J c : ℝ) : ℂ)) := by
    rw [← Chebyshev.map_T (algebraMap ℝ ℂ), T_eq_nodal hJ, Polynomial.map_mul, Polynomial.map_prod]
    simp
  have hc : ∀ c : Fin J, (2 * t + 1 - ((chebX J c : ℝ) : ℂ)) = (t - (chebNode J c : ℂ)) * 2 := by
    intro c; simp only [chebNode]; push_cast; ring
  have hp : ∏ c : Fin J, (2 * t + 1 - ((chebX J c : ℝ) : ℂ)) =
      (∏ c : Fin J, (t - (chebNode J c : ℂ))) * 2 ^ J := by
    rw [prod_congr rfl (fun c _ => hc c), prod_mul_distrib, prod_const, card_univ,
      Fintype.card_fin]
  rw [hT, eval_mul, eval_C, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [hp]
  field_simp

theorem norm_quadBasis_eval_le {J : ℕ} (a : Fin J) (t : ℂ) (ht : ‖t‖ = 1) :
    ‖((OAI.InternalCatalan.quadBasis (chebNode J) a).map (algebraMap ℝ ℂ)).eval t‖ ≤
      2 * J * ‖(T ℂ (J : ℤ)).eval (2 * t + 1)‖ := by
  have hJ : 0 < J := by have := a.isLt; omega
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  rw [OAI.InternalCatalan.quadBasis_eq, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, eval_mul,
    eval_C, eval_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X, eval_C]
  set D := ∏ c ∈ univ.erase a, (chebNode J a - chebNode J c) with hD
  have hDge := chebNode_den_ge a
  have hD0 : 0 < |D| := lt_of_lt_of_le (by positivity) hDge
  -- distance from the excluded node
  have hτ := chebNode_mem a
  have hdist : 1 / (4 * (J : ℝ) ^ 2) ≤ ‖t - (chebNode J a : ℂ)‖ := by
    refine le_trans (one_add_chebNode_ge a) ?_
    have h1 := norm_sub_norm_le t (chebNode J a : ℂ)
    rw [ht, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hτ.2] at h1
    linarith
  have hdpos : 0 < ‖t - (chebNode J a : ℂ)‖ := lt_of_lt_of_le (by positivity) hdist
  have hfull := nodal_eval_complex hJ t
  rw [← Finset.prod_erase_mul _ _ (mem_univ a)] at hfull
  have hmap : (algebraMap ℝ ℂ) (∏ c ∈ univ.erase a, (chebNode J a - chebNode J c)⁻¹) =
      ((D⁻¹ : ℝ) : ℂ) := by
    rw [hD, ← prod_inv_distrib]; simp
  rw [hmap, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv]
  have hprod : ‖∏ c ∈ univ.erase a, (t - ((chebNode J c : ℝ) : ℂ))‖ =
      ‖(T ℂ (J : ℤ)).eval (2 * t + 1)‖ / (2 ^ J * 2 ^ (J - 1)) / ‖t - (chebNode J a : ℂ)‖ := by
    have := congrArg norm hfull
    rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat] at this
    rw [eq_div_iff hdpos.ne', this]
  simp only [Complex.coe_algebraMap]
  rw [hprod]
  have h2 : (0 : ℝ) < 2 ^ J * 2 ^ (J - 1) := by positivity
  have hTn := norm_nonneg ((T ℂ (J : ℤ)).eval (2 * t + 1))
  -- |D|⁻¹ ≤ 2^(J-1) 2^(J-1) / J and 1/dist ≤ 4 J²
  have hinvD : |D|⁻¹ ≤ 2 ^ (J - 1) * 2 ^ (J - 1) / J := by
    rw [inv_le_comm₀ hD0 (by positivity), inv_div]; exact hDge
  have hinvd : ‖t - (chebNode J a : ℂ)‖⁻¹ ≤ 4 * (J : ℝ) ^ 2 := by
    rw [inv_le_comm₀ hdpos (by positivity)]; simpa using hdist
  have hJpow : (2 : ℝ) ^ J = 2 * 2 ^ (J - 1) := by
    rw [← pow_succ']; congr 1; omega
  calc |D|⁻¹ * (‖(T ℂ (J : ℤ)).eval (2 * t + 1)‖ / (2 ^ J * 2 ^ (J - 1)) /
        ‖t - (chebNode J a : ℂ)‖)
      = |D|⁻¹ * ‖t - (chebNode J a : ℂ)‖⁻¹ * (‖(T ℂ (J : ℤ)).eval (2 * t + 1)‖ /
          (2 ^ J * 2 ^ (J - 1))) := by ring
    _ ≤ (2 ^ (J - 1) * 2 ^ (J - 1) / J) * (4 * (J : ℝ) ^ 2) *
          (‖(T ℂ (J : ℤ)).eval (2 * t + 1)‖ / (2 ^ J * 2 ^ (J - 1))) := by
        gcongr
    _ = 2 * J * ‖(T ℂ (J : ℤ)).eval (2 * t + 1)‖ := by
        rw [hJpow]; field_simp; ring

end CatalanMeasure

namespace CatalanMeasure

open Polynomial Polynomial.Chebyshev Finset

/-- On the unit circle, `|ℓ_a(t) (t - 1)^q| ≤ 2 H · K^N`. -/
theorem norm_quadBasis_mul_eval_le (N : ℕ) (a : Fin (OAI.InternalCatalan.H N)) (t : ℂ)
    (ht : ‖t‖ = 1) :
    ‖((OAI.InternalCatalan.quadBasis (chebNode (OAI.InternalCatalan.H N)) a *
        (X - 1) ^ OAI.InternalCatalan.q N).map (algebraMap ℝ ℂ)).eval t‖ ≤
      2 * (OAI.InternalCatalan.H N : ℝ) * (circleK : ℝ) ^ N := by
  have hHN : OAI.InternalCatalan.H N = 65 * N := rfl
  have hqN : OAI.InternalCatalan.q N = 4 * N := rfl
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one, eval_mul, eval_pow, eval_sub, eval_X, eval_one, norm_mul, norm_pow]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ‖t + 1‖ := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact norm_nonneg _
  have hs2 : s ≤ 2 := by
    have := norm_add_le t 1
    rw [ht, norm_one, ← hs] at this
    linarith
  have hpar : ‖t - 1‖ ^ 2 = 4 - s ^ 2 := by
    have := parallelogram_law_with_norm ℝ t 1
    rw [ht, norm_one, ← hs] at this
    rw [sq, sq]
    linarith
  have hz1 : ‖(2 * t + 1) - 1‖ = 2 := by
    rw [show (2 * t + 1) - 1 = 2 * t by ring, norm_mul, ht]
    norm_num
  have hz2 : ‖(2 * t + 1) + 1‖ = 2 * s := by
    rw [show (2 * t + 1) + 1 = 2 * (t + 1) by ring, norm_mul, ← hs]
    norm_num
  have hT := norm_T_eval_le (OAI.InternalCatalan.H N) (2 * t + 1)
  rw [hz1, hz2, show (2 + 2 * s) / 2 = 1 + s by ring,
    show (1 + s) ^ 2 - 1 = s ^ 2 + 2 * s by ring] at hT
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1 + s + √(s ^ 2 + 2 * s) := ⟨_, rfl⟩
  rw [← hB] at hT
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hK : B ^ 65 * (4 - s ^ 2) ^ 2 ≤ (circleK : ℝ) := by
    rw [hB]; exact circle_ineq hs0 hs2
  have hl := norm_quadBasis_eval_le a t ht
  have e1 : ‖t - 1‖ ^ OAI.InternalCatalan.q N = ((4 - s ^ 2) ^ 2) ^ N := by
    rw [hqN, show 4 * N = 2 * (2 * N) by ring, pow_mul, hpar, pow_mul]
  have e2 : B ^ OAI.InternalCatalan.H N = (B ^ 65) ^ N := by rw [hHN, pow_mul]
  have hX0 : 0 ≤ B ^ 65 * (4 - s ^ 2) ^ 2 := by positivity
  have hn1 : 0 ≤ ‖t - 1‖ ^ OAI.InternalCatalan.q N := by positivity
  have hH0 : (0 : ℝ) ≤ 2 * (OAI.InternalCatalan.H N : ℝ) := by positivity
  calc _ ≤ (2 * (OAI.InternalCatalan.H N : ℝ) *
          ‖(T ℂ ((OAI.InternalCatalan.H N : ℕ) : ℤ)).eval (2 * t + 1)‖) *
          ‖t - 1‖ ^ OAI.InternalCatalan.q N := mul_le_mul_of_nonneg_right hl hn1
    _ ≤ (2 * (OAI.InternalCatalan.H N : ℝ) * B ^ (OAI.InternalCatalan.H N)) *
          ‖t - 1‖ ^ OAI.InternalCatalan.q N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hH0) hn1
    _ = 2 * (OAI.InternalCatalan.H N : ℝ) * (B ^ 65 * (4 - s ^ 2) ^ 2) ^ N := by
        rw [e1, e2, mul_pow, mul_assoc]
    _ ≤ 2 * (OAI.InternalCatalan.H N : ℝ) * (circleK : ℝ) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0 hK N) hH0

/-- The quadrature weights at the Chebyshev nodes: `|β_{a,k}| ≤ 8 H² K^N`. -/
theorem quadWeight_chebNode_circle_le (N : ℕ) (a : Fin (OAI.InternalCatalan.H N)) (k : ℕ) :
    |OAI.InternalCatalan.quadWeight N (chebNode (OAI.InternalCatalan.H N)) a k| ≤
      8 * (OAI.InternalCatalan.H N : ℝ) ^ 2 * (circleK : ℝ) ^ N := by
  set C := 2 * (OAI.InternalCatalan.H N : ℝ) * (circleK : ℝ) ^ N with hC
  have hg : ∀ m, |(OAI.InternalCatalan.quadBasis (chebNode (OAI.InternalCatalan.H N)) a *
      (X - 1) ^ OAI.InternalCatalan.q N).coeff m| ≤ C :=
    fun m => abs_coeff_le_of_circle _ (fun t ht => norm_quadBasis_mul_eval_le N a t ht) m
  rw [OAI.InternalCatalan.quadWeight_eq_coeff, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc 4 * |∑ d ∈ range (OAI.InternalCatalan.H N),
        (OAI.InternalCatalan.centralCoeffKernel (d : ℤ) : ℝ) *
          (OAI.InternalCatalan.quadBasis (chebNode (OAI.InternalCatalan.H N)) a *
            (X - 1) ^ OAI.InternalCatalan.q N).coeff
            (OAI.InternalCatalan.b N + k + d + OAI.InternalCatalan.q N)|
      ≤ 4 * ∑ d ∈ range (OAI.InternalCatalan.H N), C := by
        gcongr
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
        rw [abs_mul]
        calc _ ≤ 1 * C := mul_le_mul (OAI.InternalCatalan.centralCoeffKernel_abs_le_one _)
              (hg _) (abs_nonneg _) zero_le_one
          _ = C := one_mul _
    _ = 8 * (OAI.InternalCatalan.H N : ℝ) ^ 2 * (circleK : ℝ) ^ N := by
        rw [sum_const, card_range, nsmul_eq_mul, hC]
        ring

end CatalanMeasure
