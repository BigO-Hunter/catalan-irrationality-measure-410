module

public import Submission.CatalanMeasure.Integrality
public import Submission.CatalanMeasure.PrimeWindow

@[expose] public section

/-!
# An irrationality-measure criterion from polynomials indexed by primes

Suppose that for every large prime `p` there is an integer polynomial `Q p` with
* `natDegree (Q p) ≤ d * p`,
* `Q p (a / b) ≠ 0` whenever `p ∤ b` (arithmetic nonvanishing), and
* `|Q p x| ≤ exp (-(η p²))` for every real `x` with `|x - G| ≤ exp (-(ρ p))`
  (smallness on a disk around `G`).

Then `G` has a finite irrationality measure: eventually in `b`,
`|G - a / b| > b ^ (-(3 ρ max (d / η) 4))` for every integer `a`.

The proof picks a prime `p ∤ b` in `(X, 3X]` with `X = κ log b` (Chebyshev, see
`CatalanMeasure.PrimeWindow`) and compares `1 ≤ b^(d p) |Q p (a / b)|` (Liouville) with
the smallness bound.  For Catalan's constant, `Q p` is the normalized OpenAI determinant
`(n p)! · D_p · Δ_p(X)`, with `d = 48` (see `CatalanMeasure.Main`).
-/

open Polynomial Real Filter

namespace CatalanMeasure

theorem irrationality_measure_of_polynomials (G : ℝ) (d : ℕ) {η ρ : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (Q : ℕ → ℤ[X]) (P₀ : ℕ)
    (hdeg : ∀ p, (Q p).natDegree ≤ d * p)
    (hnz : ∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ∣ b →
        aeval ((a : ℝ) / b) (Q p) ≠ 0)
    (hsmall : ∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ, |x - G| ≤ exp (-(ρ * p)) →
        |aeval x (Q p)| ≤ exp (-(η * (p : ℝ) ^ 2))) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(3 * ρ * max ((d : ℝ) / η) 4)) < |G - a / b| := by
  set κ : ℝ := max ((d : ℝ) / η) 4 with hκ
  have hκ4 : 4 ≤ κ := le_max_right _ _
  have hκd : (d : ℝ) / η ≤ κ := le_max_left _ _
  have hlogb : Tendsto (fun b : ℕ => κ * log b) atTop atTop :=
    Tendsto.const_mul_atTop (by linarith)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hev : ∀ᶠ b : ℕ in atTop,
      chebError (κ * log b) ≤ κ * log b / 10 ∧ max (P₀ : ℝ) 1 ≤ κ * log b :=
    (hlogb.eventually eventually_chebError_le).and (hlogb.eventually (eventually_ge_atTop _))
  filter_upwards [hev, eventually_ge_atTop 2] with b hb hb2 a
  obtain ⟨herr, hbig⟩ := hb
  by_contra hcon
  push Not at hcon
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb0R : (0 : ℝ) < b := by linarith
  have hlogpos : 0 < log (b : ℝ) := Real.log_pos hbR
  have hX1 : 1 ≤ κ * log b := le_trans (le_max_right _ _) hbig
  have hlogX : log b ≤ κ * log b / 4 := by nlinarith
  obtain ⟨p, hp, hXp, hp3X, hpb⟩ := exists_prime_window_not_dvd hb0 hX1 herr hlogX
  have hP₀ : P₀ ≤ p := by
    have h : (P₀ : ℝ) < p := lt_of_le_of_lt (le_trans (le_max_left _ _) hbig) hXp
    exact_mod_cast h.le
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  -- closeness to `G` puts `a / b` in the disk where `Q p` is small
  have hclose : |(a : ℝ) / b - G| ≤ exp (-(ρ * p)) := by
    rw [abs_sub_comm]
    refine hcon.trans ?_
    rw [Real.rpow_def_of_pos hb0R]
    apply Real.exp_le_exp.mpr
    have h : ρ * p ≤ ρ * (3 * (κ * log b)) := mul_le_mul_of_nonneg_left hp3X hρ.le
    nlinarith
  have hQ := hsmall p hP₀ hp _ hclose
  have hne := hnz p hP₀ hp a b hb0 hpb
  have h1 := one_le_pow_mul_abs_aeval (Q p) (hdeg p) a hb0 hne
  have hpow : (b : ℝ) ^ (d * p) = exp ((d : ℝ) * p * log b) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hb0R]
    congr 1
    push_cast
    ring
  -- `p > κ log b ≥ (d / η) log b` forces `d p log b < η p²`
  have hdlog : (d : ℝ) * log b < η * p := by
    have h' : (d : ℝ) / η * log b < p :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hκd hlogpos.le) hXp
    calc (d : ℝ) * log b = η * ((d : ℝ) / η * log b) := by field_simp
      _ < η * p := mul_lt_mul_of_pos_left h' hη
  have hlt : (d : ℝ) * p * log b - η * (p : ℝ) ^ 2 < 0 := by
    nlinarith [mul_lt_mul_of_pos_right hdlog hppos]
  have hsmall' : (b : ℝ) ^ (d * p) * |aeval ((a : ℝ) / b) (Q p)| < 1 := by
    calc (b : ℝ) ^ (d * p) * |aeval ((a : ℝ) / b) (Q p)|
        ≤ exp ((d : ℝ) * p * log b) * exp (-(η * (p : ℝ) ^ 2)) := by
          rw [hpow]
          exact mul_le_mul_of_nonneg_left hQ (exp_pos _).le
      _ = exp ((d : ℝ) * p * log b - η * (p : ℝ) ^ 2) := by
          rw [← Real.exp_add]
          ring_nf
      _ < 1 := Real.exp_lt_one_iff.mpr hlt
  linarith

end CatalanMeasure
