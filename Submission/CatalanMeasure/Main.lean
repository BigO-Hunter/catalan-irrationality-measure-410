module

public import Submission.CatalanMeasure.Criterion
public import Submission.CatalanMeasure.PNTWindow
public import Submission.CatalanMeasure.IntegerValued
public import Submission.CatalanMeasure.DeltaPoly
public import Submission.CatalanMeasure.Degree
public import Submission.CatalanMeasure.Denominators
public import Submission.CatalanMeasure.Nonvanishing
public import Submission.OAI.NumberTheory.Catalan.Determinants.RealDeterminantCore
public import Submission.CatalanMeasure.DualTwo
public import Submission.OAI.NumberTheory.Catalan.Arithmetic.FinitePlaceNumerics

@[expose] public section

/-!
# A finite irrationality measure for Catalan's constant, conditional on the perturbation lemma

Everything is proved except the analytic perturbation estimate (Lemma 6 of the write-up), which
is the hypothesis `hpert`: on the disk `|x - G| ≤ exp(-ρ p)` the polynomial `Δ_p(x)` moves by at
most the same bound that OpenAI prove for `|Δ_p(G)|` itself,
`exp(n² (-2.290939875 + (log 2)/2 + ε))`.

From OpenAI's formalization we use:
* the real upper bound `eventually_realDeterminant_abs_upper_sharp` at `G`;
* the local estimates at every prime (through `Denominators.lean`, Proposition 3);
* the residue-matrix nonvanishing argument (through `Nonvanishing.lean`, Proposition 4);
* `finitePlace_constant_gt_threshold`, which makes the gap `γ = U - A` positive.

The integer polynomial is `Q_p = (n p)! · D_p · Δ_p(X)` (`IntegerValued.lean` turns integer values
at integers into integer coefficients), and `CatalanMeasure.irrationality_measure_of_polynomials`
finishes the argument.
-/

open Polynomial Filter Real
open scoped Nat

namespace OAI.InternalCatalan

/-- `U - A`: OpenAI's real-place exponent minus the finite-place exponent. -/
noncomputable def measureGap : ℝ :=
  (229180925 / 100000000 - Real.log 2 / 2) - (8609 / 4608 + 505 / 4608 * Real.log 2)

theorem measureGap_pos : 0 < measureGap := by
  unfold measureGap
  linarith [finitePlace_constant_gt_threshold]

theorem natDegree_denom_mul_deltaPoly_le (p : ℕ) :
    (C (denomBound p : ℚ) * deltaPoly p).natDegree ≤ 44 * p :=
  (natDegree_C_mul_le _ _).trans (natDegree_deltaPoly_le_44 p)

theorem denom_mul_deltaPoly_int_values {p : ℕ} (hp : 0 < p) (i : ℕ) :
    ∃ m : ℤ, (C (denomBound p : ℚ) * deltaPoly p).eval (i : ℚ) = m := by
  rw [eval_mul, eval_C, eval_deltaPoly]
  exact exists_int_denomBound_mul hp i

/-- The integer polynomial `Q_p = (44 p)! · D_p · Δ_p` (and `0` for `p = 0`). -/
noncomputable def measureIntPoly (p : ℕ) : ℤ[X] :=
  if hp : 0 < p then
    Classical.choose (CatalanMeasure.exists_int_poly_factorial_mul
      (C (denomBound p : ℚ) * deltaPoly p) (natDegree_denom_mul_deltaPoly_le p)
      (denom_mul_deltaPoly_int_values hp))
  else 0

theorem measureIntPoly_spec {p : ℕ} (hp : 0 < p) :
    (measureIntPoly p).map (Int.castRingHom ℚ) =
        C (((44 * p) ! : ℕ) : ℚ) * (C (denomBound p : ℚ) * deltaPoly p) ∧
      (measureIntPoly p).natDegree ≤ 44 * p := by
  unfold measureIntPoly
  rw [dif_pos hp]
  exact Classical.choose_spec (CatalanMeasure.exists_int_poly_factorial_mul
    (C (denomBound p : ℚ) * deltaPoly p) (natDegree_denom_mul_deltaPoly_le p)
    (denom_mul_deltaPoly_int_values hp))

theorem measureIntPoly_natDegree_le (p : ℕ) : (measureIntPoly p).natDegree ≤ 44 * p := by
  by_cases hp : 0 < p
  · exact (measureIntPoly_spec hp).2
  · unfold measureIntPoly
    rw [dif_neg hp]
    simp

theorem aeval_measureIntPoly {p : ℕ} (hp : 0 < p) (x : ℝ) :
    aeval x (measureIntPoly p) = ((44 * p) ! : ℝ) * (denomBound p : ℝ) * aeval x (deltaPoly p) := by
  rw [← aeval_map_algebraMap ℚ x (measureIntPoly p), algebraMap_int_eq,
    (measureIntPoly_spec hp).1]
  simp only [map_mul, aeval_C, eq_ratCast, Rat.cast_natCast]
  try ring

theorem aeval_ratCast_eq (P : ℚ[X]) (q : ℚ) : aeval (q : ℝ) P = ((P.eval q : ℚ) : ℝ) := by
  rw [aeval_def, ← eq_ratCast (algebraMap ℚ ℝ) q, eval₂_at_apply, eq_ratCast]

/-- `(n p)!` is `exp(o(p²))`. -/
theorem factorial_n_le_exp {c : ℝ} (hc : 0 < c) :
    ∀ᶠ p : ℕ in atTop, (((n p) ! : ℕ) : ℝ) ≤ Real.exp (c * (n p : ℝ) ^ 2) := by
  have htend : Tendsto (fun p : ℕ => ((n p : ℕ) : ℝ)) atTop atTop := by
    have : (fun p : ℕ => ((n p : ℕ) : ℝ)) = fun p : ℕ => 48 * (p : ℝ) := by
      funext p
      simp [n]
    rw [this]
    exact Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have hlog := htend.eventually (Real.isLittleO_log_id_atTop.def hc)
  filter_upwards [hlog, htend.eventually (eventually_ge_atTop 1)] with p hp h1
  have hD0 : (0 : ℝ) < ((n p : ℕ) : ℝ) := by linarith
  simp only [id, Real.norm_eq_abs] at hp
  rw [abs_of_pos hD0, abs_of_nonneg (Real.log_nonneg h1)] at hp
  have hfac : (((n p) ! : ℕ) : ℝ) ≤ ((n p : ℕ) : ℝ) ^ (n p) := by
    exact_mod_cast Nat.factorial_le_pow (n p)
  have hpow : ((n p : ℕ) : ℝ) ^ (n p) =
      Real.exp ((n p : ℝ) * Real.log ((n p : ℕ) : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log hD0]
  rw [hpow] at hfac
  refine hfac.trans (Real.exp_le_exp.mpr ?_)
  calc (n p : ℝ) * Real.log ((n p : ℕ) : ℝ) ≤ (n p : ℝ) * (c * ((n p : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hp hD0.le
    _ = c * (n p : ℝ) ^ 2 := by ring

/-- The two hypotheses of the measure criterion for `Q_p = (44 p)! · D_p · Δ_p`, from the
perturbation lemma: arithmetic nonvanishing at `a / b` with `p ∤ b`, and smallness
`|Q_p(x)| ≤ exp(-η p²)` for any `η < 2304 γ` on the disk `|x - G| ≤ exp(-ρ p)`. -/
theorem measureIntPoly_hypotheses {ρ η : ℝ} (hη : η < 2304 * measureGap)
    (hpert : ∀ ε : ℝ, 0 < ε → ∀ᶠ p : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(ρ * p)) →
        |aeval x (deltaPoly p) - aeval catalan (deltaPoly p)| ≤
          Real.exp ((n p : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + ε))) :
    ∃ P₀ : ℕ,
      (∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ∣ b →
        aeval ((a : ℝ) / b) (measureIntPoly p) ≠ 0) ∧
      (∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ, |x - catalan| ≤ Real.exp (-(ρ * p)) →
        |aeval x (measureIntPoly p)| ≤ Real.exp (-(η * (p : ℝ) ^ 2))) := by
  set γ := measureGap with hγ
  have hγ0 : 0 < γ := measureGap_pos
  set e : ℝ := (2304 * γ - η) / 9216 with he
  have he0 : 0 < e := by rw [he]; linarith
  -- eventual estimates, all at the prime index `p`
  have hev : ∀ᶠ p : ℕ in atTop,
      (∀ x : ℝ, |x - catalan| ≤ Real.exp (-(ρ * p)) →
        |aeval x (deltaPoly p) - aeval catalan (deltaPoly p)| ≤
          Real.exp ((n p : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + e))) ∧
      |determinant p| ≤
        Real.exp ((n p : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + e)) ∧
      Real.log (denomBound p) ≤ (8609 / 4608 + 505 / 4608 * Real.log 2 + e) * (n p : ℝ) ^ 2 ∧
      (((n p) ! : ℕ) : ℝ) ≤ Real.exp (e * (n p : ℝ) ^ 2) ∧
      Real.log 2 ≤ e * (n p : ℝ) ^ 2 ∧
      fixedDeterminantPrimeCutoff < p ∧ 0 < p := by
    have hlog2 : ∀ᶠ p : ℕ in atTop, Real.log 2 ≤ e * (n p : ℝ) ^ 2 := by
      have htend : Tendsto (fun p : ℕ => e * (n p : ℝ) ^ 2) atTop atTop := by
        have : (fun p : ℕ => e * (n p : ℝ) ^ 2) = fun p : ℕ => (e * 2304) * (p : ℝ) ^ 2 := by
          funext p
          simp only [n, Nat.cast_mul, Nat.cast_ofNat]
          ring
        rw [this]
        exact Tendsto.const_mul_atTop (by nlinarith [he0])
          ((tendsto_pow_atTop (n := 2) (by norm_num)).comp tendsto_natCast_atTop_atTop)
      exact htend.eventually (eventually_ge_atTop _)
    filter_upwards [hpert (e) he0,
      eventually_realDeterminant_abs_upper_dual (ε := e) he0,
      log_denomBound_eventually_le (ε := e) he0,
      factorial_n_le_exp (c := e) he0, hlog2,
      eventually_gt_atTop fixedDeterminantPrimeCutoff, eventually_gt_atTop 0]
      with p h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hev
  refine ⟨P₀, ?_, ?_⟩
  · -- arithmetic nonvanishing
    intro p hp hprime a b hb hpb
    haveI : Fact p.Prime := ⟨hprime⟩
    obtain ⟨-, -, -, -, -, hcut, hp0⟩ := hP₀ p hp
    rw [aeval_measureIntPoly hp0]
    have hx : ((a : ℝ) / b) = (((a : ℚ) / b : ℚ) : ℝ) := by
      rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    rw [hx, aeval_ratCast_eq, eval_deltaPoly]
    have hdet := determinantRat_div_ne_zero hcut a hb hpb
    have hfac : (((44 * p) ! : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hM : (denomBound p : ℝ) ≠ 0 := by exact_mod_cast denomBound_ne_zero p
    have hdetR : ((determinantRat ((a : ℚ) / b) p : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hdet
    exact mul_ne_zero (mul_ne_zero hfac hM) hdetR
  · -- smallness near `G`
    intro p hp hprime x hx
    obtain ⟨hpert', hG, hM, hfacn, hlog2, -, hp0⟩ := hP₀ p hp
    have hfac : (((44 * p) ! : ℕ) : ℝ) ≤ Real.exp (e * (n p : ℝ) ^ 2) := by
      refine le_trans ?_ hfacn
      exact_mod_cast Nat.factorial_le (by unfold n; omega)
    rw [aeval_measureIntPoly hp0]
    set E : ℝ := (n p : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + e)
      with hE
    have hΔ : |aeval x (deltaPoly p)| ≤ 2 * Real.exp E := by
      have h1 := hpert' x hx
      have h2 : aeval catalan (deltaPoly p) = determinant p := aeval_catalan_deltaPoly hp0
      calc |aeval x (deltaPoly p)|
          = |(aeval x (deltaPoly p) - aeval catalan (deltaPoly p)) +
              aeval catalan (deltaPoly p)| := by rw [sub_add_cancel]
        _ ≤ |aeval x (deltaPoly p) - aeval catalan (deltaPoly p)| +
              |aeval catalan (deltaPoly p)| := abs_add_le _ _
        _ ≤ Real.exp E + Real.exp E := add_le_add h1 (by rw [h2]; exact hG)
        _ = 2 * Real.exp E := by ring
    have hM' : (denomBound p : ℝ) ≤
        Real.exp ((8609 / 4608 + 505 / 4608 * Real.log 2 + e) * (n p : ℝ) ^ 2) := by
      have hMpos : (0 : ℝ) < denomBound p := by
        exact_mod_cast Nat.pos_of_ne_zero (denomBound_ne_zero p)
      rw [← Real.exp_log hMpos]
      exact Real.exp_le_exp.mpr hM
    have h2 : (2 : ℝ) ≤ Real.exp (e * (n p : ℝ) ^ 2) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_le_exp.mpr hlog2
    have hfac0 : (0 : ℝ) ≤ (((44 * p) ! : ℕ) : ℝ) := by positivity
    have hM0 : (0 : ℝ) ≤ (denomBound p : ℝ) := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg hfac0, abs_of_nonneg hM0]
    calc (((44 * p) ! : ℕ) : ℝ) * (denomBound p : ℝ) * |aeval x (deltaPoly p)|
        ≤ Real.exp (e * (n p : ℝ) ^ 2) *
            Real.exp ((8609 / 4608 + 505 / 4608 * Real.log 2 + e) * (n p : ℝ) ^ 2) *
            (Real.exp (e * (n p : ℝ) ^ 2) * Real.exp E) := by
          have hΔ' : |aeval x (deltaPoly p)| ≤
              Real.exp (e * (n p : ℝ) ^ 2) * Real.exp E :=
            hΔ.trans (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le)
          gcongr
      _ = Real.exp (-(η / 2304) * (n p : ℝ) ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hE]
          congr 1
          rw [he, hγ]
          unfold measureGap
          ring
      _ = Real.exp (-(η * (p : ℝ) ^ 2)) := by
          congr 1
          simp only [n, Nat.cast_mul, Nat.cast_ofNat]
          ring

/-- **Main theorem (Chebyshev window).**  Assuming the perturbation lemma, Catalan's constant
has a finite irrationality measure. -/
theorem catalan_irrationalityMeasure_of_perturbation {ρ η : ℝ} (hρ : 0 < ρ) (hη0 : 0 < η)
    (hη : η < 2304 * measureGap)
    (hpert : ∀ ε : ℝ, 0 < ε → ∀ᶠ p : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(ρ * p)) →
        |aeval x (deltaPoly p) - aeval catalan (deltaPoly p)| ≤
          Real.exp ((n p : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + ε))) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(3 * ρ * max (((44 : ℕ) : ℝ) / η) 4)) <
        |catalan - a / b| := by
  obtain ⟨P₀, hnz, hsmall⟩ := measureIntPoly_hypotheses hη hpert
  exact CatalanMeasure.irrationality_measure_of_polynomials catalan 44 hη0 hρ measureIntPoly P₀
    measureIntPoly_natDegree_le hnz hsmall

/-- **Main theorem (prime number theorem window).**  For every `ε > 0`, the exponent
`(1 + ε) ρ max (44 / η) (c / ε)` for any `0 < η < 2304 γ` and `c > 1`. -/
theorem catalan_irrationalityMeasure_of_perturbation_pnt {ρ η ε c : ℝ} (hρ : 0 < ρ)
    (hη0 : 0 < η) (hη : η < 2304 * measureGap) (hε : 0 < ε) (hc : 1 < c)
    (hpert : ∀ ε : ℝ, 0 < ε → ∀ᶠ p : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(ρ * p)) →
        |aeval x (deltaPoly p) - aeval catalan (deltaPoly p)| ≤
          Real.exp ((n p : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + ε))) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((1 + ε) * ρ * max (((44 : ℕ) : ℝ) / η) (c / ε))) <
        |catalan - a / b| := by
  obtain ⟨P₀, hnz, hsmall⟩ := measureIntPoly_hypotheses hη hpert
  exact CatalanMeasure.irrationality_measure_of_polynomials_pnt catalan 44 hη0 hρ hε hc
    measureIntPoly P₀ measureIntPoly_natDegree_le hnz hsmall

end OAI.InternalCatalan
