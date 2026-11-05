module

public import Submission.CatalanMeasure.GenD.Recycled
public import Submission.CatalanMeasure.GenD.PayW
public import Submission.CatalanMeasure.GenD.Interface
public import Submission.CatalanMeasure.Parametric.RealEvaluation

@[expose] public section

/-!
# The design-generic final theorem (module 15)

`measure_of_design : DesignData P → ∀ᶠ b, ∀ a, b^(-B) < |catalan - a/b|`.

All design constants are fields of `DesignData`; nothing in this file mentions a number.
The data are exactly the inputs of the recycled-polynomial criterion (window version):

* `Z : Normalizer P` (denominator with integer values and the recycling exponent `q^(2n)`),
  which gives the integer polynomial `Q_N = (n-g)! D_N Δ_N`, its degree bound and, by
  **Theorem C**, the coefficientwise recycling divisibility;
* the payments (`PayW`), the logarithmic growth `gD` of `D_N`, the smallness `tΔ` of `Δ_N` near
  Catalan's constant (this is the output of the field/certificate layer), and the arithmetic
  nonvanishing at `N = p` (the base-matrix certificate).
-/

namespace CatalanMeasure.GenD

open Polynomial Filter Real CatalanMeasure.Parametric OAI.InternalCatalan
open scoped Topology Nat

noncomputable section

/-- `((m N)!)` is `exp(o(N²))`. -/
theorem factorial_mul_le_exp (m : ℕ) (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (((m * N) ! : ℕ) : ℝ) ≤ Real.exp (ε * (N : ℝ) ^ 2) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htend : Tendsto (fun N : ℕ => ((m * N : ℕ) : ℝ)) atTop atTop := by
    have : (fun N : ℕ => ((m * N : ℕ) : ℝ)) = fun N : ℕ => (m : ℝ) * (N : ℝ) := by
      funext N; push_cast; ring
    rw [this]
    exact Tendsto.const_mul_atTop hmR tendsto_natCast_atTop_atTop
  have hc : 0 < ε / (m : ℝ) ^ 2 := by positivity
  have hlog := htend.eventually (Real.isLittleO_log_id_atTop.def hc)
  filter_upwards [hlog, htend.eventually (eventually_ge_atTop 1)] with N hp h1
  have hD0 : (0 : ℝ) < ((m * N : ℕ) : ℝ) := by linarith
  simp only [id, Real.norm_eq_abs] at hp
  rw [abs_of_pos hD0, abs_of_nonneg (Real.log_nonneg h1)] at hp
  have hfac : (((m * N) ! : ℕ) : ℝ) ≤ ((m * N : ℕ) : ℝ) ^ (m * N) := by
    exact_mod_cast Nat.factorial_le_pow (m * N)
  have hpow : ((m * N : ℕ) : ℝ) ^ (m * N) =
      Real.exp (((m * N : ℕ) : ℝ) * Real.log ((m * N : ℕ) : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log hD0]
  rw [hpow] at hfac
  refine hfac.trans (Real.exp_le_exp.mpr ?_)
  calc ((m * N : ℕ) : ℝ) * Real.log ((m * N : ℕ) : ℝ)
      ≤ ((m * N : ℕ) : ℝ) * (ε / (m : ℝ) ^ 2 * ((m * N : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hp hD0.le
    _ = ε * (N : ℝ) ^ 2 := by push_cast; field_simp

/-- Everything the final theorem needs. -/
structure DesignData (P : Parameters) where
  /-- Target exponent. -/
  B : ℕ
  Z : Normalizer P
  w : ℝ
  ρ : ℝ
  η : ℝ
  κ : ℝ
  δ : ℝ
  pay : PayW w ((P.n0 - P.g0 : ℕ) : ℝ) ρ η κ δ (B : ℝ)
  /-- Growth of the denominator: `log D_N ≤ (gD + ε) N²`. -/
  gD : ℝ
  D_growth : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Real.log (Z.D N) ≤ (gD + ε) * (N : ℝ) ^ 2
  /-- Smallness of `Δ_N` near Catalan's constant (the certificate layer). -/
  tΔ : ℝ
  delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
    |x - catalan| ≤ Real.exp (-(ρ * (N : ℝ))) →
      |aeval x (Parametric.deltaPoly P N)| ≤ Real.exp (-((tΔ - ε) * (N : ℝ) ^ 2))
  /-- The payments leave room for the denominator growth. -/
  eta_le : η < tΔ - gD
  /-- Arithmetic nonvanishing at `a / b` for `p ∤ b` (base-matrix certificate). -/
  nonvanishing : ∃ N1 : ℕ, ∀ p : ℕ, N1 ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
    aeval ((a : ℝ) / b) (Parametric.deltaPoly P p) ≠ 0

/-- **The design-generic measure theorem.** -/
theorem measure_of_design (P : Parameters) (D : DesignData P) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(D.B : ℝ)) < |catalan - (a : ℝ) / b| := by
  obtain ⟨hB, hη, hρ, hw0, hκ, hδ, hwin, hlin, hpay⟩ := D.pay
  have hadm := D.Z.adm
  have hd0 : 0 < P.n0 - P.g0 := by have := hadm.2.2.2.2; omega
  -- smallness of `Q_N`
  set e : ℝ := (D.tΔ - D.gD - D.η) / 4 with he
  have hepos : 0 < e := by have := D.eta_le; rw [he]; linarith
  have hsm : ∀ᶠ N : ℕ in atTop, D.Z.N0 ≤ N ∧ ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(D.ρ * (N : ℝ))) →
        |aeval x (D.Z.Q N)| ≤ Real.exp (-(D.η * (N : ℝ) ^ 2)) := by
    filter_upwards [factorial_mul_le_exp (P.n0 - P.g0) hd0 hepos, D.D_growth e hepos,
      D.delta_small e hepos, eventually_ge_atTop D.Z.N0] with N hfac hD hΔ hN0
    refine ⟨hN0, fun x hx => ?_⟩
    rw [D.Z.aeval_Q hN0, abs_mul, abs_mul]
    have hf0 : (0 : ℝ) ≤ (((P.n N - P.g N) ! : ℕ) : ℝ) := Nat.cast_nonneg _
    have hD0 : (0 : ℝ) < (D.Z.D N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (D.Z.D_ne N)
    rw [abs_of_nonneg hf0, abs_of_pos hD0]
    have hnm : P.n N - P.g N = (P.n0 - P.g0) * N := by
      simp only [Parameters.n, Parameters.g]; rw [Nat.sub_mul]
    rw [hnm]
    have hDle : (D.Z.D N : ℝ) ≤ Real.exp ((D.gD + e) * (N : ℝ) ^ 2) := by
      rw [← Real.exp_log hD0]; exact Real.exp_le_exp.mpr hD
    calc (((((P.n0 - P.g0) * N) ! : ℕ)) : ℝ) * (D.Z.D N : ℝ) * |aeval x (Parametric.deltaPoly P N)|
        ≤ Real.exp (e * (N : ℝ) ^ 2) * Real.exp ((D.gD + e) * (N : ℝ) ^ 2) *
            Real.exp (-((D.tΔ - e) * (N : ℝ) ^ 2)) := by
          gcongr
          exact hΔ x hx
      _ = Real.exp (-(D.η * (N : ℝ) ^ 2) - e * (N : ℝ) ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1
          have h4 : D.tΔ = 4 * e + D.gD + D.η := by rw [he]; ring
          rw [h4]; ring
      _ ≤ Real.exp (-(D.η * (N : ℝ) ^ 2)) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hepos.le (sq_nonneg (N : ℝ))])
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp hsm
  obtain ⟨N1, hN1⟩ := D.nonvanishing
  have key := irrationality_measure_of_recycled_polynomials_window catalan (P.n0 - P.g0)
    (η := D.η) (ρ := D.ρ) (κ := D.κ) (δ := D.δ) (w := D.w) hη hρ hw0 hκ hδ hwin hlin
    (by exact_mod_cast hpay) D.Z.Q (max N1 N2)
    (fun p => by
      refine (D.Z.Q_natDegree_le p).trans (le_of_eq ?_)
      simp only [Parameters.n, Parameters.g]; rw [Nat.sub_mul])
    (fun p hp hprime a b hb hpb => by
      have hN0 : D.Z.N0 ≤ p := (hN2 p ((le_max_right _ _).trans hp)).1
      rw [D.Z.aeval_Q hN0]
      have hΔ := hN1 p ((le_max_left _ _).trans hp) hprime a b hb hpb
      have hf : (((P.n p - P.g p) ! : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      have hD : (D.Z.D p : ℝ) ≠ 0 := by exact_mod_cast D.Z.D_ne p
      exact mul_ne_zero (mul_ne_zero hf hD) hΔ)
    (fun p hp hprime q hq hpq hq2p i _ => by
      have : Fact q.Prime := ⟨hq⟩
      have hN0 : D.Z.N0 ≤ p := (hN2 p ((le_max_right _ _).trans hp)).1
      exact D.Z.Q_coeff_prime_pow_dvd hN0 hpq hq2p i)
    (fun p hp hprime x hx => (hN2 p ((le_max_right _ _).trans hp)).2 x hx)
  rwa [hB] at key

end

end CatalanMeasure.GenD
