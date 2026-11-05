module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# The tilt `τ`-comparison `|Q_τ − Q_1| ≤ e · Σ |R_k|` (lane E2, S7)

`SpikeEnv.hℓ` (`SpikeDischarge`) asks for `Q_τ(x) − 2 T_a(x) ≤ Sup` on `[-1, 1]` at the energy tilt
`τ = realEnergyTau e = 1 - e`, where `Q_τ(x) = Σ_k refTilt R (k+1) τ^(k+1) T_(k+1)(x)`, while the
Chebyshev certificates (the FR field) compute the same series at `τ = 1`.  Here
`refTilt R (k+1) = -(-1)^(k+1) R_k / (k+1)`, so `(k+1) |refTilt R (k+1)| = |R_k|`, and
`1 - (1-e)^(k+1) ≤ (k+1) e` (Bernoulli) gives

  `|Q_τ(x) - Q_1(x)| ≤ e · Σ_k |R_k|`    for `x ∈ [-1, 1]`, `0 ≤ e ≤ 1`.

* `hasSum_tau_sub_le`: the generic form for coefficients `c_k` and factors `t_k` with `|t_k| ≤ 1`.
* `abs_chebT_le_one`: `|T_n(x)| ≤ 1` on `[-1, 1]`.
* `qTau_sub_le`: the form for the reference tilt (`refTilt R (k+1)` unfolds to the coefficient used here;
  `realEnergyTau e = 1 - e` is `rfl`).
* `qTau_sub_le_fin`: the same for a finite moment sequence (`R k = 0` for `k ≥ K`): the bound is the
  finite sum `e · Σ_{k<K} |R_k|`, ready to be evaluated by `norm_num`/`decide` on rational data.
-/

namespace CatalanMeasure.GenD.Signed.Data.Cells

open Finset

/-- `1 - (1-e)^m ≤ m e` and `(1-e)^m ≤ 1` for `0 ≤ e ≤ 1` (Bernoulli). -/
theorem one_sub_pow_le_mul (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (m : ℕ) :
    0 ≤ 1 - (1 - e) ^ m ∧ 1 - (1 - e) ^ m ≤ (m : ℝ) * e := by
  refine ⟨?_, ?_⟩
  · have := pow_le_one₀ (n := m) (by linarith : 0 ≤ 1 - e) (by linarith : 1 - e ≤ 1)
    linarith
  · induction m with
    | zero => simp
    | succ m ih =>
      have hu1 : (1 - e) ^ m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have hu0 : 0 ≤ (1 - e) ^ m := pow_nonneg (by linarith) m
      rw [pow_succ]
      push_cast
      nlinarith [mul_nonneg hu0 he0]

/-- **Generic form.**  If `Σ a_k = A` with `a_k = c_k (1-e)^(k+1) t_k` and `Σ b_k = B` with
`b_k = c_k t_k`, `|t_k| ≤ 1`, and `Σ (k+1) |c_k| = S` then `|A - B| ≤ e S`. -/
theorem hasSum_tau_sub_le {c t : ℕ → ℝ} {e A B S : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (ht : ∀ k, |t k| ≤ 1)
    (hS : HasSum (fun k : ℕ => ((k : ℝ) + 1) * |c k|) S)
    (hA : HasSum (fun k : ℕ => c k * (1 - e) ^ (k + 1) * t k) A)
    (hB : HasSum (fun k : ℕ => c k * t k) B) :
    |A - B| ≤ e * S := by
  have hAB := hA.sub hB
  have hg := hS.mul_left e
  have key := hAB.norm_le_of_bounded hg (fun k => by
    rw [Real.norm_eq_abs]
    have h1 := one_sub_pow_le_mul e he0 he1 (k + 1)
    have e1 : c k * (1 - e) ^ (k + 1) * t k - c k * t k = -(c k * t k * (1 - (1 - e) ^ (k + 1))) := by
      ring
    rw [e1, abs_neg, abs_mul, abs_mul, abs_of_nonneg h1.1]
    have h2 : |c k| * |t k| * (1 - (1 - e) ^ (k + 1)) ≤ |c k| * 1 * (((k + 1 : ℕ) : ℝ) * e) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left (ht k) (abs_nonneg _)) h1.2 h1.1
      positivity
    push_cast at h2
    nlinarith [abs_nonneg (c k)])
  simpa [Real.norm_eq_abs] using key

/-- `|T_n(x)| ≤ 1` on `[-1, 1]`. -/
theorem abs_chebT_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x| ≤ 1 := by
  have hc : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
  rw [← hc, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- **S7.**  For the reference moments `R` (`HasSum`-summable in absolute value), the `τ`-series
`Σ_k (-(-1)^(k+1) R_k/(k+1)) (1-e)^(k+1) T_(k+1)(x)` is within `e Σ |R_k|` of the `τ = 1` series
on `[-1, 1]`. (`refTilt R (k+1) = -(-1)^(k+1) R_k/(k+1)` is definitional.) -/
theorem qTau_sub_le {R : ℕ → ℝ} {e Qt Q1 x : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hR : Summable fun k => |R k|) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hQt : HasSum (fun k : ℕ => (-(-1 : ℝ) ^ (k + 1) * R k / ((k + 1 : ℕ) : ℝ)) * (1 - e) ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) Qt)
    (hQ1 : HasSum (fun k : ℕ => (-(-1 : ℝ) ^ (k + 1) * R k / ((k + 1 : ℕ) : ℝ)) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) Q1) :
    |Qt - Q1| ≤ e * ∑' k, |R k| := by
  have hS : HasSum (fun k : ℕ => ((k : ℝ) + 1) * |(-(-1 : ℝ) ^ (k + 1) * R k / ((k + 1 : ℕ) : ℝ))|)
      (∑' k, |R k|) := by
    have : (fun k : ℕ => ((k : ℝ) + 1) * |(-(-1 : ℝ) ^ (k + 1) * R k / ((k + 1 : ℕ) : ℝ))|) =
        fun k => |R k| := by
      funext k
      have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have h1 : |(-(-1 : ℝ) ^ (k + 1) * R k / ((k + 1 : ℕ) : ℝ))| = |R k| / ((k : ℝ) + 1) := by
        rw [abs_div, abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hk]
        push_cast
        ring
      rw [h1]
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    rw [this]
    exact hR.hasSum
  exact hasSum_tau_sub_le he0 he1
    (fun k => abs_chebT_le_one (k + 1) hx) hS hQt hQ1

/-- **S7, finite moment sequence** (`R k = 0` for `k ≥ K`): the bound is the finite sum. -/
theorem qTau_sub_le_fin {R : ℕ → ℝ} {K : ℕ} {e Qt Q1 x : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hK : ∀ k, K ≤ k → R k = 0) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hQt : HasSum (fun k : ℕ => (-(-1 : ℝ) ^ (k + 1) * R k / ((k + 1 : ℕ) : ℝ)) * (1 - e) ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) Qt)
    (hQ1 : HasSum (fun k : ℕ => (-(-1 : ℝ) ^ (k + 1) * R k / ((k + 1 : ℕ) : ℝ)) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) Q1) :
    |Qt - Q1| ≤ e * ∑ k ∈ range K, |R k| := by
  have hfin : HasSum (fun k => |R k|) (∑ k ∈ range K, |R k|) :=
    hasSum_sum_of_ne_finset_zero (fun k hk => by
      have : K ≤ k := by simpa using hk
      simp [hK k this])
  have := qTau_sub_le he0 he1 hfin.summable hx hQt hQ1
  rwa [hfin.tsum_eq] at this

#print axioms qTau_sub_le
#print axioms qTau_sub_le_fin

end CatalanMeasure.GenD.Signed.Data.Cells
