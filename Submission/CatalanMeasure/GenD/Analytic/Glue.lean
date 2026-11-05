module

public import Submission.CatalanMeasure.GenD.Analytic.Second
public import Submission.CatalanMeasure.GenD.Analytic.CommonField
public import Submission.CatalanMeasure.CellCert.FieldsS

@[expose] public section

/-!
# Analytic layer: from the three field suprema to `SecondTrialBounds` (design-generic)

Generic form of `CellCert.secondTrialOfFieldsS`.  For an arbitrary admissible `P = ⟨n0,b0,q0,g0,h0⟩`
the three certificate suprema (row, column, residual) are statements about the scale-free fields
* `rowFieldG α β γ u v`  with `α = A0/n0`, `β = 2 h0/n0`, `γ = H0/n0`
  (`A0 = b0+q0+2g0`, `H0 = n0+b0+q0+g0+h0`),
* `colFieldG b q v`      with `b = b0/n0`, `q = q0/n0`,
* `resFieldGen (gRes P) u` the residual field `-(d0/n0) log(1+x²) - 2 T(u)`,
and the near-field cap is the one-variable statement `near_sup` (with the weight
`θ1 = (n0 - 2 g0 - 1)/n0`, a lower bound of `(n - 1 - 2g)/n` for all `N ≥ 1`).
The finite-`N` corrections are exactly those of the old glue (`1/(n0 N)` times fixed logs).
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric CatalanMeasure.CellCert OAI.InternalCatalan Filter Set
open scoped Topology BigOperators

noncomputable section

/-- The residual field with weight `ρ` (`ρ = d0/n0 = gRes P`; `9/10` at P20). -/
def resFieldGen (ρ : ℝ) (u : ℕ → ℝ) (x : ℝ) : ℝ :=
  -ρ * Real.log (1 + x ^ 2) - 2 * barrierTrialT u x

/-- Weights of the row field (generic form of `twenty_populationRowField`). -/
theorem param_row_field_eq {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) (k x : ℝ) :
    paramPopulationRowField P N k x =
      (((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0) * Real.log |x| +
        (2 * (P.h0 : ℝ) / P.n0) * Real.log (1 - x) -
        ((((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0) + (k - 2) / 2) *
          Real.log (1 + x ^ 2) := by
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold paramPopulationRowField
  simp only [Parameters.A, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
    Parameters.q, Parameters.g, Parameters.h]
  push_cast
  field_simp

/-- Generic form of `physicalTwo_row_identity` (finite-`N` correction of the row field). -/
theorem physical_free_row_identity (P : Parameters) (N : ℕ) (pp v : ℕ → ℝ) (x : ℝ) :
    populationPhysicalFreeField P N x - 4 * barrierTrialT pp x - barrierTrialS v x -
        Real.log (1 - x) / (2 * (P.n N : ℝ)) =
      paramPopulationRowField P N 2 x - 4 * barrierTrialT pp x - barrierTrialS v x +
        (1 / ((P.n0 : ℝ) * N)) * (2 * Real.log (1 + x ^ 2) - (1 / 2) * Real.log (1 - x)) := by
  unfold populationPhysicalFreeField
  rw [n_cast]
  ring

/-- Generic form of `physical_column_identity`. -/
theorem physical_column_identity_gen {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (a : ℝ) (v : ℕ → ℝ) (s : ℝ) :
    populationEndpointColumnField P N a s + 2 * barrierTrialT v s -
        Real.log (1 - s) / (P.n N : ℝ) =
      ((P.b0 : ℝ) / P.n0) * Real.log s + ((P.q0 : ℝ) / P.n0) * Real.log (1 - s) +
        a * Real.log (1 + s) + 2 * barrierTrialT v s -
        (1 / ((P.n0 : ℝ) * N)) * Real.log (1 - s) := by
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold populationEndpointColumnField
  simp only [Parameters.b, Parameters.q, Parameters.n]
  push_cast
  field_simp

/-- `(n - 1 - 2g)/n ≥ (n0 - 2 g0 - 1)/n0` for `N ≥ 1`, in real form. -/
theorem near_coeff_ge {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) :
    ((P.n0 : ℝ) - 2 * P.g0 - 1) / P.n0 ≤ ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ) / (P.n N : ℝ) := by
  have hg := two_g_lt_n hP hN
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hn0p : (0 : ℝ) < P.n0 := n0_pos hP
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcast : ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ) = (P.n0 : ℝ) * N - 1 - 2 * (P.g0 : ℝ) * N := by
    rw [Nat.cast_sub (by omega : 2 * P.g N ≤ P.n N - 1), Nat.cast_sub (by omega : 1 ≤ P.n N)]
    simp [Parameters.n, Parameters.g]
    ring
  rw [hcast, n_cast]
  have hdiff : ((P.n0 : ℝ) * N - 1 - 2 * (P.g0 : ℝ) * N) / ((P.n0 : ℝ) * N) -
      ((P.n0 : ℝ) - 2 * P.g0 - 1) / P.n0 = ((N : ℝ) - 1) / ((P.n0 : ℝ) * N) := by
    field_simp
    ring
  have : 0 ≤ ((N : ℝ) - 1) / ((P.n0 : ℝ) * N) := by
    apply div_nonneg (by linarith only [hN1]) (by positivity)
  linarith only [hdiff, this]

/-- **The generic second-energy contract from the three field suprema.** -/
def secondTrial_of_fields {P : Parameters} (hP : Admissible P)
    {target residual cost normCap fieldCap : ℝ} {G : ℝ → Prop}
    (u v : ℕ → ℝ) (hu : Summable (fun k => |u k|)) (hv : Summable (fun k => |v k|))
    (α β γ b q : ℝ) (hα : α = ((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0)
    (hβ : β = 2 * (P.h0 : ℝ) / P.n0)
    (hγ : γ = ((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0)
    (hb : b = (P.b0 : ℝ) / P.n0) (hq : q = (P.q0 : ℝ) / P.n0)
    (MX MY nearCap : ℝ)
    (near_sup : ∀ y ∈ Ioo (0 : ℝ) 1,
      -gRes P * Real.log (1 + y ^ 2) + (((P.n0 : ℝ) - 2 * P.g0 - 1) / P.n0) * Real.log y -
        u 1 * y ≤ nearCap)
    (norm_le : 2 * barrierTrialNormSq u + barrierTrialNormSq v / 2 ≤ normCap)
    (field_sum : MX + MY = fieldCap)
    (row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldG α β γ u v x ≤ MX)
    (column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG b q v s ≤ MY)
    (residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, G x → resFieldGen (gRes P) u x ≤ residual)
    (budget : ∀ {a t : ℝ}, 0 ≤ a → 0 ≤ t →
      (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
        normCap + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 +
        (a - t) * residual + t * nearCap ≤
          -target + Real.log 2 / 2 + cost * a) :
    SecondTrialBounds P target residual nearCap cost G where
  p := u
  v := v
  MX := MX
  MY := MY
  normCap := normCap
  fieldCap := fieldCap
  p_summable := hu
  v_summable := hv
  norm_le := norm_le
  field_sum := field_sum
  row := by
    intro ε hε
    have hα0 : 0 ≤ α := by
      rw [hα]; have := n0_pos hP; positivity
    have hβ0 : 0 < β := by
      rw [hβ]; have := n0_pos hP; have : (0 : ℝ) < P.h0 := by exact_mod_cast hP.2.2.2.1
      positivity
    have hh := rowFieldG_corrected_eventually (α := α) (β := β) (γ := γ) hu hv hα0 hβ0
      (a := 2) (b := 1 / 2) (by norm_num) (by norm_num) row_sup
      (fun N : ℕ => 1 / ((P.n0 : ℝ) * N))
      (fun N => by have := n0_pos hP; positivity) (invScale_tendsto hP) hε
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc hN x hx
    rw [physical_free_row_identity, param_row_field_eq hP hN]
    have hb' := hc x hx
    rw [rowFieldG_eq, hα, hβ, hγ] at hb'
    linarith only [hb']
  column := by
    intro ε hε
    have hq0 : 0 < q := by
      rw [hq]; have := n0_pos hP; have : (0 : ℝ) < P.q0 := by exact_mod_cast hP.2.2.1
      positivity
    have hb0 : 0 ≤ b := by
      rw [hb]; have := n0_pos hP; positivity
    have hh := colFieldG_corrected_eventually (b := b) (q := q) hv hb0 hq0 column_sup
      (fun N : ℕ => 1 / ((P.n0 : ℝ) * N))
      (fun N => by have := n0_pos hP; positivity) (invScale_tendsto hP) hε
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc hN s hs
    rw [physical_column_identity_gen hP hN]
    have hb' := hc s hs
    unfold colFieldG colRegG at hb'
    rw [hb, hq] at hb'
    simp only [zero_mul, add_zero]
    linarith only [hb']
  marked := by
    intro N hN x hx hgap
    have hn : (0 : ℝ) < P.n N := by exact_mod_cast n_pos hP hN
    have hsq : x ^ 2 ≤ 1 := by nlinarith only [hx.1, hx.2]
    have hlog : Real.log (1 + x ^ 2) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by linarith only [hsq])
    have hcorr := div_le_div_of_nonneg_right hlog hn.le
    have hb' := residual_sup x hx hgap
    unfold resFieldGen at hb'
    rw [grouped_marked_field_identity hP hN]
    linarith only [hb', hcorr]
  near := by
    intro N hN y hy
    have hn : (0 : ℝ) < P.n N := by exact_mod_cast n_pos hP hN
    have hsq : y ^ 2 ≤ 1 := by nlinarith only [hy.1, hy.2]
    have hlog : Real.log (1 + y ^ 2) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by linarith only [hsq])
    have hcorr := div_le_div_of_nonneg_right hlog hn.le
    have hb' := near_sup y hy
    have hcoef := near_coeff_ge hP hN
    have hly : Real.log y ≤ 0 := Real.log_nonpos hy.1.le hy.2.le
    have hm := mul_le_mul_of_nonpos_right hcoef hly
    unfold groupedNearField
    rw [grouped_marked_field_identity hP hN, abs_of_pos hy.1]
    linarith only [hb', hcorr, hm]
  budget := budget

end
end Analytic
end CatalanMeasure.GenD
