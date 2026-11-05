module

public import Submission.CatalanMeasure.GenD.Analytic.First
public import Submission.CatalanMeasure.GenD.Analytic.Glue

@[expose] public section

/-!
# Analytic layer: from the first-trial field suprema to `FirstTrialBounds` (design-generic)

Generic form of `strongFirstTrialOfFields`.  The two certificate suprema are statements about the
scale-free fields
* `firstRowFieldG α β γ lam c p v` with `α = A0/n0`, `β = 2 h0/n0`, `γ = H0/n0 - 1/2`,
  `c = 2 g0/n0` (the case-field constant), `lam` the trial multiplier;
* `colFieldG b q v` with `b = b0/n0`, `q = q0/n0` (the first-population column has `a = 0`).
The finite-`N` corrections are `1/(n0 N)` times the fixed logs `3/2 log(1+x²) - 1/2 log(1-x)`
(row) and `log(1-s)` (column).
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric CatalanMeasure.CellCert OAI.InternalCatalan Filter Set
open scoped Topology BigOperators

noncomputable section

/-- Regular part of the first-population row field. -/
def firstRowReg (γ lam c : ℝ) (p v : ℕ → ℝ) (x : ℝ) : ℝ :=
  -γ * Real.log (1 + x ^ 2) + lam * (c - 2 * x ^ 2 / (1 + x ^ 2)) - 2 * barrierTrialT p x -
    barrierTrialS v x

/-- The first-population row field (scale-free form). -/
def firstRowFieldG (α β γ lam c : ℝ) (p v : ℕ → ℝ) (x : ℝ) : ℝ :=
  α * Real.log |x| + β * Real.log (1 - x) + firstRowReg γ lam c p v x

theorem firstRowReg_continuousOn (γ lam c : ℝ) {p v : ℕ → ℝ} (hp : Summable (fun k => |p k|))
    (hv : Summable (fun k => |v k|)) :
    ContinuousOn (firstRowReg γ lam c p v) (Icc (-1 : ℝ) 1) := by
  have hq : ContinuousOn (fun x : ℝ => 2 * x ^ 2 / (1 + x ^ 2)) (Icc (-1 : ℝ) 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x _; positivity
  have h1 : ContinuousOn (fun x : ℝ => -γ * Real.log (1 + x ^ 2)) (Icc (-1 : ℝ) 1) :=
    log_one_add_sq_continuous.continuousOn.const_mul _
  have h2 : ContinuousOn (fun x : ℝ => lam * (c - 2 * x ^ 2 / (1 + x ^ 2))) (Icc (-1 : ℝ) 1) :=
    (continuousOn_const.sub hq).const_mul _
  exact ((h1.add h2).sub ((barrierTrialT_continuousOn p hp).const_mul _)).sub
    (barrierTrialS_continuousOn v hv)

theorem firstRowFieldG_endpoint_bound {α β γ lam c : ℝ} {p v : ℕ → ℝ}
    (hp : Summable (fun k => |p k|)) (hv : Summable (fun k => |v k|)) (hα : 0 ≤ α) :
    ∃ K : ℝ, ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      firstRowFieldG α β γ lam c p v x ≤ β * Real.log (1 - x) + K := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (firstRowReg_continuousOn γ lam c hp hv)
  refine ⟨K, ?_⟩
  intro x hx
  have hxi : x ∈ Icc (-1 : ℝ) 1 := by
    rcases hx with hx | hx
    · exact ⟨hx.1, by linarith only [hx.2]⟩
    · exact ⟨by linarith only [hx.1], hx.2.le⟩
  have hlog : Real.log |x| ≤ 0 := Real.log_nonpos (abs_nonneg _) (abs_le.mpr hxi)
  have hterm : α * Real.log |x| ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα hlog
  have hreg : firstRowReg γ lam c p v x ≤ K :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hK x hxi)
  unfold firstRowFieldG
  linarith only [hterm, hreg]

theorem firstRowFieldG_corrected_eventually {α β γ lam c : ℝ} {p v : ℕ → ℝ}
    (hp : Summable (fun k => |p k|)) (hv : Summable (fun k => |v k|)) (hα : 0 ≤ α) (hβ : 0 < β)
    {M a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, firstRowFieldG α β γ lam c p v x ≤ M)
    (t : ℕ → ℝ) (ht0 : ∀ N, 0 ≤ t N) (ht : Tendsto t atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      firstRowFieldG α β γ lam c p v x +
        t N * (a * Real.log (1 + x ^ 2) - b * Real.log (1 - x)) ≤ M + ε := by
  obtain ⟨K, hK⟩ := firstRowFieldG_endpoint_bound (β := β) (γ := γ) (lam := lam) (c := c) hp hv hα
  apply CatalanMeasure.log_field_correction_eventually hβ ha hb ?_ hM hK t ht0 ht hε
  intro x hx
  rcases hx with hx | hx
  · exact ⟨hx.1, by linarith only [hx.2]⟩
  · exact ⟨by linarith only [hx.1], hx.2⟩

theorem case_ratio {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) :
    (P.g N : ℝ) / (P.n N : ℝ) = (P.g0 : ℝ) / P.n0 := by
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Parameters.g, Parameters.n]
  push_cast
  field_simp

/-- Generic form of `physicalOne_row_identity`. -/
theorem physical_one_row_identity {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (lam : ℝ) (p v : ℕ → ℝ) (x : ℝ) :
    populationPhysicalOneFreeField P N x + lam * paramCaseField P N x - 2 * barrierTrialT p x -
        barrierTrialS v x - Real.log (1 - x) / (2 * (P.n N : ℝ)) =
      firstRowFieldG (((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0) (2 * (P.h0 : ℝ) / P.n0)
        (((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0 - 1 / 2) lam (2 * (P.g0 : ℝ) / P.n0)
        p v x +
      (1 / ((P.n0 : ℝ) * N)) * ((3 / 2) * Real.log (1 + x ^ 2) - (1 / 2) * Real.log (1 - x)) := by
  have hc := case_ratio hP hN
  unfold populationPhysicalOneFreeField paramCaseField firstRowFieldG firstRowReg
  rw [param_row_field_eq hP hN, n_cast]
  have h2 : 2 * (P.g N : ℝ) / ((P.n0 : ℝ) * N) = 2 * (P.g0 : ℝ) / P.n0 := by
    rw [← n_cast, mul_div_assoc, hc]; ring
  rw [h2]
  ring

/-- **The generic first-energy contract from the two first-trial field suprema.** -/
def firstTrial_of_fields {P : Parameters} (hP : Admissible P)
    {target cost normCap fieldCap : ℝ}
    (p v : ℕ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hp : Summable (fun k => |p k|)) (hv : Summable (fun k => |v k|))
    (α β γ c b q : ℝ) (hα : α = ((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0)
    (hβ : β = 2 * (P.h0 : ℝ) / P.n0)
    (hγ : γ = ((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0 - 1 / 2)
    (hc : c = 2 * (P.g0 : ℝ) / P.n0)
    (hb : b = (P.b0 : ℝ) / P.n0) (hq : q = (P.q0 : ℝ) / P.n0)
    (MX MY : ℝ)
    (norm_le : barrierTrialNormSq p + barrierTrialNormSq v / 2 ≤ normCap)
    (field_sum : MX + MY = fieldCap)
    (row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, firstRowFieldG α β γ lam c p v x ≤ MX)
    (column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG b q v s ≤ MY)
    (budget : ∀ a : ℝ,
      (-gC0 P + gC1 P * a - a ^ 2) * Real.log 2 +
        normCap + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 +
        a * (2 * lam * ((P.g0 : ℝ) / P.n0)) ≤
          -target + Real.log 2 / 2 + cost * a) :
    FirstTrialBounds P target cost where
  p := p
  v := v
  lambda := lam
  MX := MX
  MY := MY
  normCap := normCap
  fieldCap := fieldCap
  lambda_nonneg := hlam
  p_summable := hp
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
    have hh := firstRowFieldG_corrected_eventually (α := α) (β := β) (γ := γ) (lam := lam)
      (c := c) hp hv hα0 hβ0 (a := 3 / 2) (b := 1 / 2) (by norm_num) (by norm_num) row_sup
      (fun N : ℕ => 1 / ((P.n0 : ℝ) * N))
      (fun N => by have := n0_pos hP; positivity) (invScale_tendsto hP) hε
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc' hN x hx
    have hb' := hc' x hx
    have hid := physical_one_row_identity hP hN lam p v x
    rw [← hα, ← hβ, ← hγ, ← hc] at hid
    linarith only [hb', hid]
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
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc' hN s hs
    rw [physical_column_identity_gen hP hN]
    have hb' := hc' s hs
    unfold colFieldG colRegG at hb'
    rw [hb, hq] at hb'
    simp only [zero_mul, add_zero]
    linarith only [hb']
  budget := budget

end
end Analytic
end CatalanMeasure.GenD
