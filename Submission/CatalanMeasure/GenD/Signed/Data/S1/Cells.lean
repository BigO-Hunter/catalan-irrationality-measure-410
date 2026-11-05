module

public import Submission.CatalanMeasure.GenD.Signed.Data.S1.Bridge
public import Submission.CatalanMeasure.GenD.Analytic.WeightedAtom
public import Submission.CatalanMeasure.GenD.Signed.LogEval
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public section

/-!
# S1: the kappa-cells of the Psi certificate (lane D3)

For a keyhole radius `r0` and circle exponent `wc` (per `N`) the column weight is
`<= C0 N^5 exp(n (keyholeRate r0 (k/n) + wc/n0))` (`gap_hW_nudged`), and Lemma V costs
`exp(n binomRate (k/n))`.  A *cell* `[lo, hi]` of `kappa = k/n` is certified when

  `keyholeRate 5 58 r0 kappa + max wc (416/100) / 58 + binomRate kappa <= Psi / 58`   on `[lo, hi]`.

* `binEntropy_le_tangent`: Gibbs' inequality, `H(p) <= H(q) + H'(q)(p - q)`;
* `cellB_real`: for `1/2 <= lo` the left side is convex-plus-affine in `kappa` after the tangent at
  `km`, hence checked at the two ends (`rate` is `max 0 (affine) * L`);
* `cellB`, `cellA`: Boolean checkers on rational data with the logarithms of `r0, km, 1 - km` from
  `LogEval.logQ`; `cellB_spec`, `cellA_spec` give the real statement.
-/

namespace CatalanMeasure.GenD.Signed.Data.S1
open CatalanMeasure.GenD.Analytic Set

noncomputable section

/-- Gibbs: the tangent of the binary entropy at `q` lies above it on `[0, 1]`. -/
theorem binEntropy_le_tangent {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.binEntropy p ≤ -q * Real.log q - (1 - q) * Real.log (1 - q) +
      (Real.log (1 - q) - Real.log q) * (p - q) := by
  have hq1' : 0 < 1 - q := by linarith only [hq1]
  rcases hp0.eq_or_lt with rfl | hp0'
  · simp only [Real.binEntropy_zero]
    have : 0 ≤ -Real.log (1 - q) := by
      have := Real.log_nonpos hq1'.le (by linarith only [hq0])
      linarith only [this]
    nlinarith only [this, Real.log_nonpos hq0.le hq1.le, hq0]
  rcases hp1.eq_or_lt with rfl | hp1'
  · simp only [Real.binEntropy_one]
    have h1 := Real.log_nonpos hq0.le hq1.le
    nlinarith only [h1, hq0, hq1']
  have hp1'' : 0 < 1 - p := by linarith only [hp1']
  have hb : Real.binEntropy p = -p * Real.log p - (1 - p) * Real.log (1 - p) := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog]; ring
  rw [hb]
  have h1 := Real.log_le_sub_one_of_pos (div_pos hq0 hp0')
  rw [Real.log_div hq0.ne' hp0'.ne'] at h1
  have h2 := Real.log_le_sub_one_of_pos (div_pos hq1' hp1'')
  rw [Real.log_div hq1'.ne' hp1''.ne'] at h2
  have h1' : p * (Real.log q - Real.log p) ≤ q - p := by
    have e : p * (q / p - 1) = q - p := by field_simp
    have := mul_le_mul_of_nonneg_left h1 hp0'.le
    rw [e] at this
    exact this
  have h2' : (1 - p) * (Real.log (1 - q) - Real.log (1 - p)) ≤ (1 - q) - (1 - p) := by
    have e : (1 - p) * ((1 - q) / (1 - p) - 1) = (1 - q) - (1 - p) := by field_simp
    have := mul_le_mul_of_nonneg_left h2 hp1''.le
    rw [e] at this
    exact this
  nlinarith only [h1', h2']

/-- Real core of a cell with `1/2 <= lo`. -/
theorem cellB_real {lo hi km wc Ψ L Hm Hd Lu Hmu Hdv Hde : ℝ}
    (hlh : lo ≤ hi) (hL0 : 0 ≤ L) (hLu : L ≤ Lu) (hHm : Hm ≤ Hmu) (hHd : |Hd - Hdv| ≤ Hde)
    (hflo : max 0 (lo - 10 / 58) * Lu + wc / 58 + Hmu + Hdv * (lo - km) + |lo - km| * Hde ≤ Ψ)
    (hfhi : max 0 (hi - 10 / 58) * Lu + wc / 58 + Hmu + Hdv * (hi - km) + |hi - km| * Hde ≤ Ψ)
    (htan : ∀ κ ∈ Icc lo hi, Real.binEntropy κ ≤ Hm + Hd * (κ - km)) :
    ∀ κ ∈ Icc lo hi, max 0 ((κ - 10 / 58) * L) + wc / 58 + Real.binEntropy κ ≤ Ψ := by
  have hLu0 : 0 ≤ Lu := hL0.trans hLu
  -- value of the affine-plus-max majorant at an endpoint
  have hend : ∀ e : ℝ, max 0 (e - 10 / 58) * Lu + wc / 58 + Hmu + Hdv * (e - km) +
      |e - km| * Hde ≤ Ψ → max 0 (e - 10 / 58) * L + wc / 58 + Hm + Hd * (e - km) ≤ Ψ := by
    intro e he
    have h1 : max 0 (e - 10 / 58) * L ≤ max 0 (e - 10 / 58) * Lu :=
      mul_le_mul_of_nonneg_left hLu (le_max_left _ _)
    have h2 : Hd * (e - km) ≤ Hdv * (e - km) + |e - km| * Hde := by
      have : (Hd - Hdv) * (e - km) ≤ |(Hd - Hdv) * (e - km)| := le_abs_self _
      rw [abs_mul] at this
      have h3 : |Hd - Hdv| * |e - km| ≤ Hde * |e - km| :=
        mul_le_mul_of_nonneg_right hHd (abs_nonneg _)
      nlinarith only [this, h3]
    linarith only [he, h1, h2, hHm]
  have hlo' := hend lo hflo
  have hhi' := hend hi hfhi
  intro κ hκ
  have hmax : max 0 ((κ - 10 / 58) * L) = max 0 (κ - 10 / 58) * L := by
    rw [max_mul_of_nonneg _ _ hL0, zero_mul]
  rw [hmax]
  have hT := htan κ hκ
  have hconv : max 0 (κ - 10 / 58) * L + wc / 58 + Hm + Hd * (κ - km) ≤ Ψ := by
    rcases hlh.eq_or_lt with h | h
    · have : κ = lo := le_antisymm (h ▸ hκ.2) hκ.1
      subst this; exact hlo'
    · have hd : 0 < hi - lo := sub_pos.mpr h
      set Mlo := max 0 (lo - 10 / 58) with hMlo
      set Mhi := max 0 (hi - 10 / 58) with hMhi
      have hM : (hi - lo) * max 0 (κ - 10 / 58) ≤ (hi - κ) * Mlo + (κ - lo) * Mhi := by
        have h0 : 0 ≤ (hi - κ) * Mlo + (κ - lo) * Mhi :=
          add_nonneg (mul_nonneg (sub_nonneg.mpr hκ.2) (le_max_left _ _))
            (mul_nonneg (sub_nonneg.mpr hκ.1) (le_max_left _ _))
        rcases le_total κ (10 / 58) with hc | hc
        · rw [max_eq_left (by linarith only [hc])]; simpa using h0
        · rw [max_eq_right (by linarith only [hc])]
          have a1 : lo - 10 / 58 ≤ Mlo := le_max_right _ _
          have a2 : hi - 10 / 58 ≤ Mhi := le_max_right _ _
          nlinarith only [mul_le_mul_of_nonneg_left a1 (sub_nonneg.mpr hκ.2),
            mul_le_mul_of_nonneg_left a2 (sub_nonneg.mpr hκ.1)]
      -- combine
      have hLM : (hi - lo) * (max 0 (κ - 10 / 58) * L) ≤ ((hi - κ) * Mlo + (κ - lo) * Mhi) * L := by
        have := mul_le_mul_of_nonneg_right hM hL0
        linarith only [this]
      have hlin : (hi - lo) * (wc / 58 + Hm + Hd * (κ - km)) =
          (hi - κ) * (wc / 58 + Hm + Hd * (lo - km)) + (κ - lo) * (wc / 58 + Hm + Hd * (hi - km)) := by
        ring
      have hA : (hi - κ) * (Mlo * L + (wc / 58 + Hm + Hd * (lo - km))) +
          (κ - lo) * (Mhi * L + (wc / 58 + Hm + Hd * (hi - km))) ≤ (hi - lo) * Ψ := by
        have e1 := mul_le_mul_of_nonneg_left (show Mlo * L + (wc / 58 + Hm + Hd * (lo - km)) ≤ Ψ by
          linarith only [hlo']) (sub_nonneg.mpr hκ.2)
        have e2 := mul_le_mul_of_nonneg_left (show Mhi * L + (wc / 58 + Hm + Hd * (hi - km)) ≤ Ψ by
          linarith only [hhi']) (sub_nonneg.mpr hκ.1)
        nlinarith only [e1, e2]
      have : (hi - lo) * (max 0 (κ - 10 / 58) * L + wc / 58 + Hm + Hd * (κ - km)) ≤ (hi - lo) * Ψ := by
        nlinarith only [hLM, hlin, hA]
      exact le_of_mul_le_mul_left this hd
  linarith only [hT, hconv]

/-- Real core of a cell with `hi <= 1/2` (`binomRate <= log 2` everywhere). -/
theorem cellA_real {hi wc Ψ L Lu l2 : ℝ} (hL0 : 0 ≤ L) (hLu : L ≤ Lu) (hl2 : Real.log 2 ≤ l2)
    (hf : max 0 (hi - 10 / 58) * Lu + wc / 58 + l2 ≤ Ψ) :
    ∀ κ ∈ Icc (0 : ℝ) hi, ∀ B : ℝ, B ≤ Real.log 2 →
      max 0 ((κ - 10 / 58) * L) + wc / 58 + B ≤ Ψ := by
  intro κ hκ B hB
  have hmax : max 0 ((κ - 10 / 58) * L) = max 0 (κ - 10 / 58) * L := by
    rw [max_mul_of_nonneg _ _ hL0, zero_mul]
  rw [hmax]
  have h1 : max 0 (κ - 10 / 58) ≤ max 0 (hi - 10 / 58) := max_le_max le_rfl (by linarith only [hκ.2])
  have h2 : max 0 (κ - 10 / 58) * L ≤ max 0 (hi - 10 / 58) * Lu :=
    mul_le_mul h1 hLu hL0 (le_max_left _ _)
  linarith only [h2, hB, hl2, hf]

/-- Pieces of the cover: `[lo, hi]` of `kappa`, keyhole rate radius `r0`, circle radius `r1 > r0`,
circle exponent `wc` (per `N`), tangent point `km`. -/
structure S1Cell where
  lo : ℚ
  hi : ℚ
  r0 : ℚ
  r1 : ℚ
  wc : ℚ
  km : ℚ

/-- Checker for `1/2 <= lo` cells; `Ψ` is the bound per `n` (`Psi/58`). -/
def cellB (Ψ : ℚ) (c : S1Cell) : Bool :=
  match LogEval.logQ 12 c.r0, LogEval.logQ 12 c.km, LogEval.logQ 12 (1 - c.km) with
  | some (v1, e1), some (v2, e2), some (v3, e3) =>
    decide (1 / 2 ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.hi ≤ 1 ∧ 0 < c.km ∧ c.km < 1 ∧ 0 < c.r0 ∧ c.r0 ≤ 1 ∧
      416 / 100 ≤ c.wc ∧
      max 0 (c.lo - 10 / 58) * (e1 - v1) + c.wc / 58 + (c.km * (e2 - v2) + (1 - c.km) * (e3 - v3)) +
        (v3 - v2) * (c.lo - c.km) + |c.lo - c.km| * (e2 + e3) ≤ Ψ ∧
      max 0 (c.hi - 10 / 58) * (e1 - v1) + c.wc / 58 + (c.km * (e2 - v2) + (1 - c.km) * (e3 - v3)) +
        (v3 - v2) * (c.hi - c.km) + |c.hi - c.km| * (e2 + e3) ≤ Ψ)
  | _, _, _ => false

/-- Checker for the cell `[0, hi]`, `hi <= 1/2`. -/
def cellA (Ψ : ℚ) (c : S1Cell) : Bool :=
  match LogEval.logQ 12 c.r0 with
  | some (v1, e1) =>
    decide (c.lo = 0 ∧ c.hi ≤ 1 / 2 ∧ 0 < c.r0 ∧ c.r0 ≤ 1 ∧ 416 / 100 ≤ c.wc ∧
      max 0 (c.hi - 10 / 58) * (e1 - v1) + c.wc / 58 + 6931471808 / 10 ^ 10 ≤ Ψ)
  | _ => false

/-- The statement a cell certifies (`Ψ` per `n`). -/
def CellStmt (Ψ : ℝ) (r0 wc lo hi : ℝ) : Prop :=
  ∀ κ ∈ Icc lo hi, keyholeRate 5 58 r0 κ + max wc (416 / 100) / 58 + binomRate κ ≤ Ψ

theorem keyholeRate_eq (r0 κ : ℝ) :
    keyholeRate 5 58 r0 κ = max 0 ((κ - 10 / 58) * (-Real.log r0)) := by
  unfold keyholeRate
  rw [one_div, Real.log_inv]
  push_cast
  norm_num

theorem cellB_spec {Ψ : ℚ} {c : S1Cell} (h : cellB Ψ c = true) :
    CellStmt (Ψ : ℝ) (c.r0 : ℝ) (c.wc : ℝ) (c.lo : ℝ) (c.hi : ℝ) := by
  unfold cellB at h
  split at h
  · rename_i v1 e1 v2 e2 v3 e3 h1 h2 h3
    have hd := of_decide_eq_true h
    obtain ⟨hlo, hlh, hh1, hkm0, hkm1, hr0, hr1, hwc, hflo, hfhi⟩ := hd
    obtain ⟨_, E1⟩ := LogEval.logQ_spec h1
    obtain ⟨hkp, E2⟩ := LogEval.logQ_spec h2
    obtain ⟨hkp', E3⟩ := LogEval.logQ_spec h3
    unfold LogEval.Enc at E1 E2 E3
    simp only at E1 E2 E3
    have hkm0' : (0 : ℝ) < c.km := by exact_mod_cast hkm0
    have hkm1' : (c.km : ℝ) < 1 := by exact_mod_cast hkm1
    have e3c : ((1 - c.km : ℚ) : ℝ) = 1 - (c.km : ℝ) := by push_cast; ring
    rw [e3c] at E3
    have hr1' : (c.r0 : ℝ) ≤ 1 := by exact_mod_cast hr1
    have hr0' : (0 : ℝ) < c.r0 := by exact_mod_cast hr0
    have hL0 : 0 ≤ -Real.log (c.r0 : ℝ) := by
      have := Real.log_nonpos hr0'.le hr1'
      linarith only [this]
    have hLu : -Real.log (c.r0 : ℝ) ≤ (e1 : ℝ) - v1 := by
      have := (abs_le.mp E1).1
      linarith only [this]
    have hlk : -Real.log (c.km : ℝ) ≤ (e2 : ℝ) - v2 := by
      have := (abs_le.mp E2).1; linarith only [this]
    have hl1k : -Real.log (1 - (c.km : ℝ)) ≤ (e3 : ℝ) - v3 := by
      have := (abs_le.mp E3).1; linarith only [this]
    have hHm : -(c.km : ℝ) * Real.log c.km - (1 - c.km) * Real.log (1 - (c.km : ℝ)) ≤
        (c.km : ℝ) * (e2 - v2) + (1 - c.km) * (e3 - v3) := by
      nlinarith only [mul_le_mul_of_nonneg_left hlk hkm0'.le,
        mul_le_mul_of_nonneg_left hl1k (sub_nonneg.mpr hkm1'.le)]
    have hHd : |(Real.log (1 - (c.km : ℝ)) - Real.log c.km) - ((v3 : ℝ) - v2)| ≤ (e2 : ℝ) + e3 := by
      have a2 := abs_le.mp E2
      have a3 := abs_le.mp E3
      rw [abs_le]; constructor <;> linarith only [a2.1, a2.2, a3.1, a3.2]
    have hlo' : (1 / 2 : ℝ) ≤ c.lo := by
      have := (Rat.cast_le (K := ℝ)).mpr hlo
      push_cast at this; linarith only [this]
    have hlh' : (c.lo : ℝ) ≤ c.hi := by exact_mod_cast hlh
    have hflo' := (Rat.cast_le (K := ℝ)).mpr hflo
    have hfhi' := (Rat.cast_le (K := ℝ)).mpr hfhi
    push_cast at hflo' hfhi'
    have core := cellB_real (lo := (c.lo : ℝ)) (hi := c.hi) (km := c.km) (wc := c.wc) (Ψ := Ψ)
      (L := -Real.log (c.r0 : ℝ)) (Hm := -(c.km : ℝ) * Real.log c.km - (1 - c.km) * Real.log (1 - (c.km : ℝ)))
      (Hd := Real.log (1 - (c.km : ℝ)) - Real.log c.km)
      (Lu := (e1 : ℝ) - v1) (Hmu := (c.km : ℝ) * (e2 - v2) + (1 - c.km) * (e3 - v3))
      (Hdv := (v3 : ℝ) - v2) (Hde := (e2 : ℝ) + e3) hlh' hL0 hLu hHm hHd hflo' hfhi'
      (fun κ hκ => binEntropy_le_tangent hkm0' hkm1' (by linarith only [hκ.1, hlo'])
        (by have : (c.hi : ℝ) ≤ 1 := by exact_mod_cast hh1
            linarith only [hκ.2, this]))
    intro κ hκ
    have := core κ hκ
    have hwc' : (416 / 100 : ℝ) ≤ c.wc := by
      have := (Rat.cast_le (K := ℝ)).mpr hwc
      push_cast at this; linarith only [this]
    rw [max_eq_left hwc', keyholeRate_eq]
    have hbr : binomRate κ = Real.binEntropy κ := by
      unfold binomRate
      rw [if_pos (by linarith only [hκ.1, hlo'])]
    rw [hbr]
    exact this
  · simp at h

theorem cellA_spec {Ψ : ℚ} {c : S1Cell} (h : cellA Ψ c = true) :
    CellStmt (Ψ : ℝ) (c.r0 : ℝ) (c.wc : ℝ) (c.lo : ℝ) (c.hi : ℝ) := by
  unfold cellA at h
  split at h
  · rename_i v1 e1 h1
    have hd := of_decide_eq_true h
    obtain ⟨hlo, hhi, hr0, hr1, hwc, hf⟩ := hd
    obtain ⟨_, E1⟩ := LogEval.logQ_spec h1
    unfold LogEval.Enc at E1
    simp only at E1
    have hr1' : (c.r0 : ℝ) ≤ 1 := by exact_mod_cast hr1
    have hr0' : (0 : ℝ) < c.r0 := by exact_mod_cast hr0
    have hL0 : 0 ≤ -Real.log (c.r0 : ℝ) := by
      have := Real.log_nonpos hr0'.le hr1'
      linarith only [this]
    have hLu : -Real.log (c.r0 : ℝ) ≤ (e1 : ℝ) - v1 := by
      have := (abs_le.mp E1).1
      linarith only [this]
    have hf' := (Rat.cast_le (K := ℝ)).mpr hf
    push_cast at hf'
    have hl2 : Real.log 2 ≤ (6931471808 / 10 ^ 10 : ℝ) := by
      have := Real.log_two_lt_d9
      norm_num at this ⊢
      linarith only [this]
    have core := cellA_real (hi := (c.hi : ℝ)) (wc := c.wc) (Ψ := Ψ) (L := -Real.log (c.r0 : ℝ))
      (Lu := (e1 : ℝ) - v1) (l2 := 6931471808 / 10 ^ 10) hL0 hLu hl2 hf'
    intro κ hκ
    have hwc' : (416 / 100 : ℝ) ≤ c.wc := by
      have := (Rat.cast_le (K := ℝ)).mpr hwc
      push_cast at this; linarith only [this]
    rw [max_eq_left hwc', keyholeRate_eq]
    have hlo' : (c.lo : ℝ) = 0 := by exact_mod_cast hlo
    have hbr : binomRate κ ≤ Real.log 2 := by
      unfold binomRate
      split_ifs
      · exact Real.binEntropy_le_log_two
      · exact le_rfl
    exact core κ ⟨by linarith only [hκ.1, hlo'], hκ.2⟩ _ hbr
  · simp at h

end

end CatalanMeasure.GenD.Signed.Data.S1
