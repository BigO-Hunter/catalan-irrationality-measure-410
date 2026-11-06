module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.EndGlue
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Bridge
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Core
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.L1Series
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.QTau
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.Hid

@[expose] public section

/-!
# 410 assembly: cell outputs to the contract rows

Each theorem here takes hypotheses of exactly the shape the cell modules export (`…Sup` on the interior,
`…Log` end windows, the `Fq` agreement of plogs and poles and the `ℓ¹` rounding of the polynomial) and
produces one field of `Rows410` for one trial.  No cell module is imported: the instances only plug the
cell theorems in.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly
open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.Consts OAI.InternalCatalan
open CatalanMeasure.Parametric CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Cert
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Cells
open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic

noncomputable section

/-- **Columns (`hSy`) from SC cells.**  `Ft` is the trial field (`hFt` is `hidSC` with `cfLim_eq`),
`Fc` the rounded cell field; `hsup` is the cell `Sup` on `(0,1)`, `hend` the log-form end window at `1`. -/
theorem rowSC_cell (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (Ft Fc : FieldQ) {K : ℝ}
    (hFt : ∀ s, cfLim P410 s + 2 * X.T.form.v.Tform s = fieldTower Ft (poleF Ft.poles) 0 s + K)
    (hpl : Ft.plogs = Fc.plogs) (hpo : Ft.poles = Fc.poles) {δ : ℚ} (hδ : l1Q Ft.poly Fc.poly ≤ δ)
    {T TR c lo : ℝ}
    (hsup : ∀ x ∈ Ioo (0 : ℝ) 1, fieldTower Fc (poleF Fc.poles) 0 x ≤ T)
    (hlo0 : 0 < lo) (hlo1 : lo < 1)
    (hend : ∀ x ∈ Icc lo 1, x ≠ 1 → fieldTower Fc (poleF Fc.poles) 0 x ≤ TR + c * Real.log |x - 1|)
    (hc : 0 < c) (hcmp : TR + c * Real.log (1 - lo) ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
      (famD X N).fCol s ≤ T + δ + K + ε := by
  have hbr : ∀ s ∈ Ioo (0 : ℝ) 1, cfLim P410 s + 2 * X.T.form.v.Tform s ≤
      fieldTower Fc (poleF Fc.poles) 0 s + δ + K := by
    intro s hs
    have hs1 : |s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    have := fieldTower_le_cell Ft Fc hpl hpo hδ hs1 poleF
    rw [hFt s]; linarith
  refine rowSC X hok (r := lo) (T0 := T + δ + K) (lo := lo) (T1 := TR + δ + K) (c1 := c)
    (a := lo / 2) (b := lo) (Sm := T + δ + K) hlo0 hlo1 ?_ hlo0 hlo1 hc ?_ (by linarith) (by linarith)
    hlo1 (by linarith) le_rfl ?_ le_rfl ?_ le_rfl
  · intro s hs
    have h1 := hbr s ⟨hs.1, by linarith [hs.2]⟩
    have h2 := hsup s ⟨hs.1, by linarith [hs.2]⟩
    linarith
  · intro s hs
    have h1 := hbr s ⟨by linarith [hs.1], hs.2⟩
    have h2 := hend s ⟨hs.1.le, hs.2.le⟩ (ne_of_lt hs.2)
    have habs : |s - 1| = 1 - s := by rw [abs_of_neg (by linarith [hs.2])]; ring
    rw [habs] at h2
    linarith
  · intro s hs
    have h1 := hbr s ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h2 := hsup s ⟨by linarith [hs.1], by linarith [hs.2]⟩
    linarith
  · linarith

/-- **Negative free rows (`hSn`) from SN cells.**  `hsup` is the cell `Sup` on `(-1,0)`, `hend` the
log-form end window at `0` (`fNeg_cell_zero`'s `c log|x|`). -/
theorem rowSN_cell (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    (Ft Fc : FieldQ) {K : ℝ}
    (hFt : ∀ x, fNegLim X.T.form (rfLim P410) x = fieldTower Ft (poleF Ft.poles) 0 x + K)
    (hpl : Ft.plogs = Fc.plogs) (hpo : Ft.poles = Fc.poles) {δ : ℚ} (hδ : l1Q Ft.poly Fc.poly ≤ δ)
    {T TR c lo : ℝ}
    (hsup : ∀ x ∈ Ioo (-1 : ℝ) 0, fieldTower Fc (poleF Fc.poles) 0 x ≤ T)
    (hlo0 : -1 < lo) (hlo1 : lo < 0)
    (hend : ∀ x ∈ Icc lo 0, x ≠ 0 → fieldTower Fc (poleF Fc.poles) 0 x ≤ TR + c * Real.log |x - 0|)
    (hc : 0 < c) (hcmp : TR + c * Real.log (-lo) ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0,
      (famD X N).fNeg x ≤ T + δ + K + ε := by
  have hbr : ∀ x ∈ Ioo (-1 : ℝ) 0, fNegLim X.T.form (rfLim P410) x ≤
      fieldTower Fc (poleF Fc.poles) 0 x + δ + K := by
    intro x hx
    have hx1 : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    have := fieldTower_le_cell Ft Fc hpl hpo hδ hx1 poleF
    rw [hFt x]; linarith
  refine rowSN X hok hRt (r := -lo) (Tr := TR + δ + K) (c := c) (hi := lo) (T := T + δ + K)
    (a := lo) (b := lo) (Sm := T + δ + K) (by linarith) (by linarith) hc ?_ hlo1 ?_ hlo0 le_rfl hlo1
    le_rfl (by linarith) ?_ ?_ le_rfl le_rfl
  · intro x hx
    have h1 := hbr x ⟨by linarith [hx.1], hx.2⟩
    have h2 := hend x ⟨by linarith [hx.1], hx.2.le⟩ (ne_of_lt hx.2)
    rw [sub_zero] at h2
    linarith
  · intro x hx
    have h1 := hbr x ⟨hx.1, by linarith [hx.2]⟩
    have h2 := hsup x ⟨hx.1, by linarith [hx.2]⟩
    linarith
  · intro x hx
    have h1 := hbr x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h2 := hsup x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    linarith
  · linarith

/-- **Positive free rows (`hSp`) from SP cells.**  Five regions of `(0,1)`: the log-form end window at `0`
(`hR0`, rounded interior field `F2`), the gap (`hR1`, the trial field `Ft` itself), the interior (`hR2`, `F2`),
the jump region (`hR3`, rounded field `F3`) and the log-form end window at `1` (`hR4`, `F3`).  The spike cost
`csL` is paid on `(1 - θ, 1)`, which lies inside the jump region. -/
theorem rowSP_cell (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    (Ft F2 F3 : FieldQ) (Ts : List LTerm) {K : ℝ}
    (hFt : ∀ x ∈ Ioo (0 : ℝ) 1, fPosLim X.T.form (rfLim P410) (20 / 58) (bSeq X.bs) X.bs.length
      ((X.CSP : ℝ) / 58) (1 / 1024) x = fieldTower Ft (poleF Ft.poles) 0 x + lfieldTower Ts 0 x + K +
        (X.CSP : ℝ) / 58 * (if 1 - 1 / 1024 < x then 1 else 0))
    (hcs : (0 : ℝ) ≤ X.CSP)
    (hpl2 : Ft.plogs = F2.plogs) (hpo2 : Ft.poles = F2.poles) {δ2 : ℚ} (hδ2 : l1Q Ft.poly F2.poly ≤ δ2)
    (hpl3 : Ft.plogs = F3.plogs) (hpo3 : Ft.poles = F3.poles) {δ3 : ℚ} (hδ3 : l1Q Ft.poly F3.poly ≤ δ3)
    {h0 m1 j lo1 TR0 c0 T1 T2 T3 TR4 c4 S : ℝ}
    (hh0 : 0 < h0) (hh0m : h0 < m1) (hm1j : m1 ≤ j) (hj : j = 1 - 1 / 1024) (hjlo : j < lo1) (hlo1 : lo1 < 1)
    (hR0 : ∀ x ∈ Ioc 0 h0, fieldTower F2 (poleF F2.poles) 0 x + lfieldTower Ts 0 x ≤ TR0 + c0 * Real.log |x|)
    (hc0 : 0 < c0)
    (hR1 : ∀ x ∈ Ioo h0 m1, fieldTower Ft (poleF Ft.poles) 0 x + lfieldTower Ts 0 x ≤ T1)
    (hR2 : ∀ x ∈ Icc m1 j, fieldTower F2 (poleF F2.poles) 0 x + lfieldTower Ts 0 x ≤ T2)
    (hR3 : ∀ x ∈ Ico j 1, fieldTower F3 (poleF F3.poles) 0 x + lfieldTower Ts 0 x ≤ T3)
    (hR4 : ∀ x ∈ Icc lo1 1, x ≠ 1 →
      fieldTower F3 (poleF F3.poles) 0 x + lfieldTower Ts 0 x ≤ TR4 + c4 * Real.log |x - 1|)
    (hc4 : 0 < c4)
    (hS0 : TR0 + δ2 + K + c0 * Real.log h0 ≤ S) (hS1 : T1 + K ≤ S) (hS2 : T2 + δ2 + K ≤ S)
    (hS3 : T3 + δ3 + K + (X.CSP : ℝ) / 58 ≤ S)
    (hS4 : TR4 + δ3 + K + (X.CSP : ℝ) / 58 + c4 * Real.log (1 - lo1) ≤ S) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (famD X N).fPosS x ≤ S + ε := by
  have hcs58 : (0 : ℝ) ≤ (X.CSP : ℝ) / 58 := by positivity
  have br2 : ∀ x ∈ Ioo (0 : ℝ) 1, fieldTower Ft (poleF Ft.poles) 0 x ≤ fieldTower F2 (poleF F2.poles) 0 x + δ2 :=
    fun x hx => fieldTower_le_cell Ft F2 hpl2 hpo2 hδ2
      (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]) poleF
  have br3 : ∀ x ∈ Ioo (0 : ℝ) 1, fieldTower Ft (poleF Ft.poles) 0 x ≤ fieldTower F3 (poleF F3.poles) 0 x + δ3 :=
    fun x hx => fieldTower_le_cell Ft F3 hpl3 hpo3 hδ3
      (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]) poleF
  have ind0 : ∀ x : ℝ, x ≤ j → (if 1 - 1 / 1024 < x then (1 : ℝ) else 0) = 0 := by
    intro x hx; rw [if_neg]; rw [← hj]; linarith
  have ind1 : ∀ x : ℝ, (if 1 - 1 / 1024 < x then (1 : ℝ) else 0) ≤ 1 := by
    intro x; split_ifs <;> norm_num
  have hlogh0 : ∀ x ∈ Ioc 0 h0, Real.log |x| ≤ Real.log h0 := by
    intro x hx; rw [abs_of_pos hx.1]; exact Real.log_le_log hx.1 hx.2
  refine rowSP X hok hRt (r := h0) (Tr := TR0 + δ2 + K) (c := c0) (lo := lo1)
    (T1 := TR4 + δ3 + K + (X.CSP : ℝ) / 58) (c1 := c4) (a := h0) (b := lo1) (Sm := S)
    hh0 (by linarith) hc0 ?_ (by linarith) hlo1 hc4 ?_ hh0 (by linarith) hlo1 le_rfl le_rfl ?_ hS0 hS4 le_rfl
  · intro x hx
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
    rw [hFt x hx01, ind0 x (by linarith [hx.2])]
    have := hR0 x ⟨hx.1, hx.2.le⟩
    have := br2 x hx01
    linarith
  · intro x hx
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    rw [hFt x hx01]
    have h4 := hR4 x ⟨hx.1.le, hx.2.le⟩ (ne_of_lt hx.2)
    have habs : |x - 1| = 1 - x := by rw [abs_of_neg (by linarith [hx.2])]; ring
    rw [habs] at h4
    have := br3 x hx01
    have := ind1 x
    have : (X.CSP : ℝ) / 58 * (if 1 - 1 / 1024 < x then 1 else 0) ≤ (X.CSP : ℝ) / 58 := by
      calc _ ≤ (X.CSP : ℝ) / 58 * 1 := mul_le_mul_of_nonneg_left (ind1 x) hcs58
        _ = _ := mul_one _
    linarith
  · intro x hx
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [hFt x hx01]
    rcases eq_or_lt_of_le hx.1 with hxe | hxg
    · -- the left end point of the interior: the end window at `0`
      subst hxe
      rw [ind0 _ (by linarith)]
      have := hR0 h0 ⟨hh0, le_rfl⟩
      have := br2 h0 hx01
      rw [abs_of_pos hh0] at *
      linarith
    by_cases h1 : x < m1
    · rw [ind0 x (by linarith)]
      have := hR1 x ⟨hxg, h1⟩
      linarith
    push_neg at h1
    by_cases h2 : x ≤ j
    · rw [ind0 x h2]
      have := hR2 x ⟨h1, h2⟩
      have := br2 x hx01
      linarith
    push_neg at h2
    have := hR3 x ⟨h2.le, by linarith [hx.2]⟩
    have := br3 x hx01
    have : (X.CSP : ℝ) / 58 * (if 1 - 1 / 1024 < x then 1 else 0) ≤ (X.CSP : ℝ) / 58 := by
      calc _ ≤ (X.CSP : ℝ) / 58 * 1 := mul_le_mul_of_nonneg_left (ind1 x) hcs58
        _ = _ := mul_one _
    linarith


/-- **σ⁻ rows (`hneg`) from SM cells.**  The SM `Sup` covers `(-1, g]` with `g = -gs`; on `x ≤ g` the finite-`N`
error `(-log|x|)/(2ν)` of `fNegM_le_lim` is at most `(-log (-g))/(2ν) → 0`. -/
theorem rowNeg_cell (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    (Ft Fc : FieldQ) {K : ℝ}
    (hFt : ∀ x, fNegMLim X.T.form (fun y => -((53 : ℝ) / 58) * Real.log (1 + y ^ 2)) x =
      fieldTower Ft (poleF Ft.poles) 0 x + K)
    (hpl : Ft.plogs = Fc.plogs) (hpo : Ft.poles = Fc.poles) {δ : ℚ} (hδ : l1Q Ft.poly Fc.poly ≤ δ)
    {g T : ℝ} (hg1 : -1 < g) (hg0 : g < 0)
    (hsup : ∀ x ∈ Ioc (-1 : ℝ) g, fieldTower Fc (poleF Fc.poles) 0 x ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ g →
      (famD X N).fNegM (groupedMarkedField P410 N) x ≤ T + δ + K + ε := by
  intro ε hε
  have hf := famD_family X hok
  have hP : Admissible P410 := D58.Odd.design_admissible
  have hRm := Glue410.hRm_neg hP (c := (53 : ℝ) / 58) (by norm_num [P410, D58.Odd.design])
    (Rm := fun N => groupedMarkedField P410 N) (fun N => rfl)
  have hL := fNegM_le_lim hf (famD_R_tail X hRt) (by norm_num) le_rfl hRm (ε / 2) (by linarith)
  have hlog : 0 ≤ -Real.log (-g) := by
    have : Real.log (-g) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  have h2 : ∀ᶠ N in atTop, (-Real.log (-g)) / (2 * (famD X N).ν) ≤ ε / 2 :=
    (tendsto_const_nhds.div_atTop (hf.hν.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).eventually
      (ge_mem_nhds (by linarith))
  filter_upwards [hL, h2, hf.hν.eventually_gt_atTop 0] with N hN h2N hνN x hx hxg
  have e1 := hN x hx
  have hlx : -Real.log |x| ≤ -Real.log (-g) := by
    have hax : |x| = -x := abs_of_neg hx.2
    rw [hax]
    have := Real.log_le_log (by linarith) (by linarith : -g ≤ -x)
    linarith
  have e2 : (-Real.log |x|) / (2 * (famD X N).ν) ≤ (-Real.log (-g)) / (2 * (famD X N).ν) :=
    div_le_div_of_nonneg_right hlx (by positivity)
  have hx1 : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have e3 := fieldTower_le_cell Ft Fc hpl hpo hδ hx1 poleF
  have e4 := hsup x ⟨hx.1, hxg⟩
  have e5 := hFt x
  have e6 : (groupedMarkedField P410 N) = (fun N => groupedMarkedField P410 N) N := rfl
  linarith

/-- `fPosMS_cell` on the half-open cell `[lo, hi)` (the proof uses the cell only pointwise). -/
theorem fPosMS_cell_Ico {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {Rm : ℕ → ℝ → ℝ}
    {RmL : ℝ → ℝ} {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω) (hω1 : ω < 1) (hω0 : 0 ≤ ω) {σ csL θL : ℝ}
    {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (𝓝 σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (𝓝 csL))
    (hRm : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, Rm N x - RmL x ≤ ε)
    {lo hi : ℝ} {Tf : ℝ → ℝ} (hlo : 0 < lo) (hhi : hi ≤ 1)
    (hlim : ∀ x ∈ Ico lo hi, fPosMSLim F RmL σ bL KL csL θL x ≤ Tf x) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ico lo hi, (D N).fPosMS (Rm N) x ≤ Tf x + ε := by
  intro ε hε
  set S : ℝ := ∑' k, |tseq F.a.f F.a.tail k| with hS
  set Db : ℝ := 2 * ∑ i ∈ Finset.range KL, |bL (i + 1)| with hDb
  set CR : ℝ := rW F.R with hCR
  have hBt : Tendsto (fun N => (|Real.log lo| + Real.log (1 / (1 - (D N).τ ^ 2))) / (2 * (D N).ν) +
      2 * (S * (1 - (D N).τ)) + CR * ((1 - (D N).τ) / (1 - ω)) +
      Db * |((D N).sp : ℝ) / (D N).ν - σ| + |(D N).cs - csL| +
      polyMass F.qTn * ((1 - (D N).τ ^ 2) / (1 - 1 / 8))) atTop (𝓝 0) := by
    have h9n : Tendsto (fun N => polyMass F.qTn * ((1 - (D N).τ ^ 2) / (1 - 1 / 8))) atTop
        (𝓝 0) := by
      have hτ2 : Tendsto (fun N => 1 - (D N).τ ^ 2) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hf.hτ.pow 2)
      simpa using (hτ2.div_const (1 - 1 / 8)).const_mul (polyMass F.qTn)

    have h1 : Tendsto (fun N => 1 - (D N).τ) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hf.hτ
    have h5 : Tendsto (fun N => 2 * (S * (1 - (D N).τ))) atTop (𝓝 0) := by
      simpa using (h1.const_mul S).const_mul 2
    have h6 : Tendsto (fun N => Db * |((D N).sp : ℝ) / (D N).ν - σ|) atTop (𝓝 0) := by
      simpa using ((hσ.sub_const σ).abs).const_mul Db
    have h7 : Tendsto (fun N => |(D N).cs - csL|) atTop (𝓝 0) := by
      simpa using (hcs.sub_const csL).abs
    have h8 : Tendsto (fun N => CR * ((1 - (D N).τ) / (1 - ω))) atTop (𝓝 0) := by
      simpa using (h1.div_const (1 - ω)).const_mul CR
    have h9 : Tendsto (fun N => (|Real.log lo| + Real.log (1 / (1 - (D N).τ ^ 2))) /
        (2 * (D N).ν)) atTop (𝓝 0) := by
      have a1 : Tendsto (fun N => |Real.log lo| / (2 * (D N).ν)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (hf.hν.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
      have a2 : Tendsto (fun N => Real.log (1 / (1 - (D N).τ ^ 2)) / (2 * (D N).ν)) atTop
          (𝓝 0) := by
        have : Tendsto (fun N => Real.log (1 / (1 - (D N).τ ^ 2)) / (2 * (D N).ν)) atTop
            (𝓝 ((1 / 2 : ℝ) * 0)) :=
          (hf.hℓ.const_mul (1 / 2 : ℝ)).congr (fun N => by ring)
        simpa only [mul_zero] using this
      simpa [add_div] using a1.add a2
    simpa using (((((h9.add h5).add h8).add h6).add h7).add h9n)
  have hB : ∀ᶠ N in atTop, (|Real.log lo| + Real.log (1 / (1 - (D N).τ ^ 2))) / (2 * (D N).ν) +
      2 * (S * (1 - (D N).τ)) + CR * ((1 - (D N).τ) / (1 - ω)) +
      Db * |((D N).sp : ℝ) / (D N).ν - σ| + |(D N).cs - csL| +
      polyMass F.qTn * ((1 - (D N).τ ^ 2) / (1 - 1 / 8)) ≤ ε / 2 :=
    hBt.eventually (ge_mem_nhds (by linarith))
  filter_upwards [hRm (ε / 2) (by linarith), hB, hf.hν.eventually_gt_atTop 0] with N hRmN hBN hνN
    x hx
  have hs := hf.spec N
  have hτN := hs.hτ
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hx1 : |x| ≤ 1 := TrialForm.abs_le_one_of_mem_Ioo (by norm_num) le_rfl hxI
  rw [TrialForm.fPosMS_closed hs (Rm N) hxI, hbL N, hKL N, hθL N]
  have hc0 := c0_nonneg hτN
  have eSa := Sa_block hf N hx1
  have eDil : F.dilT ((D N).τ ^ 2 * x) - F.dilT x ≤
      polyMass F.qTn * ((1 - (D N).τ ^ 2) / (1 - 1 / 8)) := by
    have hBD : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas F.qT) (D N).Cb := by
      have := hs.bd.hP true; rwa [hs.hμT] at this
    have hBDn : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas F.qTn) (D N).Cb := by
      have := hs.bd.hN true; rwa [hs.hμTn] at this
    have h1 := dilPot_mono hs.pT hBD (c := (D N).τ ^ 2 * x) (c' := x)
      (mul_pos (pow_pos hτN.1 2) hxI.1)
      (mul_le_of_le_one_left hxI.1.le (by nlinarith [hτN.1, hτN.2])) hxI.2
    have h2 := dilPot_sub_le_supp hs.pTn hBDn (polyMeas_ae_le hs.hTn)
      (by norm_num : (1 / 8 : ℝ) < 1) (c := (D N).τ ^ 2 * x) (c' := x)
      (mul_pos (pow_pos hτN.1 2) hxI.1) (by nlinarith [hτN.1, hτN.2, hxI.2]) hxI.1 hxI.2.le
    have h3 : |(D N).τ ^ 2 * x - x| ≤ 1 - (D N).τ ^ 2 := by
      have e : (D N).τ ^ 2 * x - x = -((1 - (D N).τ ^ 2) * x) := by ring
      rw [e, abs_neg, abs_mul, abs_of_nonneg (by nlinarith [hτN.1, hτN.2] : 0 ≤ 1 - (D N).τ ^ 2),
        abs_of_pos hxI.1]
      exact mul_le_of_le_one_right (by nlinarith [hτN.1, hτN.2]) hxI.2.le
    have h4 := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right h3 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 8)) (polyMass_nonneg hs.pTn)
    unfold TrialForm.dilT
    have h5 := abs_le.mp h2
    nlinarith [h5.1, h5.2, h1, h4]
  have eR := rForm_sub_rLim_le' hs.hτ hs.hRf hs.hRok hωR hω1 hω0 hx1
  have eDen : |(((D N).sp : ℝ) / (D N).ν - σ) * denPoly bL KL x| ≤
      Db * |((D N).sp : ℝ) / (D N).ν - σ| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_denPoly_le bL KL hx1) (abs_nonneg _)
  have eCs : |((D N).cs - csL) * (if 1 - θL < x then 1 else 0)| ≤ |(D N).cs - csL| := by
    rw [abs_mul]
    split_ifs <;> simp
  have hl : -Real.log |x| ≤ |Real.log lo| := by
    rw [abs_of_pos hxI.1]
    have := Real.log_le_log hlo hx.1
    linarith [le_abs_self (Real.log lo), neg_abs_le (Real.log lo)]
  have eL : ((1 - F.η) / (4 * (D N).ν)) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) ≤
      (|Real.log lo| + Real.log (1 / (1 - (D N).τ ^ 2))) / (2 * (D N).ν) := by
    have hX : 0 ≤ -Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2)) := by
      have := Real.log_nonpos (abs_nonneg x) hx1
      linarith
    have hk : ((1 - F.η) / (4 * (D N).ν)) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) ≤
        (1 / (2 * (D N).ν)) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) := by
      refine mul_le_mul_of_nonneg_right ?_ hX
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hs.hηI.1, hνN]
    refine hk.trans ?_
    rw [one_div, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have u1 := hRmN x hxI
  have u3 := abs_le.mp eSa
  have u5 := abs_le.mp eR
  have u6 := abs_le.mp eDen
  have u7 := abs_le.mp eCs
  have h := hlim x hx
  unfold fPosMSLim at h
  linarith [u1, eL, u3.1, u3.2, eDil, u5.1, u5.2, u6.1, u6.2, u7.1, u7.2]


/-- The σ⁺ limit field of a family member, with `RmL = -(53/58) log (1 + y²)` and the family's spike data. -/
abbrev posLim (X : FamPar) (x : ℝ) : ℝ :=
  fPosMSLim X.T.form (fun y => -((53 : ℝ) / 58) * Real.log (1 + y ^ 2)) (20 / 58) (bSeq X.bs) X.bs.length
    ((X.CSP : ℝ) / 58) (1 / 1024) x

/-- `fPosMS ≤ Tf + ε` on `[lo, hi)` for a member of the family, from the limit bound (`fPosMS_cell_Ico` with the
family's data). -/
theorem posMS_fam (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    {lo hi : ℝ} {Tf : ℝ → ℝ} (hlo : 0 < lo) (hhi : hi ≤ 1)
    (hlim : ∀ x ∈ Ico lo hi, posLim X x ≤ Tf x) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ico lo hi, (famD X N).fPosMS (groupedMarkedField P410 N) x ≤ Tf x + ε := by
  have hf := famD_family X hok
  have hP : Admissible P410 := D58.Odd.design_admissible
  have hRm := Glue410.hRm_pos hP (c := (53 : ℝ) / 58) (by norm_num [P410, D58.Odd.design])
    (Rm := fun N => groupedMarkedField P410 N) (fun N => rfl)
  have hcs : Tendsto (fun N => (famD X N).cs) atTop (𝓝 ((X.CSP : ℝ) / 58)) := tendsto_const_nhds
  exact fPosMS_cell_Ico hf (famD_R_tail X hRt) (by norm_num) le_rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (famD_sigma_tendsto X) hcs hRm hlo hhi hlim

/-- **σ⁺ top rows (`hposTop`) from the top cells.**  On `[xc, 1)`: the top cell `Sup` on `[xc, m]` (field `F1`) and
the jump region `[m, 1)` (field `F2`, spike cost paid there, `m = 1 - 1/1024`). -/
theorem rowPosTop_cell (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    (Ft F1 F2 : FieldQ) (Ts : List LTerm) {K : ℝ}
    (hFt : ∀ x ∈ Ioo (0 : ℝ) 1, posLim X x = fieldTower Ft (poleF Ft.poles) 0 x + lfieldTower Ts 0 x + K +
        (X.CSP : ℝ) / 58 * (if 1 - 1 / 1024 < x then 1 else 0))
    (hcs : (0 : ℝ) ≤ X.CSP)
    (hpl1 : Ft.plogs = F1.plogs) (hpo1 : Ft.poles = F1.poles) {δ1 : ℚ} (hδ1 : l1Q Ft.poly F1.poly ≤ δ1)
    (hpl2 : Ft.plogs = F2.plogs) (hpo2 : Ft.poles = F2.poles) {δ2 : ℚ} (hδ2 : l1Q Ft.poly F2.poly ≤ δ2)
    {xc m T1 T2 S : ℝ} (hxc : 0 < xc) (hxcm : xc ≤ m) (hm : m = 1 - 1 / 1024)
    (hR1 : ∀ x ∈ Icc xc m, fieldTower F1 (poleF F1.poles) 0 x + lfieldTower Ts 0 x ≤ T1)
    (hR2 : ∀ x ∈ Ico m 1, fieldTower F2 (poleF F2.poles) 0 x + lfieldTower Ts 0 x ≤ T2)
    (hS1 : T1 + δ1 + K ≤ S) (hS2 : T2 + δ2 + K + (X.CSP : ℝ) / 58 ≤ S) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, xc ≤ x →
      (famD X N).fPosMS (groupedMarkedField P410 N) x ≤ S + ε := by
  have hcs58 : (0 : ℝ) ≤ (X.CSP : ℝ) / 58 := by positivity
  have hlim : ∀ x ∈ Ico xc 1, posLim X x ≤ S := by
    intro x hx
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have hx1 : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx01.1, hx01.2]
    rw [hFt x hx01]
    by_cases h : x ≤ m
    · have hi0 : (if 1 - 1 / 1024 < x then (1 : ℝ) else 0) = 0 := by rw [if_neg]; rw [← hm]; linarith
      rw [hi0]
      have := hR1 x ⟨hx.1, h⟩
      have := fieldTower_le_cell Ft F1 hpl1 hpo1 hδ1 hx1 poleF
      linarith
    · push_neg at h
      have := hR2 x ⟨h.le, hx.2⟩
      have := fieldTower_le_cell Ft F2 hpl2 hpo2 hδ2 hx1 poleF
      have : (X.CSP : ℝ) / 58 * (if 1 - 1 / 1024 < x then 1 else 0) ≤ (X.CSP : ℝ) / 58 := by
        split_ifs <;> linarith
      linarith
  intro ε hε
  filter_upwards [posMS_fam X hok hRt (Tf := fun _ => S) hxc le_rfl hlim ε hε] with N hN x hx hxx
  exact hN x ⟨hxx, hx.2⟩

/-- **σ⁺ rows (`hpos`) from the R cells at two corners `α₁ ≤ α₂`.**  `fPosMR α = fPosMS + rc α L` is affine in
`α`; the corner cells bound `posLim + rc αₖ L` on `[g, xc)`, so every `α ∈ [α₁, α₂]` gets the chord of the corner
thresholds. -/
theorem rowPos_cell (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    {rc : ℝ} (hrc : 0 ≤ rc) {α₁ α₂ : ℝ} (hα : α₁ < α₂) (hα₁ : 0 ≤ α₁)
    (Ft₁ Ft₂ F₁ F₂ : FieldQ) (Ts : List LTerm) {K : ℝ}
    (hFt₁ : ∀ x ∈ Ioo (0 : ℝ) 1, posLim X x + rc * α₁ * (-Real.log (1 - x ^ 2)) =
      fieldTower Ft₁ (poleF Ft₁.poles) 0 x + lfieldTower Ts 0 x + K +
        (X.CSP : ℝ) / 58 * (if 1 - 1 / 1024 < x then 1 else 0))
    (hFt₂ : ∀ x ∈ Ioo (0 : ℝ) 1, posLim X x + rc * α₂ * (-Real.log (1 - x ^ 2)) =
      fieldTower Ft₂ (poleF Ft₂.poles) 0 x + lfieldTower Ts 0 x + K +
        (X.CSP : ℝ) / 58 * (if 1 - 1 / 1024 < x then 1 else 0))
    (hpl₁ : Ft₁.plogs = F₁.plogs) (hpo₁ : Ft₁.poles = F₁.poles) {δ₁ : ℚ} (hδ₁ : l1Q Ft₁.poly F₁.poly ≤ δ₁)
    (hpl₂ : Ft₂.plogs = F₂.plogs) (hpo₂ : Ft₂.poles = F₂.poles) {δ₂ : ℚ} (hδ₂ : l1Q Ft₂.poly F₂.poly ≤ δ₂)
    {g xc T₁ T₂ : ℝ} (hg : 0 < g) (hgxc : g ≤ xc) (hxc : xc ≤ 1 - 1 / 1024)
    (hR₁ : ∀ x ∈ Icc g xc, fieldTower F₁ (poleF F₁.poles) 0 x + lfieldTower Ts 0 x ≤ T₁)
    (hR₂ : ∀ x ∈ Icc g xc, fieldTower F₂ (poleF F₂.poles) 0 x + lfieldTower Ts 0 x ≤ T₂) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc α₁ α₂, ∀ x ∈ Ioo (0 : ℝ) 1, g ≤ x → x < xc →
      (famD X N).fPosMR (groupedMarkedField P410 N) rc α x ≤
        (T₁ + δ₁ + K) + (α - α₁) / (α₂ - α₁) * ((T₂ + δ₂ + K) - (T₁ + δ₁ + K)) + ε := by
  have hlimk : ∀ (αk Tk : ℝ) (Ftk Fk : FieldQ) {δk : ℚ},
      (∀ x ∈ Ioo (0 : ℝ) 1, posLim X x + rc * αk * (-Real.log (1 - x ^ 2)) =
        fieldTower Ftk (poleF Ftk.poles) 0 x + lfieldTower Ts 0 x + K +
          (X.CSP : ℝ) / 58 * (if 1 - 1 / 1024 < x then 1 else 0)) →
      Ftk.plogs = Fk.plogs → Ftk.poles = Fk.poles → l1Q Ftk.poly Fk.poly ≤ δk →
      (∀ x ∈ Icc g xc, fieldTower Fk (poleF Fk.poles) 0 x + lfieldTower Ts 0 x ≤ Tk) →
      ∀ x ∈ Ico g xc, posLim X x ≤ (fun x => Tk + δk + K - rc * αk * (-Real.log (1 - x ^ 2))) x := by
    intro αk Tk Ftk Fk δk hF hpl hpo hδ hR x hx
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hx1 : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx01.1, hx01.2]
    have e := hF x hx01
    have hi0 : (if 1 - 1 / 1024 < x then (1 : ℝ) else 0) = 0 := by rw [if_neg]; linarith [hx.2]
    rw [hi0] at e
    have := hR x ⟨hx.1, hx.2.le⟩
    have := fieldTower_le_cell Ftk Fk hpl hpo hδ hx1 poleF
    show posLim X x ≤ Tk + δk + K - rc * αk * (-Real.log (1 - x ^ 2))
    linarith
  have hxc1 : xc ≤ 1 := by linarith
  intro ε hε
  have h₁ := posMS_fam X hok hRt hg hxc1 (hlimk α₁ T₁ Ft₁ F₁ hFt₁ hpl₁ hpo₁ hδ₁ hR₁) ε hε
  have h₂ := posMS_fam X hok hRt hg hxc1 (hlimk α₂ T₂ Ft₂ F₂ hFt₂ hpl₂ hpo₂ hδ₂ hR₂) ε hε
  filter_upwards [h₁, h₂] with N hN₁ hN₂ α hα' x _ hgx hxx
  have a₁ := hN₁ x ⟨hgx, hxx⟩
  have a₂ := hN₂ x ⟨hgx, hxx⟩
  have hd : 0 < α₂ - α₁ := by linarith
  set s := (α - α₁) / (α₂ - α₁) with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith [hα'.1]) hd.le
  have hs1 : s ≤ 1 := (div_le_one hd).mpr (by linarith [hα'.2])
  have hαs : α = (1 - s) * α₁ + s * α₂ := by
    rw [hs]; field_simp; ring
  unfold SignedData.fPosMR
  set L := -Real.log (1 - x ^ 2)
  set M := (famD X N).fPosMS (groupedMarkedField P410 N) x
  have : M + rc * α * L = (1 - s) * (M + rc * α₁ * L) + s * (M + rc * α₂ * L) := by rw [hαs]; ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left a₁ (by linarith : (0 : ℝ) ≤ 1 - s), mul_le_mul_of_nonneg_left a₂ hs0]

end

end CatalanMeasure.GenD.Signed.Data.Assembly
