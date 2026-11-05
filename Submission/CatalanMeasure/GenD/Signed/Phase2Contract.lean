module

public import Submission.CatalanMeasure.GenD.Signed.Interp
public import Submission.CatalanMeasure.GenD.Signed.SigmaCap
public import Submission.CatalanMeasure.GenD.Signed.SpikeEnds
public import Submission.CatalanMeasure.GenD.Signed.SheetNear
public import Submission.CatalanMeasure.GenD.Signed.MarkedCap
public import Submission.CatalanMeasure.GenD.Signed.Brackets
public import Submission.CatalanMeasure.GenD.Signed.LemmaT
public import Submission.CatalanMeasure.GenD.Analytic.MarkedSecond

/-!
# Phase 2 contract: the complete `SignedNearBounds` from endpoint data

`Phase2Data I` bundles exactly the data a Phase 2 data module supplies for `I` α-intervals:
the two endpoint trial families `DA i`, `DB i` at `αA i < αB i`, the endpoint suprema of the row,
column and FIXED-ROW fields (`fNegM`, `fPosMS`, `fPosMR`, `fNearMS`), the endpoint constants and
curvature, the dual chord `zb`, the cap constants (`CapEnd`) and the two budget inequalities.
`Phase2Data.toBounds` assembles the contract of `EnergyNear` from

* `SignedNearBounds.ofEnds` (Theorem M) for `e_mem, v_summable, R_geom, t_geom, reference, rowNeg,
  rowPos, column, const_le, budgetFix`;
* `fixedSum_ends` (below), the endpoint form of `fixedSumAt_of_cap` (Theorem S with the top cap):
  the fixed-row fields are exactly affine in the interpolation weight (`fNegM_interp`, ...), so
  endpoint suprema suffice; `ZB := zbCap` of the chord cap data;
* `spikeFix_of_ends` (Theorem SE) for `spikeFix`.

`Phase2Data.signedSecondSheetNear` is the end-to-end corollary: `SignedSecondSheetCore` for the
sheet, given the identification of the data with the sheet's problem data.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set Filter OAI.InternalCatalan

noncomputable section

/-! ### 1. Elementary mixing -/

theorem mix_le {l a b A B ε : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (ha : a ≤ A + ε) (hb : b ≤ B + ε) :
    (1 - l) * a + l * b ≤ ((1 - l) * A + l * B) + ε := by
  nlinarith [mul_le_mul_of_nonneg_left ha (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hb h0]

theorem mix_le_const {l a b M : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (ha : a ≤ M) (hb : b ≤ M) :
    (1 - l) * a + l * b ≤ M := by
  nlinarith [mul_le_mul_of_nonneg_left ha (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hb h0]

theorem mix_nonneg {l a b : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (1 - l) * a + l * b :=
  add_nonneg (mul_nonneg (sub_nonneg.2 h1) ha) (mul_nonneg h0 hb)

theorem abs_le_one_of_Ioo {x a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) (hx : x ∈ Ioo a b) : |x| ≤ 1 :=
  abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-! ### 2. The cap data at the two endpoints and its chord -/

/-- The σ-cap data of one α-interval at its two endpoint trials `A`, `B`: the node threshold `gs`,
the top-cell start `xc`, the cap density `C1`, the off-top bounds `lam*` and the top-cell constants
`g*` of the fixed-row fields of each endpoint, the log coefficients `rSA, rSB` of the near field
and `rP` of the positive field (the latter is not interpolated: it only has to dominate
`rc α`). -/
structure CapEnd where
  gs : ℝ
  xc : ℝ
  C1 : ℝ
  lamNA : ℝ
  lamNB : ℝ
  lamPA : ℝ → ℝ
  lamPB : ℝ → ℝ
  gPA : ℝ → ℝ
  gPB : ℝ → ℝ
  rP : ℝ → ℝ
  lamSA : ℝ → ℝ → ℝ
  lamSB : ℝ → ℝ → ℝ
  gSA : ℝ → ℝ → ℝ
  gSB : ℝ → ℝ → ℝ
  rSA : ℝ → ℝ → ℝ
  rSB : ℝ → ℝ → ℝ

/-- The cap data of the interpolated family: chords of the endpoint bounds. -/
def CapEnd.toS (E : CapEnd) (αA αB : ℝ) : SigmaCapData where
  gs := E.gs
  xc := E.xc
  C1 := E.C1
  lamN := fun α => chord αA αB E.lamNA E.lamNB α
  lamP := fun α => chord αA αB (E.lamPA α) (E.lamPB α) α
  gP := fun α => chord αA αB (E.gPA α) (E.gPB α) α
  rP := E.rP
  lamS := fun α β => chord αA αB (E.lamSA α β) (E.lamSB α β) α
  gS := fun α β => chord αA αB (E.gSA α β) (E.gSB α β) α
  rS := fun α β => chord αA αB (E.rSA α β) (E.rSB α β) α

/-! ### 3. `fixedSum` of one interval from endpoint data -/

/-- **`fixedSum` of one α-interval from the endpoint bounds of the fixed-row fields.**  The fields
`fNegM, fPosMS, fPosMR, fNearMS` of the interpolated family are affine in the weight, so the
endpoint hypotheses (A and B, same form as the hypotheses of `fixedSumAt_of_cap`) give those of
the chord cap data `E.toS αA αB`; `ZB := zbCap (E.toS αA αB)`. -/
theorem fixedSum_ends {ncount : ℕ → ℕ} {Rm Rn : ℕ → ℝ → ℝ} {rc αA αB lo hi : ℝ}
    {DA DB : ℕ → SignedData} (h : IntervalEnds αA αB lo hi DA DB) (E : CapEnd)
    (constant : ℕ → ℝ → ℝ)
    {FixAdm : ∀ (N m1 m2 s : ℕ), (Fin m1 → ℝ) → (Fin m2 → ℝ) → (Fin s → ℝ) → Prop}
    (hxc0 : 0 ≤ E.xc) (hxc1 : E.xc < 1) (hC1 : 0 < E.C1) (hrc : 0 ≤ rc) (hlo : 0 ≤ lo)
    (hhi : hi ≤ 1) (hn : ∀ N, 0 < N → 0 < ncount N) (hν : ∀ N, (DA N).ν = (ncount N : ℝ))
    (hrP : ∀ α ∈ Icc lo hi, rc * α ≤ E.rP α)
    (hrSA : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, 0 ≤ E.rSA α β)
    (hrSB : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, 0 ≤ E.rSB α β)
    (umin : ℕ → ℝ) (hum0 : ∀ N, 0 < umin N) (hum1 : ∀ N, umin N ≤ 1) (Bd Rbd : ℝ)
    (hBdPA : ∀ α ∈ Icc lo hi, E.gPA α - E.lamPA α ≤ Bd)
    (hBdPB : ∀ α ∈ Icc lo hi, E.gPB α - E.lamPB α ≤ Bd)
    (hBdSA : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, E.gSA α β - E.lamSA α β ≤ Bd)
    (hBdSB : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, E.gSB α β - E.lamSB α β ≤ Bd)
    (hRP : ∀ α ∈ Icc lo hi, E.rP α ≤ Rbd)
    (hRSA : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, E.rSA α β ≤ Rbd)
    (hRSB : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, E.rSB α β ≤ Rbd)
    (hn_top : Tendsto (fun N => (ncount N : ℝ)) atTop atTop)
    (hlogu : Tendsto (fun N => -Real.log (umin N) / (ncount N : ℝ)) atTop (nhds 0))
    (hFix : ∀ N m1 m2 s (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
      FixAdm N m1 m2 s yn yp zp →
        FixAdmCap E.gs E.xc E.C1 (ncount N : ℝ) (umin N) yn yp zp)
    (hnegA : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -E.gs → (DA N).fNegM (Rm N) x ≤ E.lamNA + ε)
    (hnegB : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -E.gs → (DB N).fNegM (Rm N) x ≤ E.lamNB + ε)
    (hposA : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.gs ≤ x → x < E.xc →
        (DA N).fPosMR (Rm N) rc α x ≤ E.lamPA α + ε)
    (hposB : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.gs ≤ x → x < E.xc →
        (DB N).fPosMR (Rm N) rc α x ≤ E.lamPB α + ε)
    (hposTopA : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.xc ≤ x → (DA N).fPosMS (Rm N) x ≤ E.gPA α + ε)
    (hposTopB : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.xc ≤ x → (DB N).fPosMS (Rm N) x ≤ E.gPB α + ε)
    (hnearA : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.gs ≤ x → x < E.xc →
        (DA N).fNearMS (Rn N) α β x ≤ E.lamSA α β + ε)
    (hnearB : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.gs ≤ x → x < E.xc →
        (DB N).fNearMS (Rn N) α β x ≤ E.lamSB α β + ε)
    (hnearTopA : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.xc ≤ x →
        (DA N).fNearMS (Rn N) α β x ≤
          E.gSA α β + ε + E.rSA α β * (-Real.log (1 - x ^ 2)))
    (hnearTopB : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.xc ≤ x →
        (DB N).fNearMS (Rn N) α β x ≤
          E.gSB α β + ε + E.rSB α β * (-Real.log (1 - x ^ 2))) :
    FixedSumAt ncount (interpFamily αA αB DA DB constant) Rm Rn rc lo hi
      (zbCap (E.toS αA αB)) FixAdm := by
  have hmem : ∀ α ∈ Icc lo hi, 0 ≤ interpL αA αB α ∧ interpL αA αB α ≤ 1 :=
    fun α hα => h.mem hα
  refine fixedSumAt_of_cap (E.toS αA αB) (ZB := zbCap (E.toS αA αB)) hxc0 hxc1 hC1 hrc hlo hhi
    hn (fun N α => hν N) hrP ?_ umin hum0 hum1 Bd Rbd ?_ ?_ ?_ ?_ hn_top hlogu hFix
    (fun _ _ _ _ _ _ => le_rfl) ?_ ?_ ?_ ?_ ?_
  · intro α hα β hβ
    exact mix_nonneg (hmem α hα).1 (hmem α hα).2 (hrSA α hα β hβ) (hrSB α hα β hβ)
  · intro α hα
    have := mix_le_const (hmem α hα).1 (hmem α hα).2 (hBdPA α hα) (hBdPB α hα)
    simp only [CapEnd.toS, chord]; nlinarith [this]
  · intro α hα β hβ
    have := mix_le_const (hmem α hα).1 (hmem α hα).2 (hBdSA α hα β hβ) (hBdSB α hα β hβ)
    simp only [CapEnd.toS, chord]; nlinarith [this]
  · intro α hα
    exact hRP α hα
  · intro α hα β hβ
    exact mix_le_const (hmem α hα).1 (hmem α hα).2 (hRSA α hα β hβ) (hRSB α hα β hβ)
  · intro ε hε
    filter_upwards [h.regA, h.regB, hnegA ε hε, hnegB ε hε] with N rA rB a b α hα x hx hxg
    obtain ⟨hl0, hl1⟩ := hmem α hα
    show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (constant N α)).fNegM (Rm N) x ≤
      chord αA αB E.lamNA E.lamNB α + ε
    rw [fNegM_interp hl0 hl1 (h.compat N) rA rB (Rm N) (abs_le_one_of_Ioo le_rfl (by norm_num) hx)]
    exact mix_le hl0 hl1 (a α hα x hx hxg) (b α hα x hx hxg)
  · intro ε hε
    filter_upwards [h.regA, h.regB, hposA ε hε, hposB ε hε] with N rA rB a b α hα x hx hg hc
    obtain ⟨hl0, hl1⟩ := hmem α hα
    show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (constant N α)).fPosMR (Rm N) rc α x ≤
      chord αA αB (E.lamPA α) (E.lamPB α) α + ε
    rw [fPosMR_interp hl0 hl1 (h.compat N) rA rB (Rm N) rc α
      (abs_le_one_of_Ioo (by norm_num) le_rfl hx)]
    exact mix_le hl0 hl1 (a α hα x hx hg hc) (b α hα x hx hg hc)
  · intro ε hε
    filter_upwards [h.regA, h.regB, hposTopA ε hε, hposTopB ε hε] with N rA rB a b α hα x hx hc
    obtain ⟨hl0, hl1⟩ := hmem α hα
    show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (constant N α)).fPosMS (Rm N) x ≤
      chord αA αB (E.gPA α) (E.gPB α) α + ε
    rw [fPosMS_interp hl0 hl1 (h.compat N) rA rB (Rm N)
      (abs_le_one_of_Ioo (by norm_num) le_rfl hx)]
    exact mix_le hl0 hl1 (a α hα x hx hc) (b α hα x hx hc)
  · intro ε hε
    filter_upwards [h.regA, h.regB, hnearA ε hε, hnearB ε hε]
      with N rA rB a b α hα β hβ x hx hg hc
    obtain ⟨hl0, hl1⟩ := hmem α hα
    show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (constant N α)).fNearMS (Rn N) α β x ≤
      chord αA αB (E.lamSA α β) (E.lamSB α β) α + ε
    rw [fNearMS_interp hl0 hl1 (h.compat N) rA rB (Rn N) α β
      (abs_le_one_of_Ioo (by norm_num) le_rfl hx)]
    exact mix_le hl0 hl1 (a α hα β hβ x hx hg hc) (b α hα β hβ x hx hg hc)
  · intro ε hε
    filter_upwards [h.regA, h.regB, hnearTopA ε hε, hnearTopB ε hε]
      with N rA rB a b α hα β hβ x hx hc
    obtain ⟨hl0, hl1⟩ := hmem α hα
    show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (constant N α)).fNearMS (Rn N) α β x ≤
      chord αA αB (E.gSA α β) (E.gSB α β) α + ε +
        chord αA αB (E.rSA α β) (E.rSB α β) α * (-Real.log (1 - x ^ 2))
    rw [fNearMS_interp hl0 hl1 (h.compat N) rA rB (Rn N) α β
      (abs_le_one_of_Ioo (by norm_num) le_rfl hx)]
    have e1 := mul_le_mul_of_nonneg_left (a α hα β hβ x hx hc) (sub_nonneg.2 hl1)
    have e2 := mul_le_mul_of_nonneg_left (b α hα β hβ x hx hc) hl0
    simp only [chord]
    nlinarith [e1, e2]

/-! ### 4. The complete Phase 2 data and the contract -/

/-- **Everything a Phase 2 data module supplies** for `I` α-intervals (see `NOTES-PC.md`). -/
structure Phase2Data (I : ℕ) where
  -- scale, partition, problem data
  ncount : ℕ → ℕ
  ncount_pos : ∀ N, 0 < N → 0 < ncount N
  B : ℝ
  cost : ℝ
  α1 : ℝ
  α1_nonneg : 0 ≤ α1
  lo : Fin I → ℝ
  hi : Fin I → ℝ
  cover : ∀ α : ℝ, 0 ≤ α → α ≤ α1 → ∃ i, lo i ≤ α ∧ α ≤ hi i
  Rf : ℕ → ℝ → ℝ
  Cf : ℕ → ℝ → ℝ
  Rm : ℕ → ℝ → ℝ
  Rn : ℕ → ℝ → ℝ
  constant : ℕ → ℝ → ℝ
  -- endpoint trials
  αA : Fin I → ℝ
  αB : Fin I → ℝ
  DA : Fin I → ℕ → SignedData
  DB : Fin I → ℕ → SignedData
  hends : ∀ i, IntervalEnds (αA i) (αB i) (lo i) (hi i) (DA i) (DB i)
  hν : ∀ i N, (DA i N).ν = (ncount N : ℝ)
  hRf : ∀ i N, (DA i N).Rf = Rf N
  hCf : ∀ i N, (DA i N).Cf = Cf N
  mA : ∀ i, ∀ᶠ N : ℕ in atTop, 1 - αA i / 2 = (DA i N).μ.mass
  mB : ∀ i, ∀ᶠ N : ℕ in atTop, 1 - αB i / 2 = (DB i N).μ.mass
  -- endpoint suprema of the free-row, column fields
  SnA : Fin I → ℝ
  SnB : Fin I → ℝ
  SpA : Fin I → ℝ
  SpB : Fin I → ℝ
  SyA : Fin I → ℝ
  SyB : Fin I → ℝ
  hSnA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0,
    (DA i N).fNeg x ≤ SnA i + ε
  hSnB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0,
    (DB i N).fNeg x ≤ SnB i + ε
  hSpA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
    (DA i N).fPosS x ≤ SpA i + ε
  hSpB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
    (DB i N).fPosS x ≤ SpB i + ε
  hSyA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
    (DA i N).fCol s ≤ SyA i + ε
  hSyB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
    (DB i N).fCol s ≤ SyB i + ε
  -- endpoint constants and curvature
  cP : Fin I → ℝ → ℝ
  rA : Fin I → ℝ
  rB : Fin I → ℝ
  κc : Fin I → ℝ
  hP : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    constant N α ≤ cP i α + ε
  hrA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (DA i N).constTotal (ncount N) - (DA i N).constant ≤ rA i + ε
  hrB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (DB i N).constTotal (ncount N) - (DB i N).constant ≤ rB i + ε
  hκ : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    κc i - ε ≤ curvQ (DA i N) (DB i N) (ncount N)
  -- the rest of the contract
  κlo : Fin I → ℝ
  κhi : Fin I → ℝ
  epsSplit : Fin I → ℝ
  epsSplit_pos : ∀ i, 0 < epsSplit i
  epsSplit_le : ∀ i, epsSplit i ≤ 1
  etaA : ∀ i N, (DA i N).η = (1 - epsSplit i) / 2
  Clsf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop
  LRf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ
  cp : Fin I → ℕ → ℝ → ℝ
  cp_pos : ∀ i N α, 0 < cp i N α
  cp_le : ∀ i N α, cp i N α ≤ 1
  err_small : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ((DA i N).withCount (ncount N)).errJ3 (cp i N α) (ncount N) ≤ ε
  -- the spike data (Theorem SE): margin below theta, LRf is the log-ratio at the configuration's
  -- Heine count `q + m₂ - g`, and the class gives the count condition and a witness pair at the
  -- two endpoint trials at that count (same configuration, same margin cp i N alpha)
  cp_theta : ∀ i N α, cp i N α ≤ (DA i N).θ
  hLR : ∀ i N k q m1 m2 xn gp yn yp, LRf N k q m1 m2 xn gp yn yp =
    logRatioZ (q + m2 - (DA i N).g) (Fin.append xn yn) (Fin.append gp yp)
  hCls : ∀ i, ∀ᶠ N : ℕ in atTop, ∀ α k q m1 m2 xn gp yn yp, Clsf N k q m1 m2 xn gp yn yp →
    (0 < (DA i N).sp ∧ (DA i N).sp + (DA i N).g ≤ q + m2) ∧
    Nonempty (PairCls ((DA i N).withCount (q + m2 - (DA i N).g))
      ((DB i N).withCount (q + m2 - (DA i N).g)) (cp i N α) xn gp yn yp)
  -- the σ cap (Theorem S): endpoint data and side conditions
  capE : Fin I → CapEnd
  hxc0 : ∀ i, 0 ≤ (capE i).xc
  hxc1 : ∀ i, (capE i).xc < 1
  hC1 : ∀ i, 0 < (capE i).C1
  hlo0 : ∀ i, 0 ≤ lo i
  hhi1 : ∀ i, hi i ≤ 1
  hrP : ∀ i, ∀ α ∈ Icc (lo i) (hi i), remC (epsSplit i) * α ≤ (capE i).rP α
  hrSA : ∀ i, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc 0 α, 0 ≤ (capE i).rSA α β
  hrSB : ∀ i, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc 0 α, 0 ≤ (capE i).rSB α β
  umin : ℕ → ℝ
  hum0 : ∀ N, 0 < umin N
  hum1 : ∀ N, umin N ≤ 1
  Bd : Fin I → ℝ
  Rbd : Fin I → ℝ
  hBdPA : ∀ i, ∀ α ∈ Icc (lo i) (hi i), (capE i).gPA α - (capE i).lamPA α ≤ Bd i
  hBdPB : ∀ i, ∀ α ∈ Icc (lo i) (hi i), (capE i).gPB α - (capE i).lamPB α ≤ Bd i
  hBdSA : ∀ i, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc 0 α,
    (capE i).gSA α β - (capE i).lamSA α β ≤ Bd i
  hBdSB : ∀ i, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc 0 α,
    (capE i).gSB α β - (capE i).lamSB α β ≤ Bd i
  hRP : ∀ i, ∀ α ∈ Icc (lo i) (hi i), (capE i).rP α ≤ Rbd i
  hRSA : ∀ i, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc 0 α, (capE i).rSA α β ≤ Rbd i
  hRSB : ∀ i, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc 0 α, (capE i).rSB α β ≤ Rbd i
  hn_top : Tendsto (fun N => (ncount N : ℝ)) atTop atTop
  hlogu : Tendsto (fun N => -Real.log (umin N) / (ncount N : ℝ)) atTop (nhds 0)
  -- the common (geometric) cap parameters of the admissibility predicate `FixAdmCap gs xc C1 n umin`
  gs : ℝ
  xc : ℝ
  C1 : ℝ
  hgs : ∀ i, (capE i).gs ≤ gs
  hxc : ∀ i, xc ≤ (capE i).xc
  hC1le : ∀ i, C1 ≤ (capE i).C1
  -- endpoint bounds of the fixed-row fields
  hnegA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(capE i).gs → (DA i N).fNegM (Rm N) x ≤ (capE i).lamNA + ε
  hnegB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(capE i).gs → (DB i N).fNegM (Rm N) x ≤ (capE i).lamNB + ε
  hposA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DA i N).fPosMR (Rm N) (remC (epsSplit i)) α x ≤ (capE i).lamPA α + ε
  hposB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DB i N).fPosMR (Rm N) (remC (epsSplit i)) α x ≤ (capE i).lamPB α + ε
  hposTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x → (DA i N).fPosMS (Rm N) x ≤ (capE i).gPA α + ε
  hposTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x → (DB i N).fPosMS (Rm N) x ≤ (capE i).gPB α + ε
  hnearA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DA i N).fNearMS (Rn N) α β x ≤ (capE i).lamSA α β + ε
  hnearB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DB i N).fNearMS (Rn N) α β x ≤ (capE i).lamSB α β + ε
  hnearTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (DA i N).fNearMS (Rn N) α β x ≤
        (capE i).gSA α β + ε + (capE i).rSA α β * (-Real.log (1 - x ^ 2))
  hnearTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (DB i N).fNearMS (Rn N) α β x ≤
        (capE i).gSB α β + ε + (capE i).rSB α β * (-Real.log (1 - x ^ 2))
  -- the budget: the dual chord zb dominates zbCap, and the budget at κlo, κhi
  zb : Fin I → ℝ → ℝ
  hZB : ∀ (i : Fin I) (c d e : ℝ), 0 ≤ c → 0 ≤ d → 0 ≤ e → lo i ≤ c + d + e →
    c + d + e ≤ hi i → zbCap ((capE i).toS (αA i) (αB i)) c d e ≤ zb i (c + d + e)
  hbudLo : ∀ i, ∀ α ∈ Icc (lo i) (hi i),
    interpCInf (αA i) (αB i) (cP i α) (rA i) (rB i) (κc i) α +
      fixLog2 (epsSplit i) α * Real.log 2 +
      κlo i * chord (αA i) (αB i) (SnA i) (SnB i) α +
      (1 - κlo i - α) * chord (αA i) (αB i) (SpA i) (SpB i) α +
      (1 - α) * chord (αA i) (αB i) (SyA i) (SyB i) α + zb i α ≤ B + cost * α
  hbudHi : ∀ i, ∀ α ∈ Icc (lo i) (hi i),
    interpCInf (αA i) (αB i) (cP i α) (rA i) (rB i) (κc i) α +
      fixLog2 (epsSplit i) α * Real.log 2 +
      κhi i * chord (αA i) (αB i) (SnA i) (SnB i) α +
      (1 - κhi i - α) * chord (αA i) (αB i) (SpA i) (SpB i) α +
      (1 - α) * chord (αA i) (αB i) (SyA i) (SyB i) α + zb i α ≤ B + cost * α

theorem remC_nonneg {ε : ℝ} (h : 0 < ε) : 0 ≤ remC ε := by
  unfold remC; positivity

/-- `FixAdmCap` is monotone in the geometry: a larger node threshold, a smaller top-cell start and
a smaller cap density give a stronger predicate. -/
theorem FixAdmCap_mono {gs gs' xc xc' C1 C1' n umin : ℝ} {m1 m2 s : ℕ} {yn : Fin m1 → ℝ}
    {yp : Fin m2 → ℝ} {zp : Fin s → ℝ} (hgs : gs' ≤ gs) (hxc : xc ≤ xc') (hC : C1 ≤ C1')
    (hn : 0 ≤ n) (hu : 0 ≤ umin) (h : FixAdmCap gs xc C1 n umin yn yp zp) :
    FixAdmCap gs' xc' C1' n umin yn yp zp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have key : ∀ y : ℝ, y ≤ 1 - umin → C1 * n * (1 - y) + 1 ≤ C1' * n * (1 - y) + 1 := by
    intro y hy
    have : 0 ≤ n * (1 - y) := mul_nonneg hn (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hC this]
  refine ⟨fun j => (h1 j).trans (by linarith), fun j => hgs.trans (h2 j),
    fun j => hgs.trans (h3 j), h4, h5, fun j hj => (h6 j (hxc.trans hj)).trans (key _ (h4 j)),
    fun j hj => (h7 j (hxc.trans hj)).trans (key _ (h5 j))⟩

/-- The single admissibility predicate of the Phase 2 contract (common geometry). -/
def Phase2Data.FixAdm {I : ℕ} (D : Phase2Data I) (N m1 m2 s : ℕ) (yn : Fin m1 → ℝ)
    (yp : Fin m2 → ℝ) (zp : Fin s → ℝ) : Prop :=
  FixAdmCap D.gs D.xc D.C1 (D.ncount N : ℝ) (D.umin N) yn yp zp

/-- It implies the cap predicate of every interval. -/
theorem Phase2Data.hFix {I : ℕ} (D : Phase2Data I) (i : Fin I) :
    ∀ N m1 m2 s (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
      D.FixAdm N m1 m2 s yn yp zp →
        FixAdmCap (D.capE i).gs (D.capE i).xc (D.capE i).C1 (D.ncount N : ℝ) (D.umin N)
          yn yp zp :=
  fun N _ _ _ _ _ _ h => FixAdmCap_mono (D.hgs i) (D.hxc i) (D.hC1le i) (Nat.cast_nonneg _)
    (D.hum0 N).le h

/-! ### Admissibility of the actual marked nodes -/

/-! `MarkedCap` (the cap of the actual marked rows) is defined in `MarkedCap.lean`. -/

theorem count_sub_le {m a : ℕ} (y : Fin m → ℝ) (f : Fin a → Fin m) (hf : Function.Injective f)
    (j : Fin a) :
    (Finset.univ.filter (fun i => y (f j) ≤ y (f i))).card ≤
      (Finset.univ.filter (fun i => y (f j) ≤ y i)).card := by
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    simpa using hi
  · exact hf.injOn

/-- **`FixAdm` for every splitting** (the clause of `SignedNearClassLink`): from `MarkedCap` of the
marked rows `y`, the sign split `σy` and any splitting `τ` of the positives into first-kind and
near rows, the three lists satisfy `FixAdmCap`.  The top count of a sub-family is at most the
count of all marked rows. -/
theorem fixAdmCap_of_marked {gs xc C1 n umin : ℝ} (hxc : 0 ≤ xc) {m m1 m2 r s' : ℕ}
    {y : Fin m → ℝ} (hM : MarkedCap gs xc C1 n umin y) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m)
    (hyneg : ∀ b, y (σy (Sum.inl b)) < 0) (hypos : ∀ b, 0 < y (σy (Sum.inr b)))
    (τ : Fin r ⊕ Fin s' ≃ Fin m2) :
    FixAdmCap gs xc C1 n umin (fun b => y (σy (Sum.inl b)))
      (fun j => y (σy (Sum.inr (τ (Sum.inl j))))) (fun j => y (σy (Sum.inr (τ (Sum.inr j))))) := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => h2 _, fun j => h2 _, fun j hj => ?_,
    fun j hj => ?_⟩
  · have := h1 (σy (Sum.inl j)); rw [abs_of_neg (hyneg j)] at this; linarith
  · have := h1 (σy (Sum.inr (τ (Sum.inl j)))); rwa [abs_of_pos (hypos _)] at this
  · have := h1 (σy (Sum.inr (τ (Sum.inr j)))); rwa [abs_of_pos (hypos _)] at this
  · have hinj : Function.Injective
        (fun i : Fin r => σy (Sum.inr (τ (Sum.inl i)))) :=
      fun a b hab => Sum.inl_injective (τ.injective (Sum.inr_injective (σy.injective hab)))
    exact (Nat.cast_le.2 (count_sub_le y _ hinj j)).trans (h3 _ hj)
  · have hinj : Function.Injective
        (fun i : Fin s' => σy (Sum.inr (τ (Sum.inr i)))) :=
      fun a b hab => Sum.inr_injective (τ.injective (Sum.inr_injective (σy.injective hab)))
    exact (Nat.cast_le.2 (count_sub_le y _ hinj j)).trans (h3 _ hj)

/-- The complete contract `SignedNearBounds I` from the Phase 2 data. -/
def Phase2Data.toBounds {I : ℕ} (D : Phase2Data I) : SignedNearBounds I :=
  SignedNearBounds.ofEnds D.ncount D.ncount_pos D.B D.cost D.α1 D.α1_nonneg D.lo D.hi D.cover
    D.Rf D.Cf D.Rm D.Rn D.constant D.αA D.αB D.DA D.DB D.hends D.hν D.hRf D.hCf D.mA D.mB
    D.SnA D.SnB D.SpA D.SpB D.SyA D.SyB D.hSnA D.hSnB D.hSpA D.hSpB D.hSyA D.hSyB
    D.cP D.rA D.rB D.κc D.hP D.hrA D.hrB D.hκ D.κlo D.κhi D.epsSplit D.epsSplit_pos
    D.epsSplit_le D.etaA (fun i => zbCap ((D.capE i).toS (D.αA i) (D.αB i))) D.zb D.Clsf D.LRf D.FixAdm
    D.cp D.cp_pos D.cp_le D.err_small
    (spikeFix_of_ends D.αA D.αB D.DA D.DB D.constant D.cp D.cp_pos D.cp_le D.cp_theta
      (fun i N => ((D.hends i).compat N).sp) D.Clsf D.LRf D.hLR D.hCls)
    (fun i ε hε => fixedSum_ends (D.hends i) (D.capE i) D.constant (D.hxc0 i) (D.hxc1 i)
      (D.hC1 i) (remC_nonneg (D.epsSplit_pos i)) (D.hlo0 i) (D.hhi1 i) D.ncount_pos (D.hν i)
      (D.hrP i) (D.hrSA i) (D.hrSB i) D.umin D.hum0 D.hum1 (D.Bd i) (D.Rbd i)
      (D.hBdPA i) (D.hBdPB i) (D.hBdSA i) (D.hBdSB i) (D.hRP i) (D.hRSA i) (D.hRSB i)
      D.hn_top D.hlogu (D.hFix i) (D.hnegA i) (D.hnegB i) (D.hposA i) (D.hposB i)
      (D.hposTopA i) (D.hposTopB i) (D.hnearA i) (D.hnearB i) (D.hnearTopA i) (D.hnearTopB i)
      ε hε)
    D.hZB D.hbudLo D.hbudHi

/-- The budget's `ZB` and the `ZB` of the field `fixedSum` are the same function `zbCap`. -/
theorem Phase2Data.toBounds_ZB {I : ℕ} (D : Phase2Data I) (i : Fin I) :
    D.toBounds.ZB i = zbCap ((D.capE i).toS (D.αA i) (D.αB i)) := rfl

/-- Conformance of the produced `fixedSum` with `FixedSumAt`. -/
theorem Phase2Data.toBounds_fixedSum {I : ℕ} (D : Phase2Data I) (i : Fin I) :
    FixedSumAt D.toBounds.ncount (D.toBounds.D i) D.toBounds.Rm D.toBounds.Rn
      (remC (D.toBounds.epsSplit i)) (D.toBounds.lo i) (D.toBounds.hi i) (D.toBounds.ZB i)
      D.toBounds.FixAdm :=
  fixedSumAt_conform D.toBounds i

/-! ### 5. The end-to-end corollary -/

section Sheet

open CatalanMeasure.Parametric CatalanMeasure.GenD CatalanMeasure.GenD.Analytic

/-- **End-to-end.**  The signed second-case sheet bound (`SignedSecondSheetCore`) from the Phase 2
endpoint data `D`, the identification of the data with the sheet's problem data, the cost
`D.cost * n0 ≤ c2`, the non-class branch `hnon` (old energy route) and the class link `hlink`
(which delivers `Clsf` and `FixAdm` for every splitting).  Nothing else is needed. -/
theorem Phase2Data.signedSecondSheetNear {I : ℕ} (D : Phase2Data I) {P : Parameters}
    (hP : Admissible P) (G : ℝ → Prop) (target0 c2 : ℝ)
    (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop)
    (hn : ∀ N, D.ncount N = P.n N)
    (hconst : ∀ N r a b, r + a + b = P.n N →
      D.constant N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b)
    (hRf : ∀ N, D.Rf N = populationPhysicalFreeField P N)
    (hRm : ∀ N, D.Rm N = groupedMarkedField P N)
    (hRn : ∀ N, D.Rn N = groupedNearField P N)
    (hCf : ∀ N, D.Cf N = populationPhysicalColumnField P N (0 + 0))
    (hLRf : ∀ N k q m1 m2' xn gp yn yp', D.LRf N k q m1 m2' xn gp yn yp' =
      logRatioZ (q + m2' - P.g N) (Fin.append xn yn) (Fin.append gp yp'))
    (hB : D.B = -target0 + Real.log 2 / 2)
    (hcost : D.cost * (P.n0 : ℝ) ≤ c2)
    (hnon : GroupedMarkedProductCostOnRestr P target0 c2 G
      (fun N r _ _ z _ _ _ => ¬ Cls N r z))
    (hlink : SignedNearClassLink P D.toBounds Cls G) :
    SignedSecondSheetCore P G target0 c2 D.α1 :=
  _root_.CatalanMeasure.Signed.signedSecondSheetNear hP G target0 c2 Cls D.toBounds hn hconst hRf hRm hRn hCf hLRf hB hcost
    hnon hlink

/-- **The near-optimal class (the dichotomy of PROOF-A 17.9(a), Lemma 4), factor-free form.**  A
free configuration `z` is in the class when SOME marked selection `(x, y)` and column configuration
`s` violate the FACTOR-FREE old-route bound at `(target, cost)`: the grouped product exceeds
`(∏ (1 + s_i))^(a+b) · exp(n0² N² (-target + log 2/2) + cost N (a+b))`, with no `ε`.  The class is
measured against the factor-free product because the statement (`SignedSecondSheetCore`, S1,
PROOF-RHO §2.5) is about `markedSheetCore`, which has no factor `(∏ (1 + s))^m`; Lemma K
(`free_facts`) then compares it with the factor-free old route (`SecondTrialBoundsEnd`), and the
class excess is `(t0 - target) + (cost - c2/n0) α + δ`, constant in `α` at `c2 = n0 · cost`.  Off
the class the factor-free old route holds by definition (`hnon_nearOpt`, `hnonC_nearOpt`). -/
def nearOptCls (P : Parameters) (target cost : ℝ) (G : ℝ → Prop) :
    ∀ (N r : ℕ), (Fin r → ℝ) → Prop :=
  fun N r z => ∃ (a b : ℕ) (_ : r + a + b = P.n N) (x : Fin a → ℝ) (y : Fin b → ℝ)
    (s : Fin r → ℝ),
    (∀ i, z i ∈ Ioo (-1 : ℝ) 1) ∧ (∀ i, z i ≠ 0) ∧ (∀ i, x i ∈ Ioo (-1 : ℝ) 1) ∧
    (∀ i, G (x i)) ∧ (∀ i, y i ∈ Ioo (0 : ℝ) 1) ∧ (∀ i, s i ∈ Ioo (0 : ℝ) 1) ∧
    Function.Injective z ∧ Function.Injective (Fin.append z x) ∧ Function.Injective y ∧
    Function.Injective s ∧
    (∏ i, (1 + s i)) ^ (a + b) *
        Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2) + cost * N * (a + b)) <
      groupedProduct P N z x y s

/-- The non-class branch for the near-optimal class (factor-free grouped product): no hypothesis. -/
theorem hnon_nearOpt (P : Parameters) (target cost : ℝ) (G : ℝ → Prop) :
    GroupedFreeProductCostOnRestr P target cost G
      (fun N r _ _ z _ _ _ => ¬ nearOptCls P target cost G N r z) := by
  intro ε hε
  refine Filter.Eventually.of_forall fun N r a b hrab z x y s hz hz0 hx hxG hy hs hzi hzxi hyi hsi
    hQ => ?_
  by_contra h0
  have h := lt_of_not_ge h0
  apply hQ
  refine ⟨a, b, hrab, x, y, s, hz, hz0, hx, hxG, hy, hs, hzi, hzxi, hyi, hsi,
    lt_of_le_of_lt ?_ h⟩
  have hf : 0 ≤ (∏ i, (1 + s i)) ^ (a + b) :=
    pow_nonneg (Finset.prod_nonneg fun i _ => by linarith [(hs i).1]) _
  refine mul_le_mul_of_nonneg_left ?_ hf
  apply Real.exp_le_exp.mpr
  have h0 : 0 ≤ ((P.n0 : ℝ) * N) ^ 2 * ε := by positivity
  have e : ((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) =
      ((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2) + ((P.n0 : ℝ) * N) ^ 2 * ε := by ring
  rw [e]
  linarith

/-- The non-class branch at the level of the factor-free core (`hnonC` of
`signedSecondSheetNearNd_core`) for the near-optimal class. -/
theorem hnonC_nearOpt {P : Parameters} (hP : Admissible P) (target cost : ℝ) (G : ℝ → Prop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ (p m : ℕ) (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Set.Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Set.Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1 →
      ¬ nearOptCls P target cost G N p x →
      markedSheetCore P N hpm x y s ≤
        5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) + cost * N * m) := by
  intro ε hε
  filter_upwards [second_marked_sheet_free_on_restr hP target cost G _ (hnon_nearOpt P target cost G)
    hε] with N h p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hc
  exact h p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase (fun _ _ _ _ => hc)

/-- **Node-set form** (`Nd`, SheetNear `signedSecondSheetNearNd_core`) with the near-optimal class:
`hnon` discharged; what remains is the data `D`, the identification and the class link. -/
theorem Phase2Data.signedSecondSheetNearNd_nearOpt {I : ℕ} (D : Phase2Data I) {P : Parameters}
    (hP : Admissible P) (G : ℝ → Prop) (target0 c2 : ℝ)
    (hn : ∀ N, D.ncount N = P.n N)
    (hconst : ∀ N r a b, r + a + b = P.n N →
      D.constant N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b)
    (hRf : ∀ N, D.Rf N = populationPhysicalFreeField P N)
    (hRm : ∀ N, D.Rm N = groupedMarkedField P N)
    (hRn : ∀ N, D.Rn N = groupedNearField P N)
    (hCf : ∀ N, D.Cf N = populationPhysicalColumnField P N (0 + 0))
    (hLRf : ∀ N k q m1 m2' xn gp yn yp', D.LRf N k q m1 m2' xn gp yn yp' =
      logRatioZ (q + m2' - P.g N) (Fin.append xn yn) (Fin.append gp yp'))
    (hB : D.B = -target0 + Real.log 2 / 2)
    (hcost : D.cost * (P.n0 : ℝ) ≤ c2)
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop)
    (hlink : SignedNearClassLinkNd P D.toBounds (nearOptCls P target0 c2 G) G Nd) :
    SignedSecondSheetCoreNd P G Nd target0 c2 D.α1 :=
  _root_.CatalanMeasure.Signed.signedSecondSheetNearNd_core hP G target0 c2 _ D.toBounds hn
    hconst hRf hRm hRn hCf hLRf hB hcost (hnonC_nearOpt hP target0 c2 G) Nd hlink

/-- **End-to-end with the near-optimal class** (unrestricted marked rows). -/
theorem Phase2Data.signedSecondSheetNear_nearOpt {I : ℕ} (D : Phase2Data I) {P : Parameters}
    (hP : Admissible P) (G : ℝ → Prop) (target0 c2 : ℝ)
    (hn : ∀ N, D.ncount N = P.n N)
    (hconst : ∀ N r a b, r + a + b = P.n N →
      D.constant N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b)
    (hRf : ∀ N, D.Rf N = populationPhysicalFreeField P N)
    (hRm : ∀ N, D.Rm N = groupedMarkedField P N)
    (hRn : ∀ N, D.Rn N = groupedNearField P N)
    (hCf : ∀ N, D.Cf N = populationPhysicalColumnField P N (0 + 0))
    (hLRf : ∀ N k q m1 m2' xn gp yn yp', D.LRf N k q m1 m2' xn gp yn yp' =
      logRatioZ (q + m2' - P.g N) (Fin.append xn yn) (Fin.append gp yp'))
    (hB : D.B = -target0 + Real.log 2 / 2)
    (hcost : D.cost * (P.n0 : ℝ) ≤ c2)
    (hlink : SignedNearClassLink P D.toBounds (nearOptCls P target0 c2 G) G) :
    SignedSecondSheetCore P G target0 c2 D.α1 := by
  intro ε hε
  filter_upwards [D.signedSecondSheetNearNd_nearOpt hP G target0 c2 hn hconst hRf hRm hRn hCf
    hLRf hB hcost (fun _ _ _ => True) hlink ε hε] with N h p m hpm x y s hmle hx hx0 hy hy0 hyG
    hs hzi hsi hcase
  exact h p m hpm x y s hmle hx hx0 hy hy0 hyG trivial hs hzi hsi hcase

/-- **The `FixAdm` clause of `hlink` from the node set** (NOTES-MC wiring): for marked rows that
are node images (`NodeSub τ`) of a node set with `NodeCap` at the common cap data of `D`, every
sign split and every splitting satisfy `D.FixAdm`.  For the real nodes take
`τ := gapNodesD P (2g/(1+g²))` and `hZ := nodeCap_gap ..` (with `D.C1` the node constant
`J/(n · 2 xc √(1-a²))`, `D.umin N = √(1-a²)/(2(J+1))`). -/
theorem Phase2Data.fixAdm_of_nodeSub {I : ℕ} (D : Phase2Data I) {J : ℕ → ℕ}
    {τ : (N : ℕ) → Fin (J N) → ℝ} {N m m1 m2 r s' : ℕ} {y : Fin m → ℝ}
    (hxc : 0 ≤ D.xc)
    (hZ : NodeCap D.gs D.xc D.C1 (D.ncount N : ℝ) (D.umin N)
      (fun a => OAI.InternalCatalan.realCoordinate (τ N a)))
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hNd : NodeSub τ N m y) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m)
    (hyneg : ∀ b, y (σy (Sum.inl b)) < 0) (hypos : ∀ b, 0 < y (σy (Sum.inr b)))
    (τ' : Fin r ⊕ Fin s' ≃ Fin m2) :
    D.FixAdm N m1 r s' (fun b => y (σy (Sum.inl b)))
      (fun j => y (σy (Sum.inr (τ' (Sum.inl j))))) (fun j => y (σy (Sum.inr (τ' (Sum.inr j))))) :=
  fixAdmCap_of_marked hxc (markedCap_of_nodeSub hZ hy hNd) σy hyneg hypos τ'

end Sheet


/-! ### Spike witnesses from per-trial certificates (`spikeWitness_of_cert`)

`SpikeTrialCert D m ρ Kn Tn` is the per-trial, per-`m` data: finitely many real (in practice
rational) constants and inequalities that do not depend on the configuration.  `Kn` bounds the
number of negative rows, `Tn` the total number of rows plus one. -/

structure SpikeTrialCert (D : SignedData) (m : ℕ) (ρ Kn Tn : ℝ) where
  c1 : ℝ
  κ : ℝ
  L : ℝ
  De2 : ℝ
  Sg : ℝ
  A : ℝ
  K0 : ℝ
  A1 : ℝ
  B1 : ℝ
  BR : ℝ
  hθ : D.θ ∈ Ioc (0 : ℝ) (1 / 2)
  hc1 : 0 < c1
  hκ0 : 0 ≤ κ
  hκ1 : κ < 1
  hsp : 0 < D.sp
  hmκ : (m : ℝ) ≤ κ * D.sp
  hb : ∀ u ∈ Icc (-1 : ℝ) 1, c1 ≤ chebPs D.b u
  hpoly : ∀ u ∈ Icc (-1 : ℝ) 1,
    κ * (1 - ρ ^ 2) ≤ (chebPs D.b u - (1 - κ) * c1) * (1 + 2 * ρ * u + ρ ^ 2)
  hL0 : 0 ≤ L
  hL : Real.log (2 / (1 + realEnergyTau D.e ^ 2 * (1 - D.θ))) ≤ L
  hDe : ∀ y, 1 - D.θ ≤ y → y < 1 → barrierTrialS D.b (-y) - barrierTrialS D.b (-ρ) ≤ De2
  hSg : Real.log (1 - realEnergyTau D.e ^ 2 * (1 - D.θ) ^ 2) - Real.log (1 - ρ ^ 2) ≤ Sg
  hA : ∑' j : ℕ, |D.a j| ≤ A
  hK : costRem D.b (D.sp - m) m ρ ≤ K0
  hfin : 2 * (m : ℝ) * (Kn * L + 2 * (D.sp : ℝ) * De2 + m * Sg + 2 * D.ν * D.e * A) +
    (m : ℝ) * K0 ≤ D.ν * (((2 * m : ℕ) : ℝ) * D.cs)
  hkph : 0 ≤ D.kph
  hA1 : |barrierTrialS D.a (-D.τ * (1 - D.θ))| ≤ A1
  hB1 : |barrierTrialS D.b (-(1 - D.θ))| ≤ B1
  hBR : |∑' n : ℕ, D.R n * (D.τ * (1 - D.θ)) ^ (n + 1) / ((n : ℝ) + 1)| ≤ BR
  hph : 2 * D.ν * A1 + D.ν * BR + Tn * Real.log (1 / D.θ) + 2 * (D.sp : ℝ) * B1 + D.ν * D.cs ≤
    D.ν * D.kph

theorem SpikeTrialCert.m_lt {D : SignedData} {m : ℕ} {ρ Kn Tn : ℝ}
    (C : SpikeTrialCert D m ρ Kn Tn) : m < D.sp := by
  have h1 := C.hmκ
  have h2 : (0 : ℝ) < D.sp := by exact_mod_cast C.hsp
  have : (m : ℝ) < D.sp := by nlinarith [C.hκ1, C.hκ0]
  exact_mod_cast this

theorem SpikeTrialCert.cheb {D : SignedData} {m : ℕ} {ρ Kn Tn : ℝ} (hρ : |ρ| < 1)
    (C : SpikeTrialCert D m ρ Kn Tn) : SpikeChebOK D m ρ C.c1 :=
  spikeChebOK_of_cert hρ C.hκ0 C.hmκ C.m_lt.le C.hb C.hpoly

theorem SpikeTrialCert.costOK {D : SignedData} (E : SpikeEnv D) (rD : SignedRegular D) {m : ℕ}
    {ρ Kn Tn : ℝ} (C : SpikeTrialCert D m ρ Kn Tn) {K q' M : ℕ} (hM : M = 2 * m ∨ M + 1 = 2 * m)
    (xn : Fin K → ℝ) (y : Fin q' → ℝ) (z : Fin M → ℝ)
    (hx : ∀ b, |xn b| ≤ 1) (hy : ∀ j, |y j| ≤ 1) (hz : ∀ i, 1 - D.θ ≤ z i ∧ z i < 1)
    (hK : (K : ℝ) ≤ Kn) (hT : ((K + q' + M + 1 : ℕ) : ℝ) ≤ Tn) :
    SpikeCostOK D m xn y z (1 - D.θ) ρ := by
  have hm : m ≤ D.sp := C.m_lt.le
  have hcast : ((D.sp - m : ℕ) : ℝ) + m = D.sp := by
    rw [Nat.cast_sub hm]; ring
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hν := E.hν
  have hkL : (K : ℝ) * C.L ≤ Kn * C.L := mul_le_mul_of_nonneg_right hK C.hL0
  have hbound : ∀ w : Fin (2 * m) → ℝ, (∀ p, 1 - D.θ ≤ w p ∧ w p < 1) →
      spikeCost D.ν D.e D.a D.b (D.sp - m) m ρ (1 - D.θ) K w ≤
        D.ν * (((2 * m : ℕ) : ℝ) * D.cs) := by
    intro w hw
    have h := spikeCost_le_of_bounds hν.le E.he.1.le D.a D.b (D.sp - m) m K w C.hL
      (fun p => C.hDe _ (hw p).1 (hw p).2) C.hSg C.hA C.hK
    rw [hcast] at h
    have : 2 * (m : ℝ) * ((K : ℝ) * C.L) ≤ 2 * m * (Kn * C.L) :=
      mul_le_mul_of_nonneg_left hkL (by positivity)
    nlinarith [C.hfin, h, this]
  rcases hM with hM | hM
  · subst hM
    apply SpikeCostOK.of_even
    have := hbound z hz
    nlinarith [mul_nonneg hν.le C.hkph]
  · have hz' : ∀ i, |z i| ≤ 1 := fun i =>
      abs_le.mpr ⟨by linarith [(hz i).1, C.hθ.2], (hz i).2.le⟩
    refine SpikeCostOK.of_odd_cert D hν rD hM xn y z hx hy hz' C.hθ ρ C.hA1 C.hB1 C.hBR
      (hbound _ (extFam_mem z (1 - D.θ) (1 - D.θ) hz ⟨le_refl _, by linarith [C.hθ.1]⟩)) ?_
    have hlog : 0 ≤ Real.log (1 / D.θ) := Real.log_nonneg (by
      rw [le_div_iff₀ C.hθ.1]; linarith [C.hθ.2])
    have := mul_le_mul_of_nonneg_right hT hlog
    linarith [C.hph]

/-- The endpoint data at a Heine count (NOTES-ETA §5.1). -/
theorem InterpCompat.withCount {DA DB : SignedData} (hc : InterpCompat DA DB) (x : ℕ) :
    InterpCompat (DA.withCount x) (DB.withCount x) :=
  ⟨hc.ν, hc.e, rfl, hc.g, hc.K, hc.Rf, hc.Cf, hc.θ, hc.kph, hc.η⟩

theorem SignedRegular.withCount {D : SignedData} (h : SignedRegular D) (x : ℕ) :
    SignedRegular (D.withCount x) :=
  ⟨h.he, h.hv, h.ha, h.hR, h.ht, h.hμ, h.hC, h.hp, h.hη0⟩

def SpikeEnv.withCount {D : SignedData} (E : SpikeEnv D) {x : ℕ} (hx : (x : ℝ) ≤ D.ν) :
    SpikeEnv (D.withCount x) where
  hν := E.hν
  he := E.he
  hsp := hx
  hθ := E.hθ
  ha := E.ha
  hr := E.hr
  hra := E.hra
  Qref := E.Qref
  hQ := E.hQ
  hℓ := E.hℓ
  hbK := fun i hi => by
    show ((D.sp : ℝ) / x) * D.b i = 0
    rw [E.hbK i hi, mul_zero]

/-- The denominator trial at count `x`: `chebPs b_x = 1 + (sp/x)(chebPs b - 1)` (the conditions
`hb`, `hpoly` of a certificate at count `x` are affine in `sp/x`). -/
theorem chebPs_withCount (D : SignedData) (x : ℕ) (u : ℝ) :
    chebPs (D.withCount x).b u = 1 + ((D.sp : ℝ) / x) * (chebPs D.b u - 1) := by
  unfold chebPs
  simp only [SignedData.withCount_b]
  rw [show (fun k : ℕ => (D.sp : ℝ) / x * D.b (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u) =
      fun k : ℕ => (D.sp : ℝ) / x * (D.b (k + 1) *
        (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u) from funext fun k => by ring,
    tsum_mul_left]
  ring

/-- **The witness pair from the certificates** (the `hCls` of the contract).  For a configuration
whose free and marked rows are in range, whose counts are bounded (`Kn`, `Tn`) and whose spike count is at most `Mmax` (Lemma K,
`free_spike_count`), the per-trial certificates of both endpoints for every `m` with
`2m ≤ Mmax + 1` (one pole `ρ` per `m`, i.e. per q-interval) give a `PairCls`. -/
theorem pairCls_of_cert {DA DB : SignedData} (hc : InterpCompat DA DB) (rA : SignedRegular DA)
    (rB : SignedRegular DB) (EA : SpikeEnv DA) (EB : SpikeEnv DB) {c' Kn Tn : ℝ}
    {k q m1 m2 : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ)
    (yp : Fin m2 → ℝ) (hX : ∀ b, Fin.append xn yn b ∈ Ioo (-1 : ℝ) 0)
    (hG : ∀ p, Fin.append gp yp p ∈ Ioo (0 : ℝ) 1)
    (hK : (((k + m1 : ℕ)) : ℝ) ≤ Kn) (hT : ((k + m1 + (q + m2) + 1 : ℕ) : ℝ) ≤ Tn) {Mmax : ℕ}
    (hMc : (Finset.univ.filter (fun p => 1 - DA.θ < Fin.append gp yp p)).card ≤ Mmax)
    (hcert : ∀ m : ℕ, 2 * m ≤ Mmax + 1 → ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ DA.τ ^ 2 * (1 - DA.θ) ∧
      Nonempty (SpikeTrialCert DA m ρ Kn Tn) ∧ Nonempty (SpikeTrialCert DB m ρ Kn Tn)) :
    Nonempty (PairCls DA DB c' xn gp yn yp) := by
  classical
  set G := Fin.append gp yp with hGdef
  set X := Fin.append xn yn with hXdef
  set S := Finset.univ.filter (fun p => 1 - DA.θ < G p) with hS
  obtain ⟨q', M, τ', hnot, hin⟩ := exists_split_finset S
  set y : Fin q' → ℝ := fun j => G (τ' (Sum.inl j)) with hy
  set z : Fin M → ℝ := fun j => G (τ' (Sum.inr j)) with hz
  have hMS : M ≤ S.card := by
    have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin M))) (t := S)
      (fun j => τ' (Sum.inr j)) (fun j _ => hin j)
      (fun a _ b _ hab => Sum.inr_injective (τ'.injective hab))
    simpa using this
  obtain ⟨m, hM⟩ : ∃ m : ℕ, M = 2 * m ∨ M + 1 = 2 * m :=
    ⟨(M + 1) / 2, by omega⟩
  have h2m : 2 * m ≤ Mmax + 1 := by omega
  obtain ⟨ρ, hρ, hρd, ⟨CA⟩, ⟨CB⟩⟩ := hcert m h2m
  have hθB : DB.θ = DA.θ := hc.θ
  have hX1 : ∀ b, |X b| ≤ 1 := fun b => abs_le.mpr ⟨(hX b).1.le, by linarith [(hX b).2]⟩
  have hG1 : ∀ p, |G p| ≤ 1 := fun p => abs_le.mpr ⟨by linarith [(hG p).1], (hG p).2.le⟩
  have hy1 : ∀ j, |y j| ≤ 1 := fun j => hG1 _
  have hzA : ∀ i, 1 - DA.θ ≤ z i ∧ z i < 1 := fun i =>
    ⟨(Finset.mem_filter.mp (hin i)).2.le, (hG _).2⟩
  have hzB : ∀ i, 1 - DB.θ ≤ z i ∧ z i < 1 := by rw [hθB]; exact hzA
  have hσ : ∀ i, G ((finSumFinEquiv.symm.trans τ') i) = Fin.append y z i := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [hy]
    · simp [hz]
  have hcnt : ((k + m1 + q' + M + 1 : ℕ) : ℝ) ≤ Tn := by
    have hqM : q' + M = q + m2 := by simpa using Fintype.card_congr τ'
    have : k + m1 + q' + M + 1 = k + m1 + (q + m2) + 1 := by omega
    rw [this]; exact hT
  have hcostA := CA.costOK EA rA hM X y z hX1 hy1 hzA hK hcnt
  have hcostB := CB.costOK EB rB hM X y z hX1 hy1 hzB hK hcnt
  rw [hθB] at hcostB
  have hyns : ∀ j, y j ≤ 1 - DA.θ := fun j => by
    by_contra h
    exact hnot j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩)
  have SP : SpikePair DA DB c' X G :=
    { q' := q'
      M := M
      m := m
      y := y
      z := z
      zph := 1 - DA.θ
      σ := finSumFinEquiv.symm.trans τ'
      hσ := hσ
      hM := hM
      hm := CA.m_lt
      hy_not_spike := hyns
      hz_spike := fun i => (Finset.mem_filter.mp (hin i)).2
      hzph := ⟨le_refl _, by linarith [CA.hθ.1]⟩
      ρ := ρ
      c1A := CA.c1
      c1B := CB.c1
      hρ := hρ
      hρd := hρd
      hc1A := CA.hc1
      hc1B := CB.hc1
      hPA := CA.cheb hρ
      hPB := CB.cheb hρ
      hcostA := hcostA
      hcostB := hcostB }
  exact ⟨⟨hc, rA, rB, EA, EB, SP⟩⟩


/-- **`hCls` of `Phase2Data` from the certificates.**  If the class `Clsf` carries the ranges, the
row counts (`Kn N`, `Tn N`), the spike count `≤ Mmax N` (free spikes: `free_spike_count`;
marked spikes: the node top count of `MarkedCap`) and the count condition `0 < sp`,
`sp + g ≤ q + m₂ ≤ ν`, and every endpoint trial has its certificate at every Heine count
`x ∈ [sp, ν]` for every `m` with `2m ≤ Mmax N + 1`, then the `hCls` field holds.  Everything
is required, and concluded, only for all large `N` (`∀ᶠ N`): the only consumer,
`signed_second_energy_near_nodes`, concludes `∀ᶠ N`, and at `N = 0` (`ν = sp = 0`) no spike
environment or certificate exists. -/
theorem hCls_of_cert {I : ℕ} {DA DB : Fin I → ℕ → SignedData} (cp : Fin I → ℕ → ℝ → ℝ)
    (hc : ∀ i, ∀ᶠ N : ℕ in atTop, InterpCompat (DA i N) (DB i N))
    (rA : ∀ i, ∀ᶠ N : ℕ in atTop, SignedRegular (DA i N))
    (rB : ∀ i, ∀ᶠ N : ℕ in atTop, SignedRegular (DB i N))
    (EA : ∀ i, ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (DA i N)))
    (EB : ∀ i, ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (DB i N)))
    (Clsf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop)
    (Kn Tn : ℕ → ℝ) (Mmax : ℕ → ℕ)
    (hClsf : ∀ N k q m1 m2 xn gp yn yp, Clsf N k q m1 m2 xn gp yn yp →
      (∀ b, Fin.append xn yn b ∈ Ioo (-1 : ℝ) 0) ∧ (∀ p, Fin.append gp yp p ∈ Ioo (0 : ℝ) 1) ∧
      (((k + m1 : ℕ)) : ℝ) ≤ Kn N ∧ ((k + m1 + (q + m2) + 1 : ℕ) : ℝ) ≤ Tn N ∧
      (∀ i, (Finset.univ.filter (fun p => 1 - (DA i N).θ < Fin.append gp yp p)).card ≤ Mmax N) ∧
      ∀ i, 0 < (DA i N).sp ∧ (DA i N).sp + (DA i N).g ≤ q + m2 ∧
        ((q + m2 : ℕ) : ℝ) ≤ (DA i N).ν)
    (hcert : ∀ i, ∀ᶠ N : ℕ in atTop, ∀ (x m : ℕ), (DA i N).sp ≤ x → (x : ℝ) ≤ (DA i N).ν →
      2 * m ≤ Mmax N + 1 →
      ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ (DA i N).τ ^ 2 * (1 - (DA i N).θ) ∧
      Nonempty (SpikeTrialCert ((DA i N).withCount x) m ρ (Kn N) (Tn N)) ∧
      Nonempty (SpikeTrialCert ((DB i N).withCount x) m ρ (Kn N) (Tn N))) :
    ∀ i, ∀ᶠ N : ℕ in atTop, ∀ α k q m1 m2 xn gp yn yp, Clsf N k q m1 m2 xn gp yn yp →
      (0 < (DA i N).sp ∧ (DA i N).sp + (DA i N).g ≤ q + m2) ∧
      Nonempty (PairCls ((DA i N).withCount (q + m2 - (DA i N).g))
        ((DB i N).withCount (q + m2 - (DA i N).g)) (cp i N α) xn gp yn yp) := by
  intro i
  filter_upwards [hc i, rA i, rB i, EA i, EB i, hcert i] with N hcN rAN rBN hEA hEB hcertN
  intro α k q m1 m2 xn gp yn yp h
  obtain ⟨EAN⟩ := hEA
  obtain ⟨EBN⟩ := hEB
  obtain ⟨hX, hG, hK, hT, hM, hcnt⟩ := hClsf N k q m1 m2 xn gp yn yp h
  obtain ⟨h0, hle, hqν⟩ := hcnt i
  refine ⟨⟨h0, hle⟩, ?_⟩
  set x := q + m2 - (DA i N).g with hx
  have hxν : (x : ℝ) ≤ (DA i N).ν :=
    (Nat.cast_le.mpr (show x ≤ q + m2 by omega)).trans hqν
  have hxνB : (x : ℝ) ≤ (DB i N).ν := by rw [hcN.ν]; exact hxν
  exact pairCls_of_cert (hcN.withCount x) (rAN.withCount x) (rBN.withCount x)
    (EAN.withCount hxν) (EBN.withCount hxνB) xn gp yn yp hX hG hK hT
    (hM i) (fun m hm => hcertN x m (by omega) hxν hm)

/-! ### 6. The class link `hlink` for `nearOptCls`: counting, free facts, statistics

Everything here is about the free rows `z` of a configuration in `nearOptCls` (the old-route
violation) and the marked rows `y`.  The factor-free old (532) trial `D0 : SecondTrialBoundsEnd P 0` is the reference:
near-optimality gives the field bracket and the cosine square of the free rows at most
`excess ..` (`free_facts`), hence counts of free rows in any region where the free field is below
its cap (`card_region_le`) and one-sided linear statistics (`stat_poly_ge`).  -/

section HL

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

theorem card_filter_append {a b : ℕ} (u : Fin a → ℝ) (v : Fin b → ℝ) (P : ℝ → Prop)
    [DecidablePred P] :
    (Finset.univ.filter (fun i => P (Fin.append u v i))).card =
      (Finset.univ.filter (fun i => P (u i))).card +
        (Finset.univ.filter (fun i => P (v i))).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- **Top count of the marked rows** (`MarkedCap`, `nodeCap_gap`): the rows above `1 - θ` number at
most `C1 n θ + 1`, from the cap `#{i : y_j ≤ y_i} ≤ C1 n (1 - y_j) + 1` at the lowest such row. -/
theorem top_count_le {m : ℕ} (y : Fin m → ℝ) {xc C1 n θ : ℝ}
    (h : ∀ j, xc ≤ y j →
      ((Finset.univ.filter (fun i => y j ≤ y i)).card : ℝ) ≤ C1 * n * (1 - y j) + 1)
    (hxc : xc ≤ 1 - θ) (hθ : 0 ≤ θ) (hC : 0 ≤ C1) (hn : 0 ≤ n) :
    ((Finset.univ.filter (fun i => 1 - θ < y i)).card : ℝ) ≤ C1 * n * θ + 1 := by
  classical
  set S := Finset.univ.filter (fun i => 1 - θ < y i) with hS
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    nlinarith [mul_nonneg (mul_nonneg hC hn) hθ]
  · obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image S y hne
    have hj0' : 1 - θ < y j0 := (Finset.mem_filter.1 hj0).2
    have hsub : S ⊆ Finset.univ.filter (fun i => y j0 ≤ y i) := fun i hi =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hmin i hi⟩
    have h1 := h j0 (by linarith)
    have h2 : (S.card : ℝ) ≤ ((Finset.univ.filter (fun i => y j0 ≤ y i)).card : ℝ) :=
      Nat.cast_le.2 (Finset.card_le_card hsub)
    have h3 : C1 * n * (1 - y j0) ≤ C1 * n * θ :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC hn)
    linarith

/-- The spike count of the positives `Fin.append gp yp` of a sign/first-kind split is at most the
spike count of the free rows plus that of the marked rows. -/
theorem spike_count_split {p m k q m1 m2 r s' : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ)
    (σx : Fin k ⊕ Fin q ≃ Fin p) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m) (τ : Fin r ⊕ Fin s' ≃ Fin m2)
    (θ : ℝ) :
    (Finset.univ.filter (fun i => 1 - θ <
      Fin.append (fun b => x (σx (Sum.inr b)))
        (Fin.append (fun j => y (σy (Sum.inr (τ (Sum.inl j)))))
          (fun j => y (σy (Sum.inr (τ (Sum.inr j)))))) i)).card ≤
      (Finset.univ.filter (fun i => 1 - θ < x i)).card +
        (Finset.univ.filter (fun i => 1 - θ < y i)).card := by
  classical
  rw [card_filter_append (fun b => x (σx (Sum.inr b))) _ (fun v => 1 - θ < v)]
  have hyp : Fin.append (fun j => y (σy (Sum.inr (τ (Sum.inl j)))))
      (fun j => y (σy (Sum.inr (τ (Sum.inr j))))) =
      fun i => y (σy (Sum.inr (splitEquiv τ i))) :=
    append_split_eq τ (fun j => y (σy (Sum.inr j)))
  rw [hyp]
  apply add_le_add
  · apply Finset.card_le_card_of_injOn (fun b => σx (Sum.inr b))
    · intro b hb; simpa using hb
    · intro a _ b _ hab; exact Sum.inr_injective (σx.injective hab)
  · apply Finset.card_le_card_of_injOn (fun i => σy (Sum.inr (splitEquiv τ i)))
    · intro b hb; simpa using hb
    · intro a _ b _ hab
      exact (splitEquiv τ).injective (Sum.inr_injective (σy.injective hab))

/-- A sum over the nodes of a sign split, bounded sign by sign. -/
theorem sum_sign_le {p k q : ℕ} (σ : Fin k ⊕ Fin q ≃ Fin p) (x : Fin p → ℝ) (f : ℝ → ℝ)
    {a b : ℝ} (h1 : ∀ i, f (x (σ (Sum.inl i))) ≤ a) (h2 : ∀ i, f (x (σ (Sum.inr i))) ≤ b) :
    ∑ i, f (x i) ≤ k * a + q * b := by
  rw [← Equiv.sum_comp σ (fun i => f (x i)), Fintype.sum_sum_type]
  have e1 : ∑ i : Fin k, f (x (σ (Sum.inl i))) ≤ k * a :=
    calc _ ≤ ∑ _i : Fin k, a := Finset.sum_le_sum fun i _ => h1 i
      _ = k * a := by simp
  have e2 : ∑ i : Fin q, f (x (σ (Sum.inr i))) ≤ q * b :=
    calc _ ≤ ∑ _i : Fin q, b := Finset.sum_le_sum fun i _ => h2 i
      _ = q * b := by simp
  linarith

/-! #### Free facts of a near-optimal class member -/

/-- The excess (per `n²`) of the old route's bound over the class threshold, at `α = m/n`:
`(-target + log 2/2 + cost α + δ) - ((-t0 + log 2/2) + c2 α / n0)` (`c2 N m / n² = c2 α / n0`). -/
def excess (target cost t0 c2 δ n0 α : ℝ) : ℝ :=
  (-target + Real.log 2 / 2 + cost * α + δ) - ((-t0 + Real.log 2 / 2) + c2 * α / n0)

theorem groupedSquares_ge_free {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {a b r : ℕ} {x : Fin a → ℝ} {y : Fin b → ℝ} (z s : Fin r → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1)
    (u v w : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    sqTail v (pinCosineMoment ν e z) ≤ groupedSquares ν e u v w x y z s := by
  have h1 := (cosineSquares_nonneg hν he hx hy u hu).2
  have h3 := sqTail_nonneg w (fun j => pinPowerMoment ν e z j - 2 * pinColumnMoment ν e s j)
  unfold groupedSquares freeSquares
  linarith only [h1, h3]

/-- The factor-free second-population trial from an old one, at a free output target `target'`
and marked-fraction threshold `α1` (only the budget field mentions either). -/
def _root_.CatalanMeasure.GenD.Analytic.SecondTrialBounds.toEndAt {P : Parameters}
    {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBounds P target residual nearCap cost G)
    {α1 target' : ℝ} (cost' : ℝ)
    (hbud : ∀ {a t : ℝ}, α1 ≤ a → 0 ≤ a → 0 ≤ t →
      (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
        D.normCap + (1 - a) * D.fieldCap + (a - t) * residual + t * nearCap ≤
          -target' + Real.log 2 / 2 + cost' * a) :
    SecondTrialBoundsEnd P α1 target' residual nearCap cost' G where
  p := D.p
  v := D.v
  MX := D.MX
  MY := D.MY
  normCap := D.normCap
  fieldCap := D.fieldCap
  p_summable := D.p_summable
  v_summable := D.v_summable
  norm_le := D.norm_le
  field_sum := D.field_sum
  row := D.row
  column := D.column
  marked := D.marked
  near := D.near
  budget := hbud

/-- The factor-free (endpoint column field) old-route trial from an old-route trial and an endpoint
budget without `a (1 - a) log 2` (for K590: `K590.second_budget'_log2`, cost `secondCost'`): the
instance `α1 = 0`, original target, of `toEndAt`. -/
def SecondTrialBounds.toEnd {P : Parameters} {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBounds P target residual nearCap cost G) (cost' : ℝ)
    (hbud : ∀ {a t : ℝ}, 0 ≤ a → 0 ≤ t →
      (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
        D.normCap + (1 - a) * D.fieldCap + (a - t) * residual + t * nearCap ≤
          -target + Real.log 2 / 2 + cost' * a) :
    SecondTrialBoundsEnd P 0 target residual nearCap cost' G :=
  D.toEndAt (α1 := 0) (target' := target) cost' (fun _ ha ht => hbud ha ht)

set_option maxHeartbeats 1600000 in
/-- **`second_energy_end` keeping the dropped squares and field brackets** (the endpoint column
field, no `α log (1 + s)` term; the column bracket has cap `MY + δ/4`). -/
theorem second_energy_sq_end {P : Parameters} (hP : Admissible P)
    {α1 target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsEnd P α1 target residual nearCap cost G) {δ e : ℝ} (hδ : 0 < δ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D.p j|) + 4 * (∑' j, |D.v j|) + |D.p 1| + 20) < δ / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = P.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, G (x i)) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      α1 * (P.n N : ℝ) ≤ ((a + b : ℕ) : ℝ) →
      groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (groupedMarkedField P N)
        (groupedNearField P N) (populationEndpointColumnField P N 0)
        z x y s +
      groupedSlack (P.n N : ℝ) e D.p D.p D.v (populationPhysicalFreeField P N)
        (groupedMarkedField P N) (groupedNearField P N)
        (populationEndpointColumnField P N 0)
        (D.MX + δ / 4) (residual + δ / 4) (nearCap + δ / 4) (D.MY + δ / 4) z x y s ≤
        -target + Real.log 2 / 2 + cost * (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) + δ := by
  have hε : 0 < δ / 4 := by linarith only [hδ]
  have herr : ∀ᶠ N : ℕ in atTop,
      groupedPopulationError ((P.n0 : ℝ) * N) e D.p D.p D.v ≤ δ / 2 :=
    ((tendsto_order.mp (grouped_error_tendsto hP e D.p D.v)).2 (δ / 2) hec).mono
      (fun _ h => h.le)
  filter_upwards [log_reciprocal_eventually hP hε, herr, eventually_gt_atTop (0 : ℕ)]
    with N hsmall herror hN r a b hcount z x y s hz hz0 hx hxG hy hs hzi hxi hyi hsi hα1
  have hν : 0 < (P.n N : ℝ) := by exact_mod_cast n_pos hP hN
  have hα : 0 ≤ ((a + b : ℕ) : ℝ) / (P.n N : ℝ) := div_nonneg (Nat.cast_nonneg _) hν.le
  have hβ : 0 ≤ (b : ℝ) / (P.n N : ℝ) := div_nonneg (Nat.cast_nonneg _) hν.le
  have hα1' : α1 ≤ ((a + b : ℕ) : ℝ) / (P.n N : ℝ) := by
    rw [le_div_iff₀ hν]; exact hα1
  have hfree : (r : ℝ) / (P.n N : ℝ) = 1 - ((a + b : ℕ) : ℝ) / (P.n N : ℝ) := by
    have hf := population_fractions hP hN (show r + (a + b) = P.n N by omega)
    linarith only [hf]
  have hmarked : (a : ℝ) / (P.n N : ℝ) =
      ((a + b : ℕ) : ℝ) / (P.n N : ℝ) - (b : ℝ) / (P.n N : ℝ) := by
    rw [Nat.cast_add, add_div]
    ring
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hb := grouped_field_caps_bound_sq (constant := groupedConstant P N r a b) hν he
    (by exact_mod_cast (show r + a ≤ P.n N by omega))
    (by exact_mod_cast (show b ≤ P.n N by omega)) z x y s hz hx hy' hs hzi hxi hyi hsi
    D.p D.p D.v D.p_summable D.p_summable D.v_summable
    (populationPhysicalFreeField P N) (groupedMarkedField P N)
    (groupedNearField P N) (populationEndpointColumnField P N 0)
    (D.MX + δ / 4) (residual + δ / 4) (nearCap + δ / 4) (D.MY + δ / 4)
  have hconst := grouped_constant_le hP hN hcount
  have hbudget := D.budget hα1' hα hβ
  have hnorm := D.norm_le
  have hfields := congrArg (fun t : ℝ => (1 - ((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * t) D.field_sum
  have hεα := mul_nonneg hε.le hα
  rw [← n_cast] at herror
  rw [hfree, hmarked] at hb
  rw [hfree] at hconst
  ring_nf at hb hconst hbudget hfields hnorm herror hεα ⊢
  nlinarith only [hb, hconst, hbudget, hfields, hnorm, herror, hεα, hsmall]

/-- The physical column field is the endpoint column field plus `α log (1 + s)`
(`Analytic.grouped_value_physical_eq`, restated here). -/
theorem grouped_value_phys_end {P : Parameters} {N r a b : ℕ}
    (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ) :
    groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (groupedMarkedField P N)
        (groupedNearField P N) (populationPhysicalColumnField P N (a + b)) z x y s =
      groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (groupedMarkedField P N)
        (groupedNearField P N) (populationEndpointColumnField P N 0) z x y s +
      ((((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * ∑ i, Real.log (1 + s i)) / (P.n N : ℝ) :=
  CatalanMeasure.GenD.Analytic.grouped_value_physical_eq z x y s

set_option maxHeartbeats 1600000 in
/-- **Free facts of the near-optimal class (Lemma K), factor-free.**  For `z` in `nearOptCls`
(free rows of a configuration with `m = n - p` marked rows violating the factor-free old route at
`(t0, c2)`), measured against the factor-free old-route trial `D` (`SecondTrialBoundsEnd P 0`),
eventually in `N`: every free row has field at most the cap `MX + δ/4`, the field bracket and the
cosine square `Σ (p_k - A_k(z))²/k` are at most `excess .. (m/n)`. -/
theorem free_facts {P : Parameters} (hP : Admissible P)
    {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsEnd P 0 target residual nearCap cost G) {δ e : ℝ} (hδ : 0 < δ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D.p j|) + 4 * (∑' j, |D.v j|) + |D.p 1| + 20) < δ / 2)
    (t0 c2 : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = P.n N → ∀ z : Fin p → ℝ,
      nearOptCls P t0 c2 G N p z →
      (∀ i, freeRowX P N D.p D.v (z i) ≤ D.MX + δ / 4) ∧
      bracketSlack (P.n N : ℝ) (D.MX + δ / 4) (fun i => freeRowX P N D.p D.v (z i)) ≤
        excess target cost t0 c2 δ (P.n0 : ℝ) ((m : ℝ) / (P.n N : ℝ)) ∧
      sqTail D.p (pinCosineMoment (P.n N : ℝ) e z) ≤
        excess target cost t0 c2 δ (P.n0 : ℝ) ((m : ℝ) / (P.n N : ℝ)) := by
  have hε : 0 < δ / 4 := by linarith
  filter_upwards [second_energy_sq_end hP D hδ he hec, D.row hε, D.column hε,
    log_reciprocal_eventually hP hε, eventually_gt_atTop (0 : ℕ)]
    with N hE hrow hcol hl2 hN p m hpm z hcls
  obtain ⟨a, b, hcount, x, y, s, hz, hz0, hx, hxG, hy, hs, hzi, hzxi, hyi, hsi, hv⟩ := hcls
  have hν : 0 < (P.n N : ℝ) := by exact_mod_cast n_pos hP hN
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hE1 := hE p a b hcount z x y s hz hz0 hx hxG hy hs hzi hzxi hyi hsi
    (by rw [zero_mul]; exact Nat.cast_nonneg _)
  have hfac : 0 < (∏ i, (1 + s i)) ^ (a + b) :=
    pow_pos (Finset.prod_pos fun i _ => by linarith [(hs i).1]) _
  have hlhs : 0 < (∏ i, (1 + s i)) ^ (a + b) *
      Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-t0 + Real.log 2 / 2) + c2 * N * (a + b)) :=
    mul_pos hfac (Real.exp_pos _)
  have hlog := log_groupedProduct hP hN z x y s hz hx hy' hs hz0 (fun i => (hy i).1.ne')
    hzi hzxi hyi hsi
  have hphys := grouped_value_phys_end (P := P) (N := N) z x y s
  set V := groupedValueWithFields (P.n N : ℝ) (groupedConstant P N p a b)
    (populationPhysicalFreeField P N) (groupedMarkedField P N) (groupedNearField P N)
    (populationEndpointColumnField P N 0) z x y s with hV
  have hfaclog : Real.log ((∏ i, (1 + s i)) ^ (a + b)) =
      ((a + b : ℕ) : ℝ) * ∑ i, Real.log (1 + s i) := by
    rw [Real.log_pow, Real.log_prod (fun i _ => (show 0 < 1 + s i by linarith [(hs i).1]).ne')]
  have hV0 : ((P.n0 : ℝ) * N) ^ 2 * (-t0 + Real.log 2 / 2) + c2 * N * (a + b) <
      (P.n N : ℝ) ^ 2 * V := by
    have h1 := Real.log_lt_log hlhs hv
    rw [Real.log_mul hfac.ne' (Real.exp_pos _).ne', Real.log_exp, hfaclog, hlog, hphys] at h1
    have hk : (P.n N : ℝ) ^ 2 * (V + ((((a + b : ℕ) : ℝ) / (P.n N : ℝ)) *
        ∑ i, Real.log (1 + s i)) / (P.n N : ℝ)) =
        (P.n N : ℝ) ^ 2 * V + ((a + b : ℕ) : ℝ) * ∑ i, Real.log (1 + s i) := by
      field_simp
    rw [hk] at h1
    linarith
  have hab : (a : ℝ) + b = m := by
    have : a + b = m := by omega
    exact_mod_cast this
  have hnN : (P.n N : ℝ) = (P.n0 : ℝ) * N := n_cast P N
  have hn0 : (0 : ℝ) < P.n0 := by exact_mod_cast (hP.1)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hV1 : (-t0 + Real.log 2 / 2) + c2 * ((m : ℝ) / (P.n N : ℝ)) / (P.n0 : ℝ) < V := by
    have hn2 : 0 < (P.n N : ℝ) ^ 2 := by positivity
    rw [← n_cast] at hV0
    rw [hab] at hV0
    have e1 : ((-t0 + Real.log 2 / 2) + c2 * ((m : ℝ) / (P.n N : ℝ)) / (P.n0 : ℝ)) *
        (P.n N : ℝ) ^ 2 = (P.n N : ℝ) ^ 2 * (-t0 + Real.log 2 / 2) + c2 * N * m := by
      rw [hnN]; field_simp
    have h2 : ((-t0 + Real.log 2 / 2) + c2 * ((m : ℝ) / (P.n N : ℝ)) / (P.n0 : ℝ)) *
        (P.n N : ℝ) ^ 2 < V * (P.n N : ℝ) ^ 2 := by rw [e1]; linarith
    exact lt_of_mul_lt_mul_right h2 hn2.le
  have hzx : ∀ i, Fin.append z x i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hz j
    · simpa using hx j
  have hXz : ∀ i, freeRowX P N D.p D.v (z i) ≤ D.MX + δ / 4 := by
    intro i
    have hzi' : z i ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
      rcases lt_or_gt_of_ne (hz0 i) with h | h
      · exact Or.inl ⟨(hz i).1.le, h⟩
      · exact Or.inr ⟨h, (hz i).2⟩
    have := hrow (z i) hzi'
    unfold freeRowX
    linarith
  have hM : ∀ i, groupedMarkedField P N (x i) - 2 * barrierTrialT D.p (x i) ≤ residual + δ / 4 :=
    fun i => (D.marked hN ⟨(hx i).1.le, (hx i).2.le⟩ (hxG i)).trans (by linarith)
  have hL : ∀ i, groupedNearField P N (y i) - D.p 1 * y i ≤ nearCap + δ / 4 :=
    fun i => (D.near hN (hy i)).trans (by linarith)
  have hC : ∀ i, populationEndpointColumnField P N 0 (s i) + 2 * barrierTrialT D.v (s i) -
      Real.log (1 - s i) / (P.n N : ℝ) ≤ D.MY + δ / 4 := fun i => hcol (s i) (hs i)
  have hb2 := bracketSlack_nonneg hν hM
  have hb3 := bracketSlack_nonneg hν hL
  have hb4 := bracketSlack_nonneg hν hC
  have hsq := groupedSquares_ge_free (ν := (P.n N : ℝ)) hν he z s hzx hy' D.p D.p D.v
    D.p_summable
  have hsq0 := groupedSquares_nonneg hν he z s hzx hy' D.p D.p D.v D.p_summable
  have hUm : (-target + Real.log 2 / 2 + cost * (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) + δ) =
      (-target + Real.log 2 / 2 + cost * ((m : ℝ) / (P.n N : ℝ)) + δ) := by
    rw [Nat.cast_add, hab]
  unfold groupedSlack at hE1
  have hfree : bracketSlack (P.n N : ℝ) (D.MX + δ / 4)
      (fun i => freeRowX P N D.p D.v (z i)) ≤
      excess target cost t0 c2 δ (P.n0 : ℝ) ((m : ℝ) / (P.n N : ℝ)) := by
    unfold excess
    unfold freeRowX
    linarith
  have hb1 : 0 ≤ bracketSlack (P.n N : ℝ) (D.MX + δ / 4)
      (fun i => freeRowX P N D.p D.v (z i)) := bracketSlack_nonneg hν hXz
  unfold freeRowX at hb1
  refine ⟨hXz, hfree, ?_⟩
  unfold excess
  linarith

end HL

section HL2

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

/-- Counting: the free rows in a region where the free field is `d` below its cap number at most
`ν Δ / d` (Chebyshev inequality for the bracket). -/
theorem card_region_le {ν cap d Δ : ℝ} (hν : 0 < ν) {p : ℕ} (X : Fin p → ℝ)
    (S : Finset (Fin p)) (hX : ∀ i, X i ≤ cap) (hS : ∀ i ∈ S, X i ≤ cap - d)
    (hb : bracketSlack ν cap X ≤ Δ) : (S.card : ℝ) * d ≤ ν * Δ :=
  (card_mul_le_bracket hν X S hX hS).trans (mul_le_mul_of_nonneg_left hb hν.le)

/-- The Chebyshev polynomial `c0 + Σ_{k<K} G_k τ^{k+1} T_{k+1}(x)` of a certificate; `τ = 1 - e`
is the damping of the cosine moments `pinCosineMoment`. -/
def evalCert (e : ℝ) (K : ℕ) (G : ℕ → ℝ) (c0 x : ℝ) : ℝ :=
  c0 + ∑ k ∈ Finset.range K,
    G k * (realEnergyTau e ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x)

/-- `H = Σ_{k<K} G_k² (k+1)`: the dual norm of the certificate. -/
def certH (K : ℕ) (G : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range K, G k ^ 2 * ((k : ℝ) + 1)

/-- `Σ_{k<K} G_k p_{k+1}`: the value of the certificate on the trial. -/
def certMean (K : ℕ) (G : ℕ → ℝ) (pp : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range K, G k * pp (k + 1)

/-- **One-sided linear statistics of the free rows from the cosine square.**  If the damped
cosine moments `A_k(z)` of the `r` nodes `z` satisfy `Σ_k (p_k - A_k(z))²/k ≤ Δ`, then for any
Chebyshev polynomial `c0 + Σ_{k<K} G_k τ^{k+1} T_{k+1}`:
`(r/ν) c0 + Σ_{k<K} G_k p_{k+1} - √(H Δ) ≤ (Σ_i P(z_i))/ν`, `H = Σ G_k² (k+1)`
(Cauchy–Schwarz, `linear_statistic_bound`). -/
theorem stat_poly_ge {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {r : ℕ}
    (z : Fin r → ℝ) (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (pp : ℕ → ℝ)
    (hpp : Summable (fun k => |pp k|)) {Δ : ℝ}
    (hsq : sqTail pp (pinCosineMoment ν e z) ≤ Δ) (K : ℕ) (G : ℕ → ℝ) (c0 : ℝ) :
    ((r : ℝ) / ν) * c0 + certMean K G pp - Real.sqrt (certH K G * Δ) ≤
      (∑ i, evalCert e K G c0 (z i)) / ν := by
  have hS := pin_hasSum_cos_sq_shift hν he hz
  have hD := completed_square_hasSum pp (pinCosineMoment ν e z) hpp hS
  have hD' := hD.summable.hasSum
  have hvpos : ∀ k : ℕ, 0 < ((k + 1 : ℕ) : ℝ) := fun k => by positivity
  have hH : HasSum (fun k : ℕ => (if k < K then G k else 0) ^ 2 * ((k + 1 : ℕ) : ℝ))
      (certH K G) := by
    have h : HasSum (fun k : ℕ => (if k < K then G k else 0) ^ 2 * ((k + 1 : ℕ) : ℝ))
        (∑ k ∈ Finset.range K, (if k < K then G k else 0) ^ 2 * ((k + 1 : ℕ) : ℝ)) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by
        have : ¬ k < K := by simpa [Finset.mem_range] using hk
        simp [this])
    convert h using 1
    unfold certH
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k < K := Finset.mem_range.1 hk
    simp [this]
  have hlin := linear_statistic_bound
    (d := fun k => pp (k + 1) - pinCosineMoment ν e z (k + 1))
    (F := fun k => if k < K then G k else 0) (v := fun k => ((k + 1 : ℕ) : ℝ)) hvpos
    hD' hsq hH
  have htsum : ∑' k : ℕ, (if k < K then G k else 0) * (pp (k + 1) - pinCosineMoment ν e z (k + 1))
      = ∑ k ∈ Finset.range K, G k * (pp (k + 1) - pinCosineMoment ν e z (k + 1)) := by
    rw [tsum_eq_sum (s := Finset.range K)]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have : k < K := Finset.mem_range.1 hk
      simp [this]
    · intro k hk
      have : ¬ k < K := by simpa [Finset.mem_range] using hk
      simp [this]
  rw [htsum] at hlin
  have hsum : ∑ i, evalCert e K G c0 (z i) =
      (r : ℝ) * c0 + ν * ∑ k ∈ Finset.range K, G k * pinCosineMoment ν e z (k + 1) := by
    unfold evalCert
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold pinCosineMoment
    rw [← Finset.mul_sum]
    field_simp
  have hmean : ∑ k ∈ Finset.range K, G k * pinCosineMoment ν e z (k + 1) =
      certMean K G pp - ∑ k ∈ Finset.range K, G k * (pp (k + 1) - pinCosineMoment ν e z (k + 1)) := by
    unfold certMean
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsum, hmean]
  have e1 : ((r : ℝ) * c0 + ν * (certMean K G pp - ∑ k ∈ Finset.range K,
      G k * (pp (k + 1) - pinCosineMoment ν e z (k + 1)))) / ν =
      ((r : ℝ) / ν) * c0 + certMean K G pp - ∑ k ∈ Finset.range K,
        G k * (pp (k + 1) - pinCosineMoment ν e z (k + 1)) := by
    field_simp
    ring
  rw [e1]
  have hle := (abs_le.1 hlin).2
  linarith

/-- The lower bound of a sign count from a one-sided polynomial: if `P ≤ a` on the negative
nodes and `P ≤ b` on the positive nodes of the sign split `σ`, then
`(p/ν) c0 + Σ G_k p_{k+1} - √(H Δ) ≤ (k a + q b)/ν`. -/
theorem count_lower {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p k q : ℕ}
    (σ : Fin k ⊕ Fin q ≃ Fin p) (x : Fin p → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (pp : ℕ → ℝ) (hpp : Summable (fun k => |pp k|)) {Δ : ℝ}
    (hsq : sqTail pp (pinCosineMoment ν e x) ≤ Δ) (K : ℕ) (G : ℕ → ℝ) (c0 a b : ℝ)
    (h1 : ∀ i, evalCert e K G c0 (x (σ (Sum.inl i))) ≤ a)
    (h2 : ∀ i, evalCert e K G c0 (x (σ (Sum.inr i))) ≤ b) :
    ((p : ℝ) / ν) * c0 + certMean K G pp - Real.sqrt (certH K G * Δ) ≤
      ((k : ℝ) * a + q * b) / ν := by
  refine (stat_poly_ge hν he x hx pp hpp hsq K G c0).trans ?_
  exact div_le_div_of_nonneg_right (sum_sign_le σ x _ h1 h2) hν.le

end HL2

section HL3

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

/-- A one-sided Chebyshev-polynomial certificate: the polynomial `evalCert e K G c0`. -/
structure PolyCert where
  K : ℕ
  G : ℕ → ℝ
  c0 : ℝ

theorem certH_nonneg (K : ℕ) (G : ℕ → ℝ) : 0 ≤ certH K G :=
  Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (by positivity)

theorem sqrt_certH_le {K : ℕ} {G : ℕ → ℝ} {Δ Dtop s : ℝ} (hΔ : Δ ≤ Dtop) (hs : 0 ≤ s)
    (h : certH K G * Dtop ≤ s ^ 2) : Real.sqrt (certH K G * Δ) ≤ s :=
  Real.sqrt_le_iff.mpr ⟨hs, (mul_le_mul_of_nonneg_left hΔ (certH_nonneg K G)).trans h⟩

/-- `1 - k_t(x) ≥ 0` for `t > 0`. -/
theorem one_sub_slopeKernel_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ 1 - slopeKernel t x := by
  unfold slopeKernel
  have hd : 0 < t ^ 2 + x ^ 2 := by positivity
  have h1 : t ^ 2 / (t ^ 2 + x ^ 2) = 1 - x ^ 2 / (t ^ 2 + x ^ 2) := by
    field_simp; ring
  have h2 : 0 ≤ x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) := by positivity
  have h3 : 0 ≤ x ^ 2 / (t ^ 2 + x ^ 2) := by positivity
  linarith

/-- For small `t` and a node away from the origin, `1 - k_t(x) ≥ a²/(ts² + a²)`. -/
theorem one_sub_slopeKernel_ge_small {t x a ts : ℝ} (ht : 0 < t) (hts : t ≤ ts) (ha : 0 < a)
    (hx : a ≤ |x|) : a ^ 2 / (ts ^ 2 + a ^ 2) ≤ 1 - slopeKernel t x := by
  unfold slopeKernel
  have ht2 : t ^ 2 ≤ ts ^ 2 := by nlinarith
  have hx2 : a ^ 2 ≤ x ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg x]) hx
    simpa using this
  have hd : 0 < t ^ 2 + x ^ 2 := by positivity
  have hts0 : 0 < ts := lt_of_lt_of_le ht hts
  have h1 : t ^ 2 / (t ^ 2 + x ^ 2) = 1 - x ^ 2 / (t ^ 2 + x ^ 2) := by
    field_simp; ring
  have h2 : 0 ≤ x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) := by positivity
  have h3 : a ^ 2 / (ts ^ 2 + a ^ 2) ≤ x ^ 2 / (t ^ 2 + x ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) hd]
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 ht2), mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx2),
      mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 ht2), sq_nonneg a, sq_nonneg ts]
  linarith

/-- **`k_t(x)` is Lipschitz in `t` on `t ≥ a`**, with constant `1/a`, uniformly in `x`. -/
theorem slopeKernel_lip {x t s a : ℝ} (ha : 0 < a) (ht : a ≤ t) (hs : a ≤ s) :
    |slopeKernel t x - slopeKernel s x| ≤ |t - s| / a := by
  have ht0 : 0 < t := lt_of_lt_of_le ha ht
  have hs0 : 0 < s := lt_of_lt_of_le ha hs
  have hts : 2 * a ≤ t + s := by linarith
  -- the first term
  have hg : |t ^ 2 / (t ^ 2 + x ^ 2) - s ^ 2 / (s ^ 2 + x ^ 2)| ≤ |t - s| / (2 * a) := by
    have hd1 : 0 < t ^ 2 + x ^ 2 := by positivity
    have hd2 : 0 < s ^ 2 + x ^ 2 := by positivity
    rw [div_sub_div _ _ hd1.ne' hd2.ne']
    have hnum : t ^ 2 * (s ^ 2 + x ^ 2) - (t ^ 2 + x ^ 2) * s ^ 2 =
        x ^ 2 * (t - s) * (t + s) := by ring
    rw [hnum, abs_div, abs_of_pos (mul_pos hd1 hd2), abs_mul, abs_mul, abs_of_nonneg (sq_nonneg x),
      abs_of_pos (by linarith : 0 < t + s), div_le_div_iff₀ (mul_pos hd1 hd2) (by positivity)]
    have hden : 2 * a * (x ^ 2 * (t + s)) ≤ (t ^ 2 + x ^ 2) * (s ^ 2 + x ^ 2) := by
      nlinarith [sq_nonneg (t * s - x ^ 2), mul_nonneg (sq_nonneg x) (sub_nonneg.2 hts),
        mul_nonneg (sq_nonneg x) (sq_nonneg (t + s)), sq_nonneg x]
    have := mul_le_mul_of_nonneg_left hden (abs_nonneg (t - s))
    nlinarith [this, abs_nonneg (t - s), sq_nonneg x]
  have hh : |x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) - x ^ 2 * s ^ 2 / (1 + x ^ 2 * s ^ 2)| ≤
      |t - s| / (2 * a) := by
    have hd1 : 0 < 1 + x ^ 2 * t ^ 2 := by positivity
    have hd2 : 0 < 1 + x ^ 2 * s ^ 2 := by positivity
    rw [div_sub_div _ _ hd1.ne' hd2.ne']
    have hnum : x ^ 2 * t ^ 2 * (1 + x ^ 2 * s ^ 2) - (1 + x ^ 2 * t ^ 2) * (x ^ 2 * s ^ 2) =
        x ^ 2 * (t - s) * (t + s) := by ring
    rw [hnum, abs_div, abs_of_pos (mul_pos hd1 hd2), abs_mul, abs_mul, abs_of_nonneg (sq_nonneg x),
      abs_of_pos (by linarith : 0 < t + s), div_le_div_iff₀ (mul_pos hd1 hd2) (by positivity)]
    have hden : 2 * a * (x ^ 2 * (t + s)) ≤ (1 + x ^ 2 * t ^ 2) * (1 + x ^ 2 * s ^ 2) := by
      nlinarith [sq_nonneg (x ^ 2 * t * s - 1), mul_nonneg (sq_nonneg x) (sub_nonneg.2 hts),
        mul_nonneg (sq_nonneg x) (sq_nonneg (t + s)), sq_nonneg x]
    have := mul_le_mul_of_nonneg_left hden (abs_nonneg (t - s))
    nlinarith [this, abs_nonneg (t - s), sq_nonneg x]
  unfold slopeKernel
  have hsplit : t ^ 2 / (t ^ 2 + x ^ 2) - x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) -
      (s ^ 2 / (s ^ 2 + x ^ 2) - x ^ 2 * s ^ 2 / (1 + x ^ 2 * s ^ 2)) =
      (t ^ 2 / (t ^ 2 + x ^ 2) - s ^ 2 / (s ^ 2 + x ^ 2)) -
        (x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) - x ^ 2 * s ^ 2 / (1 + x ^ 2 * s ^ 2)) := by ring
  rw [hsplit]
  calc _ ≤ |t ^ 2 / (t ^ 2 + x ^ 2) - s ^ 2 / (s ^ 2 + x ^ 2)| +
        |x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) - x ^ 2 * s ^ 2 / (1 + x ^ 2 * s ^ 2)| := abs_sub _ _
    _ ≤ |t - s| / (2 * a) + |t - s| / (2 * a) := add_le_add hg hh
    _ = |t - s| / a := by field_simp; ring

/-- **The free part of the slope sum** (Lemma T′, slope condition for the free rows): for every
`t ∈ (0, 1]`, `Σ_i (1 - k_t(x_i)) > 2 g + 1`.  Small `t` (`t ≤ ts`): the nodes with `|x| ≥ a0` all
contribute at least `a0²/(ts²+a0²)` and fewer than `ν Dtop/dgap` nodes are in the gap.  Large `t`:
a grid `tg` of `[ts,1]` with Lipschitz constant `1/ts` and the one-sided polynomials `Ct j`
below `1 - k_{tg j}(·) - hmesh/ts`. -/
theorem free_slope_gt {ν e gg : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ}
    (x : Fin p → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (pp : ℕ → ℝ) (hpp : Summable (fun k => |pp k|)) {Δ Dtop : ℝ}
    (hsq : sqTail pp (pinCosineMoment ν e x) ≤ Δ) (hΔ : Δ ≤ Dtop)
    {a0 ts dgap ηT : ℝ} (ha0 : 0 < a0) (hts : 0 < ts) (hdgap : 0 < dgap)
    (hgapc : ((Finset.univ.filter fun i => |x i| < a0).card : ℝ) ≤ ν * Dtop / dgap)
    (hη : 1 < ν * ηT)
    (hsmall : 2 * gg / ν + ηT < ((p : ℝ) / ν - Dtop / dgap) * (a0 ^ 2 / (ts ^ 2 + a0 ^ 2)))
    {J : ℕ} (tg : Fin J → ℝ) (hmesh : ℝ) (htg : ∀ j, tg j ∈ Icc ts 1)
    (hcov : ∀ t ∈ Icc ts 1, ∃ j, |t - tg j| ≤ hmesh)
    (Ct : Fin J → PolyCert) (sT : Fin J → ℝ) (hsT0 : ∀ j, 0 ≤ sT j)
    (hsT : ∀ j, certH (Ct j).K (Ct j).G * Dtop ≤ sT j ^ 2)
    (hPt : ∀ j, ∀ y ∈ Icc (-1 : ℝ) 1, y ≠ 0 →
      evalCert e (Ct j).K (Ct j).G (Ct j).c0 y + hmesh / ts ≤ 1 - slopeKernel (tg j) y)
    (hmarg : ∀ j, 2 * gg / ν + ηT ≤
      ((p : ℝ) / ν) * (Ct j).c0 + certMean (Ct j).K (Ct j).G pp - sT j) :
    ∀ t ∈ Ioc (0 : ℝ) 1, 2 * gg + 1 < ∑ i, (1 - slopeKernel t (x i)) := by
  intro t ht
  rcases le_total t ts with hle | hge
  · -- small t: gap counting
    set S := Finset.univ.filter (fun i => |x i| < a0) with hS
    have hnn : ∀ i, 0 ≤ 1 - slopeKernel t (x i) := fun i => one_sub_slopeKernel_nonneg ht.1 _
    have hcompl : ∑ i ∈ Sᶜ, (1 - slopeKernel t (x i)) ≤ ∑ i, (1 - slopeKernel t (x i)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hnn i
    have hlow : ∑ _i ∈ Sᶜ, a0 ^ 2 / (ts ^ 2 + a0 ^ 2) ≤ ∑ i ∈ Sᶜ, (1 - slopeKernel t (x i)) :=
      Finset.sum_le_sum fun i hi => one_sub_slopeKernel_ge_small ht.1 hle ha0
        (not_lt.1 (by simpa [hS] using hi))
    have hcard : ((Sᶜ.card : ℕ) : ℝ) = p - S.card := by
      rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub (by
        simpa using (Finset.card_le_univ S))]
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at hlow
    have hκ0 : 0 < a0 ^ 2 / (ts ^ 2 + a0 ^ 2) := by positivity
    have hcs : (p : ℝ) - S.card ≥ (p : ℝ) - ν * Dtop / dgap := by linarith
    have hb : ((p : ℝ) - ν * Dtop / dgap) * (a0 ^ 2 / (ts ^ 2 + a0 ^ 2)) ≤
        ((p : ℝ) - S.card) * (a0 ^ 2 / (ts ^ 2 + a0 ^ 2)) :=
      mul_le_mul_of_nonneg_right hcs hκ0.le
    have e1 : ((p : ℝ) / ν - Dtop / dgap) * (a0 ^ 2 / (ts ^ 2 + a0 ^ 2)) =
        (((p : ℝ) - ν * Dtop / dgap) * (a0 ^ 2 / (ts ^ 2 + a0 ^ 2))) / ν := by
      field_simp
    rw [e1, lt_div_iff₀ hν] at hsmall
    have e2 : (2 * gg / ν + ηT) * ν = 2 * gg + ν * ηT := by field_simp
    rw [e2] at hsmall
    linarith
  · -- large t: grid and polynomial
    obtain ⟨j, hj⟩ := hcov t ⟨hge, ht.2⟩
    have hpt : ∀ i, evalCert e (Ct j).K (Ct j).G (Ct j).c0 (x i) ≤ 1 - slopeKernel t (x i) := by
      intro i
      have h1 := hPt j (x i) ⟨(hx i).1.le, (hx i).2.le⟩ (hx0 i)
      have h2 := slopeKernel_lip (x := x i) hts hge (htg j).1
      have h3 : |t - tg j| / ts ≤ hmesh / ts := div_le_div_of_nonneg_right hj hts.le
      have h4 := (abs_le.1 (h2.trans h3)).2
      linarith
    have hsumle : ∑ i, evalCert e (Ct j).K (Ct j).G (Ct j).c0 (x i) ≤
        ∑ i, (1 - slopeKernel t (x i)) := Finset.sum_le_sum fun i _ => hpt i
    have hst := stat_poly_ge hν he x hx pp hpp hsq (Ct j).K (Ct j).G (Ct j).c0
    have hsr := sqrt_certH_le (K := (Ct j).K) (G := (Ct j).G) hΔ (hsT0 j) (hsT j)
    have hm := hmarg j
    have h5 : 2 * gg / ν + ηT ≤
        (∑ i, evalCert e (Ct j).K (Ct j).G (Ct j).c0 (x i)) / ν := by linarith
    rw [le_div_iff₀ hν] at h5
    have e2 : (2 * gg / ν + ηT) * ν = 2 * gg + ν * ηT := by field_simp
    rw [e2] at h5
    linarith

end HL3

section HL4

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

theorem g_bound {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 2 ≤ N) :
    2 * P.g N + 2 ≤ P.n N := by
  have h := Nat.mul_le_mul_right N (show 2 * P.g0 + 1 ≤ P.n0 from hP.2.2.2.2)
  simp only [Parameters.g, Parameters.n]
  nlinarith [h]

/-- **Lemma T for ALL positives of the sheet from the free slope sum** (the first conjunct of the
class link).  The marked rows contribute `k_t ≤ 1` each, the free rows satisfy
`Σ_free (1 - k_t) > 2g + 1`, so the slope hypothesis of `lemmaT_of_slope` holds at `e = n - 1 - 2g`. -/
theorem lemmaT_of_free {P : Parameters} (hP : Admissible P) {N p m : ℕ} (hN : 2 ≤ N)
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hinj : Function.Injective (Fin.append x y))
    (hfree : ∀ t ∈ Ioc (0 : ℝ) 1, 2 * (P.g N : ℝ) + 1 < ∑ i, (1 - slopeKernel t (x i))) :
    ∀ c : Fin (P.n N) → ℝ,
      |∑ a ∈ Finset.univ.filter (fun a => 0 < sheetNodes hpm x y a),
        bDeriv (sheetNodes hpm x y) a * sheetNodes hpm x y a ^ (P.n N - 1 - 2 * P.g N) *
          c a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, c a * c b /
          (1 - sheetNodes hpm x y a * sheetNodes hpm x y b) := by
  intro c
  have hg := g_bound hP hN
  have hall : ∀ i : Fin (p + m), Fin.append x y i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hx j
    · simpa using hy j
  have hall0 : ∀ i : Fin (p + m), Fin.append x y i ≠ 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hx0 j
    · simpa using hy0 j
  have hinjz : Function.Injective (sheetNodes hpm x y) := fun a b hab =>
    Fin.cast_injective hpm.symm (hinj hab)
  have hz1 : ∀ a, |sheetNodes hpm x y a| < 1 := fun a =>
    abs_lt.2 (hall (Fin.cast hpm.symm a))
  have hz0 : ∀ a, sheetNodes hpm x y a ≠ 0 := fun a => hall0 _
  refine lemmaT_of_slope (sheetNodes hpm x y) (e := P.n N - 1 - 2 * P.g N) c hinjz hz1 hz0 (by omega) ?_
  intro t ht
  have hsum : ∑ a : Fin (P.n N), slopeKernel t (sheetNodes hpm x y a) =
      ∑ i : Fin p, slopeKernel t (x i) + ∑ j : Fin m, slopeKernel t (y j) := by
    have e1 : ∑ a : Fin (P.n N), slopeKernel t (sheetNodes hpm x y a) =
        ∑ i : Fin (p + m), slopeKernel t (Fin.append x y i) :=
      Fintype.sum_equiv (finCongr hpm.symm) _ _ (fun a => by simp [sheetNodes])
    rw [e1, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  have hcast : ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ) = (P.n N : ℝ) - 1 - 2 * (P.g N : ℝ) := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hmarked : ∑ j : Fin m, slopeKernel t (y j) ≤ m := by
    calc _ ≤ ∑ _j : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => slopeKernel_nonneg_le_one ht.1 _
      _ = m := by simp
  have hfr := hfree t ht
  have hfsum : ∑ i : Fin p, (1 - slopeKernel t (x i)) = p - ∑ i : Fin p, slopeKernel t (x i) := by
    rw [Finset.sum_sub_distrib]; simp
  have hpmR : (p : ℝ) + m = P.n N := by exact_mod_cast hpm
  show 0 < ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ) - ∑ a, slopeKernel t (sheetNodes hpm x y a)
  rw [hcast, hsum]
  linarith

/-- Lower bounds of the free sign counts `q` (positives) and `k` (negatives) from two one-sided
polynomials and the cosine square. -/
theorem sign_lower {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p k q : ℕ}
    (σ : Fin k ⊕ Fin q ≃ Fin p) (x : Fin p → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hxneg : ∀ b, x (σ (Sum.inl b)) < 0) (hxpos : ∀ b, 0 < x (σ (Sum.inr b)))
    (pp : ℕ → ℝ) (hpp : Summable (fun k => |pp k|)) {Δ Dc : ℝ}
    (hsq : sqTail pp (pinCosineMoment ν e x) ≤ Δ) (hΔ : Δ ≤ Dc) (Cp Cm : PolyCert)
    {sP sM : ℝ} (hsP0 : 0 ≤ sP) (hsM0 : 0 ≤ sM)
    (hsP : certH Cp.K Cp.G * Dc ≤ sP ^ 2) (hsM : certH Cm.K Cm.G * Dc ≤ sM ^ 2)
    (hCp_neg : ∀ y ∈ Icc (-1 : ℝ) 1, y < 0 → evalCert e Cp.K Cp.G Cp.c0 y ≤ 0)
    (hCp_pos : ∀ y ∈ Icc (-1 : ℝ) 1, 0 < y → evalCert e Cp.K Cp.G Cp.c0 y ≤ 1)
    (hCm_neg : ∀ y ∈ Icc (-1 : ℝ) 1, y < 0 → evalCert e Cm.K Cm.G Cm.c0 y ≤ 1)
    (hCm_pos : ∀ y ∈ Icc (-1 : ℝ) 1, 0 < y → evalCert e Cm.K Cm.G Cm.c0 y ≤ 0) :
    ((p : ℝ) / ν) * Cp.c0 + certMean Cp.K Cp.G pp - sP ≤ (q : ℝ) / ν ∧
      ((p : ℝ) / ν) * Cm.c0 + certMean Cm.K Cm.G pp - sM ≤ (k : ℝ) / ν := by
  have hI : ∀ b, x (σ b) ∈ Icc (-1 : ℝ) 1 := fun b => ⟨(hx _).1.le, (hx _).2.le⟩
  have h1 := count_lower hν he σ x hx pp hpp hsq Cp.K Cp.G Cp.c0 0 1
    (fun i => hCp_neg _ (hI _) (hxneg i)) (fun i => hCp_pos _ (hI _) (hxpos i))
  have h2 := count_lower hν he σ x hx pp hpp hsq Cm.K Cm.G Cm.c0 1 0
    (fun i => hCm_neg _ (hI _) (hxneg i)) (fun i => hCm_pos _ (hI _) (hxpos i))
  have s1 := sqrt_certH_le (K := Cp.K) (G := Cp.G) hΔ hsP0 hsP
  have s2 := sqrt_certH_le (K := Cm.K) (G := Cm.G) hΔ hsM0 hsM
  constructor
  · have : ((k : ℝ) * 0 + q * 1) / ν = (q : ℝ) / ν := by ring
    linarith
  · have : ((k : ℝ) * 1 + q * 0) / ν = (k : ℝ) / ν := by ring
    linarith

end HL4

section HL5

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

/-- The canonical class predicate `Clsf` (what `hCls_of_cert` needs): ranges, row counts, and the
spike count of the positives `≤ Mmax N` for every endpoint trial's `θ`. -/
def ClsfCanon {I : ℕ} (θ : Fin I → ℕ → ℝ) (sr gc : Fin I → ℕ → ℕ) (nu : Fin I → ℕ → ℝ)
    (Kn Tn : ℕ → ℝ) (Mmax : ℕ → ℕ) (N k q m1 m2 : ℕ)
    (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) : Prop :=
  (∀ b, Fin.append xn yn b ∈ Ioo (-1 : ℝ) 0) ∧ (∀ p, Fin.append gp yp p ∈ Ioo (0 : ℝ) 1) ∧
    (((k + m1 : ℕ)) : ℝ) ≤ Kn N ∧ ((k + m1 + (q + m2) + 1 : ℕ) : ℝ) ≤ Tn N ∧
    (∀ i, (Finset.univ.filter (fun p => 1 - θ i N < Fin.append gp yp p)).card ≤ Mmax N) ∧
    ∀ i, 0 < sr i N ∧ sr i N + gc i N ≤ q + m2 ∧ ((q + m2 : ℕ) : ℝ) ≤ nu i N

/-- `hCls` for the canonical class: only the per-trial spike certificates remain. -/
theorem hCls_of_canon {I : ℕ} {DA DB : Fin I → ℕ → SignedData} (cp : Fin I → ℕ → ℝ → ℝ)
    (hc : ∀ i, ∀ᶠ N : ℕ in atTop, InterpCompat (DA i N) (DB i N))
    (rA : ∀ i, ∀ᶠ N : ℕ in atTop, SignedRegular (DA i N))
    (rB : ∀ i, ∀ᶠ N : ℕ in atTop, SignedRegular (DB i N))
    (EA : ∀ i, ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (DA i N)))
    (EB : ∀ i, ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (DB i N))) (Kn Tn : ℕ → ℝ) (Mmax : ℕ → ℕ)
    (hcert : ∀ i, ∀ᶠ N : ℕ in atTop, ∀ (x m : ℕ), (DA i N).sp ≤ x → (x : ℝ) ≤ (DA i N).ν →
      2 * m ≤ Mmax N + 1 →
      ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ (DA i N).τ ^ 2 * (1 - (DA i N).θ) ∧
      Nonempty (SpikeTrialCert ((DA i N).withCount x) m ρ (Kn N) (Tn N)) ∧
      Nonempty (SpikeTrialCert ((DB i N).withCount x) m ρ (Kn N) (Tn N))) :
    ∀ i, ∀ᶠ N : ℕ in atTop, ∀ α k q m1 m2 xn gp yn yp,
      ClsfCanon (fun i N => (DA i N).θ) (fun i N => (DA i N).sp) (fun i N => (DA i N).g)
        (fun i N => (DA i N).ν) Kn Tn Mmax N k q m1 m2 xn gp yn yp →
      (0 < (DA i N).sp ∧ (DA i N).sp + (DA i N).g ≤ q + m2) ∧
      Nonempty (PairCls ((DA i N).withCount (q + m2 - (DA i N).g))
        ((DB i N).withCount (q + m2 - (DA i N).g)) (cp i N α) xn gp yn yp) :=
  hCls_of_cert cp hc rA rB EA EB (fun N k q m1 m2 xn gp yn yp =>
    ClsfCanon (fun i N => (DA i N).θ) (fun i N => (DA i N).sp) (fun i N => (DA i N).g)
      (fun i N => (DA i N).ν) Kn Tn Mmax N k q m1 m2 xn gp yn yp) Kn Tn Mmax
    (fun _ _ _ _ _ _ _ _ _ h => h) hcert

theorem card_spike_mono {n : ℕ} (v : Fin n → ℝ) {θ θ0 : ℝ} (h : θ ≤ θ0) :
    (Finset.univ.filter (fun i => 1 - θ < v i)).card ≤
      (Finset.univ.filter (fun i => 1 - θ0 < v i)).card :=
  Finset.card_le_card (fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith)

/-- The canonical `Clsf` holds for a sign/first-kind split of a configuration (ranges, counts and
the spike count `card_x + card_y ≤ Mmax`). -/
theorem canon_of_split {I : ℕ} (θ : Fin I → ℕ → ℝ) (sr gc : Fin I → ℕ → ℕ)
    (nu : Fin I → ℕ → ℝ) (Kn Tn : ℕ → ℝ) (Mmax : ℕ → ℕ) (N : ℕ)
    {p m n k q m1 m2' r s' : ℕ} (hpm : p + m = n) (x : Fin p → ℝ) (y : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1)
    (σx : Fin k ⊕ Fin q ≃ Fin p) (σy : Fin m1 ⊕ Fin m2' ≃ Fin m) (τ : Fin r ⊕ Fin s' ≃ Fin m2')
    (hxneg : ∀ b, x (σx (Sum.inl b)) < 0) (hxpos : ∀ b, 0 < x (σx (Sum.inr b)))
    (hyneg : ∀ b, y (σy (Sum.inl b)) < 0) (hypos : ∀ b, 0 < y (σy (Sum.inr b)))
    (hKn : (n : ℝ) ≤ Kn N) (hTn : (n : ℝ) + 1 ≤ Tn N)
    (hsp : ∀ i, (Finset.univ.filter (fun v => 1 - θ i N < x v)).card +
        (Finset.univ.filter (fun v => 1 - θ i N < y v)).card ≤ Mmax N)
    (hcnt : ∀ i, 0 < sr i N ∧ sr i N + gc i N ≤ q) (hnu : ∀ i, (n : ℝ) ≤ nu i N) :
    ClsfCanon θ sr gc nu Kn Tn Mmax N k q m1 (r + s') (fun b => x (σx (Sum.inl b)))
      (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inl b)))
      (Fin.append (fun j => y (σy (Sum.inr (τ (Sum.inl j)))))
        (fun j => y (σy (Sum.inr (τ (Sum.inr j)))))) := by
  have hkq : k + q = p := by simpa using Fintype.card_congr σx
  have hm12 : m1 + m2' = m := by simpa using Fintype.card_congr σy
  have hrs : r + s' = m2' := by simpa using Fintype.card_congr τ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simp only [Fin.append_left]; exact ⟨(hx _).1, hxneg j⟩
    · simp only [Fin.append_right]; exact ⟨(hy _).1, hyneg j⟩
  · intro b
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simp only [Fin.append_left]; exact ⟨hxpos j, (hx _).2⟩
    · simp only [Fin.append_right]
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
      · simp only [Fin.append_left]; exact ⟨hypos _, (hy _).2⟩
      · simp only [Fin.append_right]; exact ⟨hypos _, (hy _).2⟩
  · have h1 : k + m1 ≤ n := by omega
    exact (by exact_mod_cast h1 : ((k + m1 : ℕ) : ℝ) ≤ n).trans hKn
  · have h1 : k + m1 + (q + (r + s')) + 1 = n + 1 := by omega
    rw [h1]
    push_cast
    exact hTn
  · intro i
    exact (spike_count_split x y σx σy τ (θ i N)).trans (hsp i)
  · intro i
    obtain ⟨h0, h1⟩ := hcnt i
    refine ⟨h0, by omega, ?_⟩
    have h2 : q + (r + s') ≤ n := by omega
    exact (Nat.cast_le.mpr h2).trans (hnu i)

theorem Phase2Data.toBounds_α1 {I : ℕ} (D : Phase2Data I) : D.toBounds.α1 = D.α1 := rfl
theorem Phase2Data.toBounds_ncount {I : ℕ} (D : Phase2Data I) : D.toBounds.ncount = D.ncount := rfl
theorem Phase2Data.toBounds_lo {I : ℕ} (D : Phase2Data I) : D.toBounds.lo = D.lo := rfl
theorem Phase2Data.toBounds_hi {I : ℕ} (D : Phase2Data I) : D.toBounds.hi = D.hi := rfl
theorem Phase2Data.toBounds_κlo {I : ℕ} (D : Phase2Data I) : D.toBounds.κlo = D.κlo := rfl
theorem Phase2Data.toBounds_κhi {I : ℕ} (D : Phase2Data I) : D.toBounds.κhi = D.κhi := rfl
theorem Phase2Data.toBounds_Clsf {I : ℕ} (D : Phase2Data I) : D.toBounds.Clsf = D.Clsf := rfl
theorem Phase2Data.toBounds_FixAdm {I : ℕ} (D : Phase2Data I) : D.toBounds.FixAdm = D.FixAdm := rfl

/-- **The class-link data** (`hlink` of `Phase2Data.signedSecondSheetNearNd_nearOpt` for the
near-optimal class): the only things the data module supplies beyond the endpoint certificates are
the named constants and one-sided polynomial certificates below, every one a finite rational datum
or a pointwise inequality of one variable on `[-1, 1]` / a rational inequality in `α`.

* `Dtop`, `Dcap i`: caps of `excess α` on `[0, α1]` / on the interval `[lo i, hi i]` (affine in `α`:
  check the endpoints);
* `Cp i`, `Cm i` (`sP i`, `sM i` with `H·Dcap ≤ s²`): polynomials below the positive / negative
  indicator on `[-1,1] \ {0}`; with `hκlo`, `hκhi`, `hk0`, `hq2g` the κ-range, `0 < k`, `2 g < q`;
* `a0, dgap, ts, ηT` and the grid `tg` with polynomials `Ct j` below `1 - k_{tg j} - hmesh/ts`
  (Lemma T slope);
* `θ0, dsp, Mmax` (spike count) and `Kn, Tn`;
* the sup certificates `hsup` (free field below its cap by `dsp` on `(1-θ0, 1)`) and `hgap` (by
  `dgap` on `(-a0, a0) \ {0}`) of the factor-free OLD trial (same fields as the 532 trial). -/
structure LinkCert {I : ℕ} (D : Phase2Data I) (P : Parameters) (target residual nearCap cost : ℝ)
    (G : ℝ → Prop) (D0 : SecondTrialBoundsEnd P 0 target residual nearCap cost G) (δ e t0 c2 : ℝ) where
  Dcap : Fin I → ℝ
  hDcap : ∀ i, ∀ α ∈ Icc (D.lo i) (D.hi i), excess target cost t0 c2 δ (P.n0 : ℝ) α ≤ Dcap i
  Dtop : ℝ
  hDtop : ∀ α ∈ Icc (0 : ℝ) D.α1, excess target cost t0 c2 δ (P.n0 : ℝ) α ≤ Dtop
  -- the free sign counts
  Cp : Fin I → PolyCert
  Cm : Fin I → PolyCert
  sP : Fin I → ℝ
  sM : Fin I → ℝ
  hsP0 : ∀ i, 0 ≤ sP i
  hsM0 : ∀ i, 0 ≤ sM i
  hsP : ∀ i, certH (Cp i).K (Cp i).G * Dcap i ≤ sP i ^ 2
  hsM : ∀ i, certH (Cm i).K (Cm i).G * Dcap i ≤ sM i ^ 2
  hCp_neg : ∀ i, ∀ y ∈ Icc (-1 : ℝ) 1, y < 0 → evalCert e (Cp i).K (Cp i).G (Cp i).c0 y ≤ 0
  hCp_pos : ∀ i, ∀ y ∈ Icc (-1 : ℝ) 1, 0 < y → evalCert e (Cp i).K (Cp i).G (Cp i).c0 y ≤ 1
  hCm_neg : ∀ i, ∀ y ∈ Icc (-1 : ℝ) 1, y < 0 → evalCert e (Cm i).K (Cm i).G (Cm i).c0 y ≤ 1
  hCm_pos : ∀ i, ∀ y ∈ Icc (-1 : ℝ) 1, 0 < y → evalCert e (Cm i).K (Cm i).G (Cm i).c0 y ≤ 0
  hκlo : ∀ i, ∀ α ∈ Icc (D.lo i) (D.hi i),
    D.κlo i ≤ (1 - α) * (Cm i).c0 + certMean (Cm i).K (Cm i).G D0.p - sM i
  hκhi : ∀ i, ∀ α ∈ Icc (D.lo i) (D.hi i),
    (1 - α) - ((1 - α) * (Cp i).c0 + certMean (Cp i).K (Cp i).G D0.p - sP i) ≤ D.κhi i
  hk0 : ∀ i, 0 < D.κlo i
  hq2g : ∀ i, ∀ α ∈ Icc (D.lo i) (D.hi i),
    2 * (P.g0 : ℝ) / P.n0 < (1 - α) * (Cp i).c0 + certMean (Cp i).K (Cp i).G D0.p - sP i
  -- Lemma T (slope)
  a0 : ℝ
  ts : ℝ
  dgap : ℝ
  ηT : ℝ
  ha0 : 0 < a0
  hts : 0 < ts
  hdgap : 0 < dgap
  hηT : 0 < ηT
  hgap : ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 0 < |x| → |x| < a0 →
    freeRowX P N D0.p D0.v x ≤ D0.MX + δ / 4 - dgap
  hsmall : ∀ α ∈ Icc (0 : ℝ) D.α1,
    2 * (P.g0 : ℝ) / P.n0 + ηT < ((1 - α) - Dtop / dgap) * (a0 ^ 2 / (ts ^ 2 + a0 ^ 2))
  J : ℕ
  tg : Fin J → ℝ
  hmesh : ℝ
  htg : ∀ j, tg j ∈ Icc ts 1
  hcov : ∀ t ∈ Icc ts 1, ∃ j, |t - tg j| ≤ hmesh
  Ct : Fin J → PolyCert
  sT : Fin J → ℝ
  hsT0 : ∀ j, 0 ≤ sT j
  hsT : ∀ j, certH (Ct j).K (Ct j).G * Dtop ≤ sT j ^ 2
  hPt : ∀ j, ∀ y ∈ Icc (-1 : ℝ) 1, y ≠ 0 →
    evalCert e (Ct j).K (Ct j).G (Ct j).c0 y + hmesh / ts ≤ 1 - slopeKernel (tg j) y
  hmarg : ∀ j, ∀ α ∈ Icc (0 : ℝ) D.α1, 2 * (P.g0 : ℝ) / P.n0 + ηT ≤
    (1 - α) * (Ct j).c0 + certMean (Ct j).K (Ct j).G D0.p - sT j
  -- spikes and the canonical `Clsf`
  θ0 : ℝ
  dsp : ℝ
  hθ0 : 0 ≤ θ0
  hdsp : 0 < dsp
  hθi : ∀ i N, (D.DA i N).θ ≤ θ0
  hxcθ : D.xc ≤ 1 - θ0
  hxcnn : 0 ≤ D.xc
  hC1nn : 0 ≤ D.C1
  hsup : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (1 - θ0) 1,
    freeRowX P N D0.p D0.v x ≤ D0.MX + δ / 4 - dsp
  Kn : ℕ → ℝ
  Tn : ℕ → ℝ
  Mmax : ℕ → ℕ
  hKn : ∀ N, (P.n N : ℝ) ≤ Kn N
  hTn : ∀ N, (P.n N : ℝ) + 1 ≤ Tn N
  hMmax : ∀ N, (Dtop / dsp + D.C1 * θ0) * (P.n N : ℝ) + 1 ≤ (Mmax N : ℝ)
  -- the Heine count: offset `g` of the problem, reference count `0 < sp` with `sp + g` below the
  -- certified lower bound of the free positive count `q` on every interval (NOTES-ETA §5.7)
  hgA : ∀ i N, (D.DA i N).g = P.g N
  hspA : ∀ i N, 1 ≤ N → 0 < (D.DA i N).sp
  hspq : ∀ i i0 N, 1 ≤ N → ∀ α ∈ Icc (D.lo i0) (D.hi i0),
    ((D.DA i N).sp : ℝ) + P.g N ≤
      ((1 - α) * (Cp i0).c0 + certMean (Cp i0).K (Cp i0).G D0.p - sP i0) * P.n N
  hClsf : ∀ N k q m1 m2 xn gp yn yp,
    ClsfCanon (fun i N => (D.DA i N).θ) (fun i N => (D.DA i N).sp) (fun i N => (D.DA i N).g)
      (fun i N => (D.DA i N).ν) Kn Tn Mmax N k q m1 m2 xn gp yn yp →
    D.Clsf N k q m1 m2 xn gp yn yp

end HL5

section HL6

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

set_option maxHeartbeats 1600000 in
/-- **The class link `hlink` for the near-optimal class** (clauses 1-3 of the Phase 2 link):
Lemma T for ALL positive nodes of the sheet, `0 < k`, `2 g < q`, the κ-range of every α-interval,
the canonical `Clsf` (ranges, counts, total spike count `≤ Mmax`), and `FixAdm` for every splitting.
Everything is derived from the old-route violation `nearOptCls` (`free_facts`) and the data `L`
(`LinkCert`); the marked rows enter only through `MarkedCap` (the node set `Nd`). -/
theorem Phase2Data.hlink_nearOpt {I : ℕ} (D : Phase2Data I) {P : Parameters} (hP : Admissible P)
    {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D0 : SecondTrialBoundsEnd P 0 target residual nearCap cost G) {δ e : ℝ} (hδ : 0 < δ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D0.p j|) + 4 * (∑' j, |D0.v j|) + |D0.p 1| + 20) < δ / 2)
    (t0 c2 : ℝ) (hn : ∀ N, D.ncount N = P.n N)
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop)
    (hNd : ∀ N m y, (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → Nd N m y →
      MarkedCap D.gs D.xc D.C1 (D.ncount N : ℝ) (D.umin N) y)
    (L : LinkCert D P target residual nearCap cost G D0 δ e t0 c2) :
    SignedNearClassLinkNd P D.toBounds (nearOptCls P t0 c2 G) G Nd := by
  have hn0 : (0 : ℝ) < P.n0 := n0_pos hP
  have hηev : ∀ᶠ N : ℕ in atTop, 1 < (P.n N : ℝ) * L.ηT := by
    filter_upwards [D.hn_top.eventually_gt_atTop (1 / L.ηT)] with N hN
    have h1 : (P.n N : ℝ) = (D.ncount N : ℝ) := by rw [hn N]
    rw [h1]
    exact (div_lt_iff₀ L.hηT).1 hN
  unfold SignedNearClassLinkNd
  filter_upwards [free_facts hP D0 hδ he hec t0 c2, L.hsup, L.hgap, hηev,
    eventually_ge_atTop 2] with N hF hsup hgap hη hN2 p m hpm hmle x y hx hx0 hy hy0 hyG hNdy
    hzi hc
  have hνpos : (0 : ℝ) < P.n N := by exact_mod_cast n_pos hP (by omega : 0 < N)
  have hνD : (D.ncount N : ℝ) = P.n N := by rw [hn N]
  rw [Phase2Data.toBounds_α1, Phase2Data.toBounds_ncount, hνD] at hmle
  set α : ℝ := (m : ℝ) / (P.n N : ℝ) with hαdef
  have hα0 : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hνpos.le
  have hα1 : α ≤ D.α1 := by
    rw [hαdef, div_le_iff₀ hνpos]; linarith [hmle]
  obtain ⟨hcap, hbr, hsqf⟩ := hF p m hpm x hc
  have hΔ : excess target cost t0 c2 δ (P.n0 : ℝ) α ≤ L.Dtop := L.hDtop α ⟨hα0, hα1⟩
  have hpmR : (p : ℝ) + m = P.n N := by exact_mod_cast hpm
  have hpν : (p : ℝ) / (P.n N : ℝ) = 1 - α := by
    rw [hαdef]; field_simp; linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hgr : 2 * (P.g N : ℝ) / (P.n N : ℝ) = 2 * (P.g0 : ℝ) / P.n0 := by
    simp only [Parameters.g, n_cast]
    push_cast
    field_simp
  have hreg : ∀ (dd : ℝ) (S : Finset (Fin p)), 0 < dd →
      (∀ i ∈ S, freeRowX P N D0.p D0.v (x i) ≤ D0.MX + δ / 4 - dd) →
      (S.card : ℝ) ≤ (P.n N : ℝ) * L.Dtop / dd := by
    intro dd S hdd hS
    have h1 := card_region_le hνpos (fun i => freeRowX P N D0.p D0.v (x i)) S hcap hS hbr
    rw [le_div_iff₀ hdd]
    exact h1.trans (mul_le_mul_of_nonneg_left hΔ hνpos.le)
  have hM := hNd N m y hy hNdy
  -- Lemma T
  have hfree : ∀ t ∈ Ioc (0 : ℝ) 1, 2 * (P.g N : ℝ) + 1 < ∑ i, (1 - slopeKernel t (x i)) := by
    refine free_slope_gt (ν := (P.n N : ℝ)) (e := e) (gg := (P.g N : ℝ)) hνpos he x hx hx0
      D0.p D0.p_summable hsqf hΔ L.ha0 L.hts L.hdgap ?_ hη ?_ L.tg L.hmesh L.htg L.hcov L.Ct
      L.sT L.hsT0 L.hsT L.hPt ?_
    · exact hreg L.dgap _ L.hdgap (fun i hi => hgap (x i) (abs_pos.2 (hx0 i))
        (by simpa using hi))
    · rw [hgr, hpν]; exact L.hsmall α ⟨hα0, hα1⟩
    · intro j; rw [hgr, hpν]; exact L.hmarg j α ⟨hα0, hα1⟩
  refine ⟨lemmaT_of_free hP hN2 hpm x y hx hx0 hy hy0 hzi hfree, ?_⟩
  intro k q m1 m2' σx σy hxneg hxpos hyneg hypos
  have hm12 : m1 + m2' = m := by simpa using Fintype.card_congr σy
  have hkq : k + q = p := by simpa using Fintype.card_congr σx
  have hαeq : ((m1 + m2' : ℕ) : ℝ) / (D.toBounds.ncount N : ℝ) = α := by
    rw [hm12, Phase2Data.toBounds_ncount, hνD]
  have hsign : ∀ i, α ∈ Icc (D.lo i) (D.hi i) →
      (1 - α) * (L.Cp i).c0 + certMean (L.Cp i).K (L.Cp i).G D0.p - L.sP i ≤
        (q : ℝ) / (P.n N : ℝ) ∧
      (1 - α) * (L.Cm i).c0 + certMean (L.Cm i).K (L.Cm i).G D0.p - L.sM i ≤
        (k : ℝ) / (P.n N : ℝ) := by
    intro i hi
    have h := sign_lower hνpos he σx x hx hxneg hxpos D0.p D0.p_summable hsqf (L.hDcap i α hi)
      (L.Cp i) (L.Cm i) (L.hsP0 i) (L.hsM0 i) (L.hsP i) (L.hsM i) (L.hCp_neg i) (L.hCp_pos i)
      (L.hCm_neg i) (L.hCm_pos i)
    rw [hpν] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨i0, h1, h2⟩ := D.cover α hα0 hα1
    have hs := (hsign i0 ⟨h1, h2⟩).2
    have hk := L.hκlo i0 α ⟨h1, h2⟩
    have hk0 := L.hk0 i0
    have : 0 < (k : ℝ) / (P.n N : ℝ) := by linarith
    have hkpos : (0 : ℝ) < k := (div_pos_iff_of_pos_right hνpos).1 this
    exact_mod_cast hkpos
  · obtain ⟨i0, h1, h2⟩ := D.cover α hα0 hα1
    have hs := (hsign i0 ⟨h1, h2⟩).1
    have hq := L.hq2g i0 α ⟨h1, h2⟩
    have h3 : 2 * (P.g N : ℝ) / (P.n N : ℝ) < (q : ℝ) / (P.n N : ℝ) := by
      rw [hgr]; linarith
    have h4 : 2 * (P.g N : ℝ) < q := (div_lt_div_iff_of_pos_right hνpos).1 h3
    exact_mod_cast h4
  · intro i hlo hhi
    rw [Phase2Data.toBounds_lo, hαeq] at hlo
    rw [Phase2Data.toBounds_hi, hαeq] at hhi
    have hs := hsign i ⟨hlo, hhi⟩
    show D.κlo i ≤ (k : ℝ) / (D.ncount N : ℝ) ∧ (k : ℝ) / (D.ncount N : ℝ) ≤ D.κhi i
    rw [hνD]
    refine ⟨(L.hκlo i α ⟨hlo, hhi⟩).trans hs.2, ?_⟩
    have hkq' : (k : ℝ) / (P.n N : ℝ) = (p : ℝ) / (P.n N : ℝ) - (q : ℝ) / (P.n N : ℝ) := by
      have : (k : ℝ) = p - q := by
        have : (k : ℝ) + q = p := by exact_mod_cast hkq
        linarith
      rw [this, sub_div]
    rw [hkq', hpν]
    have := L.hκhi i α ⟨hlo, hhi⟩
    linarith [hs.1]
  · intro r s' τ
    refine ⟨?_, ?_⟩
    · -- the canonical `Clsf`
      show D.Clsf N k q m1 (r + s') _ _ _ _
      refine L.hClsf N k q m1 (r + s') _ _ _ _ ?_
      have hq2 : 2 * P.g N < q := by
        obtain ⟨i0, h1, h2⟩ := D.cover α hα0 hα1
        have hs := (hsign i0 ⟨h1, h2⟩).1
        have hq := L.hq2g i0 α ⟨h1, h2⟩
        have h3 : 2 * (P.g N : ℝ) / (P.n N : ℝ) < (q : ℝ) / (P.n N : ℝ) := by
          rw [hgr]; linarith
        have h4 : 2 * (P.g N : ℝ) < q := (div_lt_div_iff_of_pos_right hνpos).1 h3
        exact_mod_cast h4
      refine canon_of_split (fun i N => (D.DA i N).θ) (fun i N => (D.DA i N).sp)
        (fun i N => (D.DA i N).g) (fun i N => (D.DA i N).ν) L.Kn L.Tn L.Mmax N hpm x y hx hy
        σx σy τ hxneg hxpos hyneg hypos (L.hKn N) (L.hTn N) ?_ ?_ ?_
      rotate_left
      · intro i
        refine ⟨L.hspA i N (by omega), ?_⟩
        rw [L.hgA i N]
        obtain ⟨i0, h1, h2⟩ := D.cover α hα0 hα1
        have hs := (hsign i0 ⟨h1, h2⟩).1
        have hb := L.hspq i i0 N (by omega) α ⟨h1, h2⟩
        have h3 : ((L.Cp i0).c0 * (1 - α) + certMean (L.Cp i0).K (L.Cp i0).G D0.p - L.sP i0) *
            (P.n N : ℝ) ≤ q := by
          have := mul_le_mul_of_nonneg_right hs hνpos.le
          rw [div_mul_cancel₀ _ hνpos.ne'] at this
          linarith
        have h4 : ((D.DA i N).sp : ℝ) + P.g N ≤ q := by linarith
        exact_mod_cast h4
      · intro i
        rw [D.hν i N, hνD]
      intro i
      have hcx0 : ((Finset.univ.filter (fun v => 1 - L.θ0 < x v)).card : ℝ) ≤
          (P.n N : ℝ) * L.Dtop / L.dsp :=
        hreg L.dsp _ L.hdsp (fun i hi => hsup (x i)
          ⟨by simpa using hi, (hx i).2⟩)
      have hcy0 := top_count_le y hM.2.2 L.hxcθ L.hθ0 L.hC1nn (Nat.cast_nonneg _)
      rw [hνD] at hcy0
      have hcx : (Finset.univ.filter (fun v => 1 - (D.DA i N).θ < x v)).card ≤
          (Finset.univ.filter (fun v => 1 - L.θ0 < x v)).card := card_spike_mono x (L.hθi i N)
      have hcy : (Finset.univ.filter (fun v => 1 - (D.DA i N).θ < y v)).card ≤
          (Finset.univ.filter (fun v => 1 - L.θ0 < y v)).card := card_spike_mono y (L.hθi i N)
      have hMm := L.hMmax N
      have : (((Finset.univ.filter (fun v => 1 - (D.DA i N).θ < x v)).card +
          (Finset.univ.filter (fun v => 1 - (D.DA i N).θ < y v)).card : ℕ) : ℝ) ≤
          (L.Mmax N : ℝ) := by
        push_cast
        have e1 : (P.n N : ℝ) * L.Dtop / L.dsp = L.Dtop / L.dsp * (P.n N : ℝ) := by ring
        have h1 : ((Finset.univ.filter (fun v => 1 - (D.DA i N).θ < x v)).card : ℝ) ≤
            (Finset.univ.filter (fun v => 1 - L.θ0 < x v)).card := by exact_mod_cast hcx
        have h2 : ((Finset.univ.filter (fun v => 1 - (D.DA i N).θ < y v)).card : ℝ) ≤
            (Finset.univ.filter (fun v => 1 - L.θ0 < y v)).card := by exact_mod_cast hcy
        nlinarith [hcx0, hcy0, hMm, h1, h2, e1]
      exact_mod_cast this
    · show D.FixAdm N m1 r s' _ _ _
      exact fixAdmCap_of_marked L.hxcnn hM σy hyneg hypos τ

end HL6

section HL7

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

/-- **End-to-end with the near-optimal class and the class-link certificate**: the signed
second-case sheet bound from the Phase 2 endpoint data `D` and the class-link data `L`
(`LinkCert`); no `hlink`, no `hnon`. -/
theorem Phase2Data.signedSecondSheetNearNd_nearOpt_of_cert {I : ℕ} (D : Phase2Data I)
    {P : Parameters} (hP : Admissible P) (G : ℝ → Prop) (target0 c2 : ℝ)
    (hn : ∀ N, D.ncount N = P.n N)
    (hconst : ∀ N r a b, r + a + b = P.n N →
      D.constant N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b)
    (hRf : ∀ N, D.Rf N = populationPhysicalFreeField P N)
    (hRm : ∀ N, D.Rm N = groupedMarkedField P N)
    (hRn : ∀ N, D.Rn N = groupedNearField P N)
    (hCf : ∀ N, D.Cf N = populationPhysicalColumnField P N (0 + 0))
    (hLRf : ∀ N k q m1 m2' xn gp yn yp', D.LRf N k q m1 m2' xn gp yn yp' =
      logRatioZ (q + m2' - P.g N) (Fin.append xn yn) (Fin.append gp yp'))
    (hB : D.B = -target0 + Real.log 2 / 2)
    (hcost : D.cost * (P.n0 : ℝ) ≤ c2)
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop)
    (hNd : ∀ N m y, (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → Nd N m y →
      MarkedCap D.gs D.xc D.C1 (D.ncount N : ℝ) (D.umin N) y)
    {target residual nearCap cost : ℝ} (D0 : SecondTrialBoundsEnd P 0 target residual nearCap cost G)
    {δ e : ℝ} (hδ : 0 < δ) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D0.p j|) + 4 * (∑' j, |D0.v j|) + |D0.p 1| + 20) < δ / 2)
    (L : LinkCert D P target residual nearCap cost G D0 δ e target0 c2) :
    SignedSecondSheetCoreNd P G Nd target0 c2 D.α1 :=
  D.signedSecondSheetNearNd_nearOpt hP G target0 c2 hn hconst hRf hRm hRn hCf hLRf hB hcost Nd
    (D.hlink_nearOpt hP D0 hδ he hec target0 c2 hn Nd hNd L)

end HL7

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.Phase2Data.signedSecondSheetNear

#print axioms CatalanMeasure.Signed.fixedSum_ends
#print axioms CatalanMeasure.Signed.Phase2Data.toBounds
#print axioms CatalanMeasure.Signed.Phase2Data.toBounds_ZB
#print axioms CatalanMeasure.Signed.FixAdmCap_mono
#print axioms CatalanMeasure.Signed.Phase2Data.hFix
#print axioms CatalanMeasure.Signed.fixAdmCap_of_marked
#print axioms CatalanMeasure.Signed.hnon_nearOpt
#print axioms CatalanMeasure.Signed.Phase2Data.signedSecondSheetNear_nearOpt
#print axioms CatalanMeasure.Signed.Phase2Data.signedSecondSheetNearNd_nearOpt
#print axioms CatalanMeasure.Signed.Phase2Data.fixAdm_of_nodeSub
#print axioms CatalanMeasure.Signed.pairCls_of_cert
#print axioms CatalanMeasure.Signed.hCls_of_cert
#print axioms CatalanMeasure.Signed.top_count_le
#print axioms CatalanMeasure.Signed.spike_count_split
#print axioms CatalanMeasure.Signed.free_facts
#print axioms CatalanMeasure.Signed.stat_poly_ge
#print axioms CatalanMeasure.Signed.slopeKernel_lip
#print axioms CatalanMeasure.Signed.free_slope_gt
#print axioms CatalanMeasure.Signed.lemmaT_of_free
#print axioms CatalanMeasure.Signed.sign_lower
#print axioms CatalanMeasure.Signed.canon_of_split
#print axioms CatalanMeasure.Signed.hCls_of_canon
#print axioms CatalanMeasure.Signed.Phase2Data.hlink_nearOpt
#print axioms CatalanMeasure.Signed.Phase2Data.signedSecondSheetNearNd_nearOpt_of_cert
