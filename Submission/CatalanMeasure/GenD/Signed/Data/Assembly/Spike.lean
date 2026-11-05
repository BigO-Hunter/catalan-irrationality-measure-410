module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Data
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeK0
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeK1
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeK2
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeCount
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkExcess

@[expose] public section

/-!
# 410 assembly: the spike data (`cp`, `err_small`, the certificates of `hCls_of_canon`)

* `cp i N α = 1/1024 = θ` (`cp_pos`, `cp_le`, `cp_theta`);
* `err_small410`: `errJ3 ≤ ε` eventually for the family (`4 e_N · 1024 + 14 / (58 N) → 0`);
* `famD_refTrial`: the hypothesis package `RefTrial` of the spike certificates for `famD X N`, `N ≥ 1`
  (`ν = 58 N`, `sp = 20 N`, `θ = 1/1024`, `e ≤ 2^-30`, phantom charge `kph = 14`, `Kn = ν`, `Tn = ν + 1`);
* `hcertA`: the certificate hypothesis of `hcert_form` for one trial, from its `spikeCert_t`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.Consts OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Cert

set_option maxRecDepth 1000000

noncomputable section

theorem log1024_le : Real.log (1 / (1 / 1024 : ℝ)) ≤ 69316 / 10000 := by
  have h : (1 : ℝ) / (1 / 1024) = 2 ^ 10 := by norm_num
  rw [h, Real.log_pow]
  have := Real.log_two_lt_d9
  push_cast
  norm_num at this ⊢
  linarith

theorem err_small410 (X : FamPar) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((famD X N).withCount (58 * N)).errJ3 (1 / 1024) (58 * N) ≤ ε := by
  -- errJ3 = (4 e / c') (sp'/ν) (nrows/ν) + kph/ν with sp' = 58 N = ν, nrows = 58 N
  have h1 : ∀ᶠ N : ℕ in atTop, (4 : ℝ) * 1024 / 2 ^ 30 / ((N : ℝ) + 1) < ε / 2 := by
    have : Tendsto (fun N : ℕ => (4 : ℝ) * 1024 / 2 ^ 30 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop natCast_add_one_tendsto
    exact this.eventually (gt_mem_nhds (by linarith))
  have h2 : ∀ᶠ N : ℕ in atTop, (14 : ℝ) / (58 * (N : ℝ)) < ε / 2 := by
    have : Tendsto (fun N : ℕ => (14 : ℝ) / (58 * (N : ℝ))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    exact this.eventually (gt_mem_nhds (by linarith))
  filter_upwards [h1, h2, eventually_gt_atTop 0] with N a b hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold SignedData.errJ3
  show (4 * dampE N / (1 / 1024)) * (((58 * N : ℕ) : ℝ) / (58 * (N : ℝ))) *
      (((58 * N : ℕ) : ℝ) / (58 * (N : ℝ))) + 14 / (58 * (N : ℝ)) ≤ ε
  have e1 : ((58 * N : ℕ) : ℝ) / (58 * (N : ℝ)) = 1 := by push_cast; field_simp
  rw [e1]
  unfold dampE
  have : 4 * (1 / 2 ^ 30 / ((N : ℝ) + 1)) / (1 / 1024) = (4 : ℝ) * 1024 / 2 ^ 30 / ((N : ℝ) + 1) := by
    field_simp
  rw [this]
  linarith

/-- `RefTrial` for `famD X N`. -/
theorem famD_refTrial (X : FamPar) {N : ℕ} (hN : 0 < N) {A1q B1q BRq : ℚ}
    (htZ : tailZB X.T.a.tail = true) (hBR : brQ X.T.R.f ≤ BRq)
    (hph : (58 * (2 * (A1q : ℝ) + BRq + 69316 / 10000 + (40 / 58) * B1q + (X.CSP : ℝ) / 58) +
      69316 / 10000 ≤ 812))
    (hKT : True) :
    RefTrial (famD X N) N X.bs X.T.a.f X.T.a.tail X.CSP A1q B1q (BRq : ℝ) ((58 * N : ℕ) : ℝ)
      (((58 * N : ℕ) : ℝ) + 1) where
  hb := rfl
  ha := rfl
  hta := htZ
  hN := hN
  hsp := rfl
  hν := by show 58 * (N : ℝ) = _; rfl
  hθ := rfl
  he0 := (dampE_pos N).le
  he := dampE_le N
  hcs := le_refl _
  hkph := by show (0 : ℝ) ≤ 14; norm_num
  hBR := by
    refine hBR_of (famD X N) X.T.R.f rfl ?_ (by exact_mod_cast hBR)
    have h := famD_tau_mem X N
    show |(1 - dampE N) * (1 - 1 / 1024)| ≤ 1
    rw [abs_of_nonneg (by have := h.1; simp only [famD_tau] at this; nlinarith)]
    have := h.1
    simp only [famD_tau] at this
    nlinarith [dampE_pos N]
  hKn := by show ((58 * N : ℕ) : ℝ) ≤ 58 * (N : ℝ); push_cast; exact le_refl _
  hph := by
    show 2 * (58 * (N : ℝ)) * (A1q : ℝ) + 58 * (N : ℝ) * (BRq : ℝ) +
      (((58 * N : ℕ) : ℝ) + 1) * Real.log (1 / (1 / 1024 : ℝ)) + 2 * (((20 * N : ℕ) : ℝ)) * (B1q : ℝ) +
      58 * (N : ℝ) * ((X.CSP : ℝ) / 58) ≤ 58 * (N : ℝ) * 14
    have hL := log1024_le
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    push_cast
    have h3 := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ N by linarith)
    nlinarith [h3, hL, hph, hN1]

/-- The certificate hypothesis of `hcert_form` for the family member of one trial. -/
theorem hcertA (X : FamPar) {A1q B1q BRq : ℚ} {fa : List ℚ} {ta : List TailQ}
    (hfa : fa = X.T.a.f) (hta : ta = X.T.a.tail)
    (htZ : tailZB X.T.a.tail = true) (hBR : brQ X.T.R.f ≤ BRq)
    (hph : (58 * (2 * (A1q : ℝ) + BRq + 69316 / 10000 + (40 / 58) * B1q + (X.CSP : ℝ) / 58) +
      69316 / 10000 ≤ 812))
    (sc : ∀ {D : SignedData} {N : ℕ} {BR Kn Tn : ℝ}, RefTrial D N X.bs fa ta X.CSP A1q B1q BR Kn Tn →
      ∀ x m : ℕ, D.sp ≤ x → (x : ℝ) ≤ D.ν → 100 * m ≤ 57 * N →
        Nonempty (SpikeTrialCert (D.withCount x) m (rhoSel N x m) Kn Tn)) :
    ∀ᶠ N : ℕ in atTop, ∀ (x m : ℕ), (famD X N).sp ≤ x → (x : ℝ) ≤ (famD X N).ν → 100 * m ≤ 57 * N →
      Nonempty (SpikeTrialCert ((famD X N).withCount x) m (rhoSel N x m) ((58 * N : ℕ) : ℝ)
        (((58 * N : ℕ) : ℝ) + 1)) := by
  subst hfa hta
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact sc (famD_refTrial X hN htZ hBR hph trivial)

end

end CatalanMeasure.GenD.Signed.Data.Assembly
