module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Spike
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell

@[expose] public section

/-!
# 410 assembly: the spike class (`hCls`)

`hCls_of_canon` for the two intervals: interpolation compatibility and regularity of the family
members (`famD_compat`, `famD_regular`), the spike environment from a Frostman bound
`frLim ≤ S0 < Sup` of each trial (`famD_spikeEnv`; the bound is the FR cell of the trial, a
hypothesis here), and the spike certificates of the three trials (`spikeCert{t}` through `hcertA`,
paired by `hcert_form`).
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.Consts OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Cert

noncomputable section

/-- The spike parameter of the class: `cp = θ = 1/1024`. -/
def cp410 : Fin 2 → ℕ → ℝ → ℝ := fun _ _ _ => 1 / 1024

theorem hcert0 : ∀ᶠ N : ℕ in atTop, ∀ (x m : ℕ), (famD X0 N).sp ≤ x → (x : ℝ) ≤ (famD X0 N).ν →
    100 * m ≤ 57 * N → Nonempty (SpikeTrialCert ((famD X0 N).withCount x) m (rhoSel N x m)
      ((58 * N : ℕ) : ℝ) (((58 * N : ℕ) : ℝ) + 1)) :=
  hcertA X0 (fa := fa0) (ta := ta0) (A1q := 469 / 256) (B1q := 1241 / 1024) (BRq := T0.BRq) rfl rfl
    (by decide +kernel) T0.br_le (by norm_num [X0, T0.BRq]) (fun T => spikeCert0 T)

theorem hcert1 : ∀ᶠ N : ℕ in atTop, ∀ (x m : ℕ), (famD X1 N).sp ≤ x → (x : ℝ) ≤ (famD X1 N).ν →
    100 * m ≤ 57 * N → Nonempty (SpikeTrialCert ((famD X1 N).withCount x) m (rhoSel N x m)
      ((58 * N : ℕ) : ℝ) (((58 * N : ℕ) : ℝ) + 1)) :=
  hcertA X1 (fa := fa1) (ta := ta1) (A1q := 1861 / 1024) (B1q := 309 / 256) (BRq := T1.BRq) rfl rfl
    (by decide +kernel) T1.br_le (by norm_num [X1, T1.BRq]) (fun T => spikeCert1 T)

theorem hcert2 : ∀ᶠ N : ℕ in atTop, ∀ (x m : ℕ), (famD X2 N).sp ≤ x → (x : ℝ) ≤ (famD X2 N).ν →
    100 * m ≤ 57 * N → Nonempty (SpikeTrialCert ((famD X2 N).withCount x) m (rhoSel N x m)
      ((58 * N : ℕ) : ℝ) (((58 * N : ℕ) : ℝ) + 1)) :=
  hcertA X2 (fa := fa2) (ta := ta2) (A1q := 983 / 512) (B1q := 1181 / 1024) (BRq := T2.BRq) rfl rfl
    (by decide +kernel) T2.br_le (by norm_num [X2, T2.BRq]) (fun T => spikeCert2 T)

theorem hcert410 : ∀ i, ∀ᶠ N : ℕ in atTop, ∀ (x m : ℕ), (DA410 i N).sp ≤ x →
    (x : ℝ) ≤ (DA410 i N).ν → 2 * m ≤ mmaxOf s410 N + 1 →
    ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ (DA410 i N).τ ^ 2 * (1 - (DA410 i N).θ) ∧
      Nonempty (SpikeTrialCert ((DA410 i N).withCount x) m ρ ((58 * N : ℕ) : ℝ) (((58 * N : ℕ) : ℝ) + 1)) ∧
      Nonempty (SpikeTrialCert ((DB410 i N).withCount x) m ρ ((58 * N : ℕ) : ℝ) (((58 * N : ℕ) : ℝ) + 1)) :=
  hcert_form (Kn := fun N => ((58 * N : ℕ) : ℝ)) (Tn := fun N => ((58 * N : ℕ) : ℝ) + 1)
    (fun i N => by fin_cases i <;> rfl)
    (fun i N => by fin_cases i <;> exact (dampE_pos N).le)
    (fun i N => by fin_cases i <;> exact dampE_le N)
    mmax410_hMm (fun i N => by fin_cases i <;> rfl) (fun i N => by fin_cases i <;> rfl)
    (Fin.forall_fin_two.2 ⟨hcert0, hcert1⟩) (Fin.forall_fin_two.2 ⟨hcert1, hcert2⟩)

/-- **`hCls` of `Rows410`** for the canonical class, from the Frostman bounds of the three trials. -/
theorem hCls410 {S0 S1 S2 : ℝ}
    (hfr0 : ∀ x ∈ Icc (-1 : ℝ) 1, frLim X0.T.form x ≤ S0) (hg0 : S0 < X0.T.Sup)
    (hfr1 : ∀ x ∈ Icc (-1 : ℝ) 1, frLim X1.T.form x ≤ S1) (hg1 : S1 < X1.T.Sup)
    (hfr2 : ∀ x ∈ Icc (-1 : ℝ) 1, frLim X2.T.form x ≤ S2) (hg2 : S2 < X2.T.Sup) :
    ∀ i, ∀ᶠ N : ℕ in atTop, ∀ α k q m1 m2 xn gp yn yp,
      ClsfCanon (fun i N => (DA410 i N).θ) (fun i N => (DA410 i N).sp) (fun i N => (DA410 i N).g)
        (fun i N => (DA410 i N).ν) (fun N => ((58 * N : ℕ) : ℝ)) (fun N => ((58 * N : ℕ) : ℝ) + 1)
        (mmaxOf s410) N k q m1 m2 xn gp yn yp →
      (0 < (DA410 i N).sp ∧ (DA410 i N).sp + (DA410 i N).g ≤ q + m2) ∧
      Nonempty (PairCls ((DA410 i N).withCount (q + m2 - (DA410 i N).g))
        ((DB410 i N).withCount (q + m2 - (DA410 i N).g)) (cp410 i N α) xn gp yn yp) := by
  have ok0 : ∀ C : ℝ, (X0.Cb : ℝ) ≤ C → X0.T.DataOK C := fun C hC => T0.dataOK hC
  have ok1 : ∀ C : ℝ, (X1.Cb : ℝ) ≤ C → X1.T.DataOK C := fun C hC => T1.dataOK hC
  have ok2 : ∀ C : ℝ, (X2.Cb : ℝ) ≤ C → X2.T.DataOK C := fun C hC => T2.dataOK hC
  have hK : X0.bs.length = X1.bs.length := by decide +kernel
  have hK' : X1.bs.length = X2.bs.length := by decide +kernel
  have hη : (X0.T.η : ℝ) = X1.T.η := by norm_num [X0, X1, T0.trial, T1.trial]
  have hη' : (X1.T.η : ℝ) = X2.T.η := by norm_num [X1, X2, T1.trial, T2.trial]
  have r0 : ∀ N, SignedRegular (famD X0 N) := famD_regular X0 ok0 (by norm_num [X0, T0.Cb])
  have r1 : ∀ N, SignedRegular (famD X1 N) := famD_regular X1 ok1 (by norm_num [X1, T1.Cb])
  have r2 : ∀ N, SignedRegular (famD X2 N) := famD_regular X2 ok2 (by norm_num [X2, T2.Cb])
  have E0 := famD_spikeEnv X0 ok0 rfl hfr0 hg0
  have E1 := famD_spikeEnv X1 ok1 rfl hfr1 hg1
  have E2 := famD_spikeEnv X2 ok2 rfl hfr2 hg2
  exact hCls_of_canon (DA := DA410) (DB := DB410) cp410
    (Fin.forall_fin_two.2 ⟨Eventually.of_forall (famD_compat X0 X1 hK hη),
      Eventually.of_forall (famD_compat X1 X2 hK' hη')⟩)
    (Fin.forall_fin_two.2 ⟨Eventually.of_forall r0, Eventually.of_forall r1⟩)
    (Fin.forall_fin_two.2 ⟨Eventually.of_forall r1, Eventually.of_forall r2⟩)
    (Fin.forall_fin_two.2 ⟨E0, E1⟩) (Fin.forall_fin_two.2 ⟨E1, E2⟩)
    (fun N => ((58 * N : ℕ) : ℝ)) (fun N => ((58 * N : ℕ) : ℝ) + 1) (mmaxOf s410) hcert410

end

end CatalanMeasure.GenD.Signed.Data.Assembly
