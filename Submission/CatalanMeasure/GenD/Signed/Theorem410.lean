module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Near
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Link
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.RowsInst
public import Submission.CatalanMeasure.GenD.Signed.Data.S1.TrialEnd590
public import Submission.CatalanMeasure.GenD.Signed.Gate
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Hosts532Inst

@[expose] public section
set_option Elab.async false

/-!
# `μ(G) ≤ 410`

`measure_of_design Odd.design` with the 532 denominator side (normalizer, growth, nonvanishing) and the
Theorem A decay side: `delta_small_410` (first case, large case, signed near case, S1 weights),
`pay410_w35`, `gain_ok410`.
`catalan_irrationalityMeasure_410_of_rows` takes the ingredient rows (`Rows410`) and the class-link
data; `catalan_irrationalityMeasure_410_of_cells` instantiates them with the row producers, from the
cell statements of the three trials (`CellsQ0`, `CellsQ1`, `CellsQ2`).
-/

namespace CatalanMeasure.GenD.Signed
open CatalanMeasure.GenD Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank535
open CatalanMeasure.GenD.Uniform.Bank532 CatalanMeasure.GenD.Signed.Data.Assembly
open CatalanMeasure.Signed.Consts (mmaxOf s410)
open CatalanMeasure.GenD.D58.Cert590 (Pc P)
open CatalanMeasure.Signed
open CatalanMeasure.GenD.D58 CatalanMeasure.GenD.Uniform CatalanMeasure.GenD.Analytic CatalanMeasure.CellCert

noncomputable section

theorem catalan_irrationalityMeasure_410_of_near
    (hnear : FreeNearBound D58.Odd.design G410 (CatalanMeasure.Signed.NodeSub nodesτ)
      K590.target0 c2_410 (1 / 16)) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(410 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  have hfirst := Data.S1.freeFirst0 Bank540.first rfl rfl rfl
  have hlarge := Data.S1.freeLarge0 Bank540.second rfl rfl
  have h := measure_of_design D58.Odd.design
    { B := 410
      Z := canonicalNormalizer design D58.Odd.design_admissible (famLB (fams532 hosts532)) 79
        (by rw [D58.Odd.design_H]; norm_num)
      w := 3 / 5, ρ := K590.rhoEnd (879663 / 10000), η := 3833924 / 100000,
      κ := 410 / K590.rhoEnd (879663 / 10000), δ := D58.delta
      pay := by
        rw [D58.n0_sub_g0]
        exact pay410_w35
      gD := gDg gain532
      D_growth := fun ε hε => by
        filter_upwards [partial_growth532 hosts532 hε] with N hN
        unfold gDg
        convert hN using 2
      tΔ := 58 ^ 2 * (K590.target0 - Real.log 2 / 2)
      delta_small := delta_small_410 hfirst hnear hlarge
      eta_le := gain_ok410 _ (829824 / 100000) _
        (by unfold Bank540.tDelta; nlinarith [K590.target0_sub]) gain532_ge le_rfl
      nonvanishing := D58.nonvanishing_d58 D58.C3.c3_d58 }
  simpa [catalan] using h

/-- **`μ(G) ≤ 410`** from the ingredient rows and the spike class. -/
theorem catalan_irrationalityMeasure_410_of_rows (R : Rows410)
    (hCls : ∀ N k q m1 m2 xn gp yn yp,
      ClsfCanon (fun i N => ((phase2 R).DA i N).θ) (fun i N => ((phase2 R).DA i N).sp)
        (fun i N => ((phase2 R).DA i N).g) (fun i N => ((phase2 R).DA i N).ν)
        (fun N => ((58 * N : ℕ) : ℝ)) (fun N => ((58 * N : ℕ) : ℝ) + 1) (mmaxOf s410) N k q m1 m2
        xn gp yn yp → (phase2 R).Clsf N k q m1 m2 xn gp yn yp) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(410 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  have hp : (Data.S1.secondEnd Bank540.second rfl rfl).p = trialSeqS Pc P := rfl
  exact catalan_irrationalityMeasure_410_of_near
    (hnear410 R (Data.S1.secondEnd Bank540.second rfl rfl) (δ := 13 / 100000) (e := eL)
      (by norm_num) ⟨eL_mem.1, eL_mem.2⟩
      (hec410' _ hp rfl)
      (link410 R _ hp rfl rfl hCls))

/-- **`μ(G) ≤ 410`** from the cell statements of the three endpoint trials. -/
theorem catalan_irrationalityMeasure_410_of_cells (C0 : RowsQ0.CellsQ0) (C1 : RowsQ1.CellsQ1)
    (C2 : RowsQ2.CellsQ2) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(410 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  catalan_irrationalityMeasure_410_of_rows (rows410 C0 C1 C2) (fun _ _ _ _ _ _ _ _ _ h => h)

end
end CatalanMeasure.GenD.Signed
#print axioms CatalanMeasure.GenD.Signed.catalan_irrationalityMeasure_410_of_near
#print axioms CatalanMeasure.GenD.Signed.catalan_irrationalityMeasure_410_of_rows
#print axioms CatalanMeasure.GenD.Signed.catalan_irrationalityMeasure_410_of_cells
