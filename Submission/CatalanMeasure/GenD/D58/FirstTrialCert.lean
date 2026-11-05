module

public import Submission.CatalanMeasure.GenD.D58.FirstBridge
public import Submission.CatalanMeasure.GenD.D58.FirstCert.Sup

@[expose] public section

/-!
# D58: the first-trial contract with the cover certificate discharged

`hrow` / `hcol` of `FirstTrial` follow from the D58 first-trial cover certificate (`FirstCert.row_sup`,
`FirstCert.column_sup`: integer-root gaps and bracket value checks) via the field identification in
`FirstBridge`.  `hrow_D58` and `hcol_D58` carry no hypotheses; each bank instantiates `firstTrial_D58` with them.
-/

namespace CatalanMeasure.GenD
namespace D58
open Set OAI.InternalCatalan CatalanMeasure.Cert CatalanMeasure.CellCert
open CatalanMeasure.GenD.Analytic
noncomputable section

theorem hrow_D58 : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    firstRowFieldG (11 / 29) (3 / 29) (49 / 58) lamFirst (5 / 29) firstP firstV x ≤ MX1 := by
  intro x hx
  rw [firstRowFieldG_D58_eq]
  have h := FirstCert.row_sup x hx
  have e : ((FirstCert.MX : ℚ) : ℝ) = MX1 := by norm_num [FirstCert.MX, MX1]
  rw [e] at h
  exact h

theorem hcol_D58 : ∀ s ∈ Ioo (0 : ℝ) 1,
    colFieldG (9 / 58) (3 / 58) firstV s ≤ MY1 := by
  intro s hs
  rw [colFieldG_D58_eq]
  have h := FirstCert.column_sup s hs
  have e : ((FirstCert.MY : ℚ) : ℝ) = MY1 := by norm_num [FirstCert.MY, MY1]
  rw [e] at h
  exact h

end
end D58
end CatalanMeasure.GenD
