module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalNorm
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T0Data

@[expose] public section

/-!
# Weighted norms of the trial sequences (Theorem A, lane E1, item 10): part P of trial 0

One module per (trial, value) so that each stays below ~6 GB (the single module EvalNormT took 500 s and 7.5 GB).
The statements are those of the former single module; `EvalNormT` imports all parts.
-/

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalNormT
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNorm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.Cert (TailQ normOK)
open OAI.InternalCatalan (barrierTrialNormSq)
open CatalanMeasure.Signed.FieldForm (tseq)

set_option maxRecDepth 1000000
set_option Elab.async false

theorem norm_p_le_0 : barrierTrialNormSq (tseq (fQ T0.trial.p.f) (T0.trial.p.tail.map TailQ.toC))
    ≤ ((72471394 / 1000000000 : ℚ) : ℝ) :=
  norm_p_le (dl := T0.dpL) (by decide +kernel)

end CatalanMeasure.GenD.Signed.Data.Consts.EvalNormT
