module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalNorm
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Data

@[expose] public section

/-!
# Weighted norms of the trial sequences (Theorem A, lane E1, item 10): part A of trial 1

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

theorem norm_a_tail_1 : normOK [] T1.aTail (37223715 / 1000000000 : ℚ) = true := by decide +kernel

theorem norm_a_le_1 : barrierTrialNormSq (tseq (fQ T1.trial.a.f) (T1.trial.a.tail.map TailQ.toC))
    ≤ ((94951214 / 1000000000 : ℚ) : ℝ) :=
  norm_tail_le (fl := T1.aF) (tl := T1.aTail) norm_a_tail_1 (by decide +kernel)

end CatalanMeasure.GenD.Signed.Data.Consts.EvalNormT
