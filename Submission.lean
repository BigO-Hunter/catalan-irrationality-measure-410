import Submission.CatalanStatement
import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll

-- Bridge from Litsey's fixed-exponent mu(G) <= 410 theorem to the BigOSpeedrun
-- Catalan adapter. The transfer (Endpoint at a fixed exponent implies
-- UpperBoundFor at that exponent) is the inline form of `upperBoundFor_of_endpoint`
-- from challenges/catalan/Validation.lean of bigospeedrun/verifier.
open BigOSpeedrun.Catalan

theorem Race.bound : BigOSpeedrun.Catalan.Bound ((410 : ℚ) / 1) := by
  refine ⟨by norm_num, ?_⟩
  have h : Endpoint BigOSpeedrun.Catalan.constant 410 := by
    simpa [Endpoint, BigOSpeedrun.Catalan.constant] using
      CatalanMeasure.GenD.Signed.catalan_irrationalityMeasure_410
  intro s hs
  filter_upwards [h, Filter.eventually_ge_atTop 1] with b hb hb1 a
  have h1 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hs' : (410 : ℝ) ≤ s := by push_cast at hs; linarith
  exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (hb a)

#print axioms Race.bound
