module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Data
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.RInst
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.CurvInst

@[expose] public section

/-!
# 410 assembly: the constant rows of `Rows410` (`cP`, `rA`, `rB`, `hrA`, `hrB`, `κc`, `hκ`)
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed OAI.InternalCatalan CatalanMeasure.Parametric

noncomputable section

/-- `cP i α := constantLim P410 α`. -/
def cP410 : Fin 2 → ℝ → ℝ := fun _ α => Glue410.constantLim P410 α

theorem hcP410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), Glue410.constantLim P410 α ≤ cP410 i α :=
  fun _ _ _ => le_rfl

def rA410 : Fin 2 → ℝ := fun i => ((![rr0, rr1] i : ℚ) : ℝ)
def rB410 : Fin 2 → ℝ := fun i => ((![rr1, rr2] i : ℚ) : ℝ)
def κc410 : Fin 2 → ℝ := fun i => ((![kc01, kc12] i : ℚ) : ℝ)

theorem hrA410 : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (DA410 i N).constTotal (58 * N) - (DA410 i N).constant ≤ rA410 i + ε := by
  intro i ε hε
  fin_cases i
  · exact hr_0 ε hε
  · exact hr_1 ε hε

theorem hrB410 : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (DB410 i N).constTotal (58 * N) - (DB410 i N).constant ≤ rB410 i + ε := by
  intro i ε hε
  fin_cases i
  · exact hr_1 ε hε
  · exact hr_2 ε hε

theorem hκ410 : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    κc410 i - ε ≤ curvQ (DA410 i N) (DB410 i N) (58 * N) := by
  intro i ε hε
  fin_cases i
  · filter_upwards [curv_ge_01] with N hN
    show (kc01 : ℝ) - ε ≤ curvQ (famD X0 N) (famD X1 N) (58 * N)
    linarith
  · filter_upwards [curv_ge_12] with N hN
    show (kc12 : ℝ) - ε ≤ curvQ (famD X1 N) (famD X2 N) (58 * N)
    linarith

end

end CatalanMeasure.GenD.Signed.Data.Assembly
