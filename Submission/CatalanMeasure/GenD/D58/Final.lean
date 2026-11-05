module

public import Submission.CatalanMeasure.GenD.Final
public import Submission.CatalanMeasure.GenD.D58.Budget
public import Submission.CatalanMeasure.GenD.PayW
public import Submission.CatalanMeasure.GenD.D58.Normalizer
public import Submission.CatalanMeasure.GenD.Nonvanishing
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# D58: the generic final block

`n0_sub_g0`, the base-matrix certificate statement `C3` and `nonvanishing_d58` for the displaced design
`(58, 9, 3, 5, 3)`; a bank instance (`D58.Bank590`) combines them with its payments
(window parameter `w = 3/4`), the normalizer `Znorm` with its denominator growth `gD58`
(odd profile `f58`, gain windows `segs`, 2-adic constant `2673/8`) and its decay rate
`tΔ = (target - log 2 / 2) · 58²` in `measure_of_design`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Polynomial Filter Real CatalanMeasure.Parametric OAI.InternalCatalan
open scoped Topology
noncomputable section

instance fact1009 : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

/-- The C3 certificate for the displaced design (three residue determinants modulo 1009). -/
def C3 : Prop :=
  (baseB0Residue Odd.design 1009).det ≠ 0 ∧
    (baseB0Residue Odd.design 1009 + baseB1Residue Odd.design 1009).det ≠ 0 ∧
    (baseB0Residue Odd.design 1009 - baseB1Residue Odd.design 1009).det ≠ 0

theorem nonvanishing_d58 (c3 : C3) :
    ∃ N1 : ℕ, ∀ p : ℕ, N1 ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Parametric.deltaPoly Odd.design p) ≠ 0 :=
  nonvanishing_of_c3 Odd.design Odd.design_admissible (by norm_num)
    (by rw [Odd.design_H]; norm_num) c3.1 c3.2.1 c3.2.2

theorem n0_sub_g0 : ((Odd.design.n0 - Odd.design.g0 : ℕ) : ℝ) = d0 := by
  norm_num [Odd.design, d0]

end
end D58
end CatalanMeasure.GenD
