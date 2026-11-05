module

public import Submission.CatalanMeasure.GenD.Analytic.FirstGlue
public import Submission.CatalanMeasure.GenD.Analytic.Instances
public import Submission.CatalanMeasure.GenD.D58.Budget
public import Submission.CatalanMeasure.GenD.D58.OddProfile
public import Submission.CatalanMeasure.FirstStrongTrial.NormP
public import Submission.CatalanMeasure.FirstStrongTrial.NormV
public import Submission.CatalanMeasure.FirstStrongTrial.First

@[expose] public section

/-!
# D58: the first-population trial `FirstTrialBounds Odd.design target firstCost`

The frozen 40-mode first trial (`FirstStrongTrial.Data`: `Pc, P, Vc, V`, multiplier `lam`) is
design-independent data; only the weights of the two fields change.  At `(58,9,3,5,3)`:
* row   `firstRowFieldG (11/29) (3/29) (49/58) lam (5/29) p v`  with `p = 2 * trialSeq Pc P`,
* column `colFieldG (9/58) (3/58) v`,
with the caps `MX1 = -57927/50000`, `MY1 = -132981/100000` (`F1 = MX1 + MY1`, `witness-final`).

`firstTrial_D58` builds the contract from these two suprema (hypotheses `hrow`, `hcol`, to be
discharged by the D58 first-trial cover certificate); a bank instantiates it with its budget
`K.first_budget_log2`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Set Filter OAI.InternalCatalan CatalanMeasure.Cert CatalanMeasure.CellCert
open CatalanMeasure.GenD.Analytic
noncomputable section

/-- The first-trial multiplier (design independent). -/
def lamFirst : ℝ := 168493357 / 100000000
def MX1 : ℝ := -57927 / 50000
def MY1 : ℝ := -132981 / 100000

/-- Physical first sequences (the stored `P` is doubled). -/
def firstP (j : ℕ) : ℝ := 2 * trialSeq FirstStrongTrial.Pc FirstStrongTrial.P j
def firstV : ℕ → ℝ := trialSeq FirstStrongTrial.Vc FirstStrongTrial.V

theorem firstP_summable : Summable (fun j => |firstP j|) := by
  have hs := (trialSeq_summable (cs := FirstStrongTrial.Pc) FirstStrongTrial.tailsP).1
  simpa only [firstP, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    using hs.mul_left (2 : ℝ)

theorem firstV_summable : Summable (fun j => |firstV j|) :=
  (trialSeq_summable (cs := FirstStrongTrial.Vc) FirstStrongTrial.tailsV).1

theorem first_normSq_mul (c : ℝ) (u : ℕ → ℝ) :
    barrierTrialNormSq (fun j => c * u j) = c ^ 2 * barrierTrialNormSq u := by
  unfold barrierTrialNormSq
  rw [← tsum_mul_left]
  congr 1
  funext j
  ring

/-- The trial norm bound `n1 = 67761/100000` (design independent). -/
theorem first_norm_le :
    barrierTrialNormSq firstP + barrierTrialNormSq firstV / 2 ≤ n1 := by
  have hp : barrierTrialNormSq (trialSeq FirstStrongTrial.Pc FirstStrongTrial.P) ≤ (FirstStrongTrial.NP : ℝ) := normOK_spec FirstStrongTrial.hNP
  have hv : barrierTrialNormSq (trialSeq FirstStrongTrial.Vc FirstStrongTrial.V) ≤ (FirstStrongTrial.NV : ℝ) := normOK_spec FirstStrongTrial.hNV
  unfold firstP firstV
  rw [first_normSq_mul]
  norm_num [FirstStrongTrial.NP, FirstStrongTrial.NV, n1] at hp hv ⊢
  linarith only [hp, hv]

theorem MX1_add_MY1 : MX1 + MY1 = F1 := by norm_num [MX1, MY1, F1]

/-- The first-population contract at D58 from the two field suprema. -/
def firstTrial_D58 {target cost : ℝ}
    (hrow : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      firstRowFieldG (11 / 29) (3 / 29) (49 / 58) lamFirst (5 / 29) firstP firstV x ≤ MX1)
    (hcol : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG (9 / 58) (3 / 58) firstV s ≤ MY1)
    (hbud : ∀ a : ℝ,
      (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2) * Real.log 2 + n1 + (1 - a) * F1
          + a * (1 - a) * Real.log 2 + a * Lm + (9 / 10 : ℝ) * a ≤
        -target + Real.log 2 / 2 + (cost + 9 / 10) * a) :
    FirstTrialBounds Odd.design target cost :=
  firstTrial_of_fields Odd.design_admissible firstP firstV lamFirst (by norm_num [lamFirst])
    firstP_summable firstV_summable (11 / 29) (3 / 29) (49 / 58) (5 / 29) (9 / 58) (3 / 58)
    (by norm_num [Odd.design]) (by norm_num [Odd.design]) (by norm_num [Odd.design])
    (by norm_num [Odd.design]) (by norm_num [Odd.design]) (by norm_num [Odd.design])
    MX1 MY1 first_norm_le MX1_add_MY1 hrow hcol
    (by
      intro a
      have h := hbud a
      rw [Instances.d58_gC0, Instances.d58_gC1, Instances.d58_g_ratio]
      have e : c07 - 1 / 2 = 6 / 29 := by norm_num [c07]
      have e2 : c26 - 1 = 47 / 29 := by norm_num [c26]
      rw [e, e2] at h
      have e3 : Lm = lamFirst * (5 / 29) := by norm_num [Lm, lamFirst]
      rw [e3] at h
      linarith only [h])

end
end D58
end CatalanMeasure.GenD
