module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger5.Merge5
public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger6.HY11
public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Gate

@[expose] public section
set_option Elab.async false

/-!
# The ledger `Ledger5 + HY+ (s = 11)` (lane G6)

`wins6` is `wins5` with the two `s = 11` windows `(69/11, 32/5]` inserted between the MT part
(ending below `5.4`) and `wins2[0]` (starting at `6.7779`).  `gain6 = gain5 + 43/1210`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger6
open CatalanMeasure.GenD D58 Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger2
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger4
  CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.GenD.Uniform.W.HYPlus CatalanMeasure.GenD.Uniform.W.MTGlue
  CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section

def wins6 : List KapWindow :=
  glueMt ++ hy11Wins ++ wins2.take 2 ++ mWins ++ (wins2.drop 3).take 13 ++ zLWins ++ zWins ++ [mod16] ++
    wins2.drop 17

def fams6 : List (NullityLB design) := fams5

def gain6 : ℝ := gain5 + 43 / 1210

theorem wins6_mem {w : KapWindow} (h : w ∈ wins6) : w ∈ hy11Wins ∨ w ∈ wins5 := by
  simp only [wins6, wins5, List.mem_append] at h ⊢
  tauto

theorem wins6_pos : ∀ w ∈ wins6, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  rcases wins6_mem hw with h | h
  · simp only [hy11Wins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [cw] <;> norm_num
  · exact wins5_pos w h

theorem wins6_rec : ∀ w ∈ wins6, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  rcases wins6_mem hw with h | h
  · right
    simp only [hy11Wins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [cw] <;> norm_num
  · exact wins5_rec w h

theorem wins6_cert : ∀ w ∈ wins6, ∃ lb ∈ fams6, WinCert lb w := by
  intro w hw
  rcases wins6_mem hw with h | h
  · exact ⟨mLB' design adm, by simp [fams6, fams5], hy11Wins_cert w h⟩
  · exact wins5_cert w h

theorem wins6_ord : wins6.Pairwise (fun s t => s.b ≤ t.a) := by
  refine pw_of_ch _ (fun w hw => (wins6_pos w hw).2.1.le) ?_
  simp only [wins6, glueMt, gw18, gw17a, gw17b, mt1tail, mod16, hy11Wins, mWins, zWins, zLWins, mtWins,
    wins2, cw, Ch, List.cons_append, List.nil_append, List.drop, List.take, List.append_assoc]
  norm_num

theorem wins6_area : (wins6.map (KapWindow.area 58)).sum = gain6 := by
  simp only [wins6, glueMt, gw18, gw17a, gw17b, mt1tail, mod16, hy11Wins, mWins, zWins, zLWins, mtWins,
    wins2, List.drop, List.take, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, List.cons_append, List.nil_append, cw_area, gain6, gain5]
  norm_num

/-- **Denominator growth for `fams6` on `wins6`.** -/
theorem partial_growth6 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams6) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain6 + ε) * (N : ℝ) ^ 2 :=
  growth_of_families fams6 wins6 gain6 wins6_area wins6_pos wins6_ord wins6_rec wins6_cert hε

theorem gain6_ge : (21722 / 1000 : ℝ) ≤ gain6 := by
  unfold gain6 gain5; norm_num

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger6
