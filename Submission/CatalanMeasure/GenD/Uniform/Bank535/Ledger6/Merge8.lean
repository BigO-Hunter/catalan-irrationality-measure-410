module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger6.Merge7
public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger6.HY10
public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger6.HY11b

@[expose] public section
set_option Elab.async false

/-!
# The ledger `Ledger5 + HY+ (s = 9, 10, 11)` (lane G6)

`wins8` is `wins7` plus the HY+ windows of s = 11 (6.25, 69/11] and s = 10 (106/15, 78/11]; `wins7` replaces `wins2[3], wins2[4]` (dominated by HY+ s = 9) and shortens `wins2[5]` to start at `54/7`;
the two `s = 9` windows fill `(53/7, 54/7]`.
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

def wins8 : List KapWindow :=
  glueMt ++ hy11bWins ++ hy11Wins ++ wins2.take 2 ++ mWins ++ hy10Wins ++ hy9Wins ++ [mod5] ++
    (wins2.drop 6).take 10 ++ zLWins ++ zWins ++ [mod16] ++ wins2.drop 17

def gain8 : ℝ := gain7 + 67 / 6600

theorem wins8_mem {w : KapWindow} (h : w ∈ wins8) :
    w ∈ hy11bWins ∨ w ∈ hy10Wins ∨ w ∈ wins7 := by
  simp only [wins8, wins7, List.mem_append] at h ⊢
  tauto

theorem wins8_pos : ∀ w ∈ wins8, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  rcases wins8_mem hw with h | h | h
  · simp only [hy11bWins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl; simp only [cw]; norm_num
  · simp only [hy10Wins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl; simp only [cw]; norm_num
  · exact wins7_pos w h

theorem wins8_rec : ∀ w ∈ wins8, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  rcases wins8_mem hw with h | h | h
  · right
    simp only [hy11bWins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl; simp only [cw]; norm_num
  · right
    simp only [hy10Wins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl; simp only [cw]; norm_num
  · exact wins7_rec w h

theorem wins8_cert : ∀ w ∈ wins8, ∃ lb ∈ fams6, WinCert lb w := by
  intro w hw
  rcases wins8_mem hw with h | h | h
  · exact ⟨mLB' design adm, by simp [fams6, fams5], hy11bWins_cert w h⟩
  · exact ⟨mLB' design adm, by simp [fams6, fams5], hy10Wins_cert w h⟩
  · exact wins7_cert w h

theorem wins8_ord : wins8.Pairwise (fun s t => s.b ≤ t.a) := by
  refine pw_of_ch _ (fun w hw => (wins8_pos w hw).2.1.le) ?_
  simp only [wins8, glueMt, gw18, gw17a, gw17b, mt1tail, mod16, mod5, hy11bWins, hy10Wins, hy11Wins, hy9Wins, mWins, zWins,
    zLWins, mtWins, wins2, cw, Ch, List.cons_append, List.nil_append, List.drop, List.take,
    List.append_assoc]
  norm_num

theorem wins8_area : (wins8.map (KapWindow.area 58)).sum = gain8 := by
  simp only [wins8, glueMt, gw18, gw17a, gw17b, mt1tail, mod16, mod5, hy11bWins, hy10Wins, hy11Wins, hy9Wins, mWins, zWins,
    zLWins, mtWins, wins2, List.drop, List.take, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.cons_append, List.nil_append, cw_area, gain8,
    gain7, gain6, gain5]
  norm_num

/-- **Denominator growth for `fams6` on `wins8`.** -/
theorem partial_growth8 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams6) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain8 + ε) * (N : ℝ) ^ 2 :=
  growth_of_families fams6 wins8 gain8 wins8_area wins8_pos wins8_ord wins8_rec wins8_cert hε

theorem gain8_ge : (21768 / 1000 : ℝ) ≤ gain8 := by
  unfold gain8 gain7 gain6 gain5; norm_num

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger6
