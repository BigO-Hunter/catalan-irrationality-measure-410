module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger6.Merge6
public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger6.HY9Wins

@[expose] public section
set_option Elab.async false

/-!
# The ledger `Ledger5 + HY+ (s = 11) + HY+ (s = 9)` (lane G6)

`wins7` replaces `wins2[3], wins2[4]` (dominated by HY+ s = 9) and shortens `wins2[5]` to start at `54/7`;
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

/-- `wins2[5]` shortened to start at `54/7`. -/
def mod5 : KapWindow := cw (54 / 7 : ℝ) (699991 / 90000 : ℝ) (-65 : ℝ) (17 / 2 : ℝ)

theorem mod5_mem : cw (19211 / 2500 : ℝ) (699991 / 90000 : ℝ) (-65 : ℝ) (17 / 2 : ℝ) ∈ wins2 := by
  simp [wins2]

def wins7 : List KapWindow :=
  glueMt ++ hy11Wins ++ wins2.take 2 ++ mWins ++ hy9Wins ++ [mod5] ++ (wins2.drop 6).take 10 ++ zLWins ++
    zWins ++ [mod16] ++ wins2.drop 17

def gain7 : ℝ := gain6 + 780971 / 21875000

theorem wins7_mem {w : KapWindow} (h : w ∈ wins7) :
    w ∈ hy11Wins ∨ w ∈ hy9Wins ∨ w = mod5 ∨ w ∈ wins5 := by
  simp only [wins7, wins5, List.mem_append, List.mem_singleton] at h ⊢
  have hd : ∀ w, w ∈ (wins2.drop 6).take 10 → w ∈ (wins2.drop 3).take 13 := by
    intro w hw
    have h1 := List.mem_of_mem_take hw
    have h2 := List.mem_of_mem_drop h1
    have : (wins2.drop 6).take 10 = ((wins2.drop 3).take 13).drop 3 := by
      simp [wins2]
    rw [this] at hw
    exact List.mem_of_mem_drop hw
  tauto

theorem wins7_pos : ∀ w ∈ wins7, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  rcases wins7_mem hw with h | h | h | h
  · exact wins6_pos w (by simp only [wins6, List.mem_append]; tauto)
  · simp only [hy9Wins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [cw] <;> norm_num
  · subst h; simp only [mod5, cw]; norm_num
  · exact wins5_pos w h

theorem wins7_rec : ∀ w ∈ wins7, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  rcases wins7_mem hw with h | h | h | h
  · exact wins6_rec w (by simp only [wins6, List.mem_append]; tauto)
  · right
    simp only [hy9Wins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [cw] <;> norm_num
  · right; subst h; simp only [mod5, cw]; norm_num
  · exact wins5_rec w h

theorem wins7_cert : ∀ w ∈ wins7, ∃ lb ∈ fams6, WinCert lb w := by
  intro w hw
  rcases wins7_mem hw with h | h | h | h
  · exact ⟨mLB' design adm, by simp [fams6, fams5], hy11Wins_cert w h⟩
  · exact ⟨mLB' design adm, by simp [fams6, fams5], hy9Wins_cert w h⟩
  · subst h
    exact ⟨ledgerLB, by simp [fams6, fams5],
      WinCert.shrink (wins2_cert _ mod5_mem : WinCert ledgerLB _) (by norm_num) (le_refl _)⟩
  · exact wins5_cert w h

theorem wins7_ord : wins7.Pairwise (fun s t => s.b ≤ t.a) := by
  refine pw_of_ch _ (fun w hw => (wins7_pos w hw).2.1.le) ?_
  simp only [wins7, glueMt, gw18, gw17a, gw17b, mt1tail, mod16, mod5, hy11Wins, hy9Wins, mWins, zWins,
    zLWins, mtWins, wins2, cw, Ch, List.cons_append, List.nil_append, List.drop, List.take,
    List.append_assoc]
  norm_num

theorem wins7_area : (wins7.map (KapWindow.area 58)).sum = gain7 := by
  simp only [wins7, glueMt, gw18, gw17a, gw17b, mt1tail, mod16, mod5, hy11Wins, hy9Wins, mWins, zWins,
    zLWins, mtWins, wins2, List.drop, List.take, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.cons_append, List.nil_append, cw_area, gain7,
    gain6, gain5]
  norm_num

/-- **Denominator growth for `fams6` on `wins7`.** -/
theorem partial_growth7 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams6) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain7 + ε) * (N : ℝ) ^ 2 :=
  growth_of_families fams6 wins7 gain7 wins7_area wins7_pos wins7_ord wins7_rec wins7_cert hε

theorem gain7_ge : (21758 / 1000 : ℝ) ≤ gain7 := by
  unfold gain7 gain6 gain5; norm_num

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger6
