module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.Merge4
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger5.ZLWins

@[expose] public section
set_option Elab.async false

/-!
# The ledger `Ledger4 + Z_L` (lane G5h)

`wins5` is `wins4` with the three Law_L (4) windows `(13.64, 14.22]` inserted between `wins2[15]`
(ending at `146/11`) and `zWins` (starting at `15.1435`).
`gain5 = gain4 + 0.3747`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.GenD D58 Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger2
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.GenD.Uniform.W.HYPlus CatalanMeasure.GenD.Uniform.W.MTGlue
  CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section

def wins5 : List KapWindow :=
  glueMt ++ wins2.take 2 ++ mWins ++ (wins2.drop 3).take 13 ++ zLWins ++ zWins ++ [mod16] ++ wins2.drop 17

def fams5 : List (NullityLB design) :=
  [ledgerLB, mtLB3 design adm, mtGlueLB' design adm, mLB' design adm, zHLB design adm,
    zLLB design adm]

def gain5 : ℝ := 4258196248687 / 196350000000

theorem wins5_mem {w : KapWindow} (h : w ∈ wins5) : w ∈ zLWins ∨ w ∈ wins4 := by
  simp only [wins5, wins4, List.mem_append] at h ⊢
  tauto

theorem wins5_pos : ∀ w ∈ wins5, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  rcases wins5_mem hw with h | h
  · exact zLWins_pos w h
  · exact wins4_pos w h

theorem wins5_rec : ∀ w ∈ wins5, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  rcases wins5_mem hw with h | h
  · right
    simp only [zLWins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · exact wins4_rec w h

theorem wins5_cert : ∀ w ∈ wins5, ∃ lb ∈ fams5, WinCert lb w := by
  intro w hw
  rcases wins5_mem hw with h | h
  · exact ⟨zLLB design adm, by simp [fams5], zLWins_cert w h⟩
  · obtain ⟨lb, hl, hc⟩ := wins4_cert w h
    have hm : lb ∈ fams5 := by
      simp only [fams4, List.mem_cons, List.not_mem_nil, or_false] at hl
      simp only [fams5, List.mem_cons, List.not_mem_nil, or_false]
      tauto
    exact ⟨lb, hm, hc⟩

theorem wins5_ord : wins5.Pairwise (fun s t => s.b ≤ t.a) := by
  refine pw_of_ch _ (fun w hw => (wins5_pos w hw).2.1.le) ?_
  simp only [wins5, glueMt, gw18, gw17a, gw17b, mt1tail, mod16, mWins, zWins, zLWins, mtWins, wins2, cw, Ch,
    List.cons_append, List.nil_append, List.drop, List.take, List.append_assoc]
  norm_num

theorem wins5_area : (wins5.map (KapWindow.area 58)).sum = gain5 := by
  simp only [wins5, glueMt, gw18, gw17a, gw17b, mt1tail, mod16, mWins, zWins, zLWins, mtWins, wins2, List.drop,
    List.take, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    List.cons_append, List.nil_append, cw_area, gain5]
  norm_num

/-- **Denominator growth for the families `fams5` on `wins5`.** -/
theorem partial_growth5 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams5) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain5 + ε) * (N : ℝ) ^ 2 :=
  growth_of_families fams5 wins5 gain5 wins5_area wins5_pos wins5_ord wins5_rec wins5_cert hε

theorem gain5_ge : (216083 / 10000 : ℝ) ≤ gain5 := by
  unfold gain5; norm_num

theorem gain5_ge540 : (2168168 / 100000 : ℝ) ≤ gain5 := by
  unfold gain5; norm_num

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger5
