module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger6.Merge8
public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger7.HP2Cells

@[expose] public section
set_option Elab.async false

/-!
# The ledger `Ledger6 + HP2` (lane G6)

`wins9` replaces `wins2[6], wins2[7], wins2[8]` (the H' + P sum cells `75 - 19x/2` and `8 - x` on
`(7.7778, 7.9999)`) by: `wins2[6]` shortened to end at `7.7896`, the two HP2 windows
`K = 19x/2 - 73` on `(7.7896, 7.7999]`, `K = 83 - 21x/2` on `(7.8001, 7.8946]`, and `wins2[8]` shortened
to start at `7.8946`.  `gain9 = gain8 + 25194919/1700000000`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger7
open CatalanMeasure.GenD D58 Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger2
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger4
  CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.GenD.Uniform.Bank535.Ledger6
open CatalanMeasure.GenD.Uniform.W.HYPlus CatalanMeasure.GenD.Uniform.W.MTGlue
  CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.SlotsT
  CatalanMeasure.GenD.Uniform.W.Tier3
noncomputable section

def mod6 : KapWindow := cw (700009 / 90000 : ℝ) (77896 / 10000 : ℝ) (75 : ℝ) (-19 / 2 : ℝ)
def mod8 : KapWindow := cw (78946 / 10000 : ℝ) (79999 / 10000 : ℝ) (8 : ℝ) (-1 : ℝ)

theorem mod6_mem : cw (700009 / 90000 : ℝ) (77999 / 10000 : ℝ) (75 : ℝ) (-19 / 2 : ℝ) ∈ wins2 := by
  simp [wins2]
theorem mod8_mem : cw (134 / 17 : ℝ) (79999 / 10000 : ℝ) (8 : ℝ) (-1 : ℝ) ∈ wins2 := by
  simp [wins2]

def hp2Wins : List KapWindow :=
  [cw (77896 / 10000 : ℝ) (77999 / 10000 : ℝ) (-73 : ℝ) (19 / 2 : ℝ),
   cw (78001 / 10000 : ℝ) (78946 / 10000 : ℝ) (83 : ℝ) (-21 / 2 : ℝ)]

theorem odd_of_prime_gt {p : ℕ} (hp : p.Prime) (h : 2 < p) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h2 | h2
  · omega
  · exact h2

theorem hp2Wins_cert : ∀ w ∈ hp2Wins, WinCert (hp2LB design adm) w := by
  intro w hw
  simp only [hp2Wins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact wincert_cw (hp2LB design adm) (na := 77896) (da := 10000) (nb := 77999) (db := 10000)
      (A := -146) (B := 19) (d := 2) (N0 := 100000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => by
        have := hp2A_cell (N := N) (p := p) hN (odd_of_prime_gt hp (by omega)) h1 h2
        have e : (hp2LB design adm).kap N p = hp2Kap design N p := rfl
        rw [e]
        omega
  · exact wincert_cw (hp2LB design adm) (na := 78001) (da := 10000) (nb := 78946) (db := 10000)
      (A := 166) (B := -21) (d := 2) (N0 := 100000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => by
        have := hp2B_cell (N := N) (p := p) hN (odd_of_prime_gt hp (by omega)) h1 h2
        have e : (hp2LB design adm).kap N p = hp2Kap design N p := rfl
        rw [e]
        omega

def fams9 : List (NullityLB design) := fams6 ++ [hp2LB design adm]

def wins9 : List KapWindow :=
  glueMt ++ hy11bWins ++ hy11Wins ++ wins2.take 2 ++ mWins ++ hy10Wins ++ hy9Wins ++ [mod5] ++
    [mod6] ++ hp2Wins ++ [mod8] ++ (wins2.drop 9).take 7 ++ zLWins ++ zWins ++ [mod16] ++ wins2.drop 17

def gain9 : ℝ := gain8 + 25194919 / 1700000000

theorem wins9_mem {w : KapWindow} (h : w ∈ wins9) :
    w ∈ hp2Wins ∨ w = mod6 ∨ w = mod8 ∨ w ∈ wins8 := by
  simp only [wins9, wins8, List.mem_append, List.mem_singleton] at h ⊢
  have hd : (wins2.drop 9).take 7 = ((wins2.drop 6).take 10).drop 3 := by simp [wins2]
  have hd2 : ∀ w, w ∈ (wins2.drop 9).take 7 → w ∈ (wins2.drop 6).take 10 := by
    intro w hw
    rw [hd] at hw
    exact List.mem_of_mem_drop hw
  have := hd2 w
  tauto

theorem wins9_pos : ∀ w ∈ wins9, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  rcases wins9_mem hw with h | h | h | h
  · simp only [hp2Wins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [cw] <;> norm_num
  · subst h; simp only [mod6, cw]; norm_num
  · subst h; simp only [mod8, cw]; norm_num
  · exact wins8_pos w h

theorem wins9_rec : ∀ w ∈ wins9, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  rcases wins9_mem hw with h | h | h | h
  · right
    simp only [hp2Wins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [cw] <;> norm_num
  · right; subst h; simp only [mod6, cw]; norm_num
  · right; subst h; simp only [mod8, cw]; norm_num
  · exact wins8_rec w h

theorem wins9_cert : ∀ w ∈ wins9, ∃ lb ∈ fams9, WinCert lb w := by
  intro w hw
  rcases wins9_mem hw with h | h | h | h
  · exact ⟨hp2LB design adm, by simp [fams9], hp2Wins_cert w h⟩
  · subst h
    exact ⟨ledgerLB, by simp [fams9, fams6, fams5],
      WinCert.shrink (wins2_cert _ mod6_mem : WinCert ledgerLB _) (le_refl _) (by norm_num)⟩
  · subst h
    exact ⟨ledgerLB, by simp [fams9, fams6, fams5],
      WinCert.shrink (wins2_cert _ mod8_mem : WinCert ledgerLB _) (by norm_num) (le_refl _)⟩
  · obtain ⟨lb, hl, hc⟩ := wins8_cert w h
    exact ⟨lb, List.mem_append_left _ hl, hc⟩

theorem wins9_ord : wins9.Pairwise (fun s t => s.b ≤ t.a) := by
  refine pw_of_ch _ (fun w hw => (wins9_pos w hw).2.1.le) ?_
  simp only [wins9, glueMt, gw18, gw17a, gw17b, mt1tail, mod16, mod5, mod6, mod8, hy11bWins, hy10Wins,
    hy11Wins, hy9Wins, hp2Wins, mWins, zWins, zLWins, mtWins, wins2, cw, Ch, List.cons_append,
    List.nil_append, List.drop, List.take, List.append_assoc]
  norm_num

theorem wins9_area : (wins9.map (KapWindow.area 58)).sum = gain9 := by
  simp only [wins9, glueMt, gw18, gw17a, gw17b, mt1tail, mod16, mod5, mod6, mod8, hy11bWins, hy10Wins,
    hy11Wins, hy9Wins, hp2Wins, mWins, zWins, zLWins, mtWins, wins2, List.drop, List.take,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    List.cons_append, List.nil_append, cw_area, gain9, gain8, gain7, gain6, gain5]
  norm_num

/-- **Denominator growth for `fams9` on `wins9`.** -/
theorem partial_growth9 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams9) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain9 + ε) * (N : ℝ) ^ 2 :=
  growth_of_families fams9 wins9 gain9 wins9_area wins9_pos wins9_ord wins9_rec wins9_cert hε

theorem gain9_ge : (21782 / 1000 : ℝ) ≤ gain9 := by
  unfold gain9 gain8 gain7 gain6 gain5; norm_num

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger7
