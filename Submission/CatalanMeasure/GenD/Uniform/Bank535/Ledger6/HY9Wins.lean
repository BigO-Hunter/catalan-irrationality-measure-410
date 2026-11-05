module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger6.HY9

@[expose] public section
set_option Elab.async false

/-!
# HY+ `s = 9` windows: `K = 7 x - 53` on `(53/7, 69/9]` and `K = 16 - 2 x` on `(69/9, 54/7]` (lane G6)
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger6
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
  CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.GenD.Uniform.W.HYPlus
noncomputable section

theorem hy9_cell_a {N p : ℕ} (hp : p.Prime) (hZ : ZHY9 ≤ N) (hN : 1000 ≤ N) (h1 : 53 * N < 7 * p)
    (h2 : 9 * p ≤ 69 * N) :
    (-53 : ℤ) * N + 7 * p ≤ 1 * (((mLB' design adm).kap N p : ℕ) + 2 : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := hy9_core hZ hN h1 (by omega)
  omega

theorem hy9_cell_b {N p : ℕ} (hp : p.Prime) (hZ : ZHY9 ≤ N) (hN : 1000 ≤ N) (h1 : 69 * N < 9 * p)
    (h2 : 7 * p ≤ 54 * N) :
    (16 : ℤ) * N + (-2) * p ≤ 1 * (((mLB' design adm).kap N p : ℕ) + 2 : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := hy9_core (p := p) hZ hN (by omega) h2
  omega

def hy9Wins : List KapWindow :=
  [cw (53 / 7 : ℝ) (69 / 9 : ℝ) (-53 : ℝ) (7 : ℝ),
   cw (69 / 9 : ℝ) (54 / 7 : ℝ) (16 : ℝ) (-2 : ℝ)]

theorem hy9Wins_cert : ∀ w ∈ hy9Wins, WinCert (mLB' design adm) w := by
  intro w hw
  simp only [hy9Wins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact wincert_cw (mLB' design adm) (na := 53) (da := 7) (nb := 69) (db := 9) (A := -53) (B := 7)
      (d := 1) (N0 := ZHY9 + 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => by
        have hZ : ZHY9 ≤ N := Nat.le_trans (Nat.le_add_right _ _) hN
        have h1000 : 1000 ≤ N := Nat.le_trans (Nat.le_add_left _ _) hN
        clear hN
        exact hy9_cell_a hp hZ h1000 h1 h2
  · exact wincert_cw (mLB' design adm) (na := 69) (da := 9) (nb := 54) (db := 7) (A := 16) (B := -2)
      (d := 1) (N0 := ZHY9 + 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => by
        have hZ : ZHY9 ≤ N := Nat.le_trans (Nat.le_add_right _ _) hN
        have h1000 : 1000 ≤ N := Nat.le_trans (Nat.le_add_left _ _) hN
        clear hN
        exact hy9_cell_b hp hZ h1000 h1 h2

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger6
