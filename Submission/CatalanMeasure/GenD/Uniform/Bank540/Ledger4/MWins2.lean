module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.MWins

@[expose] public section
set_option Elab.async false

/-!
# Family M windows: `K = x - 6` on `(6.9, 7]` and `K = 64 - 9 x` on `(7, 7.06]` (lane G5g)
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.GenD.Uniform.W.HYPlus
noncomputable section

theorem mcell_lo {N p : ℕ} (hp : p.Prime) (hZ : ZHY10 ≤ N) (hN : 1000 ≤ N) (h1 : 69 * N < 10 * p)
    (h2 : p ≤ 7 * N) :
    (-6 : ℤ) * N + 1 * p ≤ 1 * (((mLB' design adm).kap N p : ℕ) + 2 : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := mval_core hZ hN h1 (by omega)
  omega

theorem mcell_hi {N p : ℕ} (hp : p.Prime) (hZ : ZHY10 ≤ N) (hN : 1000 ≤ N) (h1 : 7 * N < p)
    (h2 : 50 * p ≤ 353 * N) :
    (64 : ℤ) * N + (-9) * p ≤ 1 * (((mLB' design adm).kap N p : ℕ) + 2 : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := mval_core (p := p) hZ hN (by omega) (by omega)
  omega

/-- The two M windows. -/
def mWins : List KapWindow :=
  [cw (69 / 10 : ℝ) (7 : ℝ) (-6 : ℝ) (1 : ℝ),
   cw (7 : ℝ) (353 / 50 : ℝ) (64 : ℝ) (-9 : ℝ)]

theorem mWins_cert : ∀ w ∈ mWins, WinCert (mLB' design adm) w := by
  intro w hw
  simp only [mWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact wincert_cw (mLB' design adm) (na := 69) (da := 10) (nb := 7) (db := 1) (A := -6) (B := 1)
      (d := 1) (N0 := ZHY10 + 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => by
        have hZ : ZHY10 ≤ N := Nat.le_trans (Nat.le_add_right _ _) hN
        have h1000 : 1000 ≤ N := Nat.le_trans (Nat.le_add_left _ _) hN
        clear hN
        exact mcell_lo hp hZ h1000 h1 (by omega)
  · exact wincert_cw (mLB' design adm) (na := 7) (da := 1) (nb := 353) (db := 50) (A := 64) (B := -9)
      (d := 1) (N0 := ZHY10 + 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => by
        have hZ : ZHY10 ≤ N := Nat.le_trans (Nat.le_add_right _ _) hN
        have h1000 : 1000 ≤ N := Nat.le_trans (Nat.le_add_left _ _) hN
        clear hN
        exact mcell_hi hp hZ h1000 (by omega) h2

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger4
