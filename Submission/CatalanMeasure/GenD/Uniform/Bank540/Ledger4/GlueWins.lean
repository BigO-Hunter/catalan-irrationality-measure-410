module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.GlueCells

@[expose] public section
set_option Elab.async false

/-!
# MT (b) glue windows, certified (lane G5g)

* `gw18` : `(4.06, 4.1]`, `K = 3.5 x - 14` (cell `s = 18`);
* `gw17a`: `(4.2951, 4.3125]`, `K = 30.5 x - 131` (cell `s = 17`, `elo = 69 N - 16 p`);
* `gw17b`: `(4.3125, 4.33]`, `K = 14.5 x - 62` (cell `s = 17`, `elo = 0`).
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.GenD.Uniform.W.MTGlue
noncomputable section

theorem gcell18 {N p : ℕ} (hp : p.Prime) (hM : cell18.modulus < N) (hN : 1000 ≤ N)
    (h1 : 203 * N < 50 * p) (h2 : 10 * p ≤ 41 * N) :
    (-28 : ℤ) * N + 7 * p ≤ 2 * (((mtGlueLB' design adm).kap N p : ℕ) + 2 : ℤ) := by
  have h := gval18 hp hM hN h1 h2
  omega

theorem gcell17a {N p : ℕ} (hp : p.Prime) (hM : cell17.modulus < N) (hN : 1000 ≤ N)
    (h1 : 42951 * N < 10000 * p) (h2 : 16 * p ≤ 69 * N) :
    (-262 : ℤ) * N + 61 * p ≤ 2 * (((mtGlueLB' design adm).kap N p : ℕ) + 2 : ℤ) := by
  have h := gval17 hp hM hN h1 (by omega)
  omega

theorem gcell17b {N p : ℕ} (hp : p.Prime) (hM : cell17.modulus < N) (hN : 1000 ≤ N)
    (h1 : 69 * N < 16 * p) (h2 : 100 * p ≤ 433 * N) :
    (-124 : ℤ) * N + 29 * p ≤ 2 * (((mtGlueLB' design adm).kap N p : ℕ) + 2 : ℤ) := by
  have h := gval17 hp hM hN (by omega) h2
  omega

def gw18 : KapWindow := cw (203 / 50 : ℝ) (41 / 10 : ℝ) (-14 : ℝ) (7 / 2 : ℝ)
def gw17a : KapWindow := cw (42951 / 10000 : ℝ) (69 / 16 : ℝ) (-131 : ℝ) (61 / 2 : ℝ)
def gw17b : KapWindow := cw (69 / 16 : ℝ) (433 / 100 : ℝ) (-62 : ℝ) (29 / 2 : ℝ)

/-- A big enough threshold: both cell moduli and 1000. -/
def gN0 : ℕ := cell17.modulus + cell18.modulus + 1000

theorem gw18_cert : WinCert (mtGlueLB' design adm) gw18 :=
  wincert_cw (mtGlueLB' design adm) (na := 203) (da := 50) (nb := 41) (db := 10) (A := -28) (B := 7)
    (d := 2) (N0 := gN0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    fun N p hN hp h1 h2 => by
      have hM : cell18.modulus < N := lt_of_lt_of_le (by unfold gN0; omega) hN
      have h1000 : 1000 ≤ N := le_trans (by unfold gN0; omega) hN
      exact gcell18 hp hM h1000 h1 h2

theorem gw17a_cert : WinCert (mtGlueLB' design adm) gw17a :=
  wincert_cw (mtGlueLB' design adm) (na := 42951) (da := 10000) (nb := 69) (db := 16) (A := -262) (B := 61)
    (d := 2) (N0 := gN0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    fun N p hN hp h1 h2 => by
      have hM : cell17.modulus < N := lt_of_lt_of_le (by unfold gN0; omega) hN
      have h1000 : 1000 ≤ N := le_trans (by unfold gN0; omega) hN
      exact gcell17a hp hM h1000 h1 h2

theorem gw17b_cert : WinCert (mtGlueLB' design adm) gw17b :=
  wincert_cw (mtGlueLB' design adm) (na := 69) (da := 16) (nb := 433) (db := 100) (A := -124) (B := 29)
    (d := 2) (N0 := gN0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    fun N p hN hp h1 h2 => by
      have hM : cell17.modulus < N := lt_of_lt_of_le (by unfold gN0; omega) hN
      have h1000 : 1000 ≤ N := le_trans (by unfold gN0; omega) hN
      exact gcell17b hp hM h1000 h1 h2

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger4
