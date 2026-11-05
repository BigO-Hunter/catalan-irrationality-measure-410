module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZWin
@[expose] public section
set_option Elab.async false

/-!
# Law_L(4) window certificate at the design `D58` (G2h)

`zL_winCert`: any affine window `cw a b c0 c1` with `133/10 ≤ a`, `b ≤ 15` whose profile lies below the
piecewise-linear Law_L(4) profile
`FzL x = (11/2) x - 75 + min 0 (70 - 5x) + min 0 (69 - 5x) + min 0 (3 + x/2 - (78 - 5x))`
is certified (`WinCert`) against `zLLB`, for the generic window slot of `Ledger3.growth_of_families`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial OAI.InternalCatalan CatalanMeasure.Parametric Filter
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.LedgerW
  CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
noncomputable section

/-- The piecewise-linear Law_L(4) profile at `D58` (`x = p / N`). -/
def FzL (x : ℝ) : ℝ :=
  11 / 2 * x - 75 + min 0 (70 - 5 * x) + min 0 (69 - 5 * x) + min 0 (3 + x / 2 - (78 - 5 * x))

theorem zLApp5_d58 {N p : ℕ} (hZ : ZcL6 < p) (h1 : 133 * N < 10 * p) (h2 : p ≤ 15 * N)
    (hodd : p % 2 = 1) (hN : 3 ≤ N) : zLApp5 design N p := by
  refine ⟨not_dvd_ZcL6 hZ, ?_⟩
  simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q,
    Parameters.g, Parameters.h, design, D58.Odd.design]
  omega

theorem zL_winCert {a b c0 c1 : ℝ} (ha : (133 / 10 : ℝ) ≤ a) (hb : b ≤ 15)
    (hlin : ∀ x : ℝ, a ≤ x → x ≤ b → c0 + c1 * x ≤ FzL x) :
    WinCert (zLLB design D58.Odd.design_admissible) (cw a b c0 c1) := by
  unfold WinCert
  filter_upwards [eventually_ge_atTop (ZcL6 + 3)] with N hN p hp haN hbN
  change a * (N : ℝ) < p at haN
  change (p : ℝ) ≤ b * N at hbN
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have h1r : (133 : ℝ) * N < 10 * p := by nlinarith
  have h2r : (p : ℝ) ≤ 15 * N := by nlinarith
  have h1 : 133 * N < 10 * p := by exact_mod_cast h1r
  have h2 : p ≤ 15 * N := by exact_mod_cast h2r
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hZ : ZcL6 < p := by omega
  have hA := zLApp5_d58 hZ h1 h2 hodd (by omega)
  have key := zLLB_kap_ge D58.Odd.design_admissible hodd hA
  refine ⟨?_, pool_cert a b hN0 (by omega)⟩
  have hev : (N : ℝ) * (cw a b c0 c1).K.eval ((p : ℝ) / N) = c0 * N + c1 * p := by
    simp only [cw, PL.Prof.eval, PL.hinges_nil]
    field_simp
    ring
  rw [hev]
  have hx := hlin ((p : ℝ) / N) (by rw [le_div_iff₀ hNr]; exact haN.le)
    (by rw [div_le_iff₀ hNr]; exact hbN)
  have hxN : c0 * N + c1 * p ≤ (N : ℝ) * FzL ((p : ℝ) / N) := by
    have := mul_le_mul_of_nonneg_left hx hNr.le
    have e : (N : ℝ) * (c0 + c1 * ((p : ℝ) / N)) = c0 * N + c1 * p := by
      field_simp
    linarith
  -- scale `FzL`
  have hF : (N : ℝ) * FzL ((p : ℝ) / N) =
      11 / 2 * p - 75 * N + min 0 (70 * N - 5 * (p : ℝ)) + min 0 (69 * N - 5 * (p : ℝ)) +
        min 0 (3 * N + (p : ℝ) / 2 - (78 * N - 5 * (p : ℝ))) := by
    unfold FzL
    have e1 : (N : ℝ) * min 0 (70 - 5 * ((p : ℝ) / N)) = min 0 (70 * N - 5 * (p : ℝ)) := by
      rw [mul_min_of_nonneg _ _ hNr.le, mul_zero]; congr 1; field_simp
    have e2 : (N : ℝ) * min 0 (69 - 5 * ((p : ℝ) / N)) = min 0 (69 * N - 5 * (p : ℝ)) := by
      rw [mul_min_of_nonneg _ _ hNr.le, mul_zero]; congr 1; field_simp
    have e3 : (N : ℝ) * min 0 (3 + ((p : ℝ) / N) / 2 - (78 - 5 * ((p : ℝ) / N))) =
        min 0 (3 * N + (p : ℝ) / 2 - (78 * N - 5 * (p : ℝ))) := by
      rw [mul_min_of_nonneg _ _ hNr.le, mul_zero]; congr 1; field_simp
    calc (N : ℝ) * (11 / 2 * ((p : ℝ) / N) - 75 + min 0 (70 - 5 * ((p : ℝ) / N)) +
          min 0 (69 - 5 * ((p : ℝ) / N)) + min 0 (3 + ((p : ℝ) / N) / 2 - (78 - 5 * ((p : ℝ) / N))))
        = 11 / 2 * (N * ((p : ℝ) / N)) - 75 * N + N * min 0 (70 - 5 * ((p : ℝ) / N)) +
          N * min 0 (69 - 5 * ((p : ℝ) / N)) +
          N * min 0 (3 + ((p : ℝ) / N) / 2 - (78 - 5 * ((p : ℝ) / N))) := by ring
      _ = _ := by rw [e1, e2, e3]; field_simp
  -- the integer inequality, cast to ℝ
  have dL : design.L N = 70 * N := by
    simp only [Parameters.L, Parameters.n, Parameters.b, Parameters.q, design, D58.Odd.design]; omega
  have dH : design.H N = 78 * N := by
    simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q,
      Parameters.g, Parameters.h, design, D58.Odd.design]; omega
  have dh : design.h N = 3 * N := by simp only [Parameters.h, design, D58.Odd.design]
  have db : design.b N = 9 * N := by simp only [Parameters.b, design, D58.Odd.design]
  have dn : design.n N = 58 * N := by simp only [Parameters.n, design, D58.Odd.design]
  have dq : design.q N = 3 * N := by simp only [Parameters.q, design, D58.Odd.design]
  have dg : design.g N = 5 * N := by simp only [Parameters.g, design, D58.Odd.design]
  rw [dL, dH, dh, db, dn, dq, dg] at key
  have hpo2 : 2 * ((p - 1) / 2) + 1 = p := by omega
  generalize (p - 1) / 2 = hq at key hpo2
  set k : ℕ := (zLLB design D58.Odd.design_admissible).kap N p with hk
  have key' : (11 * p : ℤ) + 2 * (min 0 (70 * (N : ℤ) - 5 * p) + min 0 (69 * (N : ℤ) - 5 * p) +
      min 0 (3 * (N : ℤ) + hq - (78 * N - 5 * p))) ≤ 2 * (k : ℤ) + 150 * N + 1 := by
    push_cast at key
    omega
  have hkeyR : (11 * p : ℝ) + 2 * (min 0 (70 * (N : ℝ) - 5 * p) + min 0 (69 * (N : ℝ) - 5 * p) +
      min 0 (3 * (N : ℝ) + hq - (78 * N - 5 * p))) ≤ 2 * (k : ℝ) + 150 * N + 1 := by
    exact_mod_cast key'
  have hpo : (hq : ℝ) = ((p : ℝ) - 1) / 2 := by
    have h' : (2 : ℝ) * (hq : ℝ) + 1 = p := by exact_mod_cast hpo2
    linarith
  rw [hpo] at hkeyR
  -- final real inequality
  have m3 : min 0 (3 * (N : ℝ) + (p : ℝ) / 2 - (78 * N - 5 * (p : ℝ))) ≤
      min 0 (3 * (N : ℝ) + ((p : ℝ) - 1) / 2 - (78 * N - 5 * (p : ℝ))) + 1 / 2 := by
    have e : 3 * (N : ℝ) + (p : ℝ) / 2 - (78 * N - 5 * (p : ℝ)) =
        (3 * (N : ℝ) + ((p : ℝ) - 1) / 2 - (78 * N - 5 * (p : ℝ))) + 1 / 2 := by ring
    rw [e]
    generalize (3 * (N : ℝ) + ((p : ℝ) - 1) / 2 - (78 * N - 5 * (p : ℝ))) = y
    simp only [min_def]
    split_ifs <;> linarith
  have hgoal : c0 * N + c1 * p - 2 ≤ (k : ℝ) := by
    linarith [hxN, hF, hkeyR, m3]
  exact hgoal

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
