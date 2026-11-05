module

public import Submission.CatalanMeasure.GenD.KapHelpers
public import Submission.CatalanMeasure.GenD.D58.Ramps
public import Submission.CatalanMeasure.GenD.D58.OddProfile

@[expose] public section

/-!
# D58: the nullity lower bound `kap` as the ramp list (instance file)

`kapD58 N p = segExp segs N p - 1`.  The comparison with `famKap` is, window by window, a purely
linear (`omega`) statement: windows 0-1 are U6g, windows 2-4 are S, window 5 is T, window 6 is T
then U, window 7 is U.  The "-1" absorbs the `-1` in the proved forms of T and U.
-/

namespace CatalanMeasure.GenD
namespace D58

open PrimeGrowth CatalanMeasure.Parametric

noncomputable section

macro "d58_unfold" : tactic =>
  `(tactic| simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
    Parameters.q, Parameters.g, Parameters.h, Odd.design])

theorem cell0 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 12 * N < p) (h2 : p ≤ 13 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk (-5) (1 / 2) []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap Odd.design N p + 1 := by
  have happ : U6App Odd.design N p := by
    unfold U6App uM0
    d58_unfold
    omega
  have hv := u6Val_le_famKap happ
  have hf := floor_aux (N := N) (p := p) (v := u6Val Odd.design N p) (d := 2) (A := -10) (B := 1)
    hN (by norm_num) (by unfold u6Val uM1 uM0 sE; d58_unfold; omega) (c0 := -5) (c1 := 1 / 2)
    (by norm_num) (by norm_num)
  rw [prof_eval_nil]
  omega

theorem cell1 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 13 * N < p) (h2 : 11 * p ≤ 146 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk 73 (-11 / 2) []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap Odd.design N p + 1 := by
  have happ : U6App Odd.design N p := by
    unfold U6App uM0
    d58_unfold
    omega
  have hv := u6Val_le_famKap happ
  have hf := floor_aux (N := N) (p := p) (v := u6Val Odd.design N p) (d := 2) (A := 146) (B := -11)
    hN (by norm_num) (by unfold u6Val uM1 uM0 sE; d58_unfold; omega) (c0 := 73) (c1 := -11 / 2)
    (by norm_num) (by norm_num)
  rw [prof_eval_nil]
  omega

theorem sApp_d58 {N p : ℕ} (h1 : 12 * N ≤ p) : SApp Odd.design N p := by
  unfold SApp
  d58_unfold
  omega

theorem cell2 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 50 * N < 3 * p) (h2 : 4 * p ≤ 69 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk (-75) (9 / 2) []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap Odd.design N p + 1 := by
  have hv := sVal_le_famKap (sApp_d58 (N := N) (p := p) (by omega))
  have hf := floor_aux (N := N) (p := p) (v := sVal Odd.design N p) (d := 2) (A := -150) (B := 9)
    hN (by norm_num) (by unfold sVal sM1 sM0 sE; d58_unfold; omega) (c0 := -75) (c1 := 9 / 2)
    (by norm_num) (by norm_num)
  rw [prof_eval_nil]
  omega

theorem cell3 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 69 * N < 4 * p) (h2 : 2 * p ≤ 35 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk (-6) (1 / 2) []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap Odd.design N p + 1 := by
  have hv := sVal_le_famKap (sApp_d58 (N := N) (p := p) (by omega))
  have hf := floor_aux (N := N) (p := p) (v := sVal Odd.design N p) (d := 2) (A := -12) (B := 1)
    hN (by norm_num) (by unfold sVal sM1 sM0 sE; d58_unfold; omega) (c0 := -6) (c1 := 1 / 2)
    (by norm_num) (by norm_num)
  rw [prof_eval_nil]
  omega

theorem cell4 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 35 * N < 2 * p) (h2 : 7 * p ≤ 128 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk 64 (-7 / 2) []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap Odd.design N p + 1 := by
  have hv := sVal_le_famKap (sApp_d58 (N := N) (p := p) (by omega))
  have hf := floor_aux (N := N) (p := p) (v := sVal Odd.design N p) (d := 2) (A := 128) (B := -7)
    hN (by norm_num) (by unfold sVal sM1 sM0 sE; d58_unfold; omega) (c0 := 64) (c1 := -7 / 2)
    (by norm_num) (by norm_num)
  rw [prof_eval_nil]
  omega

theorem tApp_d58 {N p : ℕ} (hN : 0 < N) (h1 : 64 * N < 3 * p) (h2 : p ≤ 24 * N)
    (h3 : 3 * p ≤ 70 * N) : TApp Odd.design N p := by
  unfold TApp tentD
  d58_unfold
  omega

theorem cell5 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 64 * N < 3 * p) (h2 : p ≤ 23 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk (-64) 3 []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap Odd.design N p + 1 := by
  have hv := tVal_le_famKap (tApp_d58 hN h1 (by omega) (by omega))
  have hf := floor_aux (N := N) (p := p) (v := tVal Odd.design N p) (d := 1) (A := -64) (B := 3)
    hN (by norm_num) (by unfold tVal tentD; d58_unfold; omega) (c0 := -64) (c1 := 3)
    (by norm_num) (by norm_num)
  rw [prof_eval_nil]
  omega

theorem uApp_d58 {N p : ℕ} (h1 : 70 * N ≤ 3 * p) (h2 : p ≤ 26 * N) : UApp Odd.design N p := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> d58_unfold <;> omega

theorem cell6 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 23 * N < p) (h2 : p ≤ 24 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk 5 0 []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap Odd.design N p + 1 := by
  by_cases hc : 70 * N ≤ 3 * p
  · have hv := uVal_le_famKap (uApp_d58 hc (by omega))
    have hf := floor_aux (N := N) (p := p) (v := uVal Odd.design N p) (d := 1) (A := 5) (B := 0)
      hN (by norm_num) (by unfold uVal uStar; d58_unfold; omega) (c0 := 5) (c1 := 0)
      (by norm_num) (by norm_num)
    rw [prof_eval_nil]
    omega
  · have hv := tVal_le_famKap (tApp_d58 hN (by omega) h2 (by omega))
    have hf := floor_aux (N := N) (p := p) (v := tVal Odd.design N p) (d := 1) (A := 5) (B := 0)
      hN (by norm_num) (by unfold tVal tentD; d58_unfold; omega) (c0 := 5) (c1 := 0)
      (by norm_num) (by norm_num)
    rw [prof_eval_nil]
    omega

theorem cell7 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 24 * N < p) (h2 : p ≤ 26 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk 53 (-2) []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap Odd.design N p + 1 := by
  have hv := uVal_le_famKap (uApp_d58 (by omega) h2)
  have hf := floor_aux (N := N) (p := p) (v := uVal Odd.design N p) (d := 1) (A := 53) (B := -2)
    hN (by norm_num) (by unfold uVal uStar; d58_unfold; omega) (c0 := 53) (c1 := -2)
    (by norm_num) (by norm_num)
  rw [prof_eval_nil]
  omega

theorem segExp_le_famKap {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) :
    segExp segs N p ≤ famKap Odd.design N p + 1 := by
  apply segExp_le
  intro s hs hc
  simp only [segs, profSegs, cellProfs, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨hc1, hc2⟩ := hc <;> dsimp only at hc1 hc2 ⊢
  · exact cell0 hN hodd (by exact_mod_cast (by linarith : (12 : ℝ) * N < p))
      (by exact_mod_cast (by linarith : (p : ℝ) ≤ 13 * N))
  · exact cell1 hN hodd (by exact_mod_cast (by linarith : (13 : ℝ) * N < p))
      (by exact_mod_cast (by linarith : (11 : ℝ) * p ≤ 146 * N))
  · exact cell2 hN hodd (by exact_mod_cast (by linarith : (50 : ℝ) * N < 3 * p))
      (by exact_mod_cast (by linarith : (4 : ℝ) * p ≤ 69 * N))
  · exact cell3 hN hodd (by exact_mod_cast (by linarith : (69 : ℝ) * N < 4 * p))
      (by exact_mod_cast (by linarith : (2 : ℝ) * p ≤ 35 * N))
  · exact cell4 hN hodd (by exact_mod_cast (by linarith : (35 : ℝ) * N < 2 * p))
      (by exact_mod_cast (by linarith : (7 : ℝ) * p ≤ 128 * N))
  · exact cell5 hN hodd (by exact_mod_cast (by linarith : (64 : ℝ) * N < 3 * p))
      (by exact_mod_cast (by linarith : (p : ℝ) ≤ 23 * N))
  · exact cell6 hN hodd (by exact_mod_cast (by linarith : (23 : ℝ) * N < p))
      (by exact_mod_cast (by linarith : (p : ℝ) ≤ 24 * N))
  · exact cell7 hN hodd (by exact_mod_cast (by linarith : (24 : ℝ) * N < p))
      (by exact_mod_cast (by linarith : (p : ℝ) ≤ 26 * N))

end

end D58
end CatalanMeasure.GenD
