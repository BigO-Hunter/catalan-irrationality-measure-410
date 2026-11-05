module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger10.CWin
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.CLBP

@[expose] public section
set_option Elab.async false

/-!
# Theorem C' window cells (lane G6e)

Cells `S = 31, 32, 33` (`h >= p`); explicit `lo`, `hi` per piece, `cCellLBP_kap_ge`, `omega`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger10
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.LStar CatalanMeasure.GenD.Uniform.W.TheoremC
open CatalanMeasure.GenD.Uniform.Bank540.Ledger
noncomputable section

set_option hygiene false in
macro "cond_dataP" c:ident : tactic => `(tactic| (
  unfold cCondP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · (try simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · intro e l1 l2
    simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try norm_num) <;> omega))

local notation "des" => D58.Odd.design

/-- A prime `p > N` is never in an exact small ratio with `N`. -/
theorem no_ratio {N p b : ℕ} (a : ℕ) (hp : p.Prime) (hNp : N < p) (hb : 0 < b) (hbN : b ≤ N)
    (h : a * p = b * N) : False := by
  have hd : p ∣ b * N := ⟨a, by rw [← h]; ring⟩
  rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
  · exact absurd (Nat.le_of_dvd hb h1) (by omega)
  · exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)

/-- `K = -64 + (26) x` on `(32/13, 69/28]`, cell cellp1. -/
theorem p1a_cell {N p : ℕ} (hp : p.Prime) (h1 : 32 * N < 13 * p) (h2 : 28 * p ≤ 69 * N)
    (hN : cellp1.modulus + 100 ≤ N) :
    (-64 : ℤ) * N + (26) * p ≤ 1 * (((cCellLBP cellp1 des adm).kap N p : ℕ) + 2 : ℤ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hne : 28 * p ≠ 69 * N := fun h => no_ratio 28 hp (by omega) (by norm_num) (by omega) h
  have hm := cellp1.modulus_pos yp1_ne
  have hcop := cellp1.coprime_of_gt yp1_ne hp (by omega)
  have hqp : 0 < D58.Odd.design.q N := by rw [hq]; omega
  have key := cCellLBP_kap_ge cellp1 des adm (lo := 69 * N - 28 * p) (hi := 8 * N - 3 * p - 1)
    hcop hqp (by cond_dataP cellp1)
  omega

/-- `K = 5 + (-2) x` on `(69/28, 5/2]`, cell cellp1. -/
theorem p1b_cell {N p : ℕ} (hp : p.Prime) (h1 : 69 * N < 28 * p) (h2 : 2 * p ≤ 5 * N)
    (hN : cellp1.modulus + 100 ≤ N) :
    (5 : ℤ) * N + (-2) * p ≤ 1 * (((cCellLBP cellp1 des adm).kap N p : ℕ) + 2 : ℤ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hne : 2 * p ≠ 5 * N := fun h => no_ratio 2 hp (by omega) (by norm_num) (by omega) h
  have hm := cellp1.modulus_pos yp1_ne
  have hcop := cellp1.coprime_of_gt yp1_ne hp (by omega)
  have hqp : 0 < D58.Odd.design.q N := by rw [hq]; omega
  have key := cCellLBP_kap_ge cellp1 des adm (lo := 0) (hi := 8 * N - 3 * p - 1)
    hcop hqp (by cond_dataP cellp1)
  omega

/-- `K = -64 + (27) x` on `(64/27, 69/29]`, cell cellp2. -/
theorem p2a_cell {N p : ℕ} (hp : p.Prime) (h1 : 64 * N < 27 * p) (h2 : 29 * p ≤ 69 * N)
    (hN : cellp2.modulus + 100 ≤ N) :
    (-64 : ℤ) * N + (27) * p ≤ 1 * (((cCellLBP cellp2 des adm).kap N p : ℕ) + 2 : ℤ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hne : 29 * p ≠ 69 * N := fun h => no_ratio 29 hp (by omega) (by norm_num) (by omega) h
  have hm := cellp2.modulus_pos yp2_ne
  have hcop := cellp2.coprime_of_gt yp2_ne hp (by omega)
  have hqp : 0 < D58.Odd.design.q N := by rw [hq]; omega
  have key := cCellLBP_kap_ge cellp2 des adm (lo := 69 * N - 29 * p) (hi := 8 * N - 3 * p - 1)
    hcop hqp (by cond_dataP cellp2)
  omega

/-- `K = 5 + (-2) x` on `(69/29, 12/5]`, cell cellp2. -/
theorem p2b_cell {N p : ℕ} (hp : p.Prime) (h1 : 69 * N < 29 * p) (h2 : 5 * p ≤ 12 * N)
    (hN : cellp2.modulus + 100 ≤ N) :
    (5 : ℤ) * N + (-2) * p ≤ 1 * (((cCellLBP cellp2 des adm).kap N p : ℕ) + 2 : ℤ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hne : 5 * p ≠ 12 * N := fun h => no_ratio 5 hp (by omega) (by norm_num) (by omega) h
  have hm := cellp2.modulus_pos yp2_ne
  have hcop := cellp2.coprime_of_gt yp2_ne hp (by omega)
  have hqp : 0 < D58.Odd.design.q N := by rw [hq]; omega
  have key := cCellLBP_kap_ge cellp2 des adm (lo := 0) (hi := 8 * N - 3 * p - 1)
    hcop hqp (by cond_dataP cellp2)
  omega

/-- `K = 53 + (-22) x` on `(12/5, 53/22]`, cell cellp2. -/
theorem p2c_cell {N p : ℕ} (hp : p.Prime) (h1 : 12 * N < 5 * p) (h2 : 22 * p ≤ 53 * N)
    (hN : cellp2.modulus + 100 ≤ N) :
    (53 : ℤ) * N + (-22) * p ≤ 1 * (((cCellLBP cellp2 des adm).kap N p : ℕ) + 2 : ℤ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hne : 22 * p ≠ 53 * N := fun h => no_ratio 22 hp (by omega) (by norm_num) (by omega) h
  have hm := cellp2.modulus_pos yp2_ne
  have hcop := cellp2.coprime_of_gt yp2_ne hp (by omega)
  have hqp : 0 < D58.Odd.design.q N := by rw [hq]; omega
  have key := cCellLBP_kap_ge cellp2 des adm (lo := 0) (hi := 56 * N - 23 * p - 1)
    hcop hqp (by cond_dataP cellp2)
  omega

/-- `K = -16 + (7) x` on `(16/7, 23/10]`, cell cellp3. -/
theorem p3a_cell {N p : ℕ} (hp : p.Prime) (h1 : 16 * N < 7 * p) (h2 : 10 * p ≤ 23 * N)
    (hN : cellp3.modulus + 100 ≤ N) :
    (-16 : ℤ) * N + (7) * p ≤ 1 * (((cCellLBP cellp3 des adm).kap N p : ℕ) + 2 : ℤ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hne : 10 * p ≠ 23 * N := fun h => no_ratio 10 hp (by omega) (by norm_num) (by omega) h
  have hm := cellp3.modulus_pos yp3_ne
  have hcop := cellp3.coprime_of_gt yp3_ne hp (by omega)
  have hqp : 0 < D58.Odd.design.q N := by rw [hq]; omega
  have key := cCellLBP_kap_ge cellp3 des adm (lo := 69 * N - 30 * p) (hi := 56 * N - 24 * p - 1)
    hcop hqp (by cond_dataP cellp3)
  omega

/-- `K = 53 + (-23) x` on `(23/10, 53/23]`, cell cellp3. -/
theorem p3b_cell {N p : ℕ} (hp : p.Prime) (h1 : 23 * N < 10 * p) (h2 : 23 * p ≤ 53 * N)
    (hN : cellp3.modulus + 100 ≤ N) :
    (53 : ℤ) * N + (-23) * p ≤ 1 * (((cCellLBP cellp3 des adm).kap N p : ℕ) + 2 : ℤ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hne : 23 * p ≠ 53 * N := fun h => no_ratio 23 hp (by omega) (by norm_num) (by omega) h
  have hm := cellp3.modulus_pos yp3_ne
  have hcop := cellp3.coprime_of_gt yp3_ne hp (by omega)
  have hqp : 0 < D58.Odd.design.q N := by rw [hq]; omega
  have key := cCellLBP_kap_ge cellp3 des adm (lo := 0) (hi := 56 * N - 24 * p - 1)
    hcop hqp (by cond_dataP cellp3)
  omega

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger10
