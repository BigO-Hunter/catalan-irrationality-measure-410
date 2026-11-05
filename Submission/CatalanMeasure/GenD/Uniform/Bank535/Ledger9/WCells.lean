module

public import Submission.CatalanMeasure.GenD.Uniform.W.LStar2.Cell2

@[expose] public section
set_option Elab.async false

/-!
# Theorem L* window cells for `h < p` (lane G6d), `x in (3, 3.2]`

Each cell is one or two residue intervals of constant type `(mu; u1, u2; u3, u4)`; the bound
`kap >= sum of lengths` is read off `lstar2_cell1` / `lstar2_cell2`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger9
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.LStar CatalanMeasure.GenD.Uniform.W.LStar2
noncomputable section

local notation "des" => D58.Odd.design

macro "cell_data" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · intro l l1 l2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · omega
  · omega
  · omega
  · intro l l1 l2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega))


/-- `K = 67 + (-22) x` on `(3, 73/24]`. -/
theorem w1_cell {N p : ℕ} (hp : p.Prime) (h1 : 3 * N < 1 * p) (h2 : 24 * p ≤ 73 * N)
    (hN : 2000 ≤ N) :
    (67 : ℤ) * N + (-22) * p ≤ 1 * (((lstar2Kap des N p : ℕ) : ℤ) + 2) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hp0 : 0 < p := hp.pos
  have key := lstar2_cell2 (P := des) (N := N) (p := p) hp0 (by omega) (by omega) (by omega)
    (α1 := p - 3 * N) (β1 := 70 * N - 23 * p) (α2 := 6 * N - p) (β2 := p)
    (μ1 := 25) (u11 := 23) (u21 := 3) (u31 := 17) (u41 := -1)
    (μ2 := 24) (u12 := 22) (u22 := 2) (u32 := 17) (u42 := -1)
    (by omega) (by omega) (by omega) (by omega) (by cell_data) (by cell_data)
  omega

/-- `K = -6 + (2) x` on `(73/24, 70/23]`. -/
theorem w2_cell {N p : ℕ} (hp : p.Prime) (h1 : 73 * N < 24 * p) (h2 : 23 * p ≤ 70 * N)
    (hN : 2000 ≤ N) :
    (-6 : ℤ) * N + (2) * p ≤ 1 * (((lstar2Kap des N p : ℕ) : ℤ) + 2) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hp0 : 0 < p := hp.pos
  have key := lstar2_cell1 (P := des) (N := N) (p := p) hp0 (by omega) (by omega) (by omega)
    (α := 6 * N - p) (β := p) (μ := 24) (u1 := 22) (u2 := 2) (u3 := 17) (u4 := -1)
    (by omega) (by omega) (by cell_data)
  omega

/-- `K = 64 + (-21) x` on `(70/23, 64/21]`. -/
theorem w3_cell {N p : ℕ} (hp : p.Prime) (h1 : 70 * N < 23 * p) (h2 : 21 * p ≤ 64 * N)
    (hN : 2000 ≤ N) :
    (64 : ℤ) * N + (-21) * p ≤ 1 * (((lstar2Kap des N p : ℕ) : ℤ) + 2) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hp0 : 0 < p := hp.pos
  have key := lstar2_cell1 (P := des) (N := N) (p := p) hp0 (by omega) (by omega) (by omega)
    (α := 6 * N - p) (β := 70 * N - 22 * p) (μ := 24) (u1 := 22) (u2 := 2) (u3 := 17) (u4 := -1)
    (by omega) (by omega) (by cell_data)
  omega

/-- `K = -53 + (17) x` on `(53/17, 78/25]`. -/
theorem w4_cell {N p : ℕ} (hp : p.Prime) (h1 : 53 * N < 17 * p) (h2 : 25 * p ≤ 78 * N)
    (hN : 2000 ≤ N) :
    (-53 : ℤ) * N + (17) * p ≤ 1 * (((lstar2Kap des N p : ℕ) : ℤ) + 2) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hp0 : 0 < p := hp.pos
  have key := lstar2_cell1 (P := des) (N := N) (p := p) hp0 (by omega) (by omega) (by omega)
    (α := 75 * N - 24 * p) (β := 22 * N - 7 * p) (μ := 24) (u1 := 22) (u2 := 3) (u3 := 16) (u4 := -1)
    (by omega) (by omega) (by cell_data)
  omega

/-- `K = 25 + (-8) x` on `(78/25, 25/8]`. -/
theorem w5_cell {N p : ℕ} (hp : p.Prime) (h1 : 78 * N < 25 * p) (h2 : 8 * p ≤ 25 * N)
    (hN : 2000 ≤ N) :
    (25 : ℤ) * N + (-8) * p ≤ 1 * (((lstar2Kap des N p : ℕ) : ℤ) + 2) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hp0 : 0 < p := hp.pos
  have key := lstar2_cell1 (P := des) (N := N) (p := p) hp0 (by omega) (by omega) (by omega)
    (α := p - 3 * N) (β := 22 * N - 7 * p) (μ := 24) (u1 := 22) (u2 := 3) (u3 := 16) (u4 := -1)
    (by omega) (by omega) (by cell_data)
  omega

/-- `K = -75 + (24) x` on `(25/8, 69/22]`. -/
theorem w6_cell {N p : ℕ} (hp : p.Prime) (h1 : 25 * N < 8 * p) (h2 : 22 * p ≤ 69 * N)
    (hN : 2000 ≤ N) :
    (-75 : ℤ) * N + (24) * p ≤ 1 * (((lstar2Kap des N p : ℕ) : ℤ) + 2) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hp0 : 0 < p := hp.pos
  have key := lstar2_cell1 (P := des) (N := N) (p := p) hp0 (by omega) (by omega) (by omega)
    (α := 75 * N - 23 * p) (β := p) (μ := 23) (u1 := 21) (u2 := 2) (u3 := 16) (u4 := -1)
    (by omega) (by omega) (by cell_data)
  omega

/-- `K = -6 + (2) x` on `(69/22, 22/7]`. -/
theorem w7_cell {N p : ℕ} (hp : p.Prime) (h1 : 69 * N < 22 * p) (h2 : 7 * p ≤ 22 * N)
    (hN : 2000 ≤ N) :
    (-6 : ℤ) * N + (2) * p ≤ 1 * (((lstar2Kap des N p : ℕ) : ℤ) + 2) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hp0 : 0 < p := hp.pos
  have key := lstar2_cell1 (P := des) (N := N) (p := p) hp0 (by omega) (by omega) (by omega)
    (α := 6 * N - p) (β := p) (μ := 23) (u1 := 21) (u2 := 2) (u3 := 16) (u4 := -1)
    (by omega) (by omega) (by cell_data)
  omega

/-- `K = 16 + (-5) x` on `(22/7, 16/5]`. -/
theorem w8_cell {N p : ℕ} (hp : p.Prime) (h1 : 22 * N < 7 * p) (h2 : 5 * p ≤ 16 * N)
    (hN : 2000 ≤ N) :
    (16 : ℤ) * N + (-5) * p ≤ 1 * (((lstar2Kap des N p : ℕ) : ℤ) + 2) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hp0 : 0 < p := hp.pos
  have key := lstar2_cell1 (P := des) (N := N) (p := p) hp0 (by omega) (by omega) (by omega)
    (α := 6 * N - p) (β := 22 * N - 6 * p) (μ := 23) (u1 := 21) (u2 := 2) (u3 := 16) (u4 := -1)
    (by omega) (by omega) (by cell_data)
  omega

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger9
