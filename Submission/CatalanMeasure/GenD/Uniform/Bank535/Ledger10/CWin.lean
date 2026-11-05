module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger9.Merge11
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.CLB

@[expose] public section
set_option Elab.async false

/-!
# Theorem C window cells (lane G6e)

Each piece fixes explicit interval ends `lo`, `hi` (affine in `N`, `p`) of the positions `e` of a rational
cell; `cCellLB_kap_ge` gives `hi - lo - (p - q) ≤ kap`.  All side conditions are linear (`omega`).
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger10
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.LStar CatalanMeasure.GenD.Uniform.W.TheoremC
open CatalanMeasure.GenD.Uniform.Bank540.Ledger
noncomputable section

local notation "des" => D58.Odd.design

set_option hygiene false in
macro "cond_data" c:ident : tactic => `(tactic| (
  unfold cCond
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · (try simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · intro e l1 l2
    simp only [$c:ident, hH, hL, hn, hb, hq, hg, hh]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try norm_num) <;> omega))

/-- `K = -58 + (17) x` on `(58/17, 24/7]`, cell 1. -/
theorem c1a_cell {N p : ℕ} (hp : p.Prime) (h1 : 58 * N < 17 * p) (h2 : 7 * p ≤ 24 * N)
    (hN : cell1.modulus ≤ N) :
    (-58 : ℤ) * N + (17) * p ≤ 1 * (((cCellLB cell1 des adm).kap N p : ℕ) + 2 : ℤ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hm := cell1.modulus_pos y1_ne
  have hcop := cell1.coprime_of_gt y1_ne hp (by omega)
  have hqp : 0 < D58.Odd.design.q N := by rw [hq]; omega
  have key := cCellLB_kap_ge cell1 des adm (lo := 69 * N - 20 * p) (hi := 8 * N - 2 * p - 1)
    hcop hqp (by cond_data cell1)
  omega

/-- `K = -10 + (3) x` on `(24/7, 69/20]`, cell 1. -/
theorem c1b_cell {N p : ℕ} (hp : p.Prime) (h1 : 24 * N < 7 * p) (h2 : 20 * p ≤ 69 * N)
    (hN : cell1.modulus ≤ N) :
    (-10 : ℤ) * N + (3) * p ≤ 1 * (((cCellLB cell1 des adm).kap N p : ℕ) + 2 : ℤ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hm := cell1.modulus_pos y1_ne
  have hcop := cell1.coprime_of_gt y1_ne hp (by omega)
  have hqp : 0 < D58.Odd.design.q N := by rw [hq]; omega
  have key := cCellLB_kap_ge cell1 des adm (lo := 69 * N - 20 * p) (hi := 56 * N - 16 * p - 1)
    hcop hqp (by cond_data cell1)
  omega

/-- `K = 59 + (-17) x` on `(69/20, 59/17]`, cell 1. -/
theorem c1c_cell {N p : ℕ} (hp : p.Prime) (h1 : 69 * N < 20 * p) (h2 : 17 * p ≤ 59 * N)
    (hN : cell1.modulus ≤ N) :
    (59 : ℤ) * N + (-17) * p ≤ 1 * (((cCellLB cell1 des adm).kap N p : ℕ) + 2 : ℤ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hm := cell1.modulus_pos y1_ne
  have hcop := cell1.coprime_of_gt y1_ne hp (by omega)
  have hqp : 0 < D58.Odd.design.q N := by rw [hq]; omega
  have key := cCellLB_kap_ge cell1 des adm (lo := 0) (hi := 56 * N - 16 * p - 1)
    hcop hqp (by cond_data cell1)
  omega

/-- `K = -58 + (16) x` on `(29/8, 69/19]`, cell 2. -/
theorem c2a_cell {N p : ℕ} (hp : p.Prime) (h1 : 29 * N < 8 * p) (h2 : 19 * p ≤ 69 * N)
    (hN : cell2.modulus ≤ N) :
    (-58 : ℤ) * N + (16) * p ≤ 1 * (((cCellLB cell2 des adm).kap N p : ℕ) + 2 : ℤ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hm := cell2.modulus_pos y2_ne
  have hcop := cell2.coprime_of_gt y2_ne hp (by omega)
  have hqp : 0 < D58.Odd.design.q N := by rw [hq]; omega
  have key := cCellLB_kap_ge cell2 des adm (lo := 69 * N - 19 * p) (hi := 8 * N - 2 * p - 1)
    hcop hqp (by cond_data cell2)
  omega

/-- `K = 11 + (-3) x` on `(69/19, 11/3]`, cell 2. -/
theorem c2b_cell {N p : ℕ} (hp : p.Prime) (h1 : 69 * N < 19 * p) (h2 : 3 * p ≤ 11 * N)
    (hN : cell2.modulus ≤ N) :
    (11 : ℤ) * N + (-3) * p ≤ 1 * (((cCellLB cell2 des adm).kap N p : ℕ) + 2 : ℤ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hm := cell2.modulus_pos y2_ne
  have hcop := cell2.coprime_of_gt y2_ne hp (by omega)
  have hqp : 0 < D58.Odd.design.q N := by rw [hq]; omega
  have key := cCellLB_kap_ge cell2 des adm (lo := 0) (hi := 8 * N - 2 * p - 1)
    hcop hqp (by cond_data cell2)
  omega

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger10
