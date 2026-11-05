module

public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Cells

@[expose] public section
set_option Elab.async false

/-!
# Theorem L* window cells (lane G6c), `h ≥ p` (`x ≤ 3`)

Each cell is one residue interval `[α, β)` of constant type `(m; u1, u2; u3, u4)`; the bound
`kap ≥ (β - α) - (q - p)` is read off `lstar_cell1`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger8
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section

local notation "des" => D58.Odd.design

/-- `s = 25`, `K = 20 x - 59` on `(59/20, 3]`: type `(25; 23, 3; 17, -1)`, `[78N - 26p, 22N - 7p + 1)`. -/
theorem lW6_cell {N p : ℕ} (hp : p.Prime) (h1 : 59 * N < 20 * p) (h2 : p ≤ 3 * N) (hN : 2000 ≤ N) :
    (-59 : ℤ) * N + 20 * p ≤ 1 * (((lstarKap des N p : ℕ) : ℤ) + 2) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hp0 : 0 < p := hp.pos
  have h3 : p ≠ 3 * N := fun h => (Nat.not_prime_mul (by norm_num) (by omega)) (h ▸ hp)
  have key := lstar_cell1 (P := des) (N := N) (p := p) hp0 (by omega) (by omega)
    (α := 78 * N - 26 * p) (β := 22 * N - 7 * p + 1) (by omega) (by omega) 25 23 3 17 (-1) (by
      intro ℓ l1 l2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
  omega

/-- `s = 26`, `K = 58 - 20 x` on `(23/8, 29/10]`: type `(26; 24, 3; 18, -1)`, `[9N - 3p, 70N - 24p)`. -/
theorem lW5_cell {N p : ℕ} (hp : p.Prime) (h1 : 23 * N < 8 * p) (h2 : 10 * p ≤ 29 * N)
    (hN : 2000 ≤ N) :
    (58 : ℤ) * N + (-20) * p ≤ 1 * (((lstarKap des N p : ℕ) : ℤ) + 2) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hp0 : 0 < p := hp.pos
  have key := lstar_cell1 (P := des) (N := N) (p := p) hp0 (by omega) (by omega)
    (α := 9 * N - 3 * p) (β := 70 * N - 24 * p) (by omega) (by omega) 26 24 3 18 (-1) (by
      intro ℓ l1 l2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
  omega

/-- `s = 26`, `K = 4 x - 11` on `(48/17, 23/8]`: type `(26; 24, 3; 18, -1)`, `[78N - 27p, 70N - 24p)`. -/
theorem lW4_cell {N p : ℕ} (hp : p.Prime) (h1 : 48 * N < 17 * p) (h2 : 8 * p ≤ 23 * N)
    (hN : 2000 ≤ N) :
    (-11 : ℤ) * N + 4 * p ≤ 1 * (((lstarKap des N p : ℕ) : ℤ) + 2) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hp0 : 0 < p := hp.pos
  have key := lstar_cell1 (P := des) (N := N) (p := p) hp0 (by omega) (by omega)
    (α := 78 * N - 27 * p) (β := 70 * N - 24 * p) (by omega) (by omega) 26 24 3 18 (-1) (by
      intro ℓ l1 l2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
  omega

/-- `s = 26`, `K = 21 x - 59` on `(59/21, 2.8235]`: type `(26; 24, 3; 18, -1)`,
`[78N - 27p, 22N - 7p + 1)`. -/
theorem lW3_cell {N p : ℕ} (hp : p.Prime) (h1 : 59 * N < 21 * p) (h2 : 10000 * p ≤ 28235 * N)
    (hN : 2000 ≤ N) :
    (-59 : ℤ) * N + 21 * p ≤ 1 * (((lstarKap des N p : ℕ) : ℤ) + 2) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hp0 : 0 < p := hp.pos
  have key := lstar_cell1 (P := des) (N := N) (p := p) hp0 (by omega) (by omega)
    (α := 78 * N - 27 * p) (β := 22 * N - 7 * p + 1) (by omega) (by omega) 26 24 3 18 (-1) (by
      intro ℓ l1 l2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
  omega

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger8
