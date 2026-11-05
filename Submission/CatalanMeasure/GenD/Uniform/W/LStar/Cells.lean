module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Count
public import Submission.CatalanMeasure.GenD.D58.OddProfile
@[expose] public section
set_option Elab.async false

/-!
# Window cells of Theorem L* (lane G6c)

`lstarLB` is the `NullityLB` of Theorem L*.  `lstar_cell1` turns a *single residue interval*
`[α, β)` of constant combinatorial type `(m; u1, u2; u3, u4)` into the bound
`β - α + p ≤ lstarKap + q`; the per-residue hypotheses are linear in `(N, p, ℓ)` and are
discharged by `omega` in each cell.
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
noncomputable section
variable {P : Parameters} {N p : ℕ}

/-- **`lstarLB`**: Theorem L* as a nullity lower bound. -/
def lstarLB (P : Parameters) (hP : Admissible P) : NullityLB P where
  kap := lstarKap P
  ok := fun N p hN hp hp2 hH => by
    haveI : Fact p.Prime := ⟨hp⟩
    exact lstarKap_le_nullity hP hN hp2 hH

theorem sum_interval (p α β : ℕ) (hαβ : α ≤ β) (hβ : β ≤ p) :
    ∑ ℓ ∈ Finset.range p, (if α ≤ ℓ ∧ ℓ < β then 1 else 0) = β - α := by
  rw [← Finset.card_filter]
  have : (Finset.range p).filter (fun ℓ => α ≤ ℓ ∧ ℓ < β) = Finset.Ico α β := by
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]

/-- One residue interval of constant type. -/
theorem lstar_cell1 (hp : 0 < p) (hLb : p ≤ P.L N - P.b N) (hpq : p ≤ P.q N) {α β : ℕ}
    (hαβ : α ≤ β) (hβ : β ≤ p) (m u1 u2 : ℕ) (u3 u4 : ℤ)
    (hyp : ∀ ℓ, α ≤ ℓ → ℓ < β →
      (m * p + ℓ + 1 ≤ P.H N) ∧ (P.H N ≤ m * p + p + ℓ) ∧ (p ≤ P.h N) ∧
      ((P.h N - p) + (p - 1) / 2 + m * p + ℓ + 1 ≤ P.H N) ∧
      (u1 * p + ℓ + 1 ≤ P.L N) ∧ (P.b N ≤ u2 * p + ℓ) ∧ (u2 ≤ u1) ∧
      ((P.n N : ℤ) - P.g N - 1 +
        ((p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ℓ - m * p) + ((P.h N : ℤ) - p)) < (u3 + 1) * p) ∧
      ((P.g N : ℤ) +
        ((p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ℓ - m * p) + ((P.h N : ℤ) - p)) < (1 - u4) * p) ∧
      (u4 ≤ u3 + 1) ∧ ((1 : ℤ) + u3 + 1 ≤ u1 - u2 + u4)) :
    β - α + p ≤ lstarKap P N p + P.q N := by
  classical
  have h := lstarKap_ge (P := P) (N := N) hp hLb hpq
    (fun ℓ => if α ≤ ℓ ∧ ℓ < β then 1 else 0) (fun ℓ hℓ => by
      by_cases hc : α ≤ ℓ ∧ ℓ < β
      · rw [if_pos hc]
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hyp ℓ hc.1 hc.2
        exact gap_ge P N p ℓ hp hℓ m u1 u2 u3 u4 1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
      · rw [if_neg hc]
        have := lrank_le_jCard P N p ℓ
        have := jCard_pos (P := P) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p α β hαβ hβ] at h
  exact h

/-- The design facts as linear equalities. -/
theorem design_facts (N : ℕ) :
    D58.Odd.design.H N = 78 * N ∧ D58.Odd.design.L N = 70 * N ∧ D58.Odd.design.n N = 58 * N ∧
    D58.Odd.design.b N = 9 * N ∧ D58.Odd.design.q N = 3 * N ∧ D58.Odd.design.g N = 5 * N ∧
    D58.Odd.design.h N = 3 * N := by
  exact ⟨D58.Odd.design_H N, D58.Odd.design_L N, rfl, rfl, rfl, rfl, rfl⟩

end
end CatalanMeasure.GenD.Uniform.W.LStar
