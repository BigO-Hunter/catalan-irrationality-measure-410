module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar2.Count2
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Cells
@[expose] public section
set_option Elab.async false

/-!
# Window cells of Theorem L\* for `h < p` (lane G6d)

`lstar2_cell1` / `lstar2_cell2` turn one / two residue intervals `[α, β)` of constant type
`(μ; u1, u2; u3, u4)` (gain `1` per residue) into `Σ (β - α) ≤ lstar2Kap`.  All hypotheses are
linear in `(N, p, ℓ)` and are discharged by `omega` in each cell.
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar2
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section
variable {P : Parameters} {N p : ℕ}

/-- Linear data of one residue interval of constant type (gain `1` per residue). -/
def CellData (P : Parameters) (N p α β μ u1 u2 : ℕ) (u3 u4 : ℤ) : Prop :=
  p - P.h N ≤ α ∧
  (∀ ℓ'', α - (p - P.h N) ≤ ℓ'' → ℓ'' < β →
    1 ≤ u2 ∧ u1 * p + ℓ'' < P.L N ∧ P.b N ≤ u2 * p + ℓ'' ∧ P.L N ≤ (u1 + 1) * p + ℓ'' ∧
      (u2 - 1) * p + ℓ'' < P.b N) ∧
  u2 ≤ u1 ∧ u4 ≤ u3 + 1 ∧ ((1 : ℕ) : ℤ) + u3 + 1 ≤ u1 - u2 + u4 ∧
  (∀ ℓ, α ≤ ℓ → ℓ < β →
    μ * p + (ℓ - (p - P.h N)) + 1 ≤ P.H N ∧
    P.H N ≤ μ * p + p + (ℓ - (p - P.h N)) ∧
    (p - 1) / 2 + μ * p + (ℓ - (p - P.h N)) + 1 ≤ P.H N ∧
    (P.n N : ℤ) - P.g N - 1 +
      ((p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ((ℓ - (p - P.h N) : ℕ) : ℤ) - μ * p)) < (u3 + 1) * p ∧
    (P.g N : ℤ) +
      ((p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ((ℓ - (p - P.h N) : ℕ) : ℤ) - μ * p)) < (1 - u4) * p)

theorem cell_gap (hp : 0 < p) (hhp : P.h N ≤ p) {α β μ u1 u2 : ℕ} {u3 u4 : ℤ}
    (hd : CellData P N p α β μ u1 u2 u3 u4) {ℓ : ℕ} (h1 : α ≤ ℓ) (h2 : ℓ < β) (hℓ : ℓ < p) :
    1 + lrank2 P N p ℓ + 1 ≤ (jSet P N p ℓ).card := by
  obtain ⟨hα, hJ, h12, hu, hg, hyp⟩ := hd
  obtain ⟨a1, a2, a3, a4, a5⟩ := hyp ℓ h1 h2
  exact gap2_ge P N p ℓ hp hℓ hhp μ u1 u2 u3 u4 1 (by omega)
    (fun ℓ'' l1 l2 => by
      obtain ⟨b1, b2, b3, b4, b5⟩ := hJ ℓ'' (by omega) (by omega)
      exact jSet_eq_Icc hp b1 b2 b3 b4 b5)
    a1 a2 a3 a4 a5 hu h12 hg

theorem lstar2_cell1 (hp : 0 < p) (hLb : p ≤ P.L N - P.b N) (hqp : P.q N ≤ p) (hhp : P.h N ≤ p) {α β μ u1 u2 : ℕ}
    {u3 u4 : ℤ} (hαβ : α ≤ β) (hβ : β ≤ p) (hd : CellData P N p α β μ u1 u2 u3 u4) :
    β - α ≤ lstar2Kap P N p := by
  classical
  have h := lstar2Kap_ge (P := P) (N := N) hp hqp (fun ℓ => if α ≤ ℓ ∧ ℓ < β then 1 else 0)
    (fun ℓ hℓ => by
      by_cases hc : α ≤ ℓ ∧ ℓ < β
      · rw [if_pos hc]
        exact cell_gap hp hhp hd hc.1 hc.2 hℓ
      · rw [if_neg hc]
        have : lrank2 P N p ℓ ≤ (jSet P N p ℓ).card - 1 := by
          unfold lrank2
          split_ifs <;> first | exact min_le_right _ _ | exact le_rfl | exact lrank_le_jCard P N p ℓ
        have := jCard_pos (P := P) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p α β hαβ hβ] at h
  exact h

theorem lstar2_cell2 (hp : 0 < p) (hLb : p ≤ P.L N - P.b N) (hqp : P.q N ≤ p) (hhp : P.h N ≤ p) {α1 β1 α2 β2 μ1 u11 u21 μ2
    u12 u22 : ℕ} {u31 u41 u32 u42 : ℤ} (h1 : α1 ≤ β1) (hb1 : β1 ≤ α2) (h2 : α2 ≤ β2)
    (hβ : β2 ≤ p) (hd1 : CellData P N p α1 β1 μ1 u11 u21 u31 u41)
    (hd2 : CellData P N p α2 β2 μ2 u12 u22 u32 u42) :
    (β1 - α1) + (β2 - α2) ≤ lstar2Kap P N p := by
  classical
  have h := lstar2Kap_ge (P := P) (N := N) hp hqp
    (fun ℓ => (if α1 ≤ ℓ ∧ ℓ < β1 then 1 else 0) + (if α2 ≤ ℓ ∧ ℓ < β2 then 1 else 0))
    (fun ℓ hℓ => by
      by_cases hc1 : α1 ≤ ℓ ∧ ℓ < β1
      · have hc2 : ¬ (α2 ≤ ℓ ∧ ℓ < β2) := fun h => by omega
        rw [if_pos hc1, if_neg hc2]
        have := cell_gap hp hhp hd1 hc1.1 hc1.2 hℓ
        omega
      · by_cases hc2 : α2 ≤ ℓ ∧ ℓ < β2
        · rw [if_neg hc1, if_pos hc2]
          have := cell_gap hp hhp hd2 hc2.1 hc2.2 hℓ
          omega
        · rw [if_neg hc1, if_neg hc2]
          have : lrank2 P N p ℓ ≤ (jSet P N p ℓ).card - 1 := by
            unfold lrank2
            split_ifs <;> first | exact min_le_right _ _ | exact le_rfl | exact lrank_le_jCard P N p ℓ
          have := jCard_pos (P := P) (N := N) hp hLb hℓ
          omega)
  rw [Finset.sum_add_distrib, sum_interval p α1 β1 h1 (by omega),
    sum_interval p α2 β2 h2 hβ] at h
  exact h

end
end CatalanMeasure.GenD.Uniform.W.LStar2
