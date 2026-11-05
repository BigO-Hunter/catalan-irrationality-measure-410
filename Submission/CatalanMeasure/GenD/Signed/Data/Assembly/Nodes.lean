module

public import Submission.CatalanMeasure.GenD.Signed.Glue410
public import Submission.CatalanMeasure.GenD.Signed.MarkedCap
public import Submission.CatalanMeasure.GenD.Signed.Data.S1.Gap
public import Submission.CatalanMeasure.GenD.Analytic.GapWeights
public import Submission.CatalanMeasure.GenD.D58.OddProfile

@[expose] public section

/-!
# 410 assembly, row P4: the cap data of the real marked nodes

The marked rows of the near-type sheet bound are `realCoordinate` images of distinct nodes
`τ N a`, `τ := gapNodesD Odd.design aGap` (gap `g = 401/2500`, `J = 53 N` nodes, `n = 58 N`).
* `nodeCap_real`: `NodeCap g xc C1 n umin` of `realCoordinate ∘ τ N` with the 410 constants
  `gs = 401/2500`, `xc = 999/1000`, `C1 = 9631/20000`, `umin N = √(1-a²)/(106 N + 2)`
  (from `nodeCap_gap` and `Glue410.nodeCap_gap_mono`, `gap_C1_le`).
* `markedCap_real`: `MarkedCap` of every `NodeSub τ` row set with `y ∈ (-1, 1)` (all `N`; for `N = 0` the
  node set is empty).
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter
open CatalanMeasure.Signed CatalanMeasure.GenD.Analytic OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.S1

noncomputable section

/-- The gap nodes of the 410 design. -/
abbrev nodesτ : (N : ℕ) → Fin ((D58.Odd.design.n0 - D58.Odd.design.g0) * N) → ℝ :=
  gapNodesD D58.Odd.design aGap

/-- The distance of the nodes from `1`: `umin N = √(1-a²) / (2 (53 N + 1))`. -/
def umin410 (N : ℕ) : ℝ := Real.sqrt (1 - aGap ^ 2) / (106 * (N : ℝ) + 2)

theorem one_sub_aGap_sq_pos : 0 < 1 - aGap ^ 2 := by
  have h0 := aGap_pos
  have h1 := aGap_lt_one
  nlinarith

theorem umin410_pos (N : ℕ) : 0 < umin410 N := by
  unfold umin410
  have := Real.sqrt_pos.2 one_sub_aGap_sq_pos
  positivity

theorem umin410_le_one (N : ℕ) : umin410 N ≤ 1 := by
  unfold umin410
  have hs : Real.sqrt (1 - aGap ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith [aGap_pos, sq_nonneg aGap]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [div_le_one (by positivity)]
  linarith

theorem cast_nodes (N : ℕ) :
    (((D58.Odd.design.n0 - D58.Odd.design.g0) * N : ℕ) : ℝ) = 53 * (N : ℝ) := by
  norm_num [D58.Odd.design]

/-- **`NodeCap` of the real nodes** (`N ≥ 1`). -/
theorem nodeCap_real {N : ℕ} (hN : 0 < N) :
    NodeCap (401 / 2500) (999 / 1000) (9631 / 20000) (58 * (N : ℝ)) (umin410 N)
      (fun i => realCoordinate (nodesτ N i)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hJ := cast_nodes N
  have h := Glue410.nodeCap_gap_mono (g := 401 / 2500) (by norm_num) (by norm_num)
    (xc := 999 / 1000) (n := 58 * (N : ℝ)) (by norm_num) (by positivity)
    ((D58.Odd.design.n0 - D58.Odd.design.g0) * N)
    (gs' := 401 / 2500) (xc' := 999 / 1000) (C1' := 9631 / 20000) (umin' := umin410 N)
    le_rfl le_rfl
    (Glue410.gap_C1_le hN hJ rfl rfl (by norm_num))
    (by
      rw [hJ, ← aGap_eq]
      unfold umin410
      apply le_of_eq
      congr 1
      ring)
  rw [← aGap_eq] at h
  exact h

/-- **`MarkedCap` of the actual marked rows** (every `N`). -/
theorem markedCap_real (N : ℕ) {m : ℕ} {y : Fin m → ℝ} (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1)
    (h : NodeSub nodesτ N m y) :
    MarkedCap (401 / 2500) (999 / 1000) (9631 / 20000) (58 * (N : ℝ)) (umin410 N) y := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨a, _, _⟩ := h
    refine ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩ <;>
      exact absurd (a j).isLt (by simp)
  · exact markedCap_of_nodeSub (nodeCap_real hN) hy h

end

end CatalanMeasure.GenD.Signed.Data.Assembly
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.nodeCap_real
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.markedCap_real
