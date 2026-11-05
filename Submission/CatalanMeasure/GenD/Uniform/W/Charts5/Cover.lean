module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts5.PsiRows
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Graph146
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.MonoHost
@[expose] public section
set_option Elab.async false

/-!
# `CoverPt2` for the L0146 packet (window `(6, 152/25]`)

At every active column `j ∈ [9N, 70N)` and seen position `e`, the seen covector `ψ(J, S)` with `J = j / p ∈ 1..11`,
`S ∈ {12, 11}` is read off a stored row (`psi_row`), through the jets `jet0` (groups 1, 2: positions `e < w1 + w2`)
or `jetInf` (group 6, reversed index `p - 1 - e`); for `J = 11` the graph row of groups 1, 2 and the slack row
(unit `e_43`, groups 6..9) are both used.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts5
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O CatalanMeasure.GenD.D58.Odd CatalanMeasure.Parametric
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts Finset
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem design_b (N : ℕ) : design.b N = 9 * N := by
  simp [Parameters.b, Parameters.C, Parameters.L, Parameters.n, Parameters.q,
    Parameters.g, Parameters.h, design]; try ring
theorem design_L (N : ℕ) : design.L N = 70 * N := by
  simp [Parameters.b, Parameters.C, Parameters.L, Parameters.n, Parameters.q,
    Parameters.g, Parameters.h, design]; try ring

theorem rowOK_lt {g i J : ℕ} {S ε : ℤ} (h : rowOK g i J S ε = true) : i < (oRows g).length := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1

theorem chart_row_sum (g i : ℕ) (hg : g < 11) (hi : i < (oRows g).length)
    (y : Fin packetO.d → Fp)
    (hy : chartMap packetO (packetO.chart ⟨g, by rw [packetO_len]; exact hg⟩) p 44 y = 0) :
    ∑ c : Fin 44, ((((oRows g).getD i []).getD c 0 : ℤ) : Fp) * emb packetO p 44 y c = 0 := by
  have hrows := chart_rows (⟨g, by rw [packetO_len]; exact hg⟩ : Fin packetO.charts.length)
  have hi' : i < (packetO.chart ⟨g, by rw [packetO_len]; exact hg⟩).rows.length := by
    rw [hrows]; exact hi
  have := row_of_chart (K := 44) _ hy i hi'
  convert this using 2
  rw [Mx, hrows]

theorem chart_unit43 (g : ℕ) (hg : g < 11) (h : hasRow g (unitL 43) = true) (y : Fin packetO.d → Fp)
    (hy : chartMap packetO (packetO.chart ⟨g, by rw [packetO_len]; exact hg⟩) p 44 y = 0) :
    emb packetO p 44 y 43 = 0 := by
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp (List.contains_iff_mem.mp h)
  have := chart_row_sum g i hg hi y hy
  rw [List.getD_eq_getElem _ _ hi, hir] at this
  have e := sum_unitL (43 : Fin 44) (emb packetO p 44 y)
  have e2 : ((43 : Fin 44) : ℕ) = 43 := rfl
  rw [e2] at e
  exact e.symm.trans this

theorem jet0_eq (m : ℕ) (e : Fin p) (h : m = e.val) :
    (jet0 m : (Fin p → Fin packetO.d → Fp) →ₗ[Fp] (Fin packetO.d → Fp)) = LinearMap.proj e := by
  subst h; simp [jet0, e.isLt]

theorem jetInf_eq (m : ℕ) (e : Fin p) (h : m = p - 1 - e.val) :
    (jetInf m : (Fin p → Fin packetO.d → Fp) →ₗ[Fp] (Fin packetO.d → Fp)) = LinearMap.proj e := by
  have hm : m < p := by have := e.isLt; omega
  simp only [jetInf, dif_pos hm]
  congr 1
  exact Fin.ext (by simp only; omega)

/-- A seen covector read off one stored row. -/
theorem cover_row (M : MonoData design N p packetO.n) (hM : pd146.Realises M.prof) (hp : 13 < p)
    {g i J : ℕ} {S ε : ℤ} (hg : g < 11) (hok : rowOK g i J S ε = true) (hJ : J < 12)
    (hS : S.toNat + 3 ≤ 15) (hH : S.toNat + 3 ≤ design.H N) (y : Fin packetO.d → Fp)
    (hy : chartMap packetO (packetO.chart ⟨g, by rw [packetO_len]; exact hg⟩) p 44 y = 0) :
    M.sys.prof.psi (design.H N) J S (emb packetO p packetO.n y) =
      emb packetO p 44 y 42 + (ε : Fp) * emb packetO p 44 y 43 :=
  psi_row hp M.prof hM hok hJ hS hH (emb packetO p 44 y) (chart_row_sum g i hg (rowOK_lt hok) y hy)

end
end CatalanMeasure.GenD.Uniform.W.Charts5
