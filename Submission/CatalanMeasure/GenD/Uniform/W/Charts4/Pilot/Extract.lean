module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.RowsData
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Arith146O
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.JetsGeneric
@[expose] public section
set_option Elab.async false

/-!
# The jets of the L0146 packet and the extraction of the slot order conditions
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3 Finset
noncomputable section
variable {N p : ℕ} [Fact p.Prime]

local notation "Fp" => ZMod p

/-- Width of the `i`-th stored group (exact affine form, as a natural number). -/
def wd (N p i : ℕ) : ℕ := ((wInt N p).getD i 0).toNat

theorem wNatO_eq (g : Fin packetO.charts.length) : wNatO g N p = wd N p g.val := rfl

/-- The `k`-th jet of the stored group `g`. -/
def jetP (N p : ℕ) [Fact p.Prime] (g k : ℕ) :
    (Fin p → Fin packetO.d → ZMod p) →ₗ[ZMod p] (Fin packetO.d → ZMod p) :=
  match g with
  | 0 => Charts3.taylorJet (m := p) (d := packetO.d) (-1) k
  | 1 => jet0 k
  | 2 => jet0 (wd N p 1 + k)
  | 3 => Charts3.taylorJet (m := p) (d := packetO.d) 1 k
  | 4 => Charts3.taylorJet (m := p) (d := packetO.d) 1 (wd N p 3 + k)
  | 5 => Charts3.taylorJet (m := p) (d := packetO.d) 1 (wd N p 3 + wd N p 4 + k)
  | 6 => jetInf k
  | 7 => jetInf (wd N p 6 + k)
  | 8 => jetInf (wd N p 6 + wd N p 7 + k)
  | 9 => jetInf (wd N p 6 + wd N p 7 + wd N p 8 + k)
  | _ => jetInf (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + k)

/-- The jet kernel hypothesis. -/
def JetKer (N p : ℕ) [Fact p.Prime] (x : Fin p → Fin packetO.d → ZMod p) : Prop :=
  ∀ g : Fin packetO.charts.length, ∀ k : Fin (wNatO g N p),
    chartMap packetO (packetO.chart g) p 44 (jetP N p g k x) = 0

theorem chart_rows (g : Fin packetO.charts.length) : (packetO.chart g).rows = oRows g.val := by
  obtain ⟨i, hi⟩ := g
  have : i < 11 := by have : packetO.charts.length = 11 := packetO_len; omega
  simp [Packet.chart, packetO, chartO, List.getElem_map, List.getElem_range]

theorem vanish_hasRow (x : Fin p → Fin 4 → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (k : ℕ)
    (hk : k < wd N p g) (r : List ℤ) (hr : hasRow g r = true) :
    ∑ c : Fin 44, ((r.getD c 0 : ℤ) : Fp) * emb packetO p 44 (jetP N p g k x) c = 0 := by
  have hg' : g < packetO.charts.length := by rw [packetO_len]; exact hg
  have h := hker ⟨g, hg'⟩ ⟨k, hk⟩
  have hrows := chart_rows (⟨g, hg'⟩ : Fin packetO.charts.length)
  have hmem : r ∈ oRows g := List.contains_iff_mem.mp hr
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hmem
  have hi' : i < (packetO.chart ⟨g, hg'⟩).rows.length := by rw [hrows]; exact hi
  have := row_of_chart (K := 44) _ h i hi'
  convert this using 2
  rw [Mx, hrows, List.getD_eq_getElem _ _ hi, hir]

theorem sum_unitL (c0 : Fin 44) (f : Fin 44 → Fp) :
    ∑ c : Fin 44, (((unitL c0).getD c 0 : ℤ) : Fp) * f c = f c0 := by
  have : ∀ c : Fin 44, ((unitL c0).getD c 0 : ℤ) = if c = c0 then 1 else 0 := by
    intro c
    unfold unitL
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [Fin.ext_iff, c.isLt]
  simp_rw [this]
  simp

theorem sum_diff2L (a b : Fin 44) (hab : a ≠ b) (f : Fin 44 → Fp) :
    ∑ c : Fin 44, (((diff2L a b).getD c 0 : ℤ) : Fp) * f c = f a - 2 * f b := by
  have : ∀ c : Fin 44, ((diff2L a b).getD c 0 : ℤ) =
      (if c = a then 1 else 0) - (if c = b then 2 else 0) := by
    intro c
    unfold diff2L
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [Fin.ext_iff, c.isLt]
  simp_rw [this]
  push_cast
  simp [sub_mul, Finset.sum_sub_distrib]

theorem sum_virtBL (f : Fin 44 → Fp) :
    ∑ c : Fin 44, ((virtBL.getD c 0 : ℤ) : Fp) * f c = f 1 - f 3 + f 41 := by
  have : ∀ c : Fin 44, (virtBL.getD c 0 : ℤ) =
      (if c = 1 then 1 else 0) - (if c = 3 then 1 else 0) + (if c = 41 then 1 else 0) := by
    intro c
    unfold virtBL
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [Fin.ext_iff, c.isLt]
  simp_rw [this]
  push_cast
  simp [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem sum_virtTL (f : Fin 44 → Fp) :
    ∑ c : Fin 44, ((virtTL.getD c 0 : ℤ) : Fp) * f c = f 37 + f 39 := by
  have : ∀ c : Fin 44, (virtTL.getD c 0 : ℤ) = (if c = 37 then 1 else 0) + (if c = 39 then 1 else 0) := by
    intro c
    unfold virtTL
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [Fin.ext_iff, c.isLt]
  simp_rw [this]
  push_cast
  simp [add_mul, Finset.sum_add_distrib]

end
end CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
