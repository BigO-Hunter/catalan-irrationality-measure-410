module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Data
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Order of a row polynomial from the leading groups of a point chain
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx)

def rowsOf (pk : Packet) (g : ℕ) : List (List ℤ) :=
  match pk.charts[g]? with
  | some c => c.rows
  | none => []

theorem rowsOf_eq (pk : Packet) (g : ℕ) (hg : g < pk.charts.length) : (pk.chart ⟨g, hg⟩).rows = rowsOf pk g := by
  simp [CatalanMeasure.GenD.Uniform.W.Prof.Packet.chart, rowsOf, List.getElem?_eq_getElem hg]

/-- The groups at `pt0`, from the first one on, that contain the row `v`. -/
def lead (pk : Packet) (m : Meta) (pt0 : Pt) (v : List ℤ) : List ℕ :=
  (ptGroups m pt0).takeWhile fun g => decide (v ∈ rowsOf pk g)

/-- Affine total width of the leading groups. -/
def leadAff (m : Meta) (pk : Packet) (pt0 : Pt) (v : List ℤ) : Aff :=
  ((lead pk m pt0 v).map fun g => m.ws.getD g ⟨0, 0, 0⟩).foldl
    (fun a f => ⟨a.a + f.a, a.b + f.b, a.c + f.c⟩) ⟨0, 0, 0⟩

theorem ptGroups_nodup (m : Meta) (pt0 : Pt) : (ptGroups m pt0).Nodup :=
  List.Nodup.filter _ (List.nodup_range)

theorem ptGroups_mem (m : Meta) (pt0 : Pt) (g : ℕ) (hg : g ∈ ptGroups m pt0) :
    g < m.pts.length ∧ m.pts.getD g Pt.z0 = pt0 := by
  simp only [ptGroups, List.mem_filter, List.mem_range, beq_iff_eq] at hg
  exact hg

theorem lead_prefix (pk : Packet) (m : Meta) (pt0 : Pt) (v : List ℤ) : lead pk m pt0 v <+: ptGroups m pt0 :=
  List.takeWhile_prefix _

theorem takeWhile_mem_pred (L : List ℕ) (P : ℕ → Bool) (g : ℕ) (h : g ∈ L.takeWhile P) : P g = true := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    simp only [List.takeWhile_cons] at h
    split_ifs at h with hp
    · rcases List.mem_cons.mp h with rfl | h
      · exact hp
      · exact ih h
    · simp at h

theorem lead_mem_rows (pk : Packet) (m : Meta) (pt0 : Pt) (v : List ℤ) (g : ℕ) (hg : g ∈ lead pk m pt0 v) :
    v ∈ rowsOf pk g := by
  have := takeWhile_mem_pred _ _ g hg
  simpa using this

theorem grpOff_lead (pk : Packet) (m : Meta) (N p : ℕ) (pt0 : Pt) (v : List ℤ) (i : ℕ)
    (hi : i < (lead pk m pt0 v).length) :
    grpOff m N p (lead pk m pt0 v)[i] = baseOff m N p pt0 + offs ((lead pk m pt0 v).map (wdOf m N p)) i := by
  have hpre := lead_prefix pk m pt0 v
  have heq := List.prefix_iff_eq_take.mp hpre
  have hiL : i < (ptGroups m pt0).length := lt_of_lt_of_le hi hpre.length_le
  have hget : (lead pk m pt0 v)[i] = (ptGroups m pt0)[i] := hpre.getElem hi
  have hmem : (ptGroups m pt0)[i] ∈ ptGroups m pt0 := List.getElem_mem hiL
  have hpt := (ptGroups_mem m pt0 _ hmem).2
  have hidx : (ptGroups m pt0).idxOf (ptGroups m pt0)[i] = i :=
    List.get_idxOf (ptGroups_nodup m pt0) ⟨i, hiL⟩
  have htake : ((lead pk m pt0 v).take i) = (ptGroups m pt0).take i := by
    conv_lhs => rw [heq]
    rw [List.take_take]
    congr 1
    omega
  unfold grpOff
  rw [hget, hpt, hidx]
  unfold offs
  rw [List.map_take, ← List.map_take, ← List.map_take, htake]

end CatalanMeasure.GenD.Uniform.W.Charts6.Check
