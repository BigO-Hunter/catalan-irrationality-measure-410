module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Chain
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.JetsGeneric
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.SlotsToTiling
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.Count
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Checker data: group metadata, generic jets, row polynomials

`Meta` describes a packet's group structure: the point of each stored group and the affine width of each group.
`jetG` is the generic jet family (offset of a group = sum of the widths of the earlier groups at the same point),
`rowPoly` is the polynomial `∑_c v_c f_c` of a row vector `v`, and `rowpoly_vanish_*` say what a row of a chart contributes.
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx)

inductive Pt | m1 | z0 | p1 | inf
deriving DecidableEq

/-- A position region `[lo, hi)` with the chart rows `(group, row index)` used on it. -/
structure Region where
  lo : Aff
  hi : Aff
  sel : List (ℕ × ℕ)

structure Meta where
  b : ℕ
  ex : ℕ
  k0 : ℤ
  high : Bool
  vlow : Bool
  win : ℕ × ℕ × ℕ × ℕ × ℕ
  iota : List ℕ
  pts : List Pt
  ws : List Aff
  regs : List Region
  /-- the number of atoms (positions `0 .. cm - 1`; the others are zero); `p` for a full packet -/
  cm : Aff := ⟨0, 2, 1⟩

noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

def wdOf (m : Meta) (N p g : ℕ) : ℕ := ((m.ws.getD g ⟨0, 0, 0⟩).eval (N : ℤ) (((p : ℤ) - 1) / 2)).toNat

/-- The groups at the point `pt0`, in order. -/
def ptGroups (m : Meta) (pt0 : Pt) : List ℕ := (List.range m.pts.length).filter fun g => m.pts.getD g Pt.z0 == pt0

/-- The number of atoms. -/
def cmN (m : Meta) (N p : ℕ) : ℕ := (m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2)).toNat

/-- The base offset of a chain: the positions `≥ cmN` are zero, so the `inf` chain starts at `p - cmN`. -/
def baseOff (m : Meta) (N p : ℕ) (pt0 : Pt) : ℕ := if pt0 = Pt.inf then p - cmN m N p else 0

/-- Offset of a group in the jet chain of its point: the base offset plus the widths of the earlier groups at that point. -/
def grpOff (m : Meta) (N p g : ℕ) : ℕ :=
  baseOff m N p (m.pts.getD g Pt.z0) +
    (((ptGroups m (m.pts.getD g Pt.z0)).take ((ptGroups m (m.pts.getD g Pt.z0)).idxOf g)).map (wdOf m N p)).sum

def jetG {d : ℕ} (m : Meta) (N q g k : ℕ) [Fact q.Prime] :
    (Fin q → Fin d → ZMod q) →ₗ[ZMod q] (Fin d → ZMod q) :=
  match m.pts.getD g Pt.z0 with
  | .m1 => Charts3.taylorJet (m := q) (d := d) (-1) (grpOff m N q g + k)
  | .p1 => Charts3.taylorJet (m := q) (d := d) 1 (grpOff m N q g + k)
  | .z0 => jet0 (grpOff m N q g + k)
  | .inf => jetInf (grpOff m N q g + k)

def JetKerG (pk : Packet) (m : Meta) (N : ℕ) (x : Fin p → Fin pk.d → ZMod p) : Prop :=
  ∀ g : Fin pk.charts.length, ∀ k : Fin (wdOf m N p g),
    chartMap pk (pk.chart g) p pk.n (jetG m N p g k x) = 0

/-- The row polynomial `∑_c v_c f_c`. -/
def rowPoly {n : ℕ} (X : Fin p → Fin n → ZMod p) (v : List ℤ) : (ZMod p)[X] :=
  ∑ c : Fin n, C (((v.getD c 0 : ℤ)) : ZMod p) * polx X c

theorem vanish_row (pk : Packet) (m : Meta) {N : ℕ} (x : Fin p → Fin pk.d → Fp) (hker : JetKerG pk m N x)
    (g : ℕ) (hg : g < pk.charts.length) (k : ℕ) (hk : k < wdOf m N p g) (r : List ℤ)
    (hr : r ∈ (pk.chart ⟨g, hg⟩).rows) :
    ∑ c : Fin pk.n, ((r.getD c 0 : ℤ) : Fp) * emb pk p pk.n (jetG m N p g k x) c = 0 := by
  have h := hker ⟨g, hg⟩ ⟨k, hk⟩
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hr
  have := CatalanMeasure.GenD.Uniform.W.Charts4.row_of_chart (K := pk.n) _ h i hi
  convert this using 2
  rw [Mx, List.getD_eq_getElem _ _ hi, hir]

theorem rowPoly_coeff {n : ℕ} (X : Fin p → Fin n → Fp) (v : List ℤ) (j : ℕ) :
    (rowPoly X v).coeff j = ∑ c : Fin n, ((v.getD c 0 : ℤ) : Fp) * (polx X c).coeff j := by
  unfold rowPoly
  rw [finset_sum_coeff]
  exact Finset.sum_congr rfl fun c _ => coeff_C_mul _

theorem rowPoly_taylor_coeff {n : ℕ} (X : Fin p → Fin n → Fp) (v : List ℤ) (a : Fp) (j : ℕ) :
    (taylor a (rowPoly X v)).coeff j = ∑ c : Fin n, ((v.getD c 0 : ℤ) : Fp) * (taylor a (polx X c)).coeff j := by
  unfold rowPoly
  rw [map_sum, finset_sum_coeff]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Polynomial.C_mul', map_smul, coeff_smul, smul_eq_mul]

/-- A row of a group at a Taylor point (`±1`), on the row polynomial. -/
theorem rowpoly_vanish_taylor (pk : Packet) (m : Meta) {N : ℕ} (x : Fin p → Fin pk.d → Fp)
    (hker : JetKerG pk m N x) (g : ℕ) (hg : g < pk.charts.length) (a : Fp) (hpt : m.pts.getD g Pt.z0 = Pt.p1 ∧ a = 1 ∨ m.pts.getD g Pt.z0 = Pt.m1 ∧ a = -1)
    (k : ℕ) (hk : k < wdOf m N p g) (r : List ℤ) (hr : r ∈ (pk.chart ⟨g, hg⟩).rows) :
    (taylor a (rowPoly (fun e => emb pk p pk.n (x e)) r)).coeff (grpOff m N p g + k) = 0 := by
  have := vanish_row pk m x hker g hg k hk r hr
  have hj : jetG (d := pk.d) m N p g k = Charts3.taylorJet (m := p) (d := pk.d) a (grpOff m N p g + k) := by
    rcases hpt with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> (unfold jetG; rw [h])
  rw [hj, emb_taylorJet] at this
  rw [rowPoly_taylor_coeff, ← this]
  exact Finset.sum_congr rfl fun c _ => by rw [taylorJet_coord]

theorem rowpoly_vanish_z0 (pk : Packet) (m : Meta) {N : ℕ} (x : Fin p → Fin pk.d → Fp)
    (hker : JetKerG pk m N x) (g : ℕ) (hg : g < pk.charts.length) (hpt : m.pts.getD g Pt.z0 = Pt.z0)
    (k : ℕ) (hk : k < wdOf m N p g) (r : List ℤ) (hr : r ∈ (pk.chart ⟨g, hg⟩).rows) :
    (rowPoly (fun e => emb pk p pk.n (x e)) r).coeff (grpOff m N p g + k) = 0 := by
  have := vanish_row pk m x hker g hg k hk r hr
  have hj : jetG (d := pk.d) m N p g k = jet0 (grpOff m N p g + k) := by
    unfold jetG; rw [hpt]
  rw [hj, emb_jet0] at this
  rw [rowPoly_coeff, ← this]
  exact Finset.sum_congr rfl fun c _ => by rw [jet0_coord]

theorem rowpoly_vanish_inf (pk : Packet) (m : Meta) {N : ℕ} (x : Fin p → Fin pk.d → Fp)
    (hker : JetKerG pk m N x) (g : ℕ) (hg : g < pk.charts.length) (hpt : m.pts.getD g Pt.z0 = Pt.inf)
    (k : ℕ) (hk : k < wdOf m N p g) (hlt : grpOff m N p g + k < p) (r : List ℤ) (hr : r ∈ (pk.chart ⟨g, hg⟩).rows) :
    (rowPoly (fun e => emb pk p pk.n (x e)) r).coeff (p - 1 - (grpOff m N p g + k)) = 0 := by
  have := vanish_row pk m x hker g hg k hk r hr
  have hj : jetG (d := pk.d) m N p g k = jetInf (grpOff m N p g + k) := by
    unfold jetG; rw [hpt]
  rw [hj, emb_jetInf] at this
  rw [rowPoly_coeff, ← this]
  exact Finset.sum_congr rfl fun c _ => by rw [jetInf_coord, if_pos hlt]

end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
