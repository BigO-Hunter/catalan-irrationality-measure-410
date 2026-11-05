module
public import Submission.CatalanMeasure.CellCert.CellW
@[expose] public section
/-!
# One-value pieces for the cell lists

The kernel's cost of evaluating many polynomial values inside one `decide +kernel` grows much
faster than linearly (the whole term graph is retained).  These lemmas assemble the lists `AL`
and `fhL` of a cell from one kernel-checked equation per entry.
-/
namespace CatalanMeasure.CellCert

theorem map_range_succ_shift {α : Type} (f : ℕ → α) (s L : ℕ) :
    (List.range (L + 1)).map (fun k => f (s + k)) =
      f s :: (List.range L).map (fun k => f (s + 1 + k)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply]
  congr 1
  omega

theorem AL_zero (N : ℕ) (V : List ℤ) (m : ℕ) : AL N V m 0 = [] := rfl

theorem AL_cons {N : ℕ} {V : List ℤ} {m L : ℕ} {a : ℤ} {r : List ℤ}
    (h0 : zabs (V.getD m 0 * SC / (K40 * TPN N)) + 1 = a) (hr : AL N V (m + 1) L = r) :
    AL N V m (L + 1) = a :: r := by
  subst h0 hr
  exact map_range_succ_shift (fun j => zabs (V.getD j 0 * SC / (K40 * TPN N)) + 1) m L

/-- `fhL` from index `s` on -/
def fhFrom (N : ℕ) (poles : List PoleR) (cc : ℤ) (V : List ℤ) (s L : ℕ) : List ℤ :=
  (List.range L).map (fun k => fhatV N poles cc V (s + k))

theorem fhFrom_zero (N : ℕ) (poles : List PoleR) (cc : ℤ) (V : List ℤ) (s : ℕ) :
    fhFrom N poles cc V s 0 = [] := rfl

theorem fhFrom_cons {N : ℕ} {poles : List PoleR} {cc : ℤ} {V : List ℤ} {s L : ℕ} {a : ℤ}
    {r : List ℤ} (h0 : fhatV N poles cc V s = a) (hr : fhFrom N poles cc V (s + 1) L = r) :
    fhFrom N poles cc V s (L + 1) = a :: r := by
  subst h0 hr
  exact map_range_succ_shift (fhatV N poles cc V) s L

theorem fhL_of_from {N : ℕ} {poles : List PoleR} {cc : ℤ} {V : List ℤ} {m : ℕ} {FH : List ℤ}
    (h : fhFrom N poles cc V 0 m = FH) : fhL N poles cc V m = FH := by
  rw [← h]
  unfold fhL fhFrom
  simp

end CatalanMeasure.CellCert
