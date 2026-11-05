module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Order
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Row vectors in profile coordinates, the insertion map, and their polynomials
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx)

/-- Packet coordinate sitting at the profile coordinate `idx` (if any). -/
def pcOf (m : Meta) (idx : ℕ) : Option ℕ := if idx ∈ m.iota then some (m.iota.idxOf idx) else none

def unitAt (n : ℕ) (c : Option ℕ) : List ℤ := (List.range n).map fun k => if some k = c then 1 else 0

/-- The packet row vector of `∑ a_t e_{idx_t}` (absent profile coordinates contribute nothing). -/
def vecOf (m : Meta) (n : ℕ) : List (ℤ × ℕ) → List ℤ
  | [] => List.replicate n 0
  | (a, idx) :: ts => List.zipWith (· + ·) ((unitAt n (pcOf m idx)).map (a * ·)) (vecOf m n ts)

theorem unitAt_length (n : ℕ) (c : Option ℕ) : (unitAt n c).length = n := by simp [unitAt]

theorem vecOf_length (m : Meta) (n : ℕ) (ts : List (ℤ × ℕ)) : (vecOf m n ts).length = n := by
  induction ts with
  | nil => simp [vecOf]
  | cons t ts ih => simp [vecOf, unitAt_length, ih]

theorem getD_unitAt (n : ℕ) (c : Option ℕ) (k : ℕ) (hk : k < n) :
    (unitAt n c).getD k 0 = if some k = c then 1 else 0 := by
  unfold unitAt
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- The polynomial of the packet coordinate `o` (zero if absent). -/
def polAt {n : ℕ} (X : Fin p → Fin n → Fp) (o : Option ℕ) : Fp[X] :=
  match o with
  | some c => if h : c < n then polx X ⟨c, h⟩ else 0
  | none => 0

theorem rowPoly_add {n : ℕ} (X : Fin p → Fin n → Fp) (a b : List ℤ) (ha : a.length = n) (hb : b.length = n) :
    rowPoly X (List.zipWith (· + ·) a b) = rowPoly X a + rowPoly X b := by
  unfold rowPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h1 : (c : ℕ) < a.length := by rw [ha]; exact c.isLt
  have h2 : (c : ℕ) < b.length := by rw [hb]; exact c.isLt
  rw [List.getD_eq_getElem _ _ (by simp [ha, hb]), List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  simp [add_mul, C_add]

theorem rowPoly_scale {n : ℕ} (X : Fin p → Fin n → Fp) (a : List ℤ) (ha : a.length = n) (t : ℤ) :
    rowPoly X (a.map (t * ·)) = C ((t : ℤ) : Fp) * rowPoly X a := by
  unfold rowPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h1 : (c : ℕ) < a.length := by rw [ha]; exact c.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using h1), List.getD_eq_getElem _ _ h1]
  simp [mul_assoc, C_mul]

theorem rowPoly_unitAt {n : ℕ} (X : Fin p → Fin n → Fp) (o : Option ℕ) :
    rowPoly X (unitAt n o) = polAt X o := by
  unfold rowPoly
  rcases o with _ | c
  · simp only [polAt]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [getD_unitAt n none d d.isLt]; simp
  · by_cases hc : c < n
    · simp only [polAt, dif_pos hc]
      rw [Finset.sum_eq_single ⟨c, hc⟩]
      · rw [getD_unitAt n (some c) c hc]; simp
      · intro d _ hd
        rw [getD_unitAt n (some c) d d.isLt]
        have : (some (d : ℕ) = some c) = False := by
          simp only [Option.some.injEq, eq_iff_iff, iff_false]; intro h; exact hd (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [polAt, dif_neg hc]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [getD_unitAt n (some c) d d.isLt]
      have : (some (d : ℕ) = some c) = False := by
        simp only [Option.some.injEq, eq_iff_iff, iff_false]; intro h; apply hc; rw [← h]; exact d.isLt
      simp [this]

theorem rowPoly_vecOf (m : Meta) {n : ℕ} (X : Fin p → Fin n → Fp) (ts : List (ℤ × ℕ)) :
    rowPoly X (vecOf m n ts) = (ts.map fun t => C ((t.1 : ℤ) : Fp) * polAt X (pcOf m t.2)).sum := by
  induction ts with
  | nil =>
    simp only [vecOf, List.map_nil, List.sum_nil]
    unfold rowPoly
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [List.getD_eq_getElem _ _ (by simp [c.isLt])]; simp
  | cons t ts ih =>
    obtain ⟨a, idx⟩ := t
    rw [vecOf, rowPoly_add _ _ _ (by simp [unitAt_length]) (vecOf_length m n ts), rowPoly_scale _ _ (unitAt_length _ _),
      rowPoly_unitAt, ih]
    simp

end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
