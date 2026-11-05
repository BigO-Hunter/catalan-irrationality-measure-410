module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Data146O
@[expose] public section
set_option Elab.async false

/-!
# Which label rows occur in which stored chart of `packetO` (kernel-checked data)

Coordinates: block `k` (0..9, absolute block `k-1`): `AF = 4k`, `AE = 4k+1`, `CF = 4k+2`, `CE = 4k+3`;
centre `ZF = 40`, `ZE = 41`; graph coordinates `jet_0 = 42`, `@low = 43`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
open CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146

/-- The unit row `e_c` as a list of length 44. -/
def unitL (c : ℕ) : List ℤ := (List.range 44).map fun k => if k = c then 1 else 0
/-- The row `e_a - 2 e_b`. -/
def diff2L (a b : ℕ) : List ℤ := (List.range 44).map fun k => (if k = a then 1 else 0) - (if k = b then 2 else 0)
/-- The row `e_a - e_b + e_c`. -/
def virtBL : List ℤ := (List.range 44).map fun k => (if k = 1 then 1 else 0) - (if k = 3 then 1 else 0) + (if k = 41 then 1 else 0)
/-- The row `e_37 + e_39` (top virtual). -/
def virtTL : List ℤ := (List.range 44).map fun k => (if k = 37 then 1 else 0) + (if k = 39 then 1 else 0)

def hasRow (g : ℕ) (r : List ℤ) : Bool := (oRows g).contains r

set_option maxRecDepth 100000 in
theorem pt1_CF : ∀ k : Fin 10, hasRow 3 (unitL (4 * k + 2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem pt1_AF : ∀ k : Fin 10, hasRow 3 (unitL (4 * k)) = true ∧ hasRow 4 (unitL (4 * k)) = true ∧
    hasRow 5 (unitL (4 * k)) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem pt1_ZF : hasRow 3 (unitL 40) = true ∧ hasRow 4 (unitL 40) = true ∧ hasRow 5 (unitL 40) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem ptm1_C : ∀ k : Fin 10, hasRow 0 (diff2L (4 * k + 2) (4 * k + 3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem ptm1_Z : hasRow 0 (diff2L 40 41) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_AE : ∀ k : Fin 10, hasRow 6 (unitL (4 * k + 1)) = true ∧ hasRow 7 (unitL (4 * k + 1)) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem inf_ZE : hasRow 6 (unitL 41) = true ∧ hasRow 7 (unitL 41) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_CE : ∀ k : Fin 10, hasRow 6 (unitL (4 * k + 3)) = true ∧ hasRow 7 (unitL (4 * k + 3)) = true ∧
    hasRow 8 (unitL (4 * k + 3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_virtB : hasRow 6 virtBL = true ∧ hasRow 7 virtBL = true ∧ hasRow 8 virtBL = true ∧
    hasRow 9 virtBL = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_virtT : hasRow 6 virtTL = true ∧ hasRow 7 virtTL = true ∧ hasRow 8 virtTL = true ∧
    hasRow 9 virtTL = true ∧ hasRow 10 virtTL = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem pt1_jet0 : hasRow 3 (unitL 42) = true ∧ hasRow 4 (unitL 42) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_low : hasRow 6 (unitL 43) = true ∧ hasRow 7 (unitL 43) = true ∧
    hasRow 8 (unitL 43) = true ∧ hasRow 9 (unitL 43) = true := by decide +kernel

/-- The graph-coordinate entries of a raw row: `(ρ_42, ρ_43)`; `D = -ρ_42` divides `2310^40`. -/
def auxOK (g i : ℕ) (graph : Bool) : Bool :=
  let r := (oRows g).getD i []
  decide (r.getD 42 0 < 0) && decide ((2310 ^ 40 : ℤ) % (r.getD 42 0) = 0) &&
    (if graph then decide (r.getD 43 0 = r.getD 42 0) else decide (r.getD 43 0 = 0)) &&
    decide (i < (oRows g).length)

set_option maxRecDepth 100000 in
theorem raw_aux : auxOK 1 0 false = true ∧ auxOK 1 10 true = true ∧ auxOK 2 0 false = true ∧
    auxOK 2 9 true = true := by decide +kernel

/-- A raw row: contains its row, `ρ_42 | 2310^40`, `ρ_42 ≠ 0`, and `ρ_43 = c * ρ_42` for the stated `c`. -/
def rawRowOK (g i : ℕ) (c : ℤ) : Bool :=
  hasRow g ((oRows g).getD i []) && decide (((oRows g).getD i []).getD 42 0 ∣ 2310 ^ 40) &&
    decide (((oRows g).getD i []).getD 42 0 ≠ 0) &&
    decide (((oRows g).getD i []).getD 43 0 = c * ((oRows g).getD i []).getD 42 0)

set_option maxRecDepth 100000 in
theorem raw_ok : rawRowOK 1 0 0 = true ∧ rawRowOK 1 10 1 = true ∧ rawRowOK 2 0 0 = true ∧
    rawRowOK 2 9 1 = true := by decide +kernel

end CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
