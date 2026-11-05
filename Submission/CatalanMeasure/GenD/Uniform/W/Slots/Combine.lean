module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.PLB
@[expose] public section
set_option Elab.async false

/-!
# `thinLB2`: the thin-window bound with the H' and P families

`thinLB2 P hP = supList [thinLB; hpLB; perLB]`, the pointwise maximum of the accepted thin-window
bound (banked T, U, S, U6g and the T-raw tail), the H' family and the period family.  Design-generic:
no design literal occurs.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open CatalanMeasure.GenD CatalanMeasure.Parametric
noncomputable section

/-- Families added over `thinLB` by the slot API. -/
def slotFamilies (P : Parameters) (hP : Admissible P) : List (NullityLB P) :=
  [hpLB P hP, perLB P hP]

/-- **`thinLB2`**. -/
def thinLB2 (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.supList P (Thin.thinLB P hP :: slotFamilies P hP)

theorem thinLB_le_thinLB2 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (Thin.thinLB P hP).kap N p ≤ (thinLB2 P hP).kap N p :=
  NullityLB.le_supList_kap (List.mem_cons_self) N p

theorem hpLB_le_thinLB2 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (hpLB P hP).kap N p ≤ (thinLB2 P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [slotFamilies]) N p

theorem perLB_le_thinLB2 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (perLB P hP).kap N p ≤ (thinLB2 P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [slotFamilies]) N p

end
end CatalanMeasure.GenD.Uniform.W.Slots
