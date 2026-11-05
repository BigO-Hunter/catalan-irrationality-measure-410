module
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.TRawTail
@[expose] public section
set_option Elab.async false

/-!
# The thin-window nullity bound for any admissible design

`thinLB P hP` is the pointwise maximum of the banked T, U, S, U6g families and every thin-window
family proved so far (currently the T-raw tail).  No design literal occurs: each family carries
its own window as linear inequalities in `(n, b, q, g, h, p)`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Thin
open CatalanMeasure.GenD CatalanMeasure.Parametric
noncomputable section

/-- The thin-window families (new content only). -/
def thinFamilies (P : Parameters) (hP : Admissible P) : List (NullityLB P) :=
  [tTailLB P hP]

/-- Banked families together with all thin-window families. -/
def thinLB (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.supList P (NullityLB.banked P hP :: thinFamilies P hP)

theorem banked_le_thinLB (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (NullityLB.banked P hP).kap N p ≤ (thinLB P hP).kap N p :=
  NullityLB.le_supList_kap (List.mem_cons_self) N p

theorem tTail_le_thinLB (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (tTailLB P hP).kap N p ≤ (thinLB P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [thinFamilies]) N p

end
end CatalanMeasure.GenD.Uniform.W.Thin
