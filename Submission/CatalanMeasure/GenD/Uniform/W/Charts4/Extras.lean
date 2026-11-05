module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.ThetaInj
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open Module Polynomial CatalanMeasure.GenD.Uniform.Prefix
noncomputable section
variable {p : ℕ} [Fact p.Prime]
open scoped Classical

local notation "Fp" => ZMod p

/-- The coordinate is one of the graph coordinates (`jet_0`, `@low`, ...). -/
def isExtra {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (idx : Fin K) : Prop :=
  ∃ j, ckEquiv hK idx = Sum.inr (Sum.inr j)


/-- Zero the graph coordinates. -/
def projExtras {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) :
    (Fin K → Fp) →ₗ[Fp] (Fin K → Fp) :=
  LinearMap.pi fun idx => if isExtra hK idx then 0 else LinearMap.proj idx

theorem projExtras_apply {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (y : Fin K → Fp) (idx : Fin K) :
    projExtras hK y idx = if isExtra hK idx then 0 else y idx := by
  classical
  unfold projExtras
  by_cases h : isExtra hK idx <;> simp [h]

theorem sumProf_proj {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (G : CK b ex → Fp[X])
    (hG : ∀ j, G (Sum.inr (Sum.inr j)) = 0) (y : Fin K → Fp) :
    sumProf hK G (projExtras hK y) = sumProf hK G y := by
  rw [sumProf_apply, sumProf_apply]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [projExtras_apply]
  by_cases h : isExtra hK idx
  · obtain ⟨j, hj⟩ := h
    rw [if_pos ⟨j, hj⟩, hj, hG j]; simp
  · rw [if_neg h]

theorem projExtras_eq_self {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (y : Fin K → Fp)
    (hy : ∀ j, y ((ckEquiv hK).symm (Sum.inr (Sum.inr j))) = 0) : projExtras hK y = y := by
  funext idx
  rw [projExtras_apply]
  by_cases h : isExtra hK idx
  · obtain ⟨j, hj⟩ := h
    rw [if_pos ⟨j, hj⟩]
    have : idx = (ckEquiv hK).symm (Sum.inr (Sum.inr j)) := by rw [← hj]; simp
    rw [this, hy j]
  · rw [if_neg h]

end
end CatalanMeasure.GenD.Uniform.W.Charts4
