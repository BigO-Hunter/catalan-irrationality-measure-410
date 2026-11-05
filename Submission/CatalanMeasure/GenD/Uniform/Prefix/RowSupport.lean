module
public import Mathlib.LinearAlgebra.Pi
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Uniform.Prefix
variable {K : Type*} [Field K]
noncomputable section

/-- Exactly the real row interval inside the enlarged tiling; every outside
coefficient vanishes, including either endpoint and the empty interval. -/
def intervalRows (lo n total : Nat) : Submodule K (Fin total → K) where
  carrier x := ∀ i, i.val < lo ∨ lo+n ≤ i.val → x i=0
  zero_mem' := by intro i hi; rfl
  add_mem' := by intro x y hx hy i hi; simp [hx i hi,hy i hi]
  smul_mem' := by intro a x hx i hi; simp [hx i hi]

def intervalRowsEquiv (lo n total : Nat) (hlen : lo+n ≤ total) :
    (Fin n → K) ≃ₗ[K] intervalRows (K := K) lo n total where
  toFun x := ⟨fun i => if hi : lo ≤ i.val ∧ i.val < lo+n then
    x ⟨i.val-lo,by omega⟩ else 0,by
      intro i hi
      have hn : ¬(lo ≤ i.val ∧ i.val < lo+n) := by omega
      simp only [dif_neg hn]⟩
  invFun x := fun j => x.1 ⟨lo+j.val,by have := j.is_lt; omega⟩
  left_inv x := by
    funext j
    have hj := j.is_lt
    have hc : lo ≤ lo+j.val ∧ lo+j.val < lo+n := by omega
    simp only [hc, and_self, dite_true]
    congr 1
    apply Fin.ext
    simp
  right_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : lo ≤ i.val ∧ i.val < lo+n
    · simp only [hi, and_self, dite_true]
      exact congrArg x.1 (Fin.ext (by simp only; omega))
    · simp only [hi, dite_false]
      exact (x.property i (by omega)).symm
  map_add' x y := by
    apply Subtype.ext
    funext i
    by_cases hi : lo ≤ i.val ∧ i.val < lo+n
    · simp [hi]
    · simp [hi]
  map_smul' a x := by
    apply Subtype.ext
    funext i
    by_cases hi : lo ≤ i.val ∧ i.val < lo+n
    · simp [hi]
    · simp [hi]

#print axioms intervalRowsEquiv
end
end CatalanMeasure.GenD.Uniform.Prefix
