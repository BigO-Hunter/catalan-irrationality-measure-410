module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.VirtualCutoff
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Polynomial.Chebyshev
variable {K : Type*} [Field K] [NeZero (2 : K)]
noncomputable section

def bottomEndpoint (p : Nat) (c : Fin p → K) : K[X] :=
  ∑ i : Fin p, c i.rev • U K (i.val : Int)

def topEndpoint (p : Nat) (c : Fin (p+1) → K) : K[X] :=
  ∑ i : Fin p, c i.succ • U K (i.val : Int)

/-- Every virtual row below the first actual row is retained. At ja=p, the
cutoff is degree < 0, exactly the zero polynomial. -/
theorem bottomEndpoint_cut (p ja : Nat) (hja : ja ≤ p) (c : Fin p → K) :
    (bottomEndpoint p c).degree < (p-ja : Nat) ↔
      ∀ i : Fin p, i.val < ja → c i=0 := by
  rw [bottomEndpoint,chebyshevU_degree_cut]
  constructor
  · intro hc i hi
    have hrev : p-ja ≤ i.rev.val := by rw [Fin.val_rev]; have := i.is_lt; omega
    simpa only [Fin.rev_rev] using hc i.rev hrev
  · intro hc i hi
    apply hc i.rev
    rw [Fin.val_rev]
    have := i.is_lt
    omega

/-- Every virtual row above the last actual row, including the upper outer
center. rho=0 is handled by the same degree-bottom condition. -/
theorem topEndpoint_cut (p rho : Nat) (c : Fin (p+1) → K) :
    (topEndpoint p c).degree < rho ↔
      ∀ i : Fin (p+1), rho < i.val → c i=0 := by
  rw [topEndpoint,chebyshevU_degree_cut]
  constructor
  · intro hc i hi
    have hipos : 0 < i.val := by omega
    let j : Fin p := ⟨i.val-1,by have := i.is_lt; omega⟩
    have hji : j.succ=i := Fin.ext (by dsimp [j]; omega)
    rw [←hji]
    apply hc j
    dsimp [j]
    omega
  · intro hc i hi
    apply hc i.succ
    simp only [Fin.val_succ]
    omega

#print axioms bottomEndpoint_cut
#print axioms topEndpoint_cut
end
end CatalanMeasure.GenD.Uniform.Prefix


