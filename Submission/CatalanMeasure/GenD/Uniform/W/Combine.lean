module
public import Submission.CatalanMeasure.GenD.Interface
@[expose] public section
set_option Elab.async false

/-!
# Combining nullity lower bounds by pointwise maximum

* `NullityLB.zero`, `NullityLB.sup` (pointwise `max`), `NullityLB.supList`;
* `NullityLB.ofWindow` : a family value inside its window (`if App then val else 0`), from a
  per-point theorem `App N p → val N p ≤ nullity P N p` (the shape of every W instance);
* `NullityLB.banked` : the four banked families T, U, S, U6g (`famKap`), unchanged;
* `NullityLB.ofLe` : any pointwise smaller bound.
-/

namespace CatalanMeasure.GenD.NullityLB
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
noncomputable section
variable {P : Parameters}

/-- The trivial bound. -/
def zero (P : Parameters) : NullityLB P where
  kap _ _ := 0
  ok := fun _ _ _ _ _ _ => Nat.zero_le _

/-- Pointwise maximum of two nullity lower bounds. -/
def sup (A B : NullityLB P) : NullityLB P where
  kap N p := max (A.kap N p) (B.kap N p)
  ok := fun N p hN hp hp2 hH => max_le (A.ok N p hN hp hp2 hH) (B.ok N p hN hp hp2 hH)

theorem sup_kap (A B : NullityLB P) (N p : ℕ) :
    (sup A B).kap N p = max (A.kap N p) (B.kap N p) := rfl

/-- Pointwise maximum of a list of nullity lower bounds. -/
def supList (P : Parameters) : List (NullityLB P) → NullityLB P
  | [] => zero P
  | A :: L => sup A (supList P L)

theorem le_supList_kap {L : List (NullityLB P)} {A : NullityLB P} (hA : A ∈ L) (N p : ℕ) :
    A.kap N p ≤ (supList P L).kap N p := by
  induction L with
  | nil => simp at hA
  | cons B L ih =>
    rcases List.mem_cons.mp hA with h | h
    · subst h
      exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- A family value used only inside its window. -/
def ofWindow (P : Parameters) (App : ℕ → ℕ → Prop) (val : ℕ → ℕ → ℕ)
    (h : ∀ N p : ℕ, 0 < N → ∀ hp : p.Prime, p ≠ 2 → P.H N < p ^ 2 → App N p →
      haveI : Fact p.Prime := ⟨hp⟩
      val N p ≤ nullity P N p) : NullityLB P where
  kap N p := open Classical in if App N p then val N p else 0
  ok := fun N p hN hp hp2 hH => by
    classical
    by_cases hA : App N p
    · simp only [hA, ite_true]
      exact h N p hN hp hp2 hH hA
    · simp only [hA, ite_false]
      exact Nat.zero_le _

/-- The banked families T, U, S, U6g. -/
def banked (P : Parameters) (hP : Admissible P) : NullityLB P where
  kap := famKap P
  ok := fun _ _ hN hp hp2 hH => by
    have : Fact _ := ⟨hp⟩
    exact famKap_le_nullity P hP hN hp2 hH

/-- A pointwise smaller function is again a nullity lower bound. -/
def ofLe (A : NullityLB P) (kap : ℕ → ℕ → ℕ) (h : ∀ N p, kap N p ≤ A.kap N p) :
    NullityLB P where
  kap := kap
  ok := fun N p hN hp hp2 hH => (h N p).trans (A.ok N p hN hp hp2 hH)

end
end CatalanMeasure.GenD.NullityLB
