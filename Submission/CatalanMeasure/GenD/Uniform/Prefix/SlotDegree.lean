module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.FrobeniusSplit
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial
variable {K : Type*} [Field K]

/-- The leading blocks of F and (X^p-1)E are disjoint. This retains the zero
polynomial's degree bottom, so virtual bound -1 needs no exceptional convention. -/
theorem slot_degree_max (p : Nat) (hp : 0<p) (F E : K[X]) (hF : F.degree<p) :
    (F+(X^p-1)*E).degree=max F.degree ((p : WithBot Nat)+E.degree) := by
  have hbase : (X^p-1 : K[X]).degree=p := by
    simpa using (degree_X_pow_sub_C hp (1 : K))
  by_cases hE : E=0
  · simp [hE]
  · have hprod : ((X^p-1)*E).degree=(p : WithBot Nat)+E.degree := by
      rw [degree_mul,hbase]
    have hge : (p : WithBot Nat)≤((X^p-1)*E).degree := by
      rw [hprod,degree_eq_natDegree hE]
      exact_mod_cast (Nat.le_add_right p E.natDegree)
    have hle : F.degree≤(p : WithBot Nat)+E.degree := by
      rw [←hprod]
      exact (hF.trans_le hge).le
    rw [degree_add_eq_right_of_degree_lt (hF.trans_le hge),hprod,max_eq_right hle]

/-- Exact simultaneous virtual endpoint degree constraints on the unique split. -/
theorem slot_degree_le (p : Nat) (hp : 0<p) (F E : K[X]) (hF : F.degree<p)
    (D : WithBot Nat) :
    (F+(X^p-1)*E).degree≤D ↔ F.degree≤D ∧ (p : WithBot Nat)+E.degree≤D := by
  rw [slot_degree_max p hp F E hF,max_le_iff]

/-- Full degree restriction for A slots, valid at r=0 without a free E variable. -/
theorem slot_degree_shift (p r : Nat) (hp : 0<p) (F E : K[X]) (hF : F.degree<p) :
    (F+(X^p-1)*E).degree<(↑(p+r) : WithBot Nat) ↔ E.degree<r := by
  rw [slot_degree_max p hp F E hF,max_lt_iff]
  have hFr : F.degree<(p+r : Nat) :=
    hF.trans_le (by exact_mod_cast Nat.le_add_right p r)
  rw [and_iff_right hFr]
  by_cases hE : E=0
  · simp [hE]
  · rw [degree_eq_natDegree hE]
    norm_cast
    omega

#print axioms slot_degree_shift
end CatalanMeasure.GenD.Uniform.Prefix

