module
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial
variable {K : Type*} [Field K]

noncomputable def chebyshevUSequence [NeZero (2 : K)] : Polynomial.Sequence K where
  elems' i := Polynomial.Chebyshev.U K (i : Int)
  degree_eq' i := Polynomial.Chebyshev.degree_U_natCast K i

/-- Exact degree cut in any triangular polynomial sequence: every omitted
coefficient is zero. Covers cutoff0, empty spaces and cuts beyond the degree. -/
theorem sequence_degree_cut (S : Polynomial.Sequence K) (d r : Nat) (c : Fin d → K) :
    (∑ i, c i • S i.val).degree < r ↔ ∀ i : Fin d, r ≤ i.val → c i=0 := by
  classical
  have hd : ∀ i : Fin d, c i≠0 → (c i • S i.val).degree=(i.val : WithBot Nat) := by
    intro i hi
    rw [degree_smul_of_isRightRegular_leadingCoeff hi
      (IsRegular.of_ne_zero (leadingCoeff_ne_zero.mpr (S.ne_zero i.val))).right,S.degree_eq]
  have hp : Set.Pairwise {i : Fin d | i∈Finset.univ ∧ c i • S i.val≠0}
      (fun i j => (c i • S i.val).degree≠(c j • S j.val).degree) := by
    intro i hi j hj hij
    rw [hd i (smul_ne_zero_iff.mp hi.2).1,hd j (smul_ne_zero_iff.mp hj.2).1]
    intro he
    exact hij (Fin.ext (WithBot.coe_injective he))
  have hs := degree_sum_eq_of_disjoint (fun i : Fin d => c i • S i.val) Finset.univ hp
  rw [hs]
  constructor
  · intro hcut i hi
    by_contra hci
    have hle := Finset.le_sup (f := fun j : Fin d => (c j • S j.val).degree) (Finset.mem_univ i)
    rw [hd i hci] at hle
    have hlt : (i.val : WithBot Nat)<r := lt_of_le_of_lt hle hcut
    have hnat : i.val<r := WithBot.coe_lt_coe.mp hlt
    omega
  · intro hc
    apply (Finset.sup_lt_iff (by simp : (⊥ : WithBot Nat)<(r : WithBot Nat))).mpr
    intro i _
    by_cases hci : c i=0
    · simp [hci]
    · rw [hd i hci]
      have hnat : i.val<r := lt_of_not_ge (fun h => hci (hc i h))
      exact_mod_cast hnat

/-- Actual U coefficients encode every virtual row, with no boundary exceptions. -/
theorem chebyshevU_degree_cut [NeZero (2 : K)] (d r : Nat) (c : Fin d → K) :
    (∑ i, c i • Polynomial.Chebyshev.U K (i.val : Int)).degree < r ↔
      ∀ i : Fin d, r ≤ i.val → c i=0 :=
  sequence_degree_cut chebyshevUSequence d r c

#print axioms chebyshevU_degree_cut
end CatalanMeasure.GenD.Uniform.Prefix



