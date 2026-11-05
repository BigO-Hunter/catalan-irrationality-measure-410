module
public import Submission.CatalanMeasure.Parametric.UpperPrimePhysical
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section
def paramRawColumnPoolEquiv (P : Parameters) (N : ℕ) :
    Fin (P.n N + P.q N) ≃ ↥(Finset.Ico (P.b N) (P.L N)) where
  toFun c := ⟨P.b N + c.val, Finset.mem_Ico.mpr ⟨by omega, by
    have hc := c.isLt
    have hL := (show P.L N=P.n N+P.b N+P.q N from rfl)
    omega⟩⟩
  invFun j := ⟨j.val - P.b N, by
    have hj := Finset.mem_Ico.mp j.property
    have hL := (show P.L N=P.n N+P.b N+P.q N from rfl)
    omega⟩
  left_inv c := by
    apply Fin.ext
    change P.b N + c.val - P.b N = c.val
    omega
  right_inv j := by
    apply Subtype.ext
    change P.b N + (j.val - P.b N) = j.val
    have hj := Finset.mem_Ico.mp j.property
    omega

@[simp] theorem paramRawColumnPoolEquiv_apply_val (P : Parameters) (N : ℕ) (c : Fin (P.n N + P.q N)) :
    (paramRawColumnPoolEquiv P N c).val = P.b N + c.val := rfl

@[simp] theorem paramRawColumnPoolEquiv_symm_apply_val (P : Parameters) (N : ℕ)
    (j : ↥(Finset.Ico (P.b N) (P.L N))) :
    ((paramRawColumnPoolEquiv P N).symm j).val = j.val - P.b N := rfl

def paramUpperPoolSplit (P : Parameters) (p N : ℕ) :
    (↥(paramUpperRetainedSet P p N) ⊕
      (↥(paramUpperPairHighSet P p N) ⊕ ↥(paramUpperCentralSet P p N))) ≃
        ↥(Finset.Ico (P.b N) (P.L N)) := by
  classical
  let f : (↥(paramUpperRetainedSet P p N) ⊕
      (↥(paramUpperPairHighSet P p N) ⊕ ↥(paramUpperCentralSet P p N))) →
        ↥(Finset.Ico (P.b N) (P.L N)) := fun x => match x with
    | Sum.inl j => ⟨j.val, paramUpperRetainedSet_subset_raw P p N j.property⟩
    | Sum.inr (Sum.inl j) => ⟨j.val, paramUpperPairHighSet_subset_raw P p N j.property⟩
    | Sum.inr (Sum.inr j) => ⟨j.val, paramUpperCentralSet_subset_raw P p N j.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    rcases x with x | (x | x) <;> rcases y with y | (y | y)
    · change x.val = y.val at hv
      have hxy : x = y := Subtype.ext hv
      cases hxy
      rfl
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (paramUpperRetainedSet_disjoint_pairHigh P p N)) (hv ▸ x.property) y.property)
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (paramUpperRetainedSet_disjoint_central P p N)) (hv ▸ x.property) y.property)
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (paramUpperRetainedSet_disjoint_pairHigh P p N)) y.property (hv ▸ x.property))
    · change x.val = y.val at hv
      have hxy : x = y := Subtype.ext hv
      cases hxy
      rfl
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (paramUpperPairHighSet_disjoint_central P p N)) (hv ▸ x.property) y.property)
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (paramUpperRetainedSet_disjoint_central P p N)) y.property (hv ▸ x.property))
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (paramUpperPairHighSet_disjoint_central P p N)) y.property (hv ▸ x.property))
    · change x.val = y.val at hv
      have hxy : x = y := Subtype.ext hv
      cases hxy
      rfl
  · intro j
    have hj : j.val ∈ paramUpperRetainedSet P p N ∪
        (paramUpperPairHighSet P p N ∪ paramUpperCentralSet P p N) := by
      rw [paramUpperPool_partition]
      exact j.property
    rcases Finset.mem_union.mp hj with hr | hpc
    · exact ⟨Sum.inl ⟨j.val, hr⟩, rfl⟩
    · rcases Finset.mem_union.mp hpc with hp | hc
      · exact ⟨Sum.inr (Sum.inl ⟨j.val, hp⟩), rfl⟩
      · exact ⟨Sum.inr (Sum.inr ⟨j.val, hc⟩), rfl⟩

def paramUpperPoolEnumeration (P : Parameters) (p N : ℕ) :
    (Fin (Fintype.card ↥(paramUpperRetainedSet P p N)) ⊕
      (Fin (Fintype.card ↥(paramUpperPairHighSet P p N)) ⊕
        Fin (Fintype.card ↥(paramUpperCentralSet P p N)))) ≃
          ↥(Finset.Ico (P.b N) (P.L N)) :=
  (Equiv.sumCongr (Fintype.equivFin ↥(paramUpperRetainedSet P p N)).symm
    (Equiv.sumCongr (Fintype.equivFin ↥(paramUpperPairHighSet P p N)).symm
      (Fintype.equivFin ↥(paramUpperCentralSet P p N)).symm)).trans
        (paramUpperPoolSplit P p N)

@[simp] theorem paramUpperPoolEnumeration_retained_val (P : Parameters) (p N : ℕ)
    (j : Fin (Fintype.card ↥(paramUpperRetainedSet P p N))) :
    (paramUpperPoolEnumeration P p N (Sum.inl j)).val =
      ((Fintype.equivFin ↥(paramUpperRetainedSet P p N)).symm j).val := rfl

@[simp] theorem paramUpperPoolEnumeration_pairHigh_val (P : Parameters) (p N : ℕ)
    (j : Fin (Fintype.card ↥(paramUpperPairHighSet P p N))) :
    (paramUpperPoolEnumeration P p N (Sum.inr (Sum.inl j))).val =
      ((Fintype.equivFin ↥(paramUpperPairHighSet P p N)).symm j).val := rfl

@[simp] theorem paramUpperPoolEnumeration_central_val (P : Parameters) (p N : ℕ)
    (j : Fin (Fintype.card ↥(paramUpperCentralSet P p N))) :
    (paramUpperPoolEnumeration P p N (Sum.inr (Sum.inr j))).val =
      ((Fintype.equivFin ↥(paramUpperCentralSet P p N)).symm j).val := rfl

end
end CatalanMeasure.Parametric
