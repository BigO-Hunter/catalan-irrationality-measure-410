module
public import Submission.CatalanMeasure.Parametric.ShearedPrimeColumns
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section
def paramUpperPairHighSet (P : Parameters) (p N : ℕ) : Finset ℕ :=
  Finset.Ico (p + P.b N) (p + min (P.A N) (P.L N - p))

def paramUpperCentralSet (P : Parameters) (p N : ℕ) : Finset ℕ :=
  Finset.Ico (max (P.b N) (P.H N - p)) (min p (P.L N))

def paramUpperRetainedSet (P : Parameters) (p N : ℕ) : Finset ℕ :=
  Finset.Ico (P.b N) (P.L N) \
    (paramUpperPairHighSet P p N ∪ paramUpperCentralSet P p N)

def paramUpperExceptionalSet (P : Parameters) (p N : ℕ) : Finset ℕ :=
  Finset.Ico (P.L N - p) (min (P.b N) (P.H N - p))

theorem paramUpperPairHighSet_mem_iff (P : Parameters) (p N j : ℕ) :
    j ∈ paramUpperPairHighSet P p N ↔
      ∃ ell, P.b N ≤ ell ∧ ell < min (P.A N) (P.L N - p) ∧ j = p + ell := by
  simp only [paramUpperPairHighSet, Finset.mem_Ico]
  constructor
  · intro hj
    refine ⟨j - p, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨ell, hlo, hhi, rfl⟩
    constructor <;> omega

theorem paramUpperCentralSet_mem_iff (P : Parameters) (p N j : ℕ) :
    j ∈ paramUpperCentralSet P p N ↔
      P.b N ≤ j ∧ j < P.L N ∧ P.H N - p ≤ j ∧ j < p := by
  simp only [paramUpperCentralSet, Finset.mem_Ico]
  omega

theorem paramUpperPairHighSet_subset_raw (P : Parameters) (p N : ℕ) :
    paramUpperPairHighSet P p N ⊆ Finset.Ico (P.b N) (P.L N) := by
  intro j hj
  simp only [paramUpperPairHighSet, Finset.mem_Ico] at hj
  apply Finset.mem_Ico.mpr
  constructor <;> omega

theorem paramUpperCentralSet_subset_raw (P : Parameters) (p N : ℕ) :
    paramUpperCentralSet P p N ⊆ Finset.Ico (P.b N) (P.L N) := by
  intro j hj
  have h := (paramUpperCentralSet_mem_iff P p N j).mp hj
  exact Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩

theorem paramUpperRetainedSet_subset_raw (P : Parameters) (p N : ℕ) :
    paramUpperRetainedSet P p N ⊆ Finset.Ico (P.b N) (P.L N) := by
  intro j hj
  exact (Finset.mem_sdiff.mp hj).1

theorem paramUpperPairHighSet_disjoint_central (P : Parameters) (p N : ℕ) :
    Disjoint (paramUpperPairHighSet P p N) (paramUpperCentralSet P p N) := by
  apply Finset.disjoint_left.mpr
  intro j hjp hjc
  simp only [paramUpperPairHighSet, Finset.mem_Ico] at hjp
  have h := (paramUpperCentralSet_mem_iff P p N j).mp hjc
  omega

theorem paramUpperRetainedSet_disjoint_pairHigh (P : Parameters) (p N : ℕ) :
    Disjoint (paramUpperRetainedSet P p N) (paramUpperPairHighSet P p N) := by
  apply Finset.disjoint_left.mpr
  intro j hjr hjp
  exact (Finset.mem_sdiff.mp hjr).2 (Finset.mem_union.mpr (Or.inl hjp))

theorem paramUpperRetainedSet_disjoint_central (P : Parameters) (p N : ℕ) :
    Disjoint (paramUpperRetainedSet P p N) (paramUpperCentralSet P p N) := by
  apply Finset.disjoint_left.mpr
  intro j hjr hjc
  exact (Finset.mem_sdiff.mp hjr).2 (Finset.mem_union.mpr (Or.inr hjc))

theorem paramUpperPool_partition (P : Parameters) (p N : ℕ) :
    paramUpperRetainedSet P p N ∪
      (paramUpperPairHighSet P p N ∪ paramUpperCentralSet P p N) =
        Finset.Ico (P.b N) (P.L N) := by
  ext j
  simp only [paramUpperRetainedSet, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (hj | hj | hj)
    · exact hj.1
    · exact paramUpperPairHighSet_subset_raw P p N hj
    · exact paramUpperCentralSet_subset_raw P p N hj
  · intro hj
    by_cases hp : j ∈ paramUpperPairHighSet P p N
    · exact Or.inr (Or.inl hp)
    by_cases hc : j ∈ paramUpperCentralSet P p N
    · exact Or.inr (Or.inr hc)
    · exact Or.inl ⟨hj, by simp [hp, hc]⟩

theorem paramUpperRetainedSet_mem_iff (P : Parameters) (p N j : ℕ) :
    j ∈ paramUpperRetainedSet P p N ↔
      P.b N ≤ j ∧ j < P.L N ∧ (j < P.H N - p ∨ p ≤ j) ∧
        j ∉ paramUpperPairHighSet P p N := by
  constructor
  · intro hj
    have hraw := Finset.mem_Ico.mp (Finset.mem_sdiff.mp hj).1
    have hnot := (Finset.mem_sdiff.mp hj).2
    refine ⟨hraw.1, hraw.2, ?_, fun hpair => hnot (Finset.mem_union.mpr (Or.inl hpair))⟩
    by_cases hJ : j < P.H N - p
    · exact Or.inl hJ
    · apply Or.inr
      by_contra hpj
      apply hnot
      apply Finset.mem_union.mpr
      apply Or.inr
      exact (paramUpperCentralSet_mem_iff P p N j).mpr
        ⟨hraw.1, hraw.2, by omega, by omega⟩
  · rintro ⟨hb, hL, hside, hpair⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨hb, hL⟩, ?_⟩
    intro hbad
    rcases Finset.mem_union.mp hbad with hbad | hbad
    · exact hpair hbad
    · have hc := (paramUpperCentralSet_mem_iff P p N j).mp hbad
      rcases hside with hside | hside <;> omega

theorem paramUpperPairHighSet_card (P : Parameters) (p N : ℕ) :
    (paramUpperPairHighSet P p N).card = min (P.A N) (P.L N - p) - P.b N := by
  rw [paramUpperPairHighSet, Nat.card_Ico]
  omega

theorem paramUpperCentralSet_card (P : Parameters) (p N : ℕ) :
    (paramUpperCentralSet P p N).card = min p (P.L N) - max (P.b N) (P.H N - p) := by
  rw [paramUpperCentralSet, Nat.card_Ico]

theorem paramUpperRetainedSet_card (P : Parameters) (p N : ℕ) :
    (paramUpperRetainedSet P p N).card =
      (P.L N - P.b N) - (min (P.A N) (P.L N - p) - P.b N) -
        (min p (P.L N) - max (P.b N) (P.H N - p)) := by
  have hsub : paramUpperPairHighSet P p N ∪ paramUpperCentralSet P p N ⊆
      Finset.Ico (P.b N) (P.L N) := by
    intro j hj
    rcases Finset.mem_union.mp hj with hpair | hcentral
    · exact paramUpperPairHighSet_subset_raw P p N hpair
    · exact paramUpperCentralSet_subset_raw P p N hcentral
  rw [paramUpperRetainedSet, Finset.card_sdiff_of_subset hsub,
    Finset.card_union_of_disjoint (paramUpperPairHighSet_disjoint_central P p N),
    paramUpperPairHighSet_card, paramUpperCentralSet_card, Nat.card_Ico]
  omega

theorem paramUpperExceptionalSet_card (P : Parameters) (p N : ℕ) :
    (paramUpperExceptionalSet P p N).card = min (P.b N) (P.H N - p) - (P.L N - p) := by
  rw [paramUpperExceptionalSet, Nat.card_Ico]

theorem paramUpperExceptionalSet_mem_iff (P : Parameters) (p N ell : ℕ) :
    ell ∈ paramUpperExceptionalSet P p N ↔
      ell < P.H N - p ∧ ¬(P.b N ≤ ell ∨ ell < P.L N - p) := by
  simp only [paramUpperExceptionalSet, Finset.mem_Ico]
  omega

theorem paramUpperPairIndex_bounds (P : Parameters) {p N ell : ℕ}
    (hA : P.A N ≤ p) (hLH : P.L N<P.H N)
    (hell : ell∈Finset.Ico (P.b N) (min (P.A N) (P.L N-p))) :
    ell∈paramUpperRetainedSet P p N ∧ p+ell∈paramUpperPairHighSet P p N ∧
      ell<p ∧ ell<P.H N-p :=by
  have he :=Finset.mem_Ico.mp hell
  have hellp : ell<p :=by omega
  have hellJ : ell<P.H N-p :=by omega
  have hnot : ell∉paramUpperPairHighSet P p N :=by
    intro hh
    simp only [paramUpperPairHighSet,Finset.mem_Ico] at hh
    omega
  refine ⟨?_,?_,hellp,hellJ⟩
  · exact (paramUpperRetainedSet_mem_iff P p N ell).mpr ⟨he.1,by omega,Or.inl hellJ,hnot⟩
  · exact (paramUpperPairHighSet_mem_iff P p N (p+ell)).mpr ⟨ell,he.1,he.2,rfl⟩

end
end CatalanMeasure.Parametric
