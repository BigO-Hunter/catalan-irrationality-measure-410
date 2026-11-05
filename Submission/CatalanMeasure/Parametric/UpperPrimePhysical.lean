module
public import Submission.CatalanMeasure.Parametric.UpperPrimePoolSets
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section
abbrev paramUpperExceptionalSize (P : Parameters) (p N : ℕ) :=
  Fintype.card ↥(paramUpperExceptionalSet P p N)

theorem paramUpperExceptional_sum_eq (P : Parameters) (p N : ℕ) (f : ℕ → ℚ) :
    (∑ l : Fin (paramUpperExceptionalSize P p N),
      f (((Fintype.equivFin ↥(paramUpperExceptionalSet P p N)).symm l).val)) =
        ∑ ell ∈ Finset.range (P.H N - p),
          if ¬paramRepresented P p N ell then f ell else 0 := by
  have hs : paramUpperExceptionalSet P p N =
      (Finset.range (P.H N - p)).filter (fun ell => ¬paramRepresented P p N ell) := by
    ext ell
    constructor
    · intro h
      have he := (paramUpperExceptionalSet_mem_iff P p N ell).mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr he.1, he.2⟩
    · intro h
      have he := Finset.mem_filter.mp h
      exact (paramUpperExceptionalSet_mem_iff P p N ell).mpr
        ⟨Finset.mem_range.mp he.1, he.2⟩
  calc
    _ = ∑ ell : ↥(paramUpperExceptionalSet P p N), f ell.val :=
      Equiv.sum_comp (Fintype.equivFin ↥(paramUpperExceptionalSet P p N)).symm
        (fun ell => f ell.val)
    _ = ∑ ell ∈ paramUpperExceptionalSet P p N, f ell :=
      Finset.sum_coe_sort (paramUpperExceptionalSet P p N) f
    _ = _ := by rw [hs, Finset.sum_filter]

theorem paramUpperExceptional_combination_eq (P : Parameters) {p : ℕ} [Fact p.Prime]
    (z : ℚ) (N r j : ℕ) :
    (∑ l : Fin (paramUpperExceptionalSize P p N),
      (-1 / ((j - ((Fintype.equivFin ↥(paramUpperExceptionalSet P p N)).symm l).val : ℕ) : ℚ)) *
        paramLeadingLiftRat P p N r
          ((Fintype.equivFin ↥(paramUpperExceptionalSet P p N)).symm l).val) =
      paramExceptionalPartRat P z p N r j := by
  rw [paramUpperExceptional_sum_eq P p N
    (fun ell => (-1 / ((j - ell : ℕ) : ℚ)) * paramLeadingLiftRat P p N r ell)]
  unfold paramExceptionalPartRat
  apply Finset.sum_congr rfl
  intro ell hell
  by_cases hex : ¬paramRepresented P p N ell
  · rw [ite_eq_left hex, ite_eq_left hex]
    ring
  · rw [ite_eq_right hex, ite_eq_right hex]







open Classical
open scoped BigOperators

abbrev paramUpperRetainedSize (P : Parameters) (p N : ℕ) := Fintype.card ↥(paramUpperRetainedSet P p N)
abbrev paramUpperPairedSize (P : Parameters) (p N : ℕ) := Fintype.card ↥(paramUpperPairHighSet P p N)
abbrev paramUpperCentralSize (P : Parameters) (p N : ℕ) := Fintype.card ↥(paramUpperCentralSet P p N)
abbrev paramUpperPhysicalIndex (P : Parameters) (p N : ℕ) :=
  oddPhysicalIndex (paramUpperRetainedSize P p N) (paramUpperPairedSize P p N)
    (paramUpperCentralSize P p N)

def paramUpperRetainedVector (P : Parameters) (z : ℚ) (p N : ℕ)
    (j : Fin (paramUpperRetainedSize P p N)) (r : Fin (P.n N)) : ℚ :=
  (p : ℚ) ^ 2 * rawEntryRat P z N r.val
    (((Fintype.equivFin ↥(paramUpperRetainedSet P p N)).symm j).val)

def paramUpperPairedVector (P : Parameters) (z : ℚ) (p N : ℕ)
    (j : Fin (paramUpperPairedSize P p N)) (r : Fin (P.n N)) : ℚ :=
  let v := ((Fintype.equivFin ↥(paramUpperPairHighSet P p N)).symm j).val
  (p : ℚ) * (rawEntryRat P z N r.val v + rawEntryRat P z N r.val (v - p))

def paramUpperIntegralVector (P : Parameters) (z : ℚ) (p N : ℕ) [Fact p.Prime]
    (j : Fin (paramUpperCentralSize P p N)) (r : Fin (P.n N)) : ℚ :=
  paramCentralRemainderRat P z p N r.val
    (((Fintype.equivFin ↥(paramUpperCentralSet P p N)).symm j).val)

def paramUpperExceptionalVector (P : Parameters) (p N : ℕ) [Fact p.Prime]
    (ell : Fin (paramUpperExceptionalSize P p N)) (r : Fin (P.n N)) : ℚ :=
  paramLeadingLiftRat P p N r.val
    (((Fintype.equivFin ↥(paramUpperExceptionalSet P p N)).symm ell).val)

def paramUpperExceptionalCoeff (P : Parameters) (p N : ℕ)
    (j : Fin (paramUpperCentralSize P p N))
    (ell : Fin (paramUpperExceptionalSize P p N)) : ℚ :=
  let v := ((Fintype.equivFin ↥(paramUpperCentralSet P p N)).symm j).val
  let l := ((Fintype.equivFin ↥(paramUpperExceptionalSet P p N)).symm ell).val
  (-1 : ℚ) / ((v - l : ℕ) : ℚ)

def paramUpperPhysicalColumn (P : Parameters) (z : ℚ) (p N : ℕ) [Fact p.Prime]
    (j : paramUpperPhysicalIndex P p N) (r : Fin (P.n N)) : ℚ :=
  oddPhysicalColumn p (paramUpperRetainedVector P z p N)
    (paramUpperPairedVector P z p N) (paramUpperIntegralVector P z p N)
    (paramUpperExceptionalVector P p N) (paramUpperExceptionalCoeff P p N) j r

theorem paramUpperRetainedVector_den_ne_zero (P : Parameters) {p N : ℕ} [Fact p.Prime]
    (hAdm : Admissible P) (hp2 : p ≠ 2) (hHsq : P.H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (paramUpperRetainedSize P p N)) (r : Fin (P.n N)) :
    ((paramUpperRetainedVector P z p N j r).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(paramUpperRetainedSet P p N)).symm j
  have hraw := paramUpperRetainedSet_subset_raw P p N v.property
  have hvL := (Finset.mem_Ico.mp hraw).2
  have hvH : v.val < P.H N := by unfold Parameters.H Parameters.C at *;omega
  have hzp : (((p:ℚ)*z).den : ZMod p)≠0 :=(rational_residue_mul (a :=(p:ℚ)) (by simp) hz).1
  exact (scaledRawEntry_transfer (r :=r.val) hp2 hHsq hvH z hzp).1

theorem paramUpperPairedVector_den_ne_zero (P : Parameters) {p N : ℕ} [Fact p.Prime]
    (hAdm : Admissible P) (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ P.H N) (hH : P.H N ≤ 2 * p)
    (hA : P.A N ≤ p) (hLH : P.L N<P.H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (paramUpperPairedSize P p N)) (r : Fin (P.n N)) :
    ((paramUpperPairedVector P z p N j r).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(paramUpperPairHighSet P p N)).symm j
  obtain ⟨ell, hb, hell, hveq⟩ :=
    (paramUpperPairHighSet_mem_iff P p N v.val).mp v.property
  have hbounds := paramUpperPairIndex_bounds P hA hLH
    (Finset.mem_Ico.mpr ⟨hb, hell⟩)
  have hsub : v.val - p = ell := by omega
  have hwidth : P.H N ≤ ell + 2 * p := by omega
  have hhigh : p + ell < P.H N := by have := hbounds.2.2.2; omega
  have hA : ell ≤ P.A N := by omega
  have hzp : (((p:ℚ)*z).den : ZMod p)≠0 :=(rational_residue_mul (a :=(p:ℚ)) (by simp) hz).1
  have hpair := rawEntry_pair_prime_integral hAdm hp2 hN r.isLt
    hbounds.2.2.1 hwidth hhigh hA z hzp
  change (((p : ℚ) * (rawEntryRat P z N r.val v.val +
    rawEntryRat P z N r.val (v.val - p))).den : ZMod p) ≠ 0
  rw [hsub, hveq, add_comm (rawEntryRat P z N r.val (p + ell)) (rawEntryRat P z N r.val ell)]
  exact hpair

theorem paramUpperIntegralVector_den_ne_zero (P : Parameters) {p N : ℕ} [Fact p.Prime]
    (hAdm : Admissible P) (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ P.H N) (hH : P.H N ≤ 2 * p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (paramUpperCentralSize P p N)) (r : Fin (P.n N)) :
    ((paramUpperIntegralVector P z p N j r).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(paramUpperCentralSet P p N)).symm j
  have hv := (paramUpperCentralSet_mem_iff P p N v.val).mp v.property
  exact paramCentralRemainderRat_den_ne_zero P hAdm hp2 hN r.isLt hpH hH
    hv.2.2.1 hv.2.2.2 z hz

theorem paramUpperExceptionalVector_den_ne_zero (P : Parameters) {p N : ℕ} [Fact p.Prime]
    (ell : Fin (paramUpperExceptionalSize P p N)) (r : Fin (P.n N)) :
    ((paramUpperExceptionalVector P p N ell r).den : ZMod p) ≠ 0 :=
  (paramLeadingLiftRat_reduction P (p := p) (N := N) (r := r.val)
    (ell := ((Fintype.equivFin ↥(paramUpperExceptionalSet P p N)).symm ell).val)).1

theorem paramUpperExceptionalCoeff_den_ne_zero (P : Parameters) {p N : ℕ} [Fact p.Prime]
    (j : Fin (paramUpperCentralSize P p N))
    (ell : Fin (paramUpperExceptionalSize P p N)) :
    ((paramUpperExceptionalCoeff P p N j ell).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(paramUpperCentralSet P p N)).symm j
  let l := (Fintype.equivFin ↥(paramUpperExceptionalSet P p N)).symm ell
  have hv := (paramUpperCentralSet_mem_iff P p N v.val).mp v.property
  have hl := (paramUpperExceptionalSet_mem_iff P p N l.val).mp l.property
  have hdpos : 0 < v.val - l.val := by omega
  have hdlt : v.val - l.val < p := by omega
  have hd : ((v.val - l.val : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
      ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
  have hf := nat_fraction_reduced_residue (p := p) 1 (v.val - l.val) hd
  change (((-1 : ℚ) / ((v.val - l.val : ℕ) : ℚ)).den : ZMod p) ≠ 0
  simpa only [Nat.cast_one, neg_div, Rat.neg_den] using hf.1

theorem paramUpperExceptionalVector_combination (P : Parameters) {p N : ℕ} [Fact p.Prime]
    (z : ℚ) (j : Fin (paramUpperCentralSize P p N)) (r : Fin (P.n N)) :
    (∑ ell : Fin (paramUpperExceptionalSize P p N),
      paramUpperExceptionalCoeff P p N j ell * paramUpperExceptionalVector P p N ell r) =
      paramExceptionalPartRat P z p N r.val
        (((Fintype.equivFin ↥(paramUpperCentralSet P p N)).symm j).val) := by
  simpa only [paramUpperExceptionalCoeff, paramUpperExceptionalVector] using
    paramUpperExceptional_combination_eq P (p := p) z N r.val
      (((Fintype.equivFin ↥(paramUpperCentralSet P p N)).symm j).val)

end
end CatalanMeasure.Parametric
