module
public import Submission.CatalanMeasure.Parametric.UpperPrimeEnumeration
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section
def paramUpperPairIndex (P : Parameters) (p N j : ℕ) : Prop :=
  p + P.b N ≤ j ∧ j < p + min (P.A N) (P.L N - p)

def paramUpperCentralIndex (P : Parameters) (p N j : ℕ) : Prop :=
  max (P.b N) (P.H N - p) ≤ j ∧ j < min p (P.L N)

instance paramUpperPairIndex_decidable (P : Parameters) (p N j : ℕ) :
    Decidable (paramUpperPairIndex P p N j) :=
  inferInstanceAs (Decidable (p + P.b N ≤ j ∧ j < p + min (P.A N) (P.L N - p)))

instance paramUpperCentralIndex_decidable (P : Parameters) (p N j : ℕ) :
    Decidable (paramUpperCentralIndex P p N j) :=
  inferInstanceAs (Decidable (max (P.b N) (P.H N - p) ≤ j ∧ j < min p (P.L N)))

def paramUpperPoolRat (P : Parameters) (z : ℚ) (p N r j : ℕ) : ℚ :=
  if paramUpperPairIndex P p N j then
    rawEntryRat P z N r j + rawEntryRat P z N r (j - p)
  else if paramUpperCentralIndex P p N j then paramShearedRat P z p N r j
  else rawEntryRat P z N r j

def paramUpperRepresentativePoolRat (P : Parameters) (z : ℚ) (p N r ell : ℕ) : ℚ :=
  if P.b N ≤ ell then paramUpperPoolRat P z p N r ell
  else -paramUpperPoolRat P z p N r (p + ell)

theorem paramUpperPoolRat_pair_low (P : Parameters) {p N j : ℕ} (hH : P.H N ≤ 2 * p)
    (hpair : paramUpperPairIndex P p N j) (z : ℚ) (r : ℕ) :
    paramUpperPoolRat P z p N r (j - p) = rawEntryRat P z N r (j - p) := by
  have hpair' := hpair
  unfold paramUpperPairIndex at hpair'
  have hLH : P.L N ≤ P.H N := by unfold Parameters.H Parameters.C;omega
  have hKJ : P.L N - p ≤ P.H N - p := Nat.sub_le_sub_right hLH p
  have hellJ : j - p < P.H N - p := by omega
  have hellp : j - p < p := by omega
  have hnotpair : ¬paramUpperPairIndex P p N (j - p) := by
    unfold paramUpperPairIndex
    omega
  have hnotcentral : ¬paramUpperCentralIndex P p N (j - p) := by
    unfold paramUpperCentralIndex
    omega
  rw [paramUpperPoolRat, ite_eq_right hnotpair, ite_eq_right hnotcentral]

theorem paramUpperRepresentativePoolRat_eq (P : Parameters) {p N ell : ℕ}
    (hH : P.H N ≤ 2 * p) (hell : ell < P.H N - p) (z : ℚ) (r : ℕ) :
    paramUpperRepresentativePoolRat P z p N r ell =
      paramRepresentativeRat P z p N r ell := by
  have hellp : ell < p := by omega
  by_cases hb : P.b N ≤ ell
  · have hpnot : ¬paramUpperPairIndex P p N ell := by
      unfold paramUpperPairIndex
      omega
    have hcnot : ¬paramUpperCentralIndex P p N ell := by
      unfold paramUpperCentralIndex
      omega
    rw [paramUpperRepresentativePoolRat, ite_eq_left hb, paramUpperPoolRat,
      ite_eq_right hpnot, ite_eq_right hcnot, paramRepresentativeRat, ite_eq_left hb]
  · have hpnot : ¬paramUpperPairIndex P p N (p + ell) := by
      unfold paramUpperPairIndex
      omega
    have hcnot : ¬paramUpperCentralIndex P p N (p + ell) := by
      unfold paramUpperCentralIndex
      omega
    rw [paramUpperRepresentativePoolRat, ite_eq_right hb, paramUpperPoolRat,
      ite_eq_right hpnot, ite_eq_right hcnot, paramRepresentativeRat, ite_eq_right hb]

theorem paramRawEntryRat_eq_upper_pool_inverse (P : Parameters) {p N : ℕ} (hH : P.H N ≤ 2 * p)
    (z : ℚ) (r j : ℕ) :
    rawEntryRat P z N r j = paramUpperPoolRat P z p N r j -
      (if paramUpperPairIndex P p N j then paramUpperPoolRat P z p N r (j - p) else 0) -
      (if paramUpperCentralIndex P p N j then
        (p : ℚ) * ∑ ell ∈ Finset.range (P.H N - p),
          if paramRepresented P p N ell then
            paramUpperRepresentativePoolRat P z p N r ell / ((j - ell : ℕ) : ℚ)
          else 0
        else 0) := by
  classical
  by_cases hpair : paramUpperPairIndex P p N j
  · have hcentral : ¬paramUpperCentralIndex P p N j := by
      unfold paramUpperPairIndex at hpair
      unfold paramUpperCentralIndex
      omega
    rw [ite_eq_left hpair, ite_eq_right hcentral, paramUpperPoolRat, ite_eq_left hpair,
      paramUpperPoolRat_pair_low P hH hpair, sub_zero]
    ring
  · by_cases hcentral : paramUpperCentralIndex P p N j
    · have hsum :
          (∑ ell ∈ Finset.range (P.H N - p), if paramRepresented P p N ell then
            paramUpperRepresentativePoolRat P z p N r ell / ((j - ell : ℕ) : ℚ) else 0) =
          ∑ ell ∈ Finset.range (P.H N - p), if paramRepresented P p N ell then
            paramRepresentativeRat P z p N r ell / ((j - ell : ℕ) : ℚ) else 0 := by
        apply Finset.sum_congr rfl
        intro ell hell
        rw [paramUpperRepresentativePoolRat_eq P hH (Finset.mem_range.mp hell)]
      rw [ite_eq_right hpair, ite_eq_left hcentral, sub_zero, hsum,
        paramUpperPoolRat, ite_eq_right hpair, ite_eq_left hcentral, paramShearedRat]
      ring
    · rw [ite_eq_right hpair, ite_eq_right hcentral, sub_zero, sub_zero,
        paramUpperPoolRat, ite_eq_right hpair, ite_eq_right hcentral]







open Classical
open scoped BigOperators

end
end CatalanMeasure.Parametric
