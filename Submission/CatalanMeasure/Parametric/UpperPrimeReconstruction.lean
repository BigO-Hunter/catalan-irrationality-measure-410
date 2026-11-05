module
public import Submission.CatalanMeasure.Parametric.UpperPrimePoolRows
@[expose] public section
namespace CatalanMeasure.Parametric
open Classical Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section
theorem paramUpperPhysicalColumn_eq_pool (P : Parameters) {p N : ℕ} [hp : Fact p.Prime]
    (z : ℚ) (phys : paramUpperPhysicalIndex P p N) (r : Fin (P.n N)) :
    paramUpperPhysicalColumn P z p N phys r =
      paramUpperPoolRat P z p N r.val ((paramUpperPoolEnumeration P p N phys).val) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rcases phys with j | (j | j)
  · let v := (Fintype.equivFin ↥(paramUpperRetainedSet P p N)).symm j
    have hnot := (Finset.mem_sdiff.mp v.property).2
    have hnotpair : ¬paramUpperPairIndex P p N v.val := by
      intro hpair
      have hmem : v.val ∈ paramUpperPairHighSet P p N := by
        simpa only [paramUpperPairIndex, paramUpperPairHighSet, Finset.mem_Ico] using hpair
      exact hnot (Finset.mem_union.mpr (Or.inl hmem))
    have hnotcentral : ¬paramUpperCentralIndex P p N v.val := by
      intro hcentral
      have hmem : v.val ∈ paramUpperCentralSet P p N := by
        simpa only [paramUpperCentralIndex, paramUpperCentralSet, Finset.mem_Ico] using hcentral
      exact hnot (Finset.mem_union.mpr (Or.inr hmem))
    simp only [paramUpperPhysicalColumn, oddPhysicalColumn,
      paramUpperRetainedVector, paramUpperPoolEnumeration_retained_val]
    change ((p : ℚ) ^ 2)⁻¹ * ((p : ℚ) ^ 2 * rawEntryRat P z N r.val v.val) =
      paramUpperPoolRat P z p N r.val v.val
    rw [paramUpperPoolRat, ite_eq_right hnotpair, ite_eq_right hnotcentral]
    field_simp [hpq]
  · let v := (Fintype.equivFin ↥(paramUpperPairHighSet P p N)).symm j
    have hpair : paramUpperPairIndex P p N v.val := by
      simpa only [paramUpperPairIndex, paramUpperPairHighSet, Finset.mem_Ico] using v.property
    simp only [paramUpperPhysicalColumn, oddPhysicalColumn,
      paramUpperPairedVector, paramUpperPoolEnumeration_pairHigh_val]
    change (p : ℚ)⁻¹ * ((p : ℚ) * (rawEntryRat P z N r.val v.val +
      rawEntryRat P z N r.val (v.val - p))) = paramUpperPoolRat P z p N r.val v.val
    rw [paramUpperPoolRat, ite_eq_left hpair]
    field_simp [hpq]
  · let v := (Fintype.equivFin ↥(paramUpperCentralSet P p N)).symm j
    have hcentral : paramUpperCentralIndex P p N v.val := by
      simpa only [paramUpperCentralIndex, paramUpperCentralSet, Finset.mem_Ico] using v.property
    have hnotpair : ¬paramUpperPairIndex P p N v.val := by
      intro hpair
      have hmem : v.val ∈ paramUpperPairHighSet P p N := by
        simpa only [paramUpperPairIndex, paramUpperPairHighSet, Finset.mem_Ico] using hpair
      exact (Finset.disjoint_left.mp (paramUpperPairHighSet_disjoint_central P p N)) hmem v.property
    have hsum := paramUpperExceptionalVector_combination P (p := p) (N := N) z j r
    simp only [paramUpperPhysicalColumn, oddPhysicalColumn,
      paramUpperPoolEnumeration_central_val]
    rw [hsum]
    change paramCentralRemainderRat P z p N r.val v.val +
      (p : ℚ)⁻¹ * paramExceptionalPartRat P z p N r.val v.val =
        paramUpperPoolRat P z p N r.val v.val
    rw [paramUpperPoolRat, ite_eq_right hnotpair, ite_eq_left hcentral]
    exact (paramShearedRat_eq_remainder_add_exceptional P (p := p) z N r.val v.val).symm







open Classical
open scoped BigOperators

def paramUpperDelta (P : Parameters) (p N : ℕ) (phys : paramUpperPhysicalIndex P p N)
    (j : ℕ) : ℚ :=
  if (paramUpperPoolEnumeration P p N phys).val = j then 1 else 0

def paramUpperRepresentativeNumber (P : Parameters) (p N ell : ℕ) : ℕ :=
  if P.b N ≤ ell then ell else p + ell

def paramUpperRepresentativeSign (P : Parameters) (N ell : ℕ) : ℚ :=
  if P.b N ≤ ell then 1 else -1

def paramUpperShearCoeff (P : Parameters) (p N : ℕ) (phys : paramUpperPhysicalIndex P p N)
    (j ell : ℕ) : ℚ :=
  if paramRepresented P p N ell then
    (paramUpperRepresentativeSign P N ell / ((j - ell : ℕ) : ℚ)) *
      paramUpperDelta P p N phys (paramUpperRepresentativeNumber P p N ell)
  else 0

def paramUpperInverseCoeff (P : Parameters) (p N : ℕ) (phys : paramUpperPhysicalIndex P p N)
    (j : ℕ) : ℚ :=
  paramUpperDelta P p N phys j -
    (if paramUpperPairIndex P p N j then paramUpperDelta P p N phys (j - p) else 0) -
    (if paramUpperCentralIndex P p N j then
      (p : ℚ) * ∑ ell ∈ Finset.range (P.H N - p),
        paramUpperShearCoeff P p N phys j ell
    else 0)






open Classical
open scoped BigOperators

private theorem paramUpper_delta_den_ne_zero (P : Parameters) {p N : ℕ} [Fact p.Prime]
    (phys : paramUpperPhysicalIndex P p N) (j : ℕ) :
    ((paramUpperDelta P p N phys j).den : ZMod p) ≠ 0 := by
  unfold paramUpperDelta
  split_ifs <;> norm_num

private theorem paramUpper_sign_den_ne_zero (P : Parameters) {p : ℕ} [Fact p.Prime] (N ell : ℕ) :
    ((paramUpperRepresentativeSign P N ell).den : ZMod p) ≠ 0 := by
  unfold paramUpperRepresentativeSign
  split_ifs <;> norm_num

private theorem paramUpper_shearCoeff_den_ne_zero (P : Parameters) {p N : ℕ} [Fact p.Prime]
    (phys : paramUpperPhysicalIndex P p N) (j ell : ℕ)
    (hc : paramUpperCentralIndex P p N j) (hell : ell ∈ Finset.range (P.H N - p)) :
    ((paramUpperShearCoeff P p N phys j ell).den : ZMod p) ≠ 0 := by
  have hc' : max (P.b N) (P.H N - p) ≤ j ∧ j < min p (P.L N) := hc
  have he : ell < P.H N - p := Finset.mem_range.mp hell
  have hjlo : P.H N - p ≤ j := (Nat.le_max_right _ _).trans hc'.1
  have hj : j < p := hc'.2.trans_le (Nat.min_le_left _ _)
  have hdpos : 0 < j - ell := by omega
  have hdlt : j - ell < p := by omega
  have hd : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
      ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
  unfold paramUpperShearCoeff
  split_ifs with hrep
  · have hinv := nat_fraction_reduced_residue (p := p) 1 (j - ell) hd
    simp only [Nat.cast_one] at hinv
    have hsign := paramUpper_sign_den_ne_zero P (p := p) N ell
    have hmul := rational_residue_mul hsign hinv.1
    have hfrac :
        ((paramUpperRepresentativeSign P N ell / ((j - ell : ℕ) : ℚ)).den : ZMod p) ≠ 0 := by
      have heq : paramUpperRepresentativeSign P N ell / ((j - ell : ℕ) : ℚ) =
          paramUpperRepresentativeSign P N ell * (1 / ((j - ell : ℕ) : ℚ)) := by ring
      rw [heq]
      exact hmul.1
    exact (rational_residue_mul hfrac
      (paramUpper_delta_den_ne_zero P phys (paramUpperRepresentativeNumber P p N ell))).1
  · norm_num

theorem paramUpperInverseCoeff_den_ne_zero (P : Parameters) {p N : ℕ} [Fact p.Prime]
    (phys : paramUpperPhysicalIndex P p N) (j : ℕ) :
    ((paramUpperInverseCoeff P p N phys j).den : ZMod p) ≠ 0 := by
  have hbase := paramUpper_delta_den_ne_zero P phys j
  have hpair :
      ((if paramUpperPairIndex P p N j then paramUpperDelta P p N phys (j - p)
        else 0).den : ZMod p) ≠ 0 := by
    split_ifs
    · exact paramUpper_delta_den_ne_zero P phys (j - p)
    · norm_num
  have hleft := rational_residue_sub hbase hpair
  have hcentral :
      ((if paramUpperCentralIndex P p N j then
          (p : ℚ) * ∑ ell ∈ Finset.range (P.H N - p), paramUpperShearCoeff P p N phys j ell
        else 0).den : ZMod p) ≠ 0 := by
    split_ifs with hc
    · have hsum := rational_residue_sum (Finset.range (P.H N - p))
        (fun ell => paramUpperShearCoeff P p N phys j ell)
        (fun ell hell => paramUpper_shearCoeff_den_ne_zero P phys j ell hc hell)
      exact (rational_residue_mul (a := (p : ℚ)) (by simp) hsum.1).1
    · norm_num
  exact (rational_residue_sub hleft.1 hcentral).1






open Classical
open scoped BigOperators

theorem paramUpperDelta_sum (P : Parameters) {p N : ℕ} [Fact p.Prime]
    (z : ℚ) (r : Fin (P.n N)) (j : ℕ) (hj : j ∈ Finset.Ico (P.b N) (P.L N)) :
    (∑ phys : paramUpperPhysicalIndex P p N,
      paramUpperPhysicalColumn P z p N phys r * paramUpperDelta P p N phys j) =
        paramUpperPoolRat P z p N r.val j := by
  let e := paramUpperPoolEnumeration P p N
  let v : ↥(Finset.Ico (P.b N) (P.L N)) := ⟨j, hj⟩
  have htag (phys : paramUpperPhysicalIndex P p N) :
      (paramUpperPoolEnumeration P p N phys).val = j ↔ phys = e.symm v := by
    constructor
    · intro h
      have he : e phys = v := Subtype.ext h
      calc
        phys = e.symm (e phys) := (e.symm_apply_apply phys).symm
        _ = e.symm v := congrArg e.symm he
    · rintro rfl
      exact congrArg Subtype.val (e.apply_symm_apply v)
  simp only [paramUpperDelta, htag, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simpa only [e, Equiv.apply_symm_apply] using
    paramUpperPhysicalColumn_eq_pool P z (e.symm v) r

theorem paramUpperRepresentativeNumber_mem (P : Parameters) {p N ell : ℕ}
    (hN : 0 < N) (hH : P.H N ≤ 2 * p) (hbp : P.b N<p) (hJL : P.H N-p ≤ P.L N) (hell : ell < P.H N - p)
    (hrep : paramRepresented P p N ell) :
    paramUpperRepresentativeNumber P p N ell ∈ Finset.Ico (P.b N) (P.L N) := by
  unfold paramUpperRepresentativeNumber
  by_cases hb : P.b N ≤ ell
  · rw [ite_eq_left hb]
    exact Finset.mem_Ico.mpr ⟨hb, by omega⟩
  · rw [ite_eq_right hb]
    unfold paramRepresented at hrep
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem paramUpperRepresentativePoolRat_eq_sign (P : Parameters) (z : ℚ) (p N r ell : ℕ) :
    paramUpperRepresentativePoolRat P z p N r ell =
      paramUpperRepresentativeSign P N ell *
        paramUpperPoolRat P z p N r (paramUpperRepresentativeNumber P p N ell) := by
  by_cases hb : P.b N ≤ ell <;>
    simp only [paramUpperRepresentativePoolRat, paramUpperRepresentativeSign,
      paramUpperRepresentativeNumber, hb, ite_true, ite_false, one_mul, neg_one_mul]

theorem paramUpperShearCoeff_sum (P : Parameters) {p N : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hH : P.H N ≤ 2 * p) (hbp : P.b N<p) (hJL : P.H N-p ≤ P.L N) (z : ℚ) (r : Fin (P.n N))
    (j ell : ℕ) (hell : ell < P.H N - p) :
    (∑ phys : paramUpperPhysicalIndex P p N,
      paramUpperPhysicalColumn P z p N phys r * paramUpperShearCoeff P p N phys j ell) =
      if paramRepresented P p N ell then
        paramUpperRepresentativePoolRat P z p N r.val ell / ((j - ell : ℕ) : ℚ)
      else 0 := by
  by_cases hrep : paramRepresented P p N ell
  · simp only [paramUpperShearCoeff, ite_eq_left hrep]
    calc
      _ = (paramUpperRepresentativeSign P N ell / ((j - ell : ℕ) : ℚ)) *
          ∑ phys : paramUpperPhysicalIndex P p N,
            paramUpperPhysicalColumn P z p N phys r *
              paramUpperDelta P p N phys (paramUpperRepresentativeNumber P p N ell) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro phys _
        ring
      _ = _ := by
        rw [paramUpperDelta_sum P z r _
          (paramUpperRepresentativeNumber_mem P hN hH hbp hJL hell hrep),
          paramUpperRepresentativePoolRat_eq_sign]
        ring
  · simp only [paramUpperShearCoeff, ite_eq_right hrep, mul_zero, Finset.sum_const_zero]

theorem paramRawEntryRat_eq_upper_physical_sum (P : Parameters) {p N : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hH : P.H N ≤ 2 * p) (hbp : P.b N<p) (hJL : P.H N-p ≤ P.L N) (z : ℚ)
    (j : ↥(Finset.Ico (P.b N) (P.L N))) (r : Fin (P.n N)) :
    rawEntryRat P z N r.val j.val =
      ∑ phys : paramUpperPhysicalIndex P p N,
        paramUpperPhysicalColumn P z p N phys r * paramUpperInverseCoeff P p N phys j.val := by
  have hpairSum :
      (∑ phys : paramUpperPhysicalIndex P p N,
        paramUpperPhysicalColumn P z p N phys r *
          (if paramUpperPairIndex P p N j.val then
            paramUpperDelta P p N phys (j.val - p) else 0)) =
      if paramUpperPairIndex P p N j.val then
        paramUpperPoolRat P z p N r.val (j.val - p) else 0 := by
    by_cases hp : paramUpperPairIndex P p N j.val
    · simp only [ite_eq_left hp]
      apply paramUpperDelta_sum P
      have hj := Finset.mem_Ico.mp j.property
      unfold paramUpperPairIndex at hp
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · simp only [ite_eq_right hp, mul_zero, Finset.sum_const_zero]
  have hcentralSum :
      (∑ phys : paramUpperPhysicalIndex P p N,
        paramUpperPhysicalColumn P z p N phys r *
          (if paramUpperCentralIndex P p N j.val then
            (p : ℚ) * ∑ ell ∈ Finset.range (P.H N - p),
              paramUpperShearCoeff P p N phys j.val ell else 0)) =
      if paramUpperCentralIndex P p N j.val then
        (p : ℚ) * ∑ ell ∈ Finset.range (P.H N - p),
          if paramRepresented P p N ell then
            paramUpperRepresentativePoolRat P z p N r.val ell / ((j.val - ell : ℕ) : ℚ)
          else 0
      else 0 := by
    by_cases hc : paramUpperCentralIndex P p N j.val
    · simp only [ite_eq_left hc]
      calc
        _ = (p : ℚ) * ∑ phys : paramUpperPhysicalIndex P p N,
              ∑ ell ∈ Finset.range (P.H N - p),
                paramUpperPhysicalColumn P z p N phys r *
                  paramUpperShearCoeff P p N phys j.val ell := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro phys _
          apply Finset.sum_congr rfl
          intro ell _
          ring
        _ = (p : ℚ) * ∑ ell ∈ Finset.range (P.H N - p),
              ∑ phys : paramUpperPhysicalIndex P p N,
                paramUpperPhysicalColumn P z p N phys r *
                  paramUpperShearCoeff P p N phys j.val ell := by
          rw [Finset.sum_comm]
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro ell hell
          exact paramUpperShearCoeff_sum P hN hH hbp hJL z r j.val ell (Finset.mem_range.mp hell)
    · simp only [ite_eq_right hc, mul_zero, Finset.sum_const_zero]
  rw [paramRawEntryRat_eq_upper_pool_inverse P hH]
  symm
  simp only [paramUpperInverseCoeff, mul_sub, Finset.sum_sub_distrib]
  rw [paramUpperDelta_sum P z r j.val j.property, hpairSum, hcentralSum]







open Classical
open scoped BigOperators

end
end CatalanMeasure.Parametric
