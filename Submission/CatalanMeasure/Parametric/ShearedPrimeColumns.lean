module
public import Submission.CatalanMeasure.Parametric.LowHighPrimeColumns
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem paramLeadingU_zero {P : Parameters} (hAdm : Admissible P)
    {p N r ell : ℕ} [Fact p.Prime] (hN : 0<N) (hr : r<P.n N) (hA : ell ≤ P.A N) :
    paramLeadingU P p N r ell=0 :=by
  let F : (ZMod p)[X] :=(rowP P N r).map (Int.castRingHom (ZMod p))
  have hF : ∀ i,i<P.A N → F.coeff i=0 :=by
    intro i hi;simp only [F,coeff_map,rowP_coeff_eq_zero_of_lt hAdm hN hr hi,map_zero]
  have hG : ((rowD P N r).map (Int.castRingHom (ZMod p))).coeff ell=0 :=by
    simp only [coeff_map,rowD_coeff_eq_zero_of_lt hAdm hN hr (show ell<P.A N+1 by omega),map_zero]
  unfold paramLeadingU
  have hc : X*F*oddPrimeWeight p=X*oddPrimeWeight p*F :=by ring
  rw [hc,weighted_prime_coeff_zero_low F hF hA,hG]
  ring
def paramRepresented (P : Parameters) (p N ell : ℕ) : Prop :=
  P.b N ≤ ell ∨ ell < P.L N - p

instance paramRepresented_decidable (P : Parameters) (p N ell : ℕ) : Decidable (paramRepresented P p N ell) :=
  inferInstanceAs (Decidable (P.b N ≤ ell ∨ ell < P.L N - p))

def paramRepresentativeRat (P : Parameters) (z : ℚ) (p N r ell : ℕ) : ℚ :=
  if P.b N ≤ ell then rawEntryRat P z N r ell else -rawEntryRat P z N r (p + ell)

theorem paramRepresentativeRat_scaled_reduction (P : Parameters) {p N r ell : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < P.n N)
    (hpH : p ≤ P.H N) (hH : P.H N ≤ 2 * p) (hell : ell < P.H N - p)
    (_hrep : paramRepresented P p N ell) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * paramRepresentativeRat P z p N r ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * paramRepresentativeRat P z p N r ell) =
        paramLeadingV P p N r ell := by
  have hellp : ell < p := by omega
  have hwidth : P.H N ≤ ell + 2 * p := by omega
  have hhigh : p + ell < P.H N := by omega
  have hzp : (((p:ℚ)*z).den : ZMod p)≠0 :=(rational_residue_mul (a :=(p:ℚ)) (by simp) hz).1
  by_cases hb : P.b N ≤ ell
  · rw [paramRepresentativeRat, ite_eq_left hb]
    exact paramRawEntry_low_leading (r :=r) hAdm hp2 hN hellp hwidth hhigh z hzp
  · have hellA : ell ≤ P.A N := by
      unfold Parameters.A
      omega
    have hU := paramLeadingU_zero (p :=p) hAdm hN hr hellA
    have hraw := paramRawEntry_high_leading (r :=r) hAdm hp2 hN hellp hwidth hhigh z hzp
    rw [paramRepresentativeRat, ite_eq_right hb, mul_neg]
    refine ⟨?_, ?_⟩
    · simpa only [Rat.neg_den] using hraw.1
    · have hneg :
          palindromicRatResidue p (-((p : ℚ) ^ 2 * rawEntryRat P z N r (p + ell))) =
            -palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat P z N r (p + ell)) := by
        simp only [palindromicRatResidue, Rat.neg_num, Rat.neg_den, Int.cast_neg, neg_div]
      rw [hneg, hraw.2, hU, zero_sub, neg_neg]







open scoped BigOperators

def paramShearedRat (P : Parameters) (z : ℚ) (p N r j : ℕ) : ℚ := by
  classical
  exact rawEntryRat P z N r j + (p : ℚ) *
    ∑ ell ∈ Finset.range (P.H N - p),
      if paramRepresented P p N ell then
        paramRepresentativeRat P z p N r ell / ((j - ell : ℕ) : ℚ)
      else 0

theorem paramShearedRat_scaled_reduction (P : Parameters) {p N r j : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < P.n N)
    (hpH : p ≤ P.H N) (hH : P.H N ≤ 2 * p)
    (hjlo : P.H N - p ≤ j) (hj : j < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) * paramShearedRat P z p N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * paramShearedRat P z p N r j) =
        -(∑ ell ∈ Finset.range (P.H N - p),
          if ¬paramRepresented P p N ell then
            paramLeadingV P p N r ell / ((j - ell : ℕ) : ZMod p)
          else 0) := by
  classical
  let f : ℕ → ℚ := fun ell =>
    if paramRepresented P p N ell then
      (p : ℚ) ^ 2 * paramRepresentativeRat P z p N r ell /
        ((j - ell : ℕ) : ℚ)
    else 0
  have hterm (ell : ℕ) (hell : ell ∈ Finset.range (P.H N - p)) :
      ((f ell).den : ZMod p) ≠ 0 ∧
        palindromicRatResidue p (f ell) =
          if paramRepresented P p N ell then
            paramLeadingV P p N r ell / ((j - ell : ℕ) : ZMod p)
          else 0 := by
    by_cases hrep : paramRepresented P p N ell
    · have hellJ := Finset.mem_range.mp hell
      have hrepR := paramRepresentativeRat_scaled_reduction P
        hAdm hp2 hN hr hpH hH hellJ hrep z hz
      have hellj : ell < j := hellJ.trans_le hjlo
      have hdpos : 0 < j - ell := by omega
      have hdlt : j - ell < p := by omega
      have hden : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
        intro hzero
        exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
          ((ZMod.natCast_eq_zero_iff (j - ell) p).mp hzero)
      have hinv := nat_fraction_reduced_residue (p := p) 1 (j - ell) hden
      simp only [Nat.cast_one] at hinv
      have hinvR : palindromicRatResidue p (1 / ((j - ell : ℕ) : ℚ)) =
          1 / ((j - ell : ℕ) : ZMod p) := hinv.2
      have hprod := rational_residue_mul hrepR.1 hinv.1
      have heq : f ell =
          ((p : ℚ) ^ 2 * paramRepresentativeRat P z p N r ell) *
            (1 / ((j - ell : ℕ) : ℚ)) := by
        dsimp only [f]
        rw [ite_eq_left hrep]
        ring
      refine ⟨?_, ?_⟩
      · rw [heq]
        exact hprod.1
      · rw [heq, palindromicRatResidue_mul hrepR.1 hinv.1,
          hrepR.2, hinvR, ite_eq_left hrep]
        ring
    · simp [f, hrep, palindromicRatResidue]
  have hsum := rational_residue_sum (Finset.range (P.H N - p)) f
    (fun ell hell => (hterm ell hell).1)
  have hsumR : palindromicRatResidue p (∑ ell ∈ Finset.range (P.H N - p), f ell) =
      ∑ ell ∈ Finset.range (P.H N - p),
        if paramRepresented P p N ell then
          paramLeadingV P p N r ell / ((j - ell : ℕ) : ZMod p)
        else 0 := by
    calc
      _ = ∑ ell ∈ Finset.range (P.H N - p), palindromicRatResidue p (f ell) := hsum.2
      _ = _ := Finset.sum_congr rfl (fun ell hell => (hterm ell hell).2)
  have hcentral := paramRawEntry_central_layer (r :=r) hAdm hp2 hN hpH hH hjlo hj z hz
  have hadd := rational_residue_add hcentral.1 hsum.1
  have hscale : (p : ℚ) * paramShearedRat P z p N r j =
      (p : ℚ) * rawEntryRat P z N r j + ∑ ell ∈ Finset.range (P.H N - p), f ell := by
    unfold paramShearedRat
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ell hell
    dsimp only [f]
    split_ifs <;> ring
  have hpartition :
      (∑ ell ∈ Finset.range (P.H N - p),
        paramLeadingV P p N r ell / ((j - ell : ℕ) : ZMod p)) =
      (∑ ell ∈ Finset.range (P.H N - p),
        if paramRepresented P p N ell then
          paramLeadingV P p N r ell / ((j - ell : ℕ) : ZMod p) else 0) +
      (∑ ell ∈ Finset.range (P.H N - p),
        if ¬paramRepresented P p N ell then
          paramLeadingV P p N r ell / ((j - ell : ℕ) : ZMod p) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ell hell
    by_cases hrep : paramRepresented P p N ell <;> simp [hrep]
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hadd.1
  · rw [hscale, palindromicRatResidue_add hcentral.1 hsum.1,
      hcentral.2, hsumR, hpartition]
    ring







open scoped BigOperators

def paramLeadingLiftRat (P : Parameters) (p N r ell : ℕ) [Fact p.Prime] : ℚ :=
  ((paramLeadingV P p N r ell).val : ℚ)

def paramExceptionalPartRat (P : Parameters) (_z : ℚ) (p N r j : ℕ) [Fact p.Prime] : ℚ := by
  classical
  exact ∑ ell ∈ Finset.range (P.H N - p),
    if ¬paramRepresented P p N ell then
      -(paramLeadingLiftRat P p N r ell / ((j - ell : ℕ) : ℚ)) else 0

def paramCentralRemainderRat (P : Parameters) (z : ℚ) (p N r j : ℕ) [Fact p.Prime] : ℚ :=
  paramShearedRat P z p N r j - paramExceptionalPartRat P z p N r j / (p : ℚ)

theorem paramLeadingLiftRat_reduction (P : Parameters) {p N r ell : ℕ} [Fact p.Prime] :
    ((paramLeadingLiftRat P p N r ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (paramLeadingLiftRat P p N r ell) =
        paramLeadingV P p N r ell :=
  zmod_val_rat_reduction (paramLeadingV P p N r ell)

theorem paramExceptionalPartRat_reduction (P : Parameters) {p N r j : ℕ} [hp : Fact p.Prime]
    (hjlo : P.H N - p ≤ j) (hj : j < p) (z : ℚ) :
    ((paramExceptionalPartRat P z p N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (paramExceptionalPartRat P z p N r j) =
        -(∑ ell ∈ Finset.range (P.H N - p),
          if ¬paramRepresented P p N ell then
            paramLeadingV P p N r ell / ((j - ell : ℕ) : ZMod p) else 0) := by
  classical
  let f : ℕ → ℚ := fun ell => if ¬paramRepresented P p N ell then
    -(paramLeadingLiftRat P p N r ell / ((j - ell : ℕ) : ℚ)) else 0
  have ht (ell : ℕ) (hell : ell ∈ Finset.range (P.H N - p)) :
      ((f ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (f ell) =
        -(if ¬paramRepresented P p N ell then
          paramLeadingV P p N r ell / ((j - ell : ℕ) : ZMod p) else 0) := by
    by_cases hex : ¬paramRepresented P p N ell
    · have hell' : ell < P.H N - p := Finset.mem_range.mp hell
      have hd0 : 0 < j - ell := by omega
      have hdlt : j - ell < p := by omega
      have hd : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
        intro hzero
        exact (Nat.not_dvd_of_pos_of_lt hd0 hdlt)
          ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
      have hf := nat_fraction_reduced_residue (p := p) 1 (j - ell) hd
      simp only [Nat.cast_one] at hf
      have hl := paramLeadingLiftRat_reduction P (p := p) (N := N) (r := r) (ell := ell)
      have hm := rational_residue_mul hl.1 hf.1
      have hn := rational_residue_sub (p := p) (a := 0) (by norm_num) hm.1
      have heq : -(paramLeadingLiftRat P p N r ell / ((j - ell : ℕ) : ℚ)) =
          0 - paramLeadingLiftRat P p N r ell * (1 / ((j - ell : ℕ) : ℚ)) := by ring
      have hfr : palindromicRatResidue p (1 / ((j - ell : ℕ) : ℚ)) =
          1 / ((j - ell : ℕ) : ZMod p) := hf.2
      refine ⟨?_, ?_⟩
      · dsimp only [f]
        rw [ite_eq_left hex, heq]
        exact hn.1
      · dsimp only [f]
        rw [ite_eq_left hex, ite_eq_left hex, heq,
          palindromicRatResidue_sub (by norm_num) hm.1,
          palindromicRatResidue_mul hl.1 hf.1, hl.2, hfr]
        norm_num [palindromicRatResidue]
        ring
    · simp only [f, ite_eq_right hex]
      norm_num [palindromicRatResidue]
  have hs := rational_residue_sum (Finset.range (P.H N - p)) f (fun ell hell => (ht ell hell).1)
  refine ⟨hs.1, ?_⟩
  change palindromicRatResidue p (∑ ell ∈ Finset.range (P.H N - p), f ell) = _
  calc
    _ = ∑ ell ∈ Finset.range (P.H N - p), palindromicRatResidue p (f ell) := hs.2
    _ = ∑ ell ∈ Finset.range (P.H N - p),
        -(if ¬paramRepresented P p N ell then
          paramLeadingV P p N r ell / ((j - ell : ℕ) : ZMod p) else 0) :=
      Finset.sum_congr rfl (fun ell hell => (ht ell hell).2)
    _ = _ := by rw [Finset.sum_neg_distrib]

theorem paramCentralRemainderRat_den_ne_zero (P : Parameters) {p N r j : ℕ} [Fact p.Prime]
    (hAdm : Admissible P) (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < P.n N) (hpH : p ≤ P.H N)
    (hH : P.H N ≤ 2 * p) (hjlo : P.H N - p ≤ j) (hj : j < p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    ((paramCentralRemainderRat P z p N r j).den : ZMod p) ≠ 0 := by
  have hc := paramShearedRat_scaled_reduction P hAdm hp2 hN hr hpH hH hjlo hj z hz
  have he := paramExceptionalPartRat_reduction P (r := r) hjlo hj z
  exact rational_remainder_den_ne_zero_of_scaled_residue_eq hc.1 he.1
    (hc.2.trans he.2.symm)

theorem paramShearedRat_eq_remainder_add_exceptional (P : Parameters)
    {p : ℕ} [Fact p.Prime] (z : ℚ) (N r j : ℕ) :
    paramShearedRat P z p N r j = paramCentralRemainderRat P z p N r j +
      (p : ℚ)⁻¹ * paramExceptionalPartRat P z p N r j := by
  unfold paramCentralRemainderRat
  ring







open scoped BigOperators

end
end CatalanMeasure.Parametric
