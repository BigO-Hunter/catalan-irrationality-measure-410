module
public import Submission.CatalanMeasure.Parametric.Contact
public import Submission.OAI.NumberTheory.Catalan.Estimates.TwoAdicConvolution
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem param_rowP_coeff_two_pow_dvd (P : Parameters) (N r i : ℕ) :
    (2:ℤ)^(P.C N-2-i) ∣ (rowP P N r).coeff i :=by
  unfold rowP
  apply two_pow_sub_dvd_coeff_mul
  intro j
  have he : P.C N-2-j=P.C N-1-j-1 :=by omega
  rw [he]
  exact reversed_T_coeff_two_pow_dvd (P.C N) (rowDistance P N r:ℤ) j

theorem param_rowD_coeff_two_pow_dvd (P : Parameters) (N r i : ℕ) :
    (2:ℤ)^(P.C N-1-i) ∣ (rowD P N r).coeff i :=by
  unfold rowD
  rw [mul_assoc,mul_left_comm]
  apply two_pow_sub_dvd_coeff_mul
  intro j
  exact signed_reversed_U_coeff_two_pow_dvd (P.C N)
    (Int.sign (rowOffset P N r)) ((rowDistance P N r:ℤ)-1) j
def paramSmoothingColumn (P : Parameters) (N r j : ℕ) : ℚ_[2] :=
  ∑ i ∈ Finset.range (P.H N),
    ((rowP P N r).coeff i : ℚ_[2]) * smoothingMoment i j

def paramExceptionColumn (P : Parameters) (q : ℚ) (N r j : ℕ) : ℚ_[2] :=
  (4 * (q : ℚ_[2]) - smoothingMoment 0 0) *
    ∑ i ∈ Finset.range (P.H N),
      ((rowP P N r).coeff i : ℚ_[2]) *
        (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2])

def paramBoundaryColumn (P : Parameters) (N r j : ℕ) : ℚ_[2] :=
  ∑ i ∈ Finset.range (P.H N),
    ((rowD P N r).coeff i : ℚ_[2]) *
      ((-smoothingMoment 0 1) * (if i = j then 1 else 0) -
        (3 / 2 : ℚ_[2]) * (zetaRat i j : ℚ_[2]))

theorem paramRawEntryRat_two_adic_decomposition (P : Parameters) (q : ℚ) {N r j : ℕ}
    (hAdm : Admissible P) (hN : 0 < N) (hr : r < P.n N) (hj : j < P.L N) :
    (rawEntryRat P q N r j : ℚ_[2]) =
      paramSmoothingColumn P N r j + paramExceptionColumn P q N r j + paramBoundaryColumn P N r j := by
  classical
  have hjH : j < P.H N := by
    have hLH : P.L N ≤ P.H N := by unfold Parameters.H Parameters.C;omega
    exact lt_of_lt_of_le hj hLH
  have hcontact :
      (∑ i ∈ Finset.range (P.H N),
        ((rowP P N r).coeff i : ℚ_[2]) *
          (centralCoeffKernel ((j : ℤ) - i - 1) : ℚ_[2])) =
        ((rowD P N r).coeff j : ℚ_[2]) := by
    exact_mod_cast row_contact hAdm hN hr hj
  have hdelta :
      (∑ i ∈ Finset.range (P.H N),
        ((rowD P N r).coeff i : ℚ_[2]) * (if i = j then 1 else 0)) =
        ((rowD P N r).coeff j : ℚ_[2]) := by
    simp [Finset.mem_range, hjH]
  have hE :
      (∑ i ∈ Finset.range (P.H N),
        ((rowP P N r).coeff i : ℚ_[2]) *
          ((4 * (q : ℚ_[2]) - smoothingMoment 0 0) *
            (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]))) =
        paramExceptionColumn P q N r j := by
    unfold paramExceptionColumn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hB :
      (∑ i ∈ Finset.range (P.H N),
        ((rowP P N r).coeff i : ℚ_[2]) *
          ((-smoothingMoment 0 1) *
            (centralCoeffKernel ((j : ℤ) - (i : ℤ) - 1) : ℚ_[2]))) =
        (-smoothingMoment 0 1) * ((rowD P N r).coeff j : ℚ_[2]) := by
    rw [← hcontact, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hentrysum :
      (∑ i ∈ Finset.range (P.H N),
        ((rowP P N r).coeff i : ℚ_[2]) *
          ((momentRat i j : ℚ_[2]) + (4 * (q : ℚ_[2])) *
            (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]))) =
        paramSmoothingColumn P N r j + paramExceptionColumn P q N r j +
          (-smoothingMoment 0 1) * ((rowD P N r).coeff j : ℚ_[2]) := by
    simp_rw [smoothingMoment_discrepancies q, mul_add, Finset.sum_add_distrib]
    rw [hE, hB]
    rfl
  have hboundary : paramBoundaryColumn P N r j =
      (-smoothingMoment 0 1) * ((rowD P N r).coeff j : ℚ_[2]) -
        (3 / 2 : ℚ_[2]) *
          ∑ i ∈ Finset.range (P.H N),
            ((rowD P N r).coeff i : ℚ_[2]) * (zetaRat i j : ℚ_[2]) := by
    unfold paramBoundaryColumn
    calc
      _ = (-smoothingMoment 0 1) *
          (∑ i ∈ Finset.range (P.H N),
            ((rowD P N r).coeff i : ℚ_[2]) * (if i = j then 1 else 0)) -
          (3 / 2 : ℚ_[2]) *
            ∑ i ∈ Finset.range (P.H N),
              ((rowD P N r).coeff i : ℚ_[2]) * (zetaRat i j : ℚ_[2]) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [hdelta]
  have hrawcast : (rawEntryRat P q N r j : ℚ_[2]) =
      (∑ i ∈ Finset.range (P.H N),
        ((rowP P N r).coeff i : ℚ_[2]) *
          ((momentRat i j : ℚ_[2]) + (4 * (q : ℚ_[2])) *
            (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]))) -
        (3 / 2 : ℚ_[2]) *
          ∑ i ∈ Finset.range (P.H N),
            ((rowD P N r).coeff i : ℚ_[2]) * (zetaRat i j : ℚ_[2]) := by
    simp only [rawEntryRat, Rat.cast_sub, Rat.cast_mul, Rat.cast_sum,
      Rat.cast_add, Rat.cast_ofNat, Rat.cast_div, Rat.cast_intCast]
  rw [hrawcast, hentrysum, hboundary]
  ring

end
end CatalanMeasure.Parametric
