module
public import Submission.CatalanMeasure.Parametric.LowerPrimePool
public import Submission.OAI.NumberTheory.Catalan.Arithmetic.FinitePlaceAssembly
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section
theorem param_rowP_moment_central_reduction {P : Parameters} {p N r j : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ P.H N) (hH : P.H N ≤ 2 * p)
    (hjlo : P.H N - p ≤ j) (hj : j < p) :
    (((p : ℚ) * (∑ t ∈ Finset.range (P.H N),
      ((rowP P N r).coeff t : ℚ) * momentRat t j)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * (∑ t ∈ Finset.range (P.H N),
        ((rowP P N r).coeff t : ℚ) * momentRat t j)) =
        -(∑ ell ∈ Finset.range (P.H N - p),
          (2 * (X * ((rowP P N r).map (Int.castRingHom (ZMod p))) * oddPrimeWeight p).coeff (2*p+ell)) / ((j - ell : ℕ) : ZMod p)) := by
  let f : ℕ → ℚ := fun t => ((rowP P N r).coeff t : ℚ) * ((p : ℚ) * momentRat t j)
  let c : ℕ → ℕ → ZMod p := fun t ell =>
    if p + ell ≤ t then (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - t)) /
      ((j - ell : ℕ) : ZMod p) else 0
  have hterm (t : ℕ) (ht : t ∈ Finset.range (P.H N)) :
      ((f t).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (f t) = ((rowP P N r).coeff t : ZMod p) *
        (-(∑ ell ∈ Finset.range (P.H N - p), c t ell)) := by
    have ht' := Finset.mem_range.mp ht
    have hm := momentRat_central_reduction hp2 hj (show t < p + j by omega)
    have hprod := rational_residue_mul (p := p) (a := ((rowP P N r).coeff t : ℚ))
      (by simp) hm.1
    have htrim := oddPrime_central_strip_range hp.out.pos hpH ht' hjlo
      (fun ell => (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - t)) /
        ((j - ell : ℕ) : ZMod p))
    refine ⟨hprod.1, ?_⟩
    change palindromicRatResidue p
      (((rowP P N r).coeff t : ℚ) * ((p : ℚ) * momentRat t j)) = _
    rw [palindromicRatResidue_mul (by simp) hm.1, palindromicRatResidue_intCast,
      hm.2, htrim]
  have hs := rational_residue_sum (Finset.range (P.H N)) f (fun t ht => (hterm t ht).1)
  have hscale : (p : ℚ) * (∑ t ∈ Finset.range (P.H N),
      ((rowP P N r).coeff t : ℚ) * momentRat t j) = ∑ t ∈ Finset.range (P.H N), f t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [f]
    ring
  let F : (ZMod p)[X] := (rowP P N r).map (Int.castRingHom (ZMod p))
  have hP : ∀ t, P.H N ≤ t → F.coeff t = 0 := by
    intro t ht
    simp only [F, coeff_map, rowP_coeff_eq_zero_of_ge hAdm hN ht, map_zero]
  have hcast (a : ℤ) : (Int.castRingHom (ZMod p)) a = (a : ZMod p) := rfl
  have hcoefficient (ell : ℕ) :
      (∑ t ∈ Finset.range (P.H N), ((rowP P N r).coeff t : ZMod p) * c t ell) =
        (2 * (X * ((rowP P N r).map (Int.castRingHom (ZMod p))) * oddPrimeWeight p).coeff (2*p+ell)) / ((j - ell : ℕ) : ZMod p) := by
    have hcoef := oddPrime_central_P_coefficient (ell := ell) hp.out.pos hH F hP
    have hcoef' :
        (∑ t ∈ Finset.range (P.H N), ((rowP P N r).coeff t : ZMod p) *
          (if p + ell ≤ t then 2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - t) else 0)) =
          2 * (X * ((rowP P N r).map (Int.castRingHom (ZMod p))) * oddPrimeWeight p).coeff (2*p+ell) := by
      simpa only [F, coeff_map, hcast] using hcoef
    rw [← hcoef']
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [c]
    split_ifs <;> ring
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hs.1
  · rw [hscale]
    calc
      palindromicRatResidue p (∑ t ∈ Finset.range (P.H N), f t) =
          ∑ t ∈ Finset.range (P.H N), palindromicRatResidue p (f t) := hs.2
      _ = ∑ t ∈ Finset.range (P.H N), ((rowP P N r).coeff t : ZMod p) *
          (-(∑ ell ∈ Finset.range (P.H N - p), c t ell)) :=
        Finset.sum_congr rfl (fun t ht => (hterm t ht).2)
      _ = -(∑ ell ∈ Finset.range (P.H N - p), ∑ t ∈ Finset.range (P.H N),
          ((rowP P N r).coeff t : ZMod p) * c t ell) := by
        simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
        rw [Finset.sum_comm]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro ell hell
        exact hcoefficient ell

theorem param_rowD_zeta_central_coeff {P : Parameters} {p N r j : ℕ} [hp : Fact p.Prime]
    (_hN : 0 < N) (hpH : p ≤ P.H N) (_hH : P.H N ≤ 2 * p)
    (hJ : P.H N - p ≤ j) (hj : j < p) :
    (((p : ℚ) *
      (∑ i ∈ Finset.range (P.H N), ((rowD P N r).coeff i : ℚ) * zetaRat i j)).den :
        ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) *
        (∑ i ∈ Finset.range (P.H N), ((rowD P N r).coeff i : ℚ) * zetaRat i j)) =
          -(∑ ell ∈ Finset.range (P.H N - p),
            ((rowD P N r).coeff (p + ell) : ZMod p) / ((j - ell : ℕ) : ZMod p)) := by
  let f : ℕ → ℚ := fun i => ((rowD P N r).coeff i : ℚ) * ((p : ℚ) * zetaRat i j)
  have hlow (i : ℕ) (hi : i < p) :
      ((f i).den : ZMod p) ≠ 0 ∧ palindromicRatResidue p (f i) = 0 := by
    have hzeta := zetaRat_central_low_reduction hi hj
    have hmul := rational_residue_mul (a := ((rowD P N r).coeff i : ℚ))
      (by simp) hzeta.1
    refine ⟨hmul.1, ?_⟩
    change palindromicRatResidue p
      (((rowD P N r).coeff i : ℚ) * ((p : ℚ) * zetaRat i j)) = 0
    rw [palindromicRatResidue_mul (by simp) hzeta.1, hzeta.2, mul_zero]
  have hhigh (ell : ℕ) (hell : ell < P.H N - p) :
      ((f (p + ell)).den : ZMod p) ≠ 0 ∧
        palindromicRatResidue p (f (p + ell)) =
          -(((rowD P N r).coeff (p + ell) : ZMod p) / ((j - ell : ℕ) : ZMod p)) := by
    have hellj : ell < j := hell.trans_le hJ
    have hzeta := zetaRat_central_high_reduction (p := p) hellj hj
    have hmul := rational_residue_mul (a := ((rowD P N r).coeff (p + ell) : ℚ))
      (by simp) hzeta.1
    have hden : (ell : ZMod p) - (j : ZMod p) = -((j - ell : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (Nat.le_of_lt hellj)]
      ring
    refine ⟨hmul.1, ?_⟩
    change palindromicRatResidue p
      (((rowD P N r).coeff (p + ell) : ℚ) * ((p : ℚ) * zetaRat (p + ell) j)) = _
    rw [palindromicRatResidue_mul (by simp) hzeta.1,
      palindromicRatResidue_intCast, hzeta.2, hden, div_neg]
    ring
  have hden (i : ℕ) (hi : i ∈ Finset.range (P.H N)) : ((f i).den : ZMod p) ≠ 0 := by
    have hiH := Finset.mem_range.mp hi
    by_cases hip : i < p
    · exact (hlow i hip).1
    · have heq : p + (i - p) = i := by omega
      have h := (hhigh (i - p) (by omega)).1
      simpa only [heq] using h
  have hsum := rational_residue_sum (Finset.range (P.H N)) f hden
  have hscale : (p : ℚ) *
      (∑ i ∈ Finset.range (P.H N), ((rowD P N r).coeff i : ℚ) * zetaRat i j) =
        ∑ i ∈ Finset.range (P.H N), f i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f]
    ring
  have hsplit :
      (∑ i ∈ Finset.range (P.H N), palindromicRatResidue p (f i)) =
        (∑ i ∈ Finset.range p, palindromicRatResidue p (f i)) +
        ∑ ell ∈ Finset.range (P.H N - p), palindromicRatResidue p (f (p + ell)) := by
    conv_lhs => rw [show P.H N = p + (P.H N - p) by omega, Finset.sum_range_add]
  have hlowSum : (∑ i ∈ Finset.range p, palindromicRatResidue p (f i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact (hlow i (Finset.mem_range.mp hi)).2
  have hhighSum :
      (∑ ell ∈ Finset.range (P.H N - p), palindromicRatResidue p (f (p + ell))) =
        -(∑ ell ∈ Finset.range (P.H N - p),
          ((rowD P N r).coeff (p + ell) : ZMod p) / ((j - ell : ℕ) : ZMod p)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun ell hell => (hhigh ell (Finset.mem_range.mp hell)).2)
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hsum.1
  · rw [hscale]
    change (( (∑ i ∈ Finset.range (P.H N), f i).num : ZMod p) /
      ((∑ i ∈ Finset.range (P.H N), f i).den : ZMod p)) = _
    rw [hsum.2]
    change (∑ i ∈ Finset.range (P.H N), palindromicRatResidue p (f i)) = _
    rw [hsplit, hlowSum, zero_add, hhighSum]

theorem param_rowD_zeta_central_reduction {P : Parameters} {p N r j : ℕ} [Fact p.Prime]
    (hN : 0<N) (hpH : p ≤ P.H N) (hH : P.H N ≤ 2*p) (hjlo : P.H N-p ≤ j) (hj : j<p) :
    (((p:ℚ)*(∑ i ∈ Finset.range (P.H N),((rowD P N r).coeff i:ℚ)*zetaRat i j)).den : ZMod p)≠0 ∧
      palindromicRatResidue p ((p:ℚ)*(∑ i ∈ Finset.range (P.H N),((rowD P N r).coeff i:ℚ)*zetaRat i j))=
      -(∑ ell ∈ Finset.range (P.H N-p),((rowD P N r).map (Int.castRingHom (ZMod p))).coeff (p+ell)/((j-ell:ℕ):ZMod p)) :=by
  have hcast (a : ℤ) : (Int.castRingHom (ZMod p)) a=(a:ZMod p) :=rfl
  simpa only [coeff_map,hcast] using param_rowD_zeta_central_coeff (r :=r) hN hpH hH hjlo hj
def paramLeadingV (P : Parameters) (p N r ell : ℕ) [Fact p.Prime] : ZMod p :=
  2 * (X*((rowP P N r).map (Int.castRingHom (ZMod p)))*oddPrimeWeight p).coeff (2*p+ell) -
    (3 / 2 : ZMod p) * ((rowD P N r).map (Int.castRingHom (ZMod p))).coeff (p+ell)

theorem paramRawCatalanTerm_prime_reduction {p : ℕ} [Fact p.Prime]
    (P : Parameters) (hp2 : p ≠ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) (N r j : ℕ) :
    (((p : ℚ) * z * rawCatalanCoeffRat P N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * z * rawCatalanCoeffRat P N r j) = 0 := by
  have hpz := rational_residue_mul (p := p) (a := (p : ℚ)) (by simp) hz
  have hfull := rational_residue_mul hpz.1
    (rawCatalanCoeff_den P hp2 N r j)
  refine ⟨hfull.1, ?_⟩
  change (((p : ℚ) * z * rawCatalanCoeffRat P N r j).num : ZMod p) /
    (((p : ℚ) * z * rawCatalanCoeffRat P N r j).den : ZMod p) = 0
  rw [hfull.2, hpz.2]
  simp

theorem paramRawEntry_central_layer {P : Parameters} {p N r j : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ P.H N) (hH : P.H N ≤ 2 * p)
    (hjlo : P.H N - p ≤ j) (hj : j < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) * rawEntryRat P z N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * rawEntryRat P z N r j) =
        -(∑ ell ∈ Finset.range (P.H N - p),
          paramLeadingV P p N r ell / ((j - ell : ℕ) : ZMod p)) := by
  let A : ℚ := (p : ℚ) * (∑ t ∈ Finset.range (P.H N),
    ((rowP P N r).coeff t : ℚ) * momentRat t j)
  let B : ℚ := (p : ℚ) * (∑ t ∈ Finset.range (P.H N),
    ((rowD P N r).coeff t : ℚ) * zetaRat t j)
  let C : ℚ := (p : ℚ) * z * rawCatalanCoeffRat P N r j
  have hA := param_rowP_moment_central_reduction (r := r) hAdm hp2 hN hpH hH hjlo hj
  have hB := param_rowD_zeta_central_reduction (r := r) hN hpH hH hjlo hj
  have hC := paramRawCatalanTerm_prime_reduction P hp2 z hz N r j
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpgt : 2 < p := by have := hp.out.two_le; omega
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hpgt) hdiv
  have h32 := nat_fraction_reduced_residue (p := p) 3 2 htwo
  have hBprod := rational_residue_mul h32.1 hB.1
  have hdiff := rational_residue_sub hA.1 hBprod.1
  have hsum := rational_residue_add hdiff.1 hC.1
  have hsplit : (p : ℚ) * rawEntryRat P z N r j = A - (3 / 2 : ℚ) * B + C := by
    dsimp only [A, B, C]
    rw [rawEntryRat_affine, rawEntryRat_zero]
    ring
  have hAR : palindromicRatResidue p A =
      -(∑ ell ∈ Finset.range (P.H N - p),
        (2 * (X*((rowP P N r).map (Int.castRingHom (ZMod p)))*oddPrimeWeight p).coeff (2*p+ell)) / ((j - ell : ℕ) : ZMod p)) := hA.2
  have hBR : palindromicRatResidue p B =
      -(∑ ell ∈ Finset.range (P.H N - p),
        ((rowD P N r).map (Int.castRingHom (ZMod p))).coeff (p+ell) / ((j - ell : ℕ) : ZMod p)) := hB.2
  have hCR : palindromicRatResidue p C = 0 := hC.2
  have h32R : palindromicRatResidue p (3 / 2 : ℚ) = (3 / 2 : ZMod p) := h32.2
  have hsumR : palindromicRatResidue p (A - (3 / 2 : ℚ) * B + C) =
      palindromicRatResidue p (A - (3 / 2 : ℚ) * B) + palindromicRatResidue p C := hsum.2
  have hdiffR : palindromicRatResidue p (A - (3 / 2 : ℚ) * B) =
      palindromicRatResidue p A - palindromicRatResidue p ((3 / 2 : ℚ) * B) := hdiff.2
  have hprodR : palindromicRatResidue p ((3 / 2 : ℚ) * B) =
      palindromicRatResidue p (3 / 2 : ℚ) * palindromicRatResidue p B := hBprod.2
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hsum.1
  · rw [hsplit, hsumR, hdiffR, hprodR, hAR, hBR, hCR, h32R, add_zero]
    simp only [paramLeadingV, sub_div, Finset.sum_sub_distrib,
      mul_div_assoc, ← Finset.mul_sum]
    ring

end
end CatalanMeasure.Parametric
