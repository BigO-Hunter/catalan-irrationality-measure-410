module
public import Submission.CatalanMeasure.Parametric.BaseResidues
public import Submission.OAI.NumberTheory.Catalan.Arithmetic.OddPrimeCentralZetaContraction
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem H_scale (P : Parameters) (N : ℕ) : P.H N = P.H 1 * N := by
  simp only [Parameters.H]
  rw [C_scale P N]
  simp only [Parameters.h, Nat.mul_one]
  ring

theorem raw_zero_digit_reduction (P : Parameters) {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (hj : j < P.H N) :
    (((p : ℚ) ^ 2 * rawEntryRat P 0 N r j).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * rawEntryRat P 0 N r j).num : ZMod p) /
        (((p : ℚ) ^ 2 * rawEntryRat P 0 N r j).den : ZMod p) =
          (∑ i ∈ Finset.range (P.H N), ((rowP P N r).coeff i : ZMod p) *
            (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
              (((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).num : ZMod p) /
                ((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).den : ZMod p))) -
            (3 / 2 : ZMod p) *
              ∑ i ∈ Finset.range (P.H N), ((rowD P N r).coeff i : ZMod p) *
                (if i % p = j % p then
                  ((zetaRat (i / p) (j / p)).num : ZMod p) /
                    ((zetaRat (i / p) (j / p)).den : ZMod p) else 0) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  let fM : ℕ → ℚ := fun i => ((rowP P N r).coeff i : ℚ) * ((p : ℚ) ^ 2 * momentRat i j)
  let fZ : ℕ → ℚ := fun i => ((rowD P N r).coeff i : ℚ) * ((p : ℚ) ^ 2 * zetaRat i j)
  let A : ℚ := ∑ i ∈ Finset.range (P.H N), fM i
  let B : ℚ := ∑ i ∈ Finset.range (P.H N), fZ i
  have hj2 : j < p ^ 2 := hj.trans hH
  have hM (i : ℕ) (hi : i ∈ Finset.range (P.H N)) :
      ((fM i).den : ZMod p) ≠ 0 ∧
        R (fM i) = ((rowP P N r).coeff i : ZMod p) *
          (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
            R (momentRatSigned (oddPrimeDigitRow p i j) (j / p)) := by
    have hd := momentRat_prime_digit_reduction hp2
      ((Finset.mem_range.mp hi).trans hH) hj2
    have hm := rational_residue_mul (a := ((rowP P N r).coeff i : ℚ)) (by simp) hd.1
    refine ⟨hm.1, ?_⟩
    have hmr : R (fM i) = ((rowP P N r).coeff i : ZMod p) *
        R ((p : ℚ) ^ 2 * momentRat i j) := by
      simpa [R, fM] using hm.2
    have hdr : R ((p : ℚ) ^ 2 * momentRat i j) =
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
          R (momentRatSigned (oddPrimeDigitRow p i j) (j / p)) := hd.2.2
    rw [hmr, hdr]
    ring
  have hZ (i : ℕ) (hi : i ∈ Finset.range (P.H N)) :
      ((fZ i).den : ZMod p) ≠ 0 ∧
        R (fZ i) = ((rowD P N r).coeff i : ZMod p) *
          (if i % p = j % p then R (zetaRat (i / p) (j / p)) else 0) := by
    have hd := zetaRat_prime_digit_reduction
      ((Finset.mem_range.mp hi).trans hH) hj2
    have hm := rational_residue_mul (a := ((rowD P N r).coeff i : ℚ)) (by simp) hd.1
    refine ⟨hm.1, ?_⟩
    have hmr : R (fZ i) = ((rowD P N r).coeff i : ZMod p) *
        R ((p : ℚ) ^ 2 * zetaRat i j) := by
      simpa [R, fZ] using hm.2
    have hdr : R ((p : ℚ) ^ 2 * zetaRat i j) =
        if i % p = j % p then R (zetaRat (i / p) (j / p)) else 0 := hd.2
    rw [hmr, hdr]
  have hA := rational_residue_sum (Finset.range (P.H N)) fM (fun i hi => (hM i hi).1)
  have hB := rational_residue_sum (Finset.range (P.H N)) fZ (fun i hi => (hZ i hi).1)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hlt : 2 < p := by have := hp.out.two_le; omega
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hlt) hdiv
  have h32 := nat_fraction_reduced_residue (p := p) 3 2 htwo
  have hBprod := rational_residue_mul h32.1 hB.1
  have hdiff := rational_residue_sub hA.1 hBprod.1
  have hAeq : A = (p : ℚ) ^ 2 *
      (∑ i ∈ Finset.range (P.H N), ((rowP P N r).coeff i : ℚ) * momentRat i j) := by
    dsimp only [A, fM]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hBeq : B = (p : ℚ) ^ 2 *
      (∑ i ∈ Finset.range (P.H N), ((rowD P N r).coeff i : ℚ) * zetaRat i j) := by
    dsimp only [B, fZ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsplit : (p : ℚ) ^ 2 * rawEntryRat P 0 N r j = A - (3 / 2 : ℚ) * B := by
    rw [rawEntryRat_zero, hAeq, hBeq]
    ring
  have hAres : R A =
      ∑ i ∈ Finset.range (P.H N), ((rowP P N r).coeff i : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
          R (momentRatSigned (oddPrimeDigitRow p i j) (j / p)) := by
    calc
      R A = ∑ i ∈ Finset.range (P.H N), R (fM i) := hA.2
      _ = _ := Finset.sum_congr rfl (fun i hi => (hM i hi).2)
  have hBres : R B =
      ∑ i ∈ Finset.range (P.H N), ((rowD P N r).coeff i : ZMod p) *
        (if i % p = j % p then R (zetaRat (i / p) (j / p)) else 0) := by
    calc
      R B = ∑ i ∈ Finset.range (P.H N), R (fZ i) := hB.2
      _ = _ := Finset.sum_congr rfl (fun i hi => (hZ i hi).2)
  have h32R : R (3 / 2 : ℚ) = (3 / 2 : ZMod p) := h32.2
  have hBprodR : R ((3 / 2 : ℚ) * B) = R (3 / 2 : ℚ) * R B := hBprod.2
  have hdiffR : R (A - (3 / 2 : ℚ) * B) = R A - R ((3 / 2 : ℚ) * B) := hdiff.2
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hdiff.1
  · change R ((p : ℚ) ^ 2 * rawEntryRat P 0 N r j) = _
    rw [hsplit, hdiffR, hBprodR, h32R, hAres, hBres]


theorem P_digit_contraction (P : Parameters) {p r0 : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hp2 : p ≠ 2) (hr : r0 < P.n0) (i ell : Fin p) (k : ℕ) :
    (∑ t ∈ Finset.range (P.H 1 * p), ((rowP P p (p * r0 + i.val)).coeff t : ZMod p) *
      (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell.val)) *
      palindromicRatResidue p
        (momentRatSigned (oddPrimeDigitRow p t (k * p + ell.val)) k)) =
    ∑ u ∈ Finset.range (P.H 1),
      (X * (rowP P p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
        oddPrimeWeight p).coeff ((u + 1) * p + ell.val) *
          palindromicRatResidue p (momentRat u k) := by
  let Ppoly : (ZMod p)[X] := (rowP P p (p * r0 + i.val)).map (Int.castRingHom (ZMod p))
  let Q : (ZMod p)[X] := X * Ppoly * oddPrimeWeight p
  have hcoeff : ∀ t, P.H 1 * p ≤ t → Ppoly.coeff t = 0 := by
    intro t ht
    simp only [Ppoly, coeff_map, ZModIntCast_apply,
      rowP_coeff_eq_zero_of_ge hAdm hp.out.pos (show P.H p ≤ t by rw [H_scale P p]; exact ht), Int.cast_zero]
  have h := oddPrime_P_coefficient_contraction (B := P.H 1) (k := k)
    hp.out.pos ell.isLt Ppoly hcoeff (fun v => palindromicRatResidue p (momentRatSigned v k))
  have hzero : Q.coeff ell.val = 0 :=
    actual_P_extraction_below P hAdm hp2 hr i ell
  have hshift :
      (∑ v ∈ Finset.range (P.H 1 + 1), Q.coeff (v * p + ell.val) *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) k)) =
      ∑ u ∈ Finset.range (P.H 1), Q.coeff ((u + 1) * p + ell.val) *
        palindromicRatResidue p (momentRat u k) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      momentRatSigned_natCast, zero_mul, zero_add, hzero, add_zero]
  have hh :
      (∑ t ∈ Finset.range (P.H 1 * p), ((rowP P p (p * r0 + i.val)).coeff t : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell.val)) *
        palindromicRatResidue p
          (momentRatSigned (oddPrimeDigitRow p t (k * p + ell.val)) k)) =
      ∑ v ∈ Finset.range (P.H 1 + 1), Q.coeff (v * p + ell.val) *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) k) := by
    simpa only [Ppoly, Q, coeff_map, ZModIntCast_apply] using h
  exact hh.trans hshift

theorem D_digit_contraction (P : Parameters) {p r0 : ℕ} [hp : Fact p.Prime]
    (i ell : Fin p) (k : ℕ) :
    (∑ t ∈ Finset.range (P.H 1 * p), ((rowD P p (p * r0 + i.val)).coeff t : ZMod p) *
      (if t % p = ell.val then palindromicRatResidue p (zetaRat (t / p) k) else 0)) =
    ∑ u ∈ Finset.range (P.H 1),
      ((rowD P p (p * r0 + i.val)).coeff (u * p + ell.val) : ZMod p) *
        palindromicRatResidue p (zetaRat u k) := by
  simpa only [mul_ite, mul_zero] using
    (oddPrime_block_residue_sum_gather (B := P.H 1) hp.out.pos ell.isLt
      (fun t => ((rowD P p (p * r0 + i.val)).coeff t : ZMod p))
      (fun u => palindromicRatResidue p (zetaRat u k)))


theorem rawCatalanCoeff_den (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (N r j : ℕ) :
    ((rawCatalanCoeffRat P N r j).den : ZMod p) ≠ 0 := by
  unfold rawCatalanCoeffRat
  apply (rational_residue_sum (p := p) (Finset.range (P.H N))
    (fun i => ((rowP P N r).coeff i : ℚ) * (4 * centralCoeffKernel ((i : ℤ) - (j : ℤ)))) ?_).1
  intro i hi
  have hkernel := centralCoeffKernel_odd_prime_den_ne_zero hp2 ((i : ℤ) - (j : ℤ))
  have hfour := rational_residue_mul (a := (4 : ℚ)) (by norm_num) hkernel
  exact (rational_residue_mul (a := ((rowP P N r).coeff i : ℚ)) (by simp) hfour.1).1

theorem scaledRawCatalanCoeff_zero (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0) (N r j : ℕ) :
    (((p : ℚ)^2 * z * rawCatalanCoeffRat P N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ)^2 * z * rawCatalanCoeffRat P N r j) = 0 := by
  have hz := rational_residue_mul (a := (p : ℚ)) (b := (p : ℚ) * z) (by simp) hzp
  have hf := rational_residue_mul hz.1 (rawCatalanCoeff_den P hp2 N r j)
  have he : (p : ℚ) * ((p : ℚ) * z) * rawCatalanCoeffRat P N r j =
      (p : ℚ)^2 * z * rawCatalanCoeffRat P N r j := by ring
  rw [← he]
  refine ⟨hf.1, ?_⟩
  unfold palindromicRatResidue
  rw [hf.2, hz.2]
  simp

theorem scaledRawEntry_transfer {P : Parameters} {p N r j : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (hj : j < P.H N)
    (z : ℚ) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat P z N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat P z N r j) =
        palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat P 0 N r j) := by
  have hbase := (raw_zero_digit_reduction P (r := r) hp2 hH hj).1
  have hterm := scaledRawCatalanCoeff_zero P hp2 z hzp N r j
  have he : (p : ℚ)^2 * rawEntryRat P z N r j =
      (p : ℚ)^2 * rawEntryRat P 0 N r j + (p : ℚ)^2 * z * rawCatalanCoeffRat P N r j := by
    rw [rawEntryRat_affine]
    ring
  rw [he]
  refine ⟨(rational_residue_add hbase hterm.1).1, ?_⟩
  rw [palindromicRatResidue_add hbase hterm.1, hterm.2, add_zero]

theorem raw_block_reduction (P : Parameters) {p r0 k : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hp2 : p ≠ 2) (hpH : P.H 1 < p) (hr : r0 < P.n0)
    (i ell : Fin p) (hk : k < P.H 1) (z : ℚ)
    (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat P z p (p * r0 + i.val) (k * p + ell.val)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p
        ((p : ℚ) ^ 2 * rawEntryRat P z p (p * r0 + i.val) (k * p + ell.val)) =
        extractedRawContraction P p r0 i ell k := by
  have hH : P.H p < p ^ 2 := by rw [H_scale]; have := hp.out.pos; nlinarith
  have hbound : (k + 1) * p ≤ P.H 1 * p := Nat.mul_le_mul_right p hk
  have hj : k * p + ell.val < P.H p := by rw [H_scale]; have := ell.isLt; nlinarith
  have hquot : (k * p + ell.val) / p = k := by
    rw [Nat.mul_comm k p, Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt ell.isLt, add_zero]
  have hmod : (k * p + ell.val) % p = ell.val := by
    simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt ell.isLt]
  have hraw := raw_zero_digit_reduction P (p := p) (r := p * r0 + i.val) hp2 hH hj
  have htransfer := scaledRawEntry_transfer (r := p * r0 + i.val) hp2 hH hj z hzp
  refine ⟨htransfer.1, ?_⟩
  rw [htransfer.2]
  have hres :
      palindromicRatResidue p
        ((p : ℚ) ^ 2 * rawEntryRat P 0 p (p * r0 + i.val) (k * p + ell.val)) =
      (∑ t ∈ Finset.range (P.H 1 * p), ((rowP P p (p * r0 + i.val)).coeff t : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell.val)) *
        palindromicRatResidue p (momentRatSigned (oddPrimeDigitRow p t (k * p + ell.val)) k)) -
      (3 / 2 : ZMod p) *
        ∑ t ∈ Finset.range (P.H 1 * p), ((rowD P p (p * r0 + i.val)).coeff t : ZMod p) *
          (if t % p = ell.val then palindromicRatResidue p (zetaRat (t / p) k) else 0) := by
    simpa only [H_scale P p, palindromicRatResidue, hquot, hmod] using hraw.2
  rw [hres, P_digit_contraction P hAdm hp2 hr i ell k, D_digit_contraction P i ell k]
  rfl

end
end CatalanMeasure.Parametric
