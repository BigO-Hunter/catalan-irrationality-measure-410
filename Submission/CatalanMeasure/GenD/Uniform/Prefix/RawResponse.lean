module
public import Submission.CatalanMeasure.GenD.RankU
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponseReflect
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset CatalanMeasure.Parametric OAI.InternalCatalan
/-- Digit samples in the common reversal frame, with exact integer indices. -/
theorem primeDigitSample_intrinsic {R : Type*} [CommRing R]
    (H p ell D : ℕ) (f : ℕ→R) (Q : R[X]) (hQ : Q.natDegree≤D) :
    primeDigitSample H p ell f Q =
      ∑ v ∈ range H,intrinsicCoeff (reflect D Q) ((D:ℤ)-((v*p+ell:ℕ):ℤ))*f v := by
  unfold primeDigitSample
  exact Finset.sum_congr rfl (fun v _ => by rw [reflect_coeff_intrinsic Q D (v*p+ell) hQ])

#print axioms primeDigitSample_intrinsic
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

def intrinsicT (P : Parameters) (N p : ℕ) [Fact p.Prime]
    (c : Fin (P.n N)→ZMod p) : (ZMod p)[X] :=
  ∑ r,C (c r)*Chebyshev.T (ZMod p) ((r.val:ℤ)-P.g N)

def intrinsicU (P : Parameters) (N p : ℕ) [Fact p.Prime]
    (c : Fin (P.n N)→ZMod p) : (ZMod p)[X] :=
  ∑ r,C (c r)*Chebyshev.U (ZMod p) ((r.val:ℤ)-P.g N-1)

theorem reflect_uS (c : Fin (P.n N)→Fp) :
    reflect (P.C N-1) (uS p (P.C N) (P.g N) (P.n N) c)=intrinsicT P N p c := by
  simp only [uS,combLin_apply,reflect_combination,uSv,reflect_reflect,intrinsicT]

theorem reflect_uU (c : Fin (P.n N)→Fp) :
    reflect (P.C N-1) (uU p (P.C N) (P.g N) (P.n N) c)=intrinsicU P N p c := by
  simp only [uU,combLin_apply,reflect_combination,uUv,reflect_reflect,intrinsicU]

theorem physical_common_reversal (hP : Admissible P) (hN : 0<N) (hp2 : p≠2)
    (c : Fin (P.n N)→Fp) :
    (reflect (P.H N-1) ((1-X)^P.h N*uS p (P.C N) (P.g N) (P.n N) c)=
      (X-1)^P.h N*intrinsicT P N p c) ∧
    (reflect (P.H N-1) ((1-X)^P.h N*uU p (P.C N) (P.g N) (P.n N) c)=
      (X-1)^P.h N*intrinsicU P N p c) := by
  have hg := two_g_lt_n hP hN
  have hNC : P.n N+P.g N≤P.C N := by
    simp only [Parameters.C,Parameters.L]
    omega
  have hC : 0<P.C N := by omega
  have he : P.H N-1=P.h N+(P.C N-1) := by simp only [Parameters.H];omega
  have hh : ((1-X : Fp[X])^P.h N).natDegree≤P.h N := one_sub_X_pow_natDegree_le _
  constructor
  · rw [he,reflect_mul _ _ hh (uS_natDegree_le hp2 hg hNC c),reflect_one_sub_X_pow,reflect_uS]
  · rw [he,reflect_mul _ _ hh (uU_natDegree_le hp2 hg hNC c),reflect_one_sub_X_pow,reflect_uU]

theorem weight_common_reversal (hp2 : p≠2) :
    reflect p (X*oddPrimeWeight p : Fp[X])=(X^2-1)^((p-1)/2) := by
  have ho := odd_of_ne_two hp2
  have he : p=1+2*((p-1)/2) := by omega
  have hw : ((1-X^2 : Fp[X])^((p-1)/2)).natDegree≤2*((p-1)/2) := by
    apply natDegree_pow_le.trans
    have h : (1-X^2 : Fp[X]).natDegree≤2 := by compute_degree
    nlinarith [Nat.mul_le_mul_left ((p-1)/2) h]
  have hr := reflect_mul (X : Fp[X]) ((1-X^2)^((p-1)/2))
    (show (X : Fp[X]).natDegree≤1 by simp) hw
  rw [←he,reflect_one_X,reflect_one_sub_X_sq_pow,one_mul] at hr
  exact hr
/-- Intrinsic formula (R), with arbitrary actual physical row coefficients.
All negative/beyond-support indices vanish in the common H-1 reversal frame. -/
theorem raw_response_intrinsic (hP : Admissible P) (hN : 0<N) (hp2 : p≠2)
    (hH : P.H N<p^2) {j : ℕ} (hj : j<P.H N) (c : Fin (P.n N)→Fp) :
    uResp P N p j c =
    (∑ v ∈ range (P.H N+1),
      intrinsicCoeff ((X-1)^P.h N*(X^2-1)^((p-1)/2)*intrinsicT P N p c)
        ((P.H N:ℤ)-1-(j%p:ℕ)-((v:ℤ)-1)*p)*
        palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) (j/p))) -
    (3/2:Fp)*(∑ v ∈ range (P.H N),
      intrinsicCoeff ((X-1)^P.h N*intrinsicU P N p c)
        ((P.H N:ℤ)-1-(j%p:ℕ)-(v:ℤ)*p)*
        palindromicRatResidue p (zetaRat v (j/p))) := by
  have hg := two_g_lt_n hP hN
  have hNC : P.n N+P.g N≤P.C N := by simp only [Parameters.C,Parameters.L];omega
  have hC : 0<P.C N := by omega
  have hpos : 0<P.H N := by omega
  have hp0 : 0<p := (Fact.out:p.Prime).pos
  have hcH : ((P.H N-1:ℕ):ℤ)=(P.H N:ℤ)-1 := by omega
  have hcHP : ((P.H N+p-1:ℕ):ℤ)=(P.H N:ℤ)+p-1 := by omega
  have hSF : ((1-X : Fp[X])^P.h N*uS p (P.C N) (P.g N) (P.n N) c).natDegree≤P.H N-1 := by
    apply natDegree_mul_le.trans
    have h1 := one_sub_X_pow_natDegree_le (p:=p) (P.h N)
    have h2 := uS_natDegree_le hp2 hg hNC c
    simp only [Parameters.H]
    omega
  have hUF : ((1-X : Fp[X])^P.h N*uU p (P.C N) (P.g N) (P.n N) c).natDegree≤P.H N-1 := by
    apply natDegree_mul_le.trans
    have h1 := one_sub_X_pow_natDegree_le (p:=p) (P.h N)
    have h2 := uU_natDegree_le hp2 hg hNC c
    simp only [Parameters.H]
    omega
  have hw : (X*oddPrimeWeight p : Fp[X]).natDegree≤p := by
    apply natDegree_mul_le.trans
    have ho := odd_of_ne_two hp2
    have hd : (oddPrimeWeight p).natDegree≤((p-1)/2)*2 := by
      exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ (by compute_degree))
    simp only [natDegree_X]
    omega
  have hprod : (X*oddPrimeWeight p*((1-X)^P.h N*uS p (P.C N) (P.g N) (P.n N) c)).natDegree≤P.H N+p-1 := by
    apply natDegree_mul_le.trans
    omega
  have hrev := physical_common_reversal hP hN hp2 c
  have hrevprod : reflect (P.H N+p-1)
      (X*oddPrimeWeight p*((1-X)^P.h N*uS p (P.C N) (P.g N) (P.n N) c))=
      (X-1)^P.h N*(X^2-1)^((p-1)/2)*intrinsicT P N p c := by
    rw [show P.H N+p-1=p+(P.H N-1) by omega,reflect_mul _ _ hw hSF,
      weight_common_reversal hp2,hrev.1]
    ring
  rw [uResp_eq hP hN hp2 hH hj c]
  unfold primeDigitPair
  rw [primeDigitSample_intrinsic _ _ _ (P.H N+p-1) _ _ hprod,
    primeDigitSample_intrinsic _ _ _ (P.H N-1) _ _ hUF,hrevprod,hrev.2]
  congr 1
  · apply Finset.sum_congr rfl
    intro v _
    congr 2
    rw [hcHP]
    push_cast
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro v _
    congr 2
    rw [hcH]
    push_cast
    ring
#print axioms raw_response_intrinsic
end
end CatalanMeasure.GenD.Uniform.Prefix




