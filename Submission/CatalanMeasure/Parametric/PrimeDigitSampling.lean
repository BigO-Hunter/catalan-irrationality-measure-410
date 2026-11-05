module
public import Submission.CatalanMeasure.Parametric.SparseRowIdentities
public import Submission.CatalanMeasure.Parametric.SparseDigitResidues
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

def primeDigitSample {R : Type*} [Semiring R] (H p ell : ℕ) (f : ℕ → R) (Q : R[X]) : R :=
  ∑ v ∈ Finset.range H, Q.coeff (v*p+ell)*f v

theorem primeDigitSample_add {R : Type*} [Semiring R] (H p ell : ℕ)
    (f : ℕ → R) (Q S : R[X]) :
    primeDigitSample H p ell f (Q+S)=primeDigitSample H p ell f Q+primeDigitSample H p ell f S := by
  simp [primeDigitSample,add_mul,Finset.sum_add_distrib]

theorem primeDigitSample_sub {R : Type*} [Ring R] (H p ell : ℕ)
    (f : ℕ → R) (Q S : R[X]) :
    primeDigitSample H p ell f (Q-S)=primeDigitSample H p ell f Q-primeDigitSample H p ell f S := by
  simp [primeDigitSample,sub_mul,Finset.sum_sub_distrib]

theorem primeDigitSample_C_mul {R : Type*} [Semiring R] (H p ell : ℕ)
    (f : ℕ → R) (c : R) (Q : R[X]) :
    primeDigitSample H p ell f (C c*Q)=c*primeDigitSample H p ell f Q := by
  simp only [primeDigitSample,coeff_C_mul,mul_assoc,Finset.mul_sum]

theorem primeDigitSample_two_mul {R : Type*} [Semiring R] (H p ell : ℕ)
    (f : ℕ → R) (Q : R[X]) :
    primeDigitSample H p ell f (2*Q)=2*primeDigitSample H p ell f Q := by
  simpa only [C_ofNat] using primeDigitSample_C_mul H p ell f (2:R) Q

theorem primeDigitSample_single {R : Type*} [Semiring R] {H p ell a : ℕ}
    (hp : 0<p) (hell : ell<p) (ha : a<H) (f : ℕ → R) (Q : R[X])
    (hsupp : ∀ i, Q.coeff i≠0 → a*p ≤ i ∧ i<(a+1)*p) :
    primeDigitSample H p ell f Q=Q.coeff (a*p+ell)*f a := by
  unfold primeDigitSample
  apply Finset.sum_eq_single a
  · intro v hv hva
    have hz : Q.coeff (v*p+ell)=0 := by
      by_contra h
      have hs :=hsupp _ h
      have hvnot : v≠a :=hva
      rcases lt_or_gt_of_ne hvnot with hlt | hgt
      · have hm :=Nat.mul_le_mul_right p (show v+1 ≤ a by omega)
        nlinarith
      · have hm :=Nat.mul_le_mul_right p (show a+1 ≤ v by omega)
        nlinarith
    rw [hz,zero_mul]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr ha)).elim

theorem primeDigitSample_shift_single {R : Type*} [Semiring R] {H p ell a t : ℕ}
    (hp : 0<p) (hell : ell<p) (ha : a+t<H) (f : ℕ → R) (Q : R[X])
    (hsupp : ∀ i, Q.coeff i≠0 → a*p ≤ i ∧ i<(a+1)*p) :
    primeDigitSample H p ell f (X^(t*p)*Q)=Q.coeff (a*p+ell)*f (a+t) := by
  have hshift : ∀ i, (X^(t*p)*Q).coeff i≠0 →
      (a+t)*p ≤ i ∧ i<(a+t+1)*p := by
    intro i hi
    rw [coeff_X_pow_mul'] at hi
    split_ifs at hi with hit
    · have hh :=hsupp (i-t*p) hi
      constructor <;> nlinarith [Nat.sub_add_cancel hit]
    · exact (hi rfl).elim
  rw [primeDigitSample_single hp hell ha f _ hshift,coeff_X_pow_mul']
  rw [if_pos (by nlinarith : t*p ≤ (a+t)*p+ell)]
  have hidx : (a+t)*p+ell-t*p=a*p+ell :=by rw [Nat.add_mul]; omega
  rw [hidx]

def primeDigitPair (H p j : ℕ) [Fact p.Prime] (F G : (ZMod p)[X]) : ZMod p :=
  primeDigitSample (H+1) p (j%p)
    (fun v => palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) (j/p)))
    (X*oddPrimeWeight p*F) -
  (3/2:ZMod p)*primeDigitSample H p (j%p)
    (fun v => palindromicRatResidue p (zetaRat v (j/p))) G

theorem primeDigitPair_sub (H p j : ℕ) [Fact p.Prime] (F G F' G' : (ZMod p)[X]) :
    primeDigitPair H p j (F-F') (G-G')=
      primeDigitPair H p j F G-primeDigitPair H p j F' G' := by
  unfold primeDigitPair
  rw [mul_sub,primeDigitSample_sub,primeDigitSample_sub]
  ring

end
end CatalanMeasure.Parametric
