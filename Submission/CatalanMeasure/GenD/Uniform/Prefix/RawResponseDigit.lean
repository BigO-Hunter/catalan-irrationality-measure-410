module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponseReflect
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset
variable {R : Type*} [CommRing R]

/-- Exact digit block multiplication: only one small-polynomial coefficient can
contribute to a fixed residue; no source or response flag is assumed. -/
theorem coeff_digit_product (A F : R[X]) (p e S : ℕ) (hp : 0<p)
    (he : e<p) (hF : F.degree<p) :
    (A.comp (X^p)*F).coeff (e+S*p)=A.coeff S*F.coeff e := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp only [add_comp,add_mul,coeff_add,hA,hB]
  | monomial n a =>
    rw [monomial_comp,←pow_mul,mul_assoc,coeff_C_mul,coeff_X_pow_mul',coeff_monomial]
    by_cases hn : n=S
    · subst n
      rw [if_pos (by nlinarith : p*S≤e+S*p),if_pos rfl]
      congr 1
      congr 1
      rw [Nat.mul_comm p S,Nat.add_sub_cancel]
    · rw [if_neg hn]
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · have hle : p*n≤e+S*p := by nlinarith [Nat.mul_le_mul_right p hlt.le]
        rw [if_pos hle]
        have hidx : p≤e+S*p-p*n := by
          apply Nat.le_sub_of_add_le
          nlinarith [Nat.mul_le_mul_right p (show n+1≤S by omega)]
        rw [coeff_eq_zero_of_degree_lt (hF.trans_le (by exact_mod_cast hidx)),mul_zero,zero_mul]
      · have hnot : ¬p*n≤e+S*p := by nlinarith [Nat.mul_le_mul_right p (show S+1≤n by omega)]
        rw [if_neg hnot,mul_zero,zero_mul]

/-- Signed quotient form, including every negative outside coefficient. -/
theorem intrinsicCoeff_digit_product (A F : R[X]) (p e : ℕ) (S : ℤ)
    (hp : 0<p) (he : e<p) (hF : F.degree<p) :
    intrinsicCoeff (A.comp (X^p)*F) ((e:ℤ)+S*p)=intrinsicCoeff A S*F.coeff e := by
  by_cases hs : 0≤S
  · have hS : S=(S.toNat:ℤ) := (Int.toNat_of_nonneg hs).symm
    rw [hS]
    have hi : (e:ℤ)+(S.toNat:ℤ)*p=((e+S.toNat*p:ℕ):ℤ) := by push_cast;ring
    rw [hi,intrinsicCoeff_nat,intrinsicCoeff_nat]
    exact coeff_digit_product A F p e S.toNat hp he hF
  · have hidx : (e:ℤ)+S*p<0 := by
      have hs1 : S≤-1 := by omega
      nlinarith
    simp only [intrinsicCoeff,if_neg hs,if_neg (not_le.mpr hidx),zero_mul]

/-- The E coefficient is the genuine first difference of the quotient factor. -/
theorem intrinsicCoeff_split_product (A F E : R[X]) (p e : ℕ) (S : ℤ)
    (hp : 0<p) (he : e<p) (hF : F.degree<p) (hE : E.degree<p) :
    intrinsicCoeff (A.comp (X^p)*(F+(X^p-1)*E)) ((e:ℤ)+S*p)=
      intrinsicCoeff A S*F.coeff e+intrinsicCoeff (A*(X-1)) S*E.coeff e := by
  have hid : A.comp (X^p)*(F+(X^p-1)*E)=
      A.comp (X^p)*F+(A*(X-1)).comp (X^p)*E := by
    simp only [mul_comp,sub_comp,X_comp,one_comp]
    ring
  rw [hid]
  have hadd : ∀ B C : R[X],∀ i:ℤ,intrinsicCoeff (B+C) i=intrinsicCoeff B i+intrinsicCoeff C i := by
    intro B C i
    by_cases hi : 0≤i <;> simp [intrinsicCoeff,hi,coeff_add]
  rw [hadd,intrinsicCoeff_digit_product A F p e S hp he hF,
    intrinsicCoeff_digit_product (A*(X-1)) E p e S hp he hE]

/-- Finite source covector from the individual moment summands. -/
def digitPhi (H : ℕ) (S : ℤ) (M Z : ℕ→R) (a b : R[X]) (c : R) : R :=
  (∑ v∈range (H+1),intrinsicCoeff a (S+1-v)*M v)-
    c*(∑ v∈range H,intrinsicCoeff b (S-v)*Z v)

theorem digit_response_contraction (H p e : ℕ) (S : ℤ) (M Z : ℕ→R)
    (a b F E : R[X]) (c : R) (hp : 0<p) (he : e<p)
    (hF : F.degree<p) (hE : E.degree<p) :
    ((∑ v∈range (H+1),intrinsicCoeff (a.comp (X^p)*(F+(X^p-1)*E))
       ((e:ℤ)+(S+1-v)*p)*M v)-
     c*(∑ v∈range H,intrinsicCoeff (b.comp (X^p)*(F+(X^p-1)*E))
       ((e:ℤ)+(S-v)*p)*Z v)) =
    digitPhi H S M Z a b c*F.coeff e+
      digitPhi H S M Z (a*(X-1)) (b*(X-1)) c*E.coeff e := by
  simp_rw [intrinsicCoeff_split_product _ F E p e _ hp he hF hE]
  have hsum (s : Finset ℕ) (A B w : ℕ→R) :
      (∑ v∈s,(A v*F.coeff e+B v*E.coeff e)*w v)=
      (∑ v∈s,A v*w v)*F.coeff e+(∑ v∈s,B v*w v)*E.coeff e := by
    rw [Finset.sum_mul,Finset.sum_mul,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [hsum,hsum]
  unfold digitPhi
  ring
/-- Multiplication by Y-1 gives the exact neighboring quotient difference. -/
theorem intrinsicCoeff_mul_sub_one (A : R[X]) (i : ℤ) :
    intrinsicCoeff (A*(X-1)) i=intrinsicCoeff A (i-1)-intrinsicCoeff A i := by
  cases i with
  | ofNat n =>
    cases n with
    | zero => simp [intrinsicCoeff,mul_sub,coeff_sub]
    | succ n =>
      have hi : ((n+1:ℕ):ℤ)-1=(n:ℤ) := by omega
      change intrinsicCoeff (A*(X-1)) ((n+1:ℕ):ℤ)=
        intrinsicCoeff A (((n+1:ℕ):ℤ)-1)-intrinsicCoeff A ((n+1:ℕ):ℤ)
      rw [hi,intrinsicCoeff_nat,intrinsicCoeff_nat,intrinsicCoeff_nat]
      simp [mul_sub,coeff_mul_X]
  | negSucc n => simp [intrinsicCoeff]

/-- Thus the E covector is Psi(S-1)-Psi(S), with every boundary term retained. -/
theorem digitPhi_neighbor_difference (H : ℕ) (S : ℤ) (M Z : ℕ→R)
    (a b : R[X]) (c : R) :
    digitPhi H S M Z (a*(X-1)) (b*(X-1)) c =
      digitPhi H (S-1) M Z a b c-digitPhi H S M Z a b c := by
  unfold digitPhi
  simp_rw [intrinsicCoeff_mul_sub_one,sub_mul]
  have h1 : ∀v:ℕ,S+1-v-1=S-v := by intro v;ring
  have h2 : ∀v:ℕ,S-1+1-v=S-v := by intro v;ring
  have h3 : ∀v:ℕ,S-v-1=S-1-v := by intro v;ring
  simp_rw [h1,h2,h3,Finset.sum_sub_distrib]
  ring
#print axioms digit_response_contraction
end CatalanMeasure.GenD.Uniform.Prefix




