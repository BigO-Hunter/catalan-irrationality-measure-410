module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponseDigit
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PStep
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset
variable {R : Type*} [CommRing R]

/-- The quotient-h combination of the actual individual moment summands. -/
noncomputable def digitPsi (H ah : ℕ) (S : ℤ) (M Z : ℕ→R) (a b : R[X]) (c : R) : R :=
  digitPhi H S M Z (a*(X-1)^ah) (b*(X-1)^ah) c

 theorem normalized_response_contraction (H ah p e : ℕ) (S : ℤ) (M Z : ℕ→R)
    (a b F E : R[X]) (c : R) (hp : 0<p) (he : e<p)
    (hF : F.degree<p) (hE : E.degree<p) :
    ((∑ v∈range (H+1),intrinsicCoeff ((a*(X-1)^ah).comp (X^p)*(F+(X^p-1)*E))
       ((e:ℤ)+(S+1-v)*p)*M v)-
     c*(∑ v∈range H,intrinsicCoeff ((b*(X-1)^ah).comp (X^p)*(F+(X^p-1)*E))
       ((e:ℤ)+(S-v)*p)*Z v)) =
    digitPsi H ah S M Z a b c*F.coeff e+
      (digitPsi H ah (S-1) M Z a b c-digitPsi H ah S M Z a b c)*E.coeff e := by
  rw [digit_response_contraction H p e S M Z _ _ F E c hp he hF hE,
    digitPhi_neighbor_difference]
  rfl

/-- Exact finite covector compression of the genuine p-step J shifts. -/
def pstepCovector (q : ℕ) (psi : ℕ→ℤ→R) (J : ℕ) (S : ℤ) : R :=
  ∑ k∈range (q+1),(-1:R)^(q-k)*(q.choose k:R)*psi (J+k) S

 theorem pstep_response_contraction (q J : ℕ) (S : ℤ) (psi : ℕ→ℤ→R) (f e : R) :
    (∑ k∈range (q+1),(-1:R)^(q-k)*(q.choose k:R)*
      (psi (J+k) S*f+(psi (J+k) (S-1)-psi (J+k) S)*e)) =
    pstepCovector q psi J S*f+
      (pstepCovector q psi J (S-1)-pstepCovector q psi J S)*e := by
  simp only [pstepCovector,mul_add,mul_sub,←mul_assoc,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,←Finset.sum_mul]
/-- The apparent physical-H loop has a quotient-index cutoff. This makes the
individual moments finite chart data, without dropping nonunit denominators. -/
theorem digitPhi_cutoff (H s : ℕ) (hH : s+1≤H) (M Z : ℕ→R)
    (a b : R[X]) (c : R) :
    digitPhi H (s:ℤ) M Z a b c=digitPhi (s+1) (s:ℤ) M Z a b c := by
  have hM : (∑ v∈range (H+1),intrinsicCoeff a ((s:ℤ)+1-v)*M v)=
      ∑ v∈range (s+1+1),intrinsicCoeff a ((s:ℤ)+1-v)*M v := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro v _ hv
    have hv' : s+1+1≤v := by simpa only [Finset.mem_range,not_lt] using hv
    rw [intrinsicCoeff,if_neg (by omega : ¬0≤(s:ℤ)+1-v),zero_mul]
  have hZ : (∑ v∈range H,intrinsicCoeff b ((s:ℤ)-v)*Z v)=
      ∑ v∈range (s+1),intrinsicCoeff b ((s:ℤ)-v)*Z v := by
    symm
    apply Finset.sum_subset (Finset.range_mono hH)
    intro v _ hv
    have hv' : s+1≤v := by simpa only [Finset.mem_range,not_lt] using hv
    rw [intrinsicCoeff,if_neg (by omega : ¬0≤(s:ℤ)-v),zero_mul]
  simp only [digitPhi,hM,hZ]

#print axioms normalized_response_contraction
#print axioms pstep_response_contraction
#print axioms digitPhi_cutoff
end CatalanMeasure.GenD.Uniform.Prefix


