module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponseIndices
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponsePhi
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.LowFilterEquiv
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset CatalanMeasure.Parametric OAI.InternalCatalan
noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

def sourceM (J v : ℕ) : Fp := palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) J)
def sourceZ (J v : ℕ) : Fp := palindromicRatResidue p (zetaRat v J)

def intrinsicResponse (H J ell : ℕ) (PG PD : Fp[X]) : Fp :=
  (∑ v ∈ range (H+1),intrinsicCoeff PG ((H:ℤ)-1-ell-((v:ℤ)-1)*p)*sourceM J v)-
    (3/2:Fp)*(∑ v ∈ range H,intrinsicCoeff PD ((H:ℤ)-1-ell-(v:ℤ)*p)*sourceZ J v)

theorem uResp_intrinsicResponse {P : Parameters} {N j : ℕ}
    (hP : Admissible P) (hN : 0<N) (hp2 : p≠2) (hH : P.H N<p^2)
    (hj : j<P.H N) (c : Fin (P.n N)→Fp) :
    uResp P N p j c=intrinsicResponse (P.H N) (j/p) (j%p)
      ((X-1)^P.h N*(X^2-1)^((p-1)/2)*intrinsicT P N p c)
      ((X-1)^P.h N*intrinsicU P N p c) :=
  raw_response_intrinsic hP hN hp2 hH hj c

def sourcePsi (H ah J : ℕ) (S : ℤ) (a b : Fp[X]) : Fp :=
  digitPsi H ah S (sourceM J) (sourceZ J) a b (3/2)

/-- Signed cutoff also covers the S=-1 boundary covector of E. -/
theorem digitPhi_cutoff_signed (H K : ℕ) (S : ℤ) (hK : K≤H) (hS : S+1≤K)
    (M Z : ℕ→Fp) (a b : Fp[X]) (c : Fp) :
    digitPhi H S M Z a b c=digitPhi K S M Z a b c := by
  have hM : (∑ v ∈ range (H+1),intrinsicCoeff a (S+1-v)*M v)=
      ∑ v ∈ range (K+1),intrinsicCoeff a (S+1-v)*M v := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro v _ hv
    have hv' : K+1≤v := by simpa only [Finset.mem_range,not_lt] using hv
    rw [intrinsicCoeff,if_neg (by omega : ¬0≤S+1-v),zero_mul]
  have hZ : (∑ v ∈ range H,intrinsicCoeff b (S-v)*Z v)=
      ∑ v ∈ range K,intrinsicCoeff b (S-v)*Z v := by
    symm
    apply Finset.sum_subset (Finset.range_mono hK)
    intro v _ hv
    have hv' : K≤v := by simpa only [Finset.mem_range,not_lt] using hv
    rw [intrinsicCoeff,if_neg (by omega : ¬0≤S-v),zero_mul]
  simp only [digitPhi,hM,hZ]

theorem sourcePsi_cutoff (H K ah J : ℕ) (S : ℤ) (hK : K≤H) (hS : S+1≤K)
    (a b : Fp[X]) : sourcePsi H ah J S a b=sourcePsi K ah J S a b := by
  unfold sourcePsi digitPsi
  exact digitPhi_cutoff_signed H K S hK hS _ _ _ _ _
/-- A native slot's actual intrinsic functional equals one F/E covector. -/
theorem intrinsicResponse_normalized (H ah J ell : ℕ) (hell : ell<H)
    (a b F E : Fp[X]) (hF : F.degree<p) (hE : E.degree<p) :
    intrinsicResponse H J ell
      ((a*(X-1)^ah).comp (X^p)*(F+(X^p-1)*E))
      ((b*(X-1)^ah).comp (X^p)*(F+(X^p-1)*E)) =
    sourcePsi H ah J (((H-1-ell)/p:ℕ):ℤ) a b*F.coeff ((H-1-ell)%p)+
    (sourcePsi H ah J ((((H-1-ell)/p:ℕ):ℤ)-1) a b-
      sourcePsi H ah J (((H-1-ell)/p:ℕ):ℤ) a b)*E.coeff ((H-1-ell)%p) := by
  unfold intrinsicResponse
  simp_rw [intrinsic_window_P_index H p ell _ hell,intrinsic_window_D_index H p ell _ hell]
  exact normalized_response_contraction H ah p ((H-1-ell)%p) (((H-1-ell)/p:ℕ):ℤ)
    (sourceM J) (sourceZ J) a b F E (3/2) (Fact.out:p.Prime).pos
    (Nat.mod_lt _ (Fact.out:p.Prime).pos) hF hE

/-- The actual constant covector polynomial in one fixed quotient zone. -/
def sourceCovectorPolynomial {ι : Type*} [Fintype ι] (H ah J : ℕ) (S : ℤ)
    (a b F E : ι→Fp[X]) : Fp[X] :=
  ∑ t, (C (sourcePsi H ah J S (a t) (b t))*F t+
    C (sourcePsi H ah J (S-1) (a t) (b t)-sourcePsi H ah J S (a t) (b t))*E t)

/-- Exact observed-residue equation: the covector window minus the UNIQUE B
prefix represents the real intrinsic response, with the original p frame. -/
theorem source_covector_window {ι : Type*} [Fintype ι]
    (H ah J ell : ℕ) (hell : ell<H) (a b F E : ι→Fp[X])
    (hF : ∀t,(F t).degree<p) (hE : ∀t,(E t).degree<p) (B : Fp[X]) :
    (sourceCovectorPolynomial H ah J (((H-1-ell)/p:ℕ):ℤ) a b F E-
      residuePolynomial (((H-1)%p:ℕ):Fp) B).coeff ((H-1-ell)%p)=
    (∑ t,intrinsicResponse H J ell
      (((a t)*(X-1)^ah).comp (X^p)*(F t+(X^p-1)*E t))
      (((b t)*(X-1)^ah).comp (X^p)*(F t+(X^p-1)*E t)))-B.eval (ell:Fp) := by
  rw [coeff_sub,coeff_residuePolynomial,if_pos (Nat.mod_lt _ (Fact.out:p.Prime).pos)]
  have he := intrinsic_residue_eta H p ell hell
  have he' : (((H-1)%p:ℕ):Fp)-(((H-1-ell)%p:ℕ):Fp)=(ell:Fp) := by rw [he];ring
  rw [he']
  congr 1
  simp only [sourceCovectorPolynomial,finsetSum_coeff,coeff_add,coeff_C_mul]
  exact Finset.sum_congr rfl (fun t _ => (intrinsicResponse_normalized H ah J ell hell
    (a t) (b t) (F t) (E t) (hF t) (hE t)).symm)

/-- Concrete list of ALL individual rational moment summands at a cutoff. -/
def sourceMomentList (J K : ℕ) : Finset ℚ :=
  {3/2} ∪ (range (K+1)).image (fun v : ℕ => momentRatSigned ((v:ℤ)-1) J) ∪
    (range K).image (fun v => zetaRat v J)

def sourceMomentException (J K : ℕ) : ℕ := ∏ q ∈ sourceMomentList J K,q.den

theorem sourceMomentException_pos (J K : ℕ) : 0<sourceMomentException J K := by
  apply Finset.prod_pos
  intro q _
  exact q.den_pos

/-- Excluding the displayed finite product makes each summand denominator a
unit BEFORE residue sums are combined. -/
theorem sourceMoment_units (J K : ℕ) (hpD : ¬p∣sourceMomentException J K) :
    ∀q ∈ sourceMomentList J K,(q.den:Fp)≠0 := by
  intro q hq hz
  apply hpD
  exact ((ZMod.natCast_eq_zero_iff q.den p).mp hz).trans
    (Finset.dvd_prod_of_mem (fun x : ℚ => x.den) hq)

#print axioms uResp_intrinsicResponse
#print axioms source_covector_window
#print axioms sourceMoment_units
end
end CatalanMeasure.GenD.Uniform.Prefix



