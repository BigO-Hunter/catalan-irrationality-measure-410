module
public import Submission.CatalanMeasure.Parametric.SparseRowEvaluation
public import Submission.CatalanMeasure.Parametric.ReversalShift
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

def sparseRowPDelta (P : Parameters) (N p k d : ℕ) : ℤ[X] :=
  rowP P N (P.g N+k*p+d)-rowP P N (P.g N+k*p-d)
def sparseRowDDelta (P : Parameters) (N p k d : ℕ) : ℤ[X] :=
  rowD P N (P.g N+k*p+d)-rowD P N (P.g N+k*p-d)

theorem sparseRow_distance_bounds (P : Parameters) (N p k d : ℕ)
    (hdg : d ≤ P.g N) (hcut : k*p+d<P.C N) :
    rowDistance P N (P.g N+k*p+d)<P.C N ∧
      rowDistance P N (P.g N+k*p-d)<P.C N := by
  unfold rowDistance rowOffset
  constructor <;> omega

theorem sparseRowPDelta_eval₂ {K : Type*} [Field K] (phi : ℤ →+* K)
    (P : Parameters) (N p k d : ℕ) (hdg : d ≤ P.g N) (hcut : k*p+d<P.C N)
    {x : K} (hx : x ≠ 0) :
    (sparseRowPDelta P N p k d).eval₂ phi x =
      (1-x)^(P.h N)*x^(P.C N-1)*
        (Chebyshev.T ℤ (((k*p:ℕ):ℤ)+(d:ℤ))-
          Chebyshev.T ℤ (((k*p:ℕ):ℤ)-(d:ℤ))).eval₂ phi x⁻¹ := by
  have hh :=sparseRow_distance_bounds P N p k d hdg hcut
  have hp : rowOffset P N (P.g N+k*p+d)=((k*p:ℕ):ℤ)+(d:ℤ) := by
    unfold rowOffset
    omega
  have hm : rowOffset P N (P.g N+k*p-d)=((k*p:ℕ):ℤ)-(d:ℤ) := by
    unfold rowOffset
    omega
  rw [sparseRowPDelta,eval₂_sub,rowP_eval₂_signed phi hh.1 hx,rowP_eval₂_signed phi hh.2 hx,hp,hm]
  rw [eval₂_sub]
  ring

theorem sparseRowDDelta_eval₂ {K : Type*} [Field K] (phi : ℤ →+* K)
    (P : Parameters) (N p k d : ℕ) (hdg : d ≤ P.g N) (hcut : k*p+d<P.C N)
    {x : K} (hx : x ≠ 0) :
    (sparseRowDDelta P N p k d).eval₂ phi x =
      (1-x)^(P.h N)*x^(P.C N-1)*
        (Chebyshev.U ℤ (((k*p:ℕ):ℤ)+(d:ℤ)-1)-
          Chebyshev.U ℤ (((k*p:ℕ):ℤ)-(d:ℤ)-1)).eval₂ phi x⁻¹ := by
  have hh :=sparseRow_distance_bounds P N p k d hdg hcut
  have hp : rowOffset P N (P.g N+k*p+d)=((k*p:ℕ):ℤ)+(d:ℤ) := by
    unfold rowOffset
    omega
  have hm : rowOffset P N (P.g N+k*p-d)=((k*p:ℕ):ℤ)-(d:ℤ) := by
    unfold rowOffset
    omega
  rw [sparseRowDDelta,eval₂_sub,rowD_eval₂_signed phi hh.1 hx,rowD_eval₂_signed phi hh.2 hx,hp,hm]
  rw [eval₂_sub]
  ring

end
end CatalanMeasure.Parametric
