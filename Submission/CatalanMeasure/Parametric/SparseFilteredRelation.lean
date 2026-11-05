module
public import Submission.CatalanMeasure.Parametric.SparseUniformRelation
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem filteredEntry_scaled_residue_sum_general {P : Parameters} {p N r k : ℕ}
    [hp : Fact p.Prime] (hp2 : p≠2) (hH : P.H N<p^2) (hk : k<P.n N)
    (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    (((p:ℚ)^2*filteredEntryRat P z N r k).den : ZMod p)≠0 ∧
    palindromicRatResidue p ((p:ℚ)^2*filteredEntryRat P z N r k)=
      ∑ v ∈ Finset.range (P.q N+1),palindromicRatResidue p (filterCoeffRat P N v)*
        palindromicRatResidue p ((p:ℚ)^2*rawEntryRat P z N r (P.b N+k+v)) := by
  let f : ℕ → ℚ :=fun v =>filterCoeffRat P N v*((p:ℚ)^2*rawEntryRat P z N r (P.b N+k+v))
  have hterm (v : ℕ) (hv : v ∈ Finset.range (P.q N+1)) :
      ((f v).den : ZMod p)≠0 ∧ palindromicRatResidue p (f v)=
        palindromicRatResidue p (filterCoeffRat P N v)*
          palindromicRatResidue p ((p:ℚ)^2*rawEntryRat P z N r (P.b N+k+v)) :=by
    have hv' : v ≤ P.q N :=by have :=Finset.mem_range.mp hv; omega
    have hj : P.b N+k+v<P.H N :=by
      have hjL :=rawColumn_lt_L hk hv'
      unfold Parameters.H Parameters.C
      omega
    exact rational_residue_mul (filterCoeff_den P N v) (scaledRawEntry_transfer hp2 hH hj z hzp).1
  have hs :=rational_residue_sum (p:=p) (Finset.range (P.q N+1)) f (fun v hv =>(hterm v hv).1)
  have he : (p:ℚ)^2*filteredEntryRat P z N r k=∑ v ∈ Finset.range (P.q N+1),f v :=by
    unfold filteredEntryRat
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [f]
    ring
  rw [he]
  refine ⟨hs.1,?_⟩
  rw [palindromicRatResidue_sum _ _ (fun v hv =>(hterm v hv).1)]
  exact Finset.sum_congr rfl (fun v hv =>(hterm v hv).2)

def sparseFilteredResidueDelta (P : Parameters) (p N a d k : ℕ) [Fact p.Prime] (z : ℚ) : ZMod p :=
  palindromicRatResidue p ((p:ℚ)^2*filteredEntryRat P z N (P.g N+a*p+d) k)-
    palindromicRatResidue p ((p:ℚ)^2*filteredEntryRat P z N (P.g N+a*p-d) k)

theorem sparseFilteredResidueDelta_eq_sum {P : Parameters} {p N a d k : ℕ}
    [hp : Fact p.Prime] (hp2 : p≠2) (hH : P.H N<p^2) (hk : k<P.n N)
    (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    sparseFilteredResidueDelta P p N a d k z=
      ∑ v ∈ Finset.range (P.q N+1),palindromicRatResidue p (filterCoeffRat P N v)*
        sparseRawResidueDelta P p N a d (P.b N+k+v) z := by
  unfold sparseFilteredResidueDelta
  rw [(filteredEntry_scaled_residue_sum_general hp2 hH hk z hzp).2,
    (filteredEntry_scaled_residue_sum_general hp2 hH hk z hzp).2,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  unfold sparseRawResidueDelta
  ring

/-- A uniform leading-residue dependency for the actual filtered matrix. -/
theorem sparse_filtered_residue_relation {P : Parameters} {p N d k : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hN : 0<N) (hlarge : 1000000 ≤ p) (hHsq : P.H N<p^2)
    (hd : 0<d) (hdg : d ≤ P.g N) (hcut : 3*p+d ≤ P.C N)
    (hhi : P.H N ≤ 4*p) (hH : 4<P.H N) (hwindow : P.H N ≤ 3*p+P.b N)
    (hk : k<P.n N) (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    sparseFilteredResidueDelta P p N 2 d k z=
      (292/59:ZMod p)*sparseFilteredResidueDelta P p N 1 d k z-
      (3281/177:ZMod p)*sparseFilteredResidueDelta P p N 0 d k z := by
  have hp2 : p≠2 :=by omega
  rw [sparseFilteredResidueDelta_eq_sum hp2 hHsq hk z hzp,
    sparseFilteredResidueDelta_eq_sum hp2 hHsq hk z hzp,
    sparseFilteredResidueDelta_eq_sum hp2 hHsq hk z hzp,
    Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  have hv' : v ≤ P.q N :=by have :=Finset.mem_range.mp hv; omega
  rw [sparse_raw_residue_relation hAdm hN hlarge hHsq hd hdg hcut hhi hH hwindow
    (rawColumn_ge_b P N k v) (rawColumn_lt_L hk hv') z hzp]
  ring

end
end CatalanMeasure.Parametric
