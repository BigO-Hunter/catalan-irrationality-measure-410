module
public import Submission.CatalanMeasure.Parametric.ResidueFactorization
public import Mathlib.LinearAlgebra.Matrix.Rank
@[expose] public section
namespace CatalanMeasure.Parametric
open Matrix Finset OAI.InternalCatalan
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 1200000 in
theorem matrix_rank_factorization {K : Type*} [Field K] {n : ℕ}
    (R : Matrix (Fin n) (Fin n) K) :
    ∃ A : Matrix (Fin n) (Fin R.rank) K,∃ B : Matrix (Fin R.rank) (Fin n) K,A*B=R :=by
  classical
  let V :=LinearMap.range R.mulVecLin
  let basis : Module.Basis (Fin R.rank) K V :=Module.finBasis K V
  let col (j : Fin n) : V :=⟨fun i =>R i j,by
    refine ⟨Pi.single j 1,?_⟩
    ext i
    simp [Matrix.mulVecLin_apply,Matrix.mulVec_single_one]⟩
  let A : Matrix (Fin n) (Fin R.rank) K :=Matrix.of fun i k =>(basis k).val i
  let B : Matrix (Fin R.rank) (Fin n) K :=Matrix.of fun k j =>basis.repr (col j) k
  refine ⟨A,B,?_⟩
  ext i j
  have hh :=congrArg (fun v : V =>v.val i) (basis.sum_repr (col j))
  simp only [Submodule.coe_sum,Finset.sum_apply,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul] at hh
  simpa only [Matrix.mul_apply,A,B,Matrix.of_apply,col,mul_comm] using hh

def scaledResidueMatrix {p n : ℕ} [Fact p.Prime] (M : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) (ZMod p) :=Matrix.of fun i j =>palindromicRatResidue p ((p:ℚ)^2*M i j)

/-- A bound on the actual leading residue rank gives a uniform determinant bound. -/
theorem residue_rank_valuation_lower {p n e : ℕ} [hp : Fact p.Prime]
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : ∀ i j,(((p:ℚ)^2*M i j).den : ZMod p)≠0)
    (he : e ≤ n) (hr : (scaledResidueMatrix (p:=p) M).rank ≤ n-e) :
    -((2*n-e:ℕ):ℤ) ≤ padicValRat p M.det :=by
  let R :=scaledResidueMatrix (p:=p) M
  obtain ⟨A0,B0,hAB⟩ :=matrix_rank_factorization R
  let A : Matrix (Fin n) (Fin R.rank) ℚ :=Matrix.of fun i j =>((A0 i j).val:ℚ)
  let B : Matrix (Fin R.rank) (Fin n) ℚ :=Matrix.of fun i j =>((B0 i j).val:ℚ)
  have hA (i j) : ((A i j).den : ZMod p)≠0 :=by
    simp only [A,Matrix.of_apply,Rat.den_natCast,Nat.cast_one,ne_eq,one_ne_zero,not_false_eq_true]
  have hB (i j) : ((B i j).den : ZMod p)≠0 :=by
    simp only [B,Matrix.of_apply,Rat.den_natCast,Nat.cast_one,ne_eq,one_ne_zero,not_false_eq_true]
  have hres (i j) : palindromicRatResidue p ((p:ℚ)^2*M i j)=
      ∑ k,palindromicRatResidue p (A i k)*palindromicRatResidue p (B k j) :=by
    change R i j=∑ k : Fin R.rank,palindromicRatResidue p ((A0 i k).val:ℚ)*
      palindromicRatResidue p ((B0 k j).val:ℚ)
    have hh :=congrArg (fun Q : Matrix (Fin n) (Fin n) (ZMod p) =>Q i j) hAB
    simp only [Matrix.mul_apply] at hh
    simpa only [palindromicRatResidue,
      Rat.num_natCast,Rat.den_natCast,Int.cast_natCast,Nat.cast_one,div_one,
      ZMod.natCast_zmod_val] using hh.symm
  have hv :=residue_factorization_valuation_lower M A B hM hA hB hres
  have hm :=Nat.min_le_right n R.rank
  have hh : n+min n R.rank ≤ 2*n-e :=by
    have hsub :=Nat.sub_add_cancel he
    change R.rank ≤ n-e at hr
    omega
  omega

end
end CatalanMeasure.Parametric
