module
public import Submission.OAI.NumberTheory.Catalan.Estimates.OddPhysicalCombination
@[expose] public section
namespace CatalanMeasure.Parametric
open Matrix Finset OAI.InternalCatalan
open scoped BigOperators
noncomputable section

/-- A simple pole whose residue factors through a space of dimension r. -/
def lowRankPoleMatrix {n r : ℕ} (p : ℕ)
    (C : Matrix (Fin n) (Fin n) ℚ) (A : Matrix (Fin n) (Fin r) ℚ)
    (B : Matrix (Fin r) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  C+(p:ℚ)⁻¹ • (A*B)

theorem lowRankPole_valuation_lower {p n r : ℕ} [Fact p.Prime]
    (C : Matrix (Fin n) (Fin n) ℚ) (A : Matrix (Fin n) (Fin r) ℚ)
    (B : Matrix (Fin r) (Fin n) ℚ)
    (hC : ∀ i j,((C i j).den:ZMod p)≠0)
    (hA : ∀ i j,((A i j).den:ZMod p)≠0)
    (hB : ∀ i j,((B i j).den:ZMod p)≠0) :
    -((min n r:ℕ):ℤ)≤padicValRat p (lowRankPoleMatrix p C A B).det := by
  classical
  let E : Fin 0 → Fin n → ℚ :=fun j =>Fin.elim0 j
  let I : Fin n → Fin n → ℚ :=fun j i =>C i j
  let V : Fin r → Fin n → ℚ :=fun j i =>A i j
  let a : Fin n → Fin r → ℚ :=fun j l =>B l j
  let g : oddPhysicalIndex 0 0 n → Fin n → ℚ :=fun j k =>
    match j with
    | Sum.inl l =>Fin.elim0 l
    | Sum.inr (Sum.inl l) =>Fin.elim0 l
    | Sum.inr (Sum.inr j) =>if j=k then 1 else 0
  have hg : ∀ j k,((g j k).den:ZMod p)≠0 := by
    intro j k
    rcases j with j | (j | j)
    · exact Fin.elim0 j
    · exact Fin.elim0 j
    · dsimp [g]
      split_ifs <;> norm_num
  have hh :=oddPhysicalCombination_valuation_lower E E I V a g
    (fun j =>Fin.elim0 j) (fun j =>Fin.elim0 j)
    (fun j i =>hC i j) (fun j i =>hA i j) (fun j l =>hB l j) hg
  have hmatrix : (Matrix.of fun i k : Fin n =>
      ∑ j,oddPhysicalColumn p E E I V a j i*g j k)=lowRankPoleMatrix p C A B := by
    ext i k
    simp only [Matrix.of_apply,Fintype.sum_sum_type,Fintype.sum_empty,zero_add]
    simp only [oddPhysicalColumn,g,I,V,a]
    rw [sum_eq_single k]
    · simp [lowRankPoleMatrix,Matrix.mul_apply,mul_comm]
    · intro j _ hj
      simp [hj]
    · simp
  rw [hmatrix] at hh
  have hcount : min (2*n) (min (n+0) (2*0+0+r))=min n r := by omega
  simpa only [hcount] using hh

/-- A double-pole matrix with a residue factoring through r dimensions costs
at most n+min(n,r) prime powers in its determinant. -/
theorem doublePole_valuation_lower {p n r : ℕ} [hp : Fact p.Prime]
    (M C : Matrix (Fin n) (Fin n) ℚ) (A : Matrix (Fin n) (Fin r) ℚ)
    (B : Matrix (Fin r) (Fin n) ℚ)
    (hC : ∀ i j,((C i j).den:ZMod p)≠0)
    (hA : ∀ i j,((A i j).den:ZMod p)≠0)
    (hB : ∀ i j,((B i j).den:ZMod p)≠0)
    (heq : (p:ℚ) • M=lowRankPoleMatrix p C A B) :
    -((n+min n r:ℕ):ℤ)≤padicValRat p M.det := by
  by_cases hM : M.det=0
  · rw [hM,padicValRat.zero]
    omega
  have hpq : (p:ℚ)≠0 := by exact_mod_cast hp.out.ne_zero
  have hh :=lowRankPole_valuation_lower C A B hC hA hB
  rw [← heq,Matrix.det_smul,Fintype.card_fin,
    padicValRat.mul (pow_ne_zero _ hpq) hM,padicValRat.pow,
    padicValRat.self hp.out.one_lt] at hh
  push_cast at hh ⊢
  omega

end
end CatalanMeasure.Parametric
