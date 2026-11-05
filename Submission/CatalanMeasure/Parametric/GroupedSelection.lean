module

public import Submission.CatalanMeasure.Parametric.GroupedLaurentSheet
public import Mathlib.Logic.Equiv.Sum

/-!
# Reindexing an arbitrary actual/near selection

Reorder nodes independently of the physical monomial basis. The determinant's
absolute value is unchanged, so each multilinear term can use the grouped bound.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open Finset OAI.InternalCatalan
open scoped BigOperators

noncomputable section

theorem exists_bool_partition {n : ℕ} (t : Fin n → Bool) :
    ∃ p q : ℕ, p + q = n ∧ ∃ e : Fin p ⊕ Fin q ≃ Fin n,
      (∀ i, t (e (Sum.inl i)) = false) ∧ (∀ i, t (e (Sum.inr i)) = true) := by
  classical
  let A := {i : Fin n // t i = false}
  let B := {i : Fin n // ¬t i = false}
  let e : Fin (Fintype.card A) ⊕ Fin (Fintype.card B) ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivFin A).symm (Fintype.equivFin B).symm).trans
      (Equiv.sumCompl (fun i : Fin n => t i = false))
  have hcard : Fintype.card A + Fintype.card B = n := by
    simpa using Fintype.card_congr e
  refine ⟨_, _, hcard, e, ?_, ?_⟩
  · intro i
    exact ((Fintype.equivFin A).symm i).property
  · intro i
    have hi := ((Fintype.equivFin B).symm i).property
    change t (((Fintype.equivFin B).symm i).val) = true
    cases hv : t (((Fintype.equivFin B).symm i).val)
    · exact False.elim (hi hv)
    · rfl

theorem selected_laurent_det_reindex {n p q g : ℕ} (h : p + q = n)
    (x : Fin n → ℝ) (t : Fin n → Bool) (e : Fin p ⊕ Fin q ≃ Fin n)
    (hleft : ∀ i, t (e (Sum.inl i)) = false)
    (hright : ∀ i, t (e (Sum.inr i)) = true) :
    |(Matrix.of fun i r : Fin n => if t i then x i ^ ((r : ℤ) - g)
      else actualLaurentEntry g r (x i)).det| =
      |(groupedLaurentMatrix (p := p) (q := q)
        (fun j => x (e (finSumFinEquiv.symm j))) g).det| := by
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i r =>
    if t i then x i ^ ((r : ℤ) - g) else actualLaurentEntry g r (x i)
  let f : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  have hm : M.submatrix e f = groupedLaurentMatrix (p := p) (q := q)
      (fun j => x (e (finSumFinEquiv.symm j))) g := by
    ext i r
    rcases i with i | i
    · simp [M, f, groupedLaurentMatrix, hleft]
    · simp [M, f, groupedLaurentMatrix, hright]
  calc
    _ = |(M.submatrix e f).det| := (Matrix.abs_det_submatrix_equiv_equiv e f M).symm
    _ = _ := congrArg (fun A => |A.det|) hm

def groupedLaurentMajorant {p q : ℕ} (x : Fin (p + q) → ℝ) (g : ℕ) : ℝ :=
  (∏ i : Fin (p + q), |x i| ^ ((g : ℤ) - (p + q - 1 : ℕ))) *
    ((∏ i : Fin q, |x (Fin.natAdd p i)| ^ (p + q - 1 - 2 * g)) *
      ((1 + 10 * Real.exp 12 * ((p + q : ℕ) : ℝ)) ^ p *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (x (Fin.castAdd q j) - x (Fin.castAdd q i))| *
        |∏ i : Fin q, ∏ j ∈ Ioi i, (x (Fin.natAdd p j) - x (Fin.natAdd p i))| *
        crossCauchyProduct (fun i => x (Fin.castAdd q i)) (fun i => x (Fin.natAdd p i))))

theorem selected_laurent_det_bound {n p q g : ℕ} (h : p + q = n)
    (x : Fin n → ℝ) (t : Fin n → Bool) (e : Fin p ⊕ Fin q ≃ Fin n)
    (hleft : ∀ i, t (e (Sum.inl i)) = false)
    (hright : ∀ i, t (e (Sum.inr i)) = true)
    (hn : 48 ≤ p + q) (hng : 2 * g + 1 < p + q)
    (hx0 : ∀ i, x i ≠ 0) (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x)
    (hweight : (∑ i : Fin p, blaschkeWeight (x (e (Sum.inl i)))) ≤
      ((p + q - 1 - 2 * g : ℕ) : ℝ)) :
    |(Matrix.of fun i r : Fin n => if t i then x i ^ ((r : ℤ) - g)
      else actualLaurentEntry g r (x i)).det| ≤
      groupedLaurentMajorant (p := p) (q := q)
        (fun j => x (e (finSumFinEquiv.symm j))) g := by
  rw [selected_laurent_det_reindex h x t e hleft hright]
  apply grouped_laurent_det_bound _ hn hng (fun i => hx0 _) (fun i => hx _)
  · exact hxi.comp (e.injective.comp finSumFinEquiv.symm.injective)
  · simpa using hweight

end

end CatalanMeasure.Parametric
