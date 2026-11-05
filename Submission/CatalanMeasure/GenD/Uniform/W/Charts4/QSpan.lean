module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.TilingPoly
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.NativeCoordinates
@[expose] public section
set_option Elab.async false

/-!
# `QA`, `QC` in the native bases: coordinates, degrees, independence
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open CatalanMeasure.GenD.Uniform.Prefix Polynomial Finset
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- Coordinates of `QA t k` in `plusVectors`. -/
def gA {b : ℕ} (t : TilingCoordinates (K := ZMod p) b ((p - 1) / 2)) (k : Fin b)
    (i : Fin ((p - 1) / 2 + 1)) : ZMod p :=
  if h : i.val < (p - 1) / 2 then t.1.1 (finProdFinEquiv (k, Fin.rev ⟨i.val, h⟩)) else t.2 k.succ

/-- Coordinates of `QC t k` in `minusVectors`. -/
def gC {b : ℕ} (t : TilingCoordinates (K := ZMod p) b ((p - 1) / 2)) (k : Fin b)
    (i : Fin ((p - 1) / 2)) : ZMod p :=
  t.1.2 (finProdFinEquiv (k, Fin.rev i))

theorem QA_eq {b : ℕ} (t : TilingCoordinates (K := ZMod p) b ((p - 1) / 2)) (k : Fin b) :
    QA t k = ∑ i : Fin ((p - 1) / 2 + 1), gA t k i • plusVectors (p := p) i := by
  have hl : gA t k (Fin.last _) • plusVectors (p := p) (Fin.last _) =
      t.2 k.succ • nativeCenter (p := p) := by
    simp [gA, plusVectors]
  have hsum : ∑ j : Fin ((p - 1) / 2), t.1.1 (finProdFinEquiv (k, j)) • nativePlus (p := p) ((j : ℤ) + 1) =
      ∑ i : Fin ((p - 1) / 2), gA t k (Fin.castSucc i) • plusVectors (p := p) (Fin.castSucc i) := by
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun j => ?_)
    have hj := j.isLt
    have e1 : gA t k (Fin.castSucc (Fin.revPerm j)) = t.1.1 (finProdFinEquiv (k, j)) := by
      have hlt : (Fin.castSucc (Fin.revPerm j)).val < (p - 1) / 2 := by
        simp only [Fin.revPerm_apply, Fin.val_castSucc, Fin.val_rev]; omega
      unfold gA
      rw [dif_pos hlt]
      have hrev : Fin.rev (⟨(Fin.castSucc (Fin.revPerm j)).val, hlt⟩ : Fin ((p - 1) / 2)) = j :=
        Fin.ext (by simp only [Fin.revPerm_apply, Fin.val_rev, Fin.val_castSucc]; omega)
      rw [hrev]
    have e2 : plusVectors (p := p) (Fin.castSucc (Fin.revPerm j)) =
        nativePlus (p := p) ((j : ℤ) + 1) := by
      have hlt : (Fin.castSucc (Fin.revPerm j)).val < (p - 1) / 2 := by
        simp only [Fin.revPerm_apply, Fin.val_castSucc, Fin.val_rev]; omega
      simp only [plusVectors, hlt, if_true]
      congr 1
      simp only [Fin.revPerm_apply, Fin.val_castSucc, Fin.val_rev]
      omega
    rw [e1, e2]
  unfold QA
  rw [Fin.sum_univ_castSucc, hl, hsum, add_comm]

theorem QC_eq {b : ℕ} (t : TilingCoordinates (K := ZMod p) b ((p - 1) / 2)) (k : Fin b) :
    QC t k = ∑ i : Fin ((p - 1) / 2), gC t k i • minusVectors (p := p) i := by
  unfold QC
  refine (Equiv.sum_comp Fin.revPerm
    (fun j : Fin ((p - 1) / 2) => t.1.2 (finProdFinEquiv (k, j)) • nativeMinus (p := p) ((j : ℤ) + 1))).symm.trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  simp only [gC, minusVectors, Fin.revPerm_apply]
  congr 2
  simp only [Fin.val_rev]
  omega

theorem QA_zero (hp2 : p ≠ 2) {b : ℕ} (t : TilingCoordinates (K := ZMod p) b ((p - 1) / 2))
    (k : Fin b) (h : QA t k = 0) :
    t.2 k.succ = 0 ∧ ∀ j, t.1.1 (finProdFinEquiv (k, j)) = 0 := by
  have hli := (plusNativeBasis (p := p) hp2).linearIndependent
  have h0 := Fintype.linearIndependent_iff.mp hli (gA t k)
    (by show ∑ i, gA t k i • plusVectors (p := p) i = 0; rw [← QA_eq]; exact h)
  refine ⟨?_, fun j => ?_⟩
  · simpa [gA] using h0 (Fin.last _)
  · have hj := j.isLt
    have hlt : (Fin.castSucc (Fin.rev j)).val < (p - 1) / 2 := by
      simp only [Fin.val_castSucc, Fin.val_rev]; omega
    have := h0 (Fin.castSucc (Fin.rev j))
    unfold gA at this
    rw [dif_pos hlt] at this
    have hrev : Fin.rev (⟨(Fin.castSucc (Fin.rev j)).val, hlt⟩ : Fin ((p - 1) / 2)) = j :=
      Fin.ext (by simp only [Fin.val_rev, Fin.val_castSucc]; omega)
    rw [hrev] at this
    exact this

theorem QC_zero (hp2 : p ≠ 2) {b : ℕ} (t : TilingCoordinates (K := ZMod p) b ((p - 1) / 2))
    (k : Fin b) (h : QC t k = 0) : ∀ j, t.1.2 (finProdFinEquiv (k, j)) = 0 := by
  have hli := (minusNativeBasis (p := p) hp2).linearIndependent
  have h0 := Fintype.linearIndependent_iff.mp hli (gC t k)
    (by show ∑ i, gC t k i • minusVectors (p := p) i = 0; rw [← QC_eq]; exact h)
  intro j
  have := h0 (Fin.rev j)
  simpa [gC] using this

theorem QA_degree (hp2 : p ≠ 2) {b : ℕ} (t : TilingCoordinates (K := ZMod p) b ((p - 1) / 2))
    (k : Fin b) : (QA t k).degree < p := by
  have hm : QA t k ∈ Submodule.span (ZMod p) (Set.range (plusVectors (p := p))) := by
    rw [QA_eq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [plus_native_span hp2] at hm
  obtain ⟨A, hA, hAe⟩ := hm
  have hA' := mem_degreeLT.mp hA
  have hhe := native_half_identity hp2
  change (X - 1) ^ ((p - 1) / 2) * A = QA t k at hAe
  rw [← hAe]
  have hd : ((X - 1 : (ZMod p)[X])).degree = 1 := by simpa using degree_X_sub_C (1 : ZMod p)
  by_cases h0 : A = 0
  · simp [h0]
  · rw [degree_mul, degree_pow, hd]
    have : A.degree < ((p - 1) / 2 + 1 : ℕ) := hA'
    calc ((p - 1) / 2 : ℕ) • (1 : WithBot ℕ) + A.degree
        < ((p - 1) / 2 : ℕ) • (1 : WithBot ℕ) + (((p - 1) / 2 + 1 : ℕ) : WithBot ℕ) := by
          exact WithBot.add_lt_add_left (by simp) this
      _ = p := by
          simp only [nsmul_eq_mul, mul_one]
          norm_cast
          omega

end
end CatalanMeasure.GenD.Uniform.W.Charts4
