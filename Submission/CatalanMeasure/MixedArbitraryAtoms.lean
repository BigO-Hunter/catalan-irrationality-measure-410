module

public import Submission.CatalanMeasure.WeightedMixedAndreief

@[expose] public section

/-!
# Mixed Andreief bounds with arbitrary fixed columns

The fixed columns need not be point values of the functions used for the
integrated columns. For an atomless measure, change those functions at a
finite set of distinct auxiliary points and apply the existing mixed bound.
The change preserves every integral and almost-everywhere integrand bound.
-/

namespace CatalanMeasure
open MeasureTheory
open scoped BigOperators
noncomputable section

def rowDetWithAtoms {p m : ℕ} (F : Fin (p+m) → ℝ → ℝ)
    (V : Fin (p+m) → Fin m → ℝ) (t : Fin p → ℝ) : ℝ :=
  (Matrix.of fun r c => Fin.addCases (fun i => F r (t i)) (fun j => V r j) c).det

def mixedDoubleWithAtoms {p m : ℕ} (F : Fin (p+m) → ℝ → ℝ)
    (V : Fin (p+m) → Fin m → ℝ) (G : Fin p → ℝ → ℝ)
    (K : ℝ → ℝ → ℝ) (t s : Fin p → ℝ) : ℝ :=
  rowDetWithAtoms F V t * (Matrix.of fun i j : Fin p => K (t i) (s j)).det *
    (Matrix.of fun j i : Fin p => G i (s j)).det

def mixedMatrixWithAtoms {p m : ℕ} (μ ν : Measure ℝ)
    (F : Fin (p+m) → ℝ → ℝ) (V : Fin (p+m) → Fin m → ℝ)
    (G : Fin p → ℝ → ℝ) (K : ℝ → ℝ → ℝ) :
    Matrix (Fin (p+m)) (Fin (p+m)) ℝ :=
  Matrix.of fun r c => Fin.addCases
    (fun i => ∫ z : ℝ × ℝ, F r z.1 * (G i z.2 * K z.1 z.2) ∂μ.prod ν)
    (fun j => V r j) c

private def atomTestPoint {m : ℕ} (j : Fin m) : ℝ := (j.val : ℝ)

private theorem atomTestPoint_injective {m : ℕ} :
    Function.Injective (atomTestPoint (m := m)) := by
  intro i j hij
  apply Fin.ext
  change (i.val : ℝ) = (j.val : ℝ) at hij
  exact_mod_cast hij

private def patchAtomRow {p m : ℕ} (F : Fin (p+m) → ℝ → ℝ)
    (V : Fin (p+m) → Fin m → ℝ) (r : Fin (p+m)) (t : ℝ) : ℝ :=
  if h : ∃ j : Fin m, atomTestPoint j = t then V r h.choose else F r t

private theorem patchAtomRow_at {p m : ℕ} (F : Fin (p+m) → ℝ → ℝ)
    (V : Fin (p+m) → Fin m → ℝ) (r : Fin (p+m)) (j : Fin m) :
    patchAtomRow F V r (atomTestPoint j) = V r j := by
  unfold patchAtomRow
  split
  · rename_i h
    congr 1
    exact atomTestPoint_injective h.choose_spec
  · rename_i h
    exact False.elim (h ⟨j, rfl⟩)

private theorem patchAtomRow_ae {p m : ℕ} (μ : Measure ℝ) [NullSingletonClass μ]
    (F : Fin (p+m) → ℝ → ℝ) (V : Fin (p+m) → Fin m → ℝ) :
    ∀ᵐ t ∂μ, ∀ r, patchAtomRow F V r t = F r t := by
  have ha : ∀ᵐ t ∂μ, ∀ j : Fin m, t ≠ atomTestPoint j := by
    apply ae_all_iff.mpr
    intro j
    simpa only [Set.mem_singleton_iff] using
      (measure_eq_zero_iff_ae_notMem.mp (measure_singleton (atomTestPoint j) :
        μ {atomTestPoint j} = 0))
  filter_upwards [ha] with t ht r
  unfold patchAtomRow
  rw [dite_eq_right]
  rintro ⟨j, hj⟩
  exact ht j hj.symm

theorem abs_det_mixedMatrixWithAtoms_mul_weight_le {p m : ℕ}
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NullSingletonClass μ]
    (F : Fin (p+m) → ℝ → ℝ) (V : Fin (p+m) → Fin m → ℝ)
    (G : Fin p → ℝ → ℝ) (K : ℝ → ℝ → ℝ) {W Bd : ℝ} (hW : 0 ≤ W)
    (hint : ∀ r i, Integrable
      (fun z : ℝ × ℝ => F r z.1 * (G i z.2 * K z.1 z.2)) (μ.prod ν))
    (hBd : ∀ᵐ w ∂pairMeasure μ ν p,
      |mixedDoubleWithAtoms F V G K w.1 w.2| * W ≤ Bd) :
    |(mixedMatrixWithAtoms μ ν F V G K).det| * W ≤
      Bd * (pairMeasure μ ν p).real Set.univ := by
  classical
  have hF := patchAtomRow_ae μ F V
  have hprod : ∀ᵐ z ∂μ.prod ν, ∀ r, patchAtomRow F V r z.1 = F r z.1 :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae hF
  have hint' : ∀ r i, Integrable
      (fun z : ℝ × ℝ => patchAtomRow F V r z.1 * (G i z.2 * K z.1 z.2))
        (μ.prod ν) := by
    intro r i
    apply (hint r i).congr
    filter_upwards [hprod] with z hz
    rw [hz r]
  have hmatrix : mixedMatrix μ ν (patchAtomRow F V) atomTestPoint G K =
      mixedMatrixWithAtoms μ ν F V G K := by
    ext r c
    refine Fin.addCases (fun i => ?_) (fun j => ?_) c
    · simp only [mixedMatrix, mixedMatrixWithAtoms, Matrix.of_apply,
        Fin.addCases_left]
      apply integral_congr_ae
      filter_upwards [hprod] with z hz
      rw [hz r]
    · simp [mixedMatrix, mixedMatrixWithAtoms, patchAtomRow_at]
  have hpi : ∀ᵐ t ∂Measure.pi (fun _ : Fin p => μ),
      ∀ i r, patchAtomRow F V r (t i) = F r (t i) := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin p => μ) (i := i)).eventually hF
  have hpairs : ∀ᵐ w ∂pairMeasure μ ν p,
      ∀ i r, patchAtomRow F V r (w.1 i) = F r (w.1 i) := by
    exact Measure.quasiMeasurePreserving_fst.tendsto_ae hpi
  have hrow : ∀ᵐ w ∂pairMeasure μ ν p,
      rowDet (patchAtomRow F V) atomTestPoint w.1 = rowDetWithAtoms F V w.1 := by
    filter_upwards [hpairs] with w hw
    unfold rowDet rowDetWithAtoms
    congr 1
    ext r c
    refine Fin.addCases (fun i => ?_) (fun j => ?_) c
    · simpa only [Matrix.of_apply, Fin.append_left, Fin.addCases_left] using hw i r
    · simp [patchAtomRow_at]
  have hBd' : ∀ᵐ w ∂pairMeasure μ ν p,
      |mixedDouble (patchAtomRow F V) atomTestPoint G K w.1 w.2| * W ≤ Bd := by
    filter_upwards [hBd, hrow] with w hw hr
    simpa only [mixedDouble, mixedDoubleWithAtoms, hr] using hw
  have h := abs_det_mixedMatrix_mul_weight_le μ ν (patchAtomRow F V)
    atomTestPoint G K hW hint' hBd'
  rwa [hmatrix] at h

end
end CatalanMeasure
