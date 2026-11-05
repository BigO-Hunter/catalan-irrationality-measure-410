module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMom
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMD

@[expose] public section

/-!
# Moments of a merged reference

The species moments `mposQ R n` depend only on the signed density of the `T` species, so under
`MergeOK` they agree with those of the merged reference `Rm` (`mposQ_merge`). The merged references
`Rm0, Rm1, Rm2` of `EvalRefMD` have one `T` piece on `[0, 1]` and no negative `T` pieces, so their
moments are `Σ_j c_j / (n + j + 2)` without powers of the cut points: the partial sums `ipPartQ` and
`ipDiffRQ` with `K = 1000` are evaluated on the merged references.
-/

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef

open CatalanMeasure.Signed.FieldForm
open MeasureTheory Set

noncomputable section

theorem sumMom_eq_Sfun (k : ℕ) : ∀ X : List PieceQ, ((sumMom X k : ℚ) : ℝ) = Sfun X (fun t => t ^ k)
  | [] => by simp [sumMom, Sfun]
  | q :: X => by
    rw [Sfun_cons, int_dens_pow q k, ← sumMom_eq_Sfun k X]
    simp only [sumMom]
    push_cast
    ring

theorem Sfun_append (A B : List PieceQ) (f : ℝ → ℝ) : Sfun (A ++ B) f = Sfun A f + Sfun B f := by
  simp [Sfun, List.map_append, List.sum_append]

theorem mposQ_eq_Sfun (R : RefQ) (n : ℕ) :
    ((mposQ R n : ℚ) : ℝ) = Sfun (sgnT R) (fun t => t ^ (n + 1)) := by
  unfold mposQ sgnT
  rw [Sfun_append, Sfun_map_negQ, ← sumMom_eq_Sfun, ← sumMom_eq_Sfun]
  push_cast
  ring

/-- **The moments depend only on the signed density.** -/
theorem mposQ_merge {cT cF : List ℚ} {R Rm : RefQ} (h : MergeOK cT cF R Rm) (n : ℕ) :
    mposQ R n = mposQ Rm n := by
  have hf : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => t ^ (n + 1)) volume a b :=
    fun a b => (continuous_pow (n + 1)).intervalIntegrable a b
  have e := Sfun_congr_ae h.1.le_left h.1.le_right _ hf (sameDens_of_refines h.1)
  exact_mod_cast (mposQ_eq_Sfun R n).trans (e.trans (mposQ_eq_Sfun Rm n).symm)

theorem ipPartQ_merge {cT cF : List ℚ} {R Rm : RefQ} (h : MergeOK cT cF R Rm) (K : ℕ) :
    ipPartQ R K = ipPartQ Rm K := by
  unfold ipPartQ
  exact Finset.sum_congr rfl fun n _ => by rw [mposQ_merge h]

/-- `Σ_{n<K} (mposQ R n − mposQ S n)² / (n+1)`. -/
def ipDiffRQ (R S : RefQ) (K : ℕ) : ℚ :=
  ∑ n ∈ Finset.range K, (mposQ R n - mposQ S n) ^ 2 / ((n : ℚ) + 1)

theorem ipDiffRQ_merge {cT cF cT' cF' : List ℚ} {R Rm S Sm : RefQ} (h : MergeOK cT cF R Rm)
    (h' : MergeOK cT' cF' S Sm) (K : ℕ) : ipDiffRQ R S K = ipDiffRQ Rm Sm K := by
  unfold ipDiffRQ
  exact Finset.sum_congr rfl fun n _ => by rw [mposQ_merge h, mposQ_merge h']

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
