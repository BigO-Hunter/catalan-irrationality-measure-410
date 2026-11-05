module

public import Submission.CatalanMeasure.Cert.FieldDeriv

@[expose] public section

/-!
# Trial sequences at the scale `2^40`

`Cert.trialSeq` stores the finite coefficients as `cs / 10^8` (OAI's `barrierFiniteCoeff`).  The 728
witness stores them as `cs / 2^40`.  `trialSeqS` is the same sequence with the scale `2^40`; the
tails are the same `TailQ` data.
-/

open OAI.InternalCatalan

namespace CatalanMeasure.CellCert
open CatalanMeasure.Cert

/-- The finite coefficient `cs[k-1] / 2^40` (and `0` at `k = 0`). -/
noncomputable def finCoeffS (cs : List ℤ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else (cs.getD (k - 1) 0 : ℝ) / 1099511627776

/-- `u_k = cs[k-1] / 2^40 + Re Σ_j r_j z_j^k` for `k ≥ 1`, and `u_0 = 0`. -/
noncomputable def trialSeqS (cs : List ℤ) (tail : List TailQ) : ℕ → ℝ :=
  fun k => if k = 0 then 0 else finCoeffS cs k +
    (((tail.map TailQ.toC).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum).re

theorem finCoeffS_eq_zero {cs : List ℤ} {k : ℕ} (hk : cs.length < k) : finCoeffS cs k = 0 := by
  unfold finCoeffS
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega)]; simp

theorem finCoeffS_succ (cs : List ℤ) (k : ℕ) :
    finCoeffS cs (k + 1) = (cs.getD k 0 : ℝ) / 1099511627776 := by
  unfold finCoeffS; simp

theorem trialSeqS_abs_le (cs : List ℤ) (tail : List TailQ) (k : ℕ) :
    |trialSeqS cs tail k| ≤ |finCoeffS cs k| + tailMajorant tail k := by
  have hm := tailMajorant_nonneg tail k
  unfold trialSeqS
  by_cases hk : k = 0
  · subst hk; simp; exact add_nonneg (abs_nonneg _) hm
  · rw [if_neg hk]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (Complex.abs_re_le_norm _).trans ((listNorm_sum_le _).trans (le_of_eq ?_))
    unfold tailMajorant
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro zr _
    simp [norm_mul, norm_pow]

theorem finCoeffS_summable (cs : List ℤ) :
    Summable (fun k => |finCoeffS cs k|) ∧
      Summable (fun k : ℕ => (k : ℝ) * |finCoeffS cs k|) := by
  constructor
  · apply summable_of_ne_finset_zero (s := Finset.range (cs.length + 1))
    intro k hk
    rw [finCoeffS_eq_zero (by simp at hk; omega)]; simp
  · apply summable_of_ne_finset_zero (s := Finset.range (cs.length + 1))
    intro k hk
    rw [finCoeffS_eq_zero (by simp at hk; omega)]; simp

theorem trialSeqS_summable {cs : List ℤ} {tail : List TailQ} (h : tailsInDisk tail = true) :
    Summable (fun k => |trialSeqS cs tail k|) ∧
      Summable (fun k : ℕ => (k : ℝ) * |trialSeqS cs tail k|) := by
  obtain ⟨f1, f2⟩ := finCoeffS_summable cs
  obtain ⟨g1, g2⟩ := tailMajorant_summable h
  refine ⟨(f1.add g1).of_nonneg_of_le (fun k => abs_nonneg _) (trialSeqS_abs_le cs tail),
    (f2.add g2).of_nonneg_of_le (fun k => by positivity) (fun k => ?_)⟩
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (trialSeqS_abs_le cs tail k) (Nat.cast_nonneg k)

end CatalanMeasure.CellCert
