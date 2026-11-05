module
public import Submission.CatalanMeasure.Parametric.TwoAdicColumns
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem paramSmoothingColumn_term_norm_le (P : Parameters) (N r i j : ℕ) (hi : i < P.H N) (hj : j < P.H N) :
    ‖((rowP P N r).coeff i : ℚ_[2]) * smoothingMoment i j‖ ≤
      8 * (P.H N : ℝ) ^ 2 / (2 : ℝ) ^ P.C N := by
  have hp := padic_two_norm_int_le_of_pow_dvd (param_rowP_coeff_two_pow_dvd P N r i)
  have hm := smoothingMoment_norm_le_uniform (P.H N) i j hi hj
  have hexp : P.C N ≤ (P.C N - 2 - i) + i + 2 := by omega
  have hpow : (2 : ℝ) ^ P.C N ≤
      (2 : ℝ) ^ ((P.C N - 2 - i) + i) * 4 := by
    calc
      (2 : ℝ) ^ P.C N ≤ (2 : ℝ) ^ (((P.C N - 2 - i) + i) + 2) :=
        pow_le_pow_right₀ (by norm_num) hexp
      _ = (2 : ℝ) ^ ((P.C N - 2 - i) + i) * 4 := by
        rw [pow_add]
        norm_num
  rw [norm_mul]
  calc
    ‖((rowP P N r).coeff i : ℚ_[2])‖ * ‖smoothingMoment i j‖ ≤
        (1 / (2 : ℝ) ^ (P.C N - 2 - i)) *
          (2 * (P.H N : ℝ) ^ 2 / (2 : ℝ) ^ i) :=
      mul_le_mul hp hm (norm_nonneg _) (by positivity)
    _ = 2 * (P.H N : ℝ) ^ 2 / (2 : ℝ) ^ ((P.C N - 2 - i) + i) := by
      rw [pow_add]
      ring
    _ ≤ 8 * (P.H N : ℝ) ^ 2 / (2 : ℝ) ^ P.C N := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 2 * (P.H N : ℝ) ^ 2)
      nlinarith only [hh]

theorem paramSmoothingColumn_norm_le (P : Parameters) (N r j : ℕ) (hj : j < P.H N) :
    ‖paramSmoothingColumn P N r j‖ ≤ 8 * (P.H N : ℝ) ^ 2 / (2 : ℝ) ^ P.C N := by
  unfold paramSmoothingColumn
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro i hi
  exact paramSmoothingColumn_term_norm_le P N r i j (Finset.mem_range.mp hi) hj







theorem paramSmoothing_full_minor_norm_le (P : Parameters) (N : ℕ)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N))) :
    ‖Matrix.det (fun r k : Fin (P.n N) => paramSmoothingColumn P N r.val (c k).val)‖ ≤
      (8 * (P.H N : ℝ) ^ 2 / (2 : ℝ) ^ P.C N) ^ P.n N := by
  have hentry (r k : Fin (P.n N)) :
      ‖paramSmoothingColumn P N r.val (c k).val‖ ≤
        8 * (P.H N : ℝ) ^ 2 / (2 : ℝ) ^ P.C N := by
    have hjL : (c k).val < P.L N := (Finset.mem_Ico.mp (c k).property).2
    have hLH : P.L N ≤ P.H N := by unfold Parameters.H Parameters.C; omega
    exact paramSmoothingColumn_norm_le P N r.val (c k).val (lt_of_lt_of_le hjL hLH)
  have hdet := padic_two_det_norm_le_prod_column
    (fun r k : Fin (P.n N) => paramSmoothingColumn P N r.val (c k).val)
    (fun _ => 8 * (P.H N : ℝ) ^ 2 / (2 : ℝ) ^ P.C N)
    (fun _ => by positivity) hentry
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hdet


end
end CatalanMeasure.Parametric
