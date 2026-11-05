module
public import Submission.CatalanMeasure.Cert.IntegerAffine
public import Submission.CatalanMeasure.Cert.IntegerGap
@[expose] public section

open Set
namespace CatalanMeasure.Cert

/-- Only the final scalar division is rational; all coefficient arithmetic is integer. -/
def ipRatioBound (A Q : List ℤ) (cA cQ l w : ℚ) : Option ℚ :=
  let d : ℤ := (l.den : ℤ) * (w.den : ℤ)
  let a : ℤ := l.num * (w.den : ℤ)
  let h : ℤ := w.num * (l.den : ℤ)
  let TA := (ipAffine a h d A).2
  match (ipAffine a h d Q).2 with
  | [] => none
  | c :: q =>
    let low := |c| - ipAbsSum q
    if 0 < low ∧ 0 < cQ then
      some (|cA| * (d : ℚ) ^ Q.length * (ipAbsSum TA : ℚ) /
        (cQ * (d : ℚ) ^ A.length * (low : ℚ)))
    else none

theorem ipAffine_abs_bounds (p : List ℤ) {a h d : ℤ} {u : ℝ}
    (hd : (0 : ℝ) < d) (hu : |u| ≤ 1) :
    |ipEval p (((a : ℝ) + h * u) / d)| ≤
      (d : ℝ) * ipAbsSum (ipAffine a h d p).2 / (d : ℝ) ^ p.length := by
  have he := (ipAffine_eval p a h d u hd.ne').2
  have he' := congrArg abs he
  rw [abs_mul, abs_mul, abs_of_pos hd, abs_of_pos (pow_pos hd _)] at he'
  apply (le_div_iff₀ (pow_pos hd _)).mpr
  rw [mul_comm, ← he']
  exact mul_le_mul_of_nonneg_left (abs_ipEval_le _ hu) hd.le

theorem ipAffine_abs_lower (p : List ℤ) {a h d c : ℤ} {q : List ℤ} {u : ℝ}
    (hd : (0 : ℝ) < d) (hu : |u| ≤ 1) (hT : (ipAffine a h d p).2 = c :: q) :
    (d : ℝ) * ((|c| - ipAbsSum q : ℤ) : ℝ) / (d : ℝ) ^ p.length ≤
      |ipEval p (((a : ℝ) + h * u) / d)| := by
  have he := (ipAffine_eval p a h d u hd.ne').2
  have he' := congrArg abs he
  rw [abs_mul, abs_mul, abs_of_pos hd, abs_of_pos (pow_pos hd _), hT] at he'
  apply (div_le_iff₀ (pow_pos hd _)).mpr
  rw [mul_comm _ ((d : ℝ) ^ p.length), ← he']
  exact mul_le_mul_of_nonneg_left (abs_ipEval_ge c q hu) hd.le

theorem ipRatioBound_spec {A Q : List ℚ} {AZ QZ : List ℤ} {cA cQ l w B : ℚ}
    (hA : A = lpSmul cA (AZ.map (fun (z : ℤ) => (z : ℚ))))
    (hQ : Q = lpSmul cQ (QZ.map (fun (z : ℤ) => (z : ℚ))))
    (hw : 0 < w) (h : ipRatioBound AZ QZ cA cQ l w = some B)
    {t : ℝ} (ht : t ∈ Icc (l : ℝ) (l + w)) :
    lpEval Q t ≠ 0 ∧ |lpEval A t / lpEval Q t| ≤ B := by
  let d : ℤ := (l.den : ℤ) * (w.den : ℤ)
  let a : ℤ := l.num * (w.den : ℤ)
  let hh : ℤ := w.num * (l.den : ℤ)
  have hd : (0 : ℝ) < d := by
    dsimp [d]; push_cast
    exact mul_pos (Nat.cast_pos.mpr l.den_pos) (Nat.cast_pos.mpr w.den_pos)
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  let u : ℝ := (t - l) / w
  have hu0 : 0 ≤ u := div_nonneg (by linarith [ht.1]) hwR.le
  have hu1 : u ≤ 1 := (div_le_one hwR).mpr (by linarith [ht.2])
  have hu : |u| ≤ 1 := abs_le.mpr ⟨by linarith, hu1⟩
  have hs : ((a : ℝ) + hh * u) / d = t := by
    have ha : (a : ℝ) / d = l := rational_cross_endpoint l w
    have hh' : (hh : ℝ) / d = w := by
      dsimp [hh, d]; rw [mul_comm (l.den : ℤ)]
      exact rational_cross_endpoint w l
    rw [add_div, mul_div_right_comm, ha, hh']
    dsimp [u]; field_simp; ring
  unfold ipRatioBound at h
  change (match (ipAffine a hh d QZ).2 with
    | [] => none
    | c :: q => if 0 < |c| - ipAbsSum q ∧ 0 < cQ then
        some (|cA| * (d : ℚ) ^ QZ.length * (ipAbsSum (ipAffine a hh d AZ).2 : ℚ) /
          (cQ * (d : ℚ) ^ AZ.length * ((|c| - ipAbsSum q : ℤ) : ℚ)))
      else none) = some B at h
  split at h
  · simp at h
  · rename_i c q hT
    split_ifs at h with hpos
    · have hlow : (0 : ℝ) < ((|c| - ipAbsSum q : ℤ) : ℝ) := by exact_mod_cast hpos.1
      have hcQ : (0 : ℝ) < cQ := by exact_mod_cast hpos.2
      have hsum : (0 : ℝ) ≤ ipAbsSum (ipAffine a hh d AZ).2 := by
        exact_mod_cast ipAbsSum_nonneg (ipAffine a hh d AZ).2
      simp only [Option.some.injEq] at h
      have hupp := ipAffine_abs_bounds AZ (a := a) (h := hh) hd hu
      have hdown := ipAffine_abs_lower QZ (a := a) (h := hh) hd hu hT
      rw [hs] at hupp hdown
      have hQabs : 0 < |lpEval Q t| := by
        rw [hQ, lpEval_smul, lpEval_int_cast, abs_mul, abs_of_pos hcQ]
        exact mul_pos hcQ (lt_of_lt_of_le (by positivity) hdown)
      refine ⟨abs_pos.mp hQabs, ?_⟩
      rw [abs_div]
      have hupper : |lpEval A t| ≤ |(cA : ℝ)| * ((d : ℝ) * ipAbsSum (ipAffine a hh d AZ).2 / (d : ℝ) ^ AZ.length) := by
        rw [hA, lpEval_smul, lpEval_int_cast, abs_mul]
        exact mul_le_mul_of_nonneg_left hupp (abs_nonneg _)
      have hlower : (cQ : ℝ) * ((d : ℝ) * ((|c| - ipAbsSum q : ℤ) : ℝ) / (d : ℝ) ^ QZ.length) ≤ |lpEval Q t| := by
        rw [hQ, lpEval_smul, lpEval_int_cast, abs_mul, abs_of_pos hcQ]
        exact mul_le_mul_of_nonneg_left hdown hcQ.le
      calc
        _ ≤ (|(cA : ℝ)| * ((d : ℝ) * ipAbsSum (ipAffine a hh d AZ).2 / (d : ℝ) ^ AZ.length)) /
            ((cQ : ℝ) * ((d : ℝ) * ((|c| - ipAbsSum q : ℤ) : ℝ) / (d : ℝ) ^ QZ.length)) := by
          exact div_le_div₀ (by positivity) hupper (by positivity) hlower
        _ = B := by
          rw [← h]
          push_cast
          field_simp <;> ring
end CatalanMeasure.Cert
