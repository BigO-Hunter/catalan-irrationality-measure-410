module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Submission.CatalanMeasure.CellCert.EvalS
public import Submission.CatalanMeasure.GenD.Cert.WLog.P1

@[expose] public section

open CatalanMeasure.Cert OAI.InternalCatalan
namespace CatalanMeasure.WLog

/-! # Weight-scaled logarithm evaluator: generic series lemmas -/


/-- series length from the weight: `w * 2^-(base*(2n+1)) <= 2^-40` -/
def lenL (w : ℚ) : ℕ :=
  let A := 42 + w.num.natAbs.log2
  let D := w.den.log2 + 9
  if A ≤ D then 0 else (A - D + 17) / 18

def lenA (w : ℚ) : ℕ :=
  let A := 42 + w.num.natAbs.log2
  let D := w.den.log2 + 7
  if A ≤ D then 0 else (A - D + 13) / 14

/-- one weighted log term: cutoff, or `lnQ` (+ `argQ` when the weight `d` is not zero) -/
def wTerm (nL nA : ℕ) (t : LogTerm) : Option (ℚ × ℚ) :=
  let q := t.a * t.a + t.b * t.b
  match findExpY q with
  | none => none
  | some (m, y) =>
    let cut := qabs t.c * (qabs (m : ℚ) + 1) / 2 + 4 * qabs t.d
    if cut ≤ 1 / 2 ^ 40 then some (0, cut) else
    match lnQy nL y m with
    | none => none
    | some (l, el) =>
      if t.d = 0 then some (t.c / 2 * l, qabs t.c / 2 * el)
      else match argQ nA t.a t.b with
        | none => none
        | some (ar, ea) => some (t.c / 2 * l - t.d * ar, qabs t.c / 2 * el + qabs t.d * ea)

theorem wTerm_spec {nL nA : ℕ} {t : LogTerm} {v e : ℚ} (h : wTerm nL nA t = some (v, e)) :
    |t.val - (v : ℝ)| ≤ (e : ℝ) := by
  have hval : t.val = (t.c : ℝ) * (Real.log ((t.a * t.a + t.b * t.b : ℚ) : ℝ) / 2) -
      (t.d : ℝ) * Complex.arg ⟨(t.a : ℝ), (t.b : ℝ)⟩ := by
    have := barrierComplexLog_weighted_re (barrierComplex t.c t.d) ⟨(t.a : ℝ), (t.b : ℝ)⟩
    have h0 : t.val = (barrierComplex t.c t.d * Complex.log ⟨(t.a : ℝ), (t.b : ℝ)⟩).re := rfl
    rw [h0, this]
    simp only [barrierComplex]
    push_cast
    ring_nf
  have hqc : ((qabs t.c : ℚ) : ℝ) = |(t.c : ℝ)| := by rw [qabs_eq]; push_cast; rfl
  have hqd : ((qabs t.d : ℚ) : ℝ) = |(t.d : ℝ)| := by rw [qabs_eq]; push_cast; rfl
  unfold wTerm at h
  simp only at h
  split at h
  · simp at h
  · rename_i m y hmy
    obtain ⟨hyq, hy1, hy2⟩ := findExpY_spec hmy
    have hqy : ((t.a * t.a + t.b * t.b : ℚ) : ℝ) = (2 : ℝ) ^ m * (y : ℝ) := by
      have h0 := congrArg (fun t : ℚ => (t : ℝ)) hyq
      have h1 : (y : ℝ) = ((t.a * t.a + t.b * t.b : ℚ) : ℝ) / (2 : ℝ) ^ m := by simpa using h0
      rw [h1]; field_simp
    have hqm : ((qabs (m : ℚ) : ℚ) : ℝ) = |(m : ℝ)| := by rw [qabs_eq]; push_cast; rfl
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hl : |Real.log ((t.a * t.a + t.b * t.b : ℚ) : ℝ)| ≤ |(m : ℝ)| + 1 := by
        rw [hqy]; exact log_crude' hy1 hy2
      have harg := Complex.abs_arg_le_pi (⟨(t.a : ℝ), (t.b : ℝ)⟩ : ℂ)
      have hpi := Real.pi_lt_four
      rw [hval, Rat.cast_zero, sub_zero]
      push_cast
      rw [hqc, hqd, hqm]
      have h1 : |(t.c : ℝ) * (Real.log ((t.a * t.a + t.b * t.b : ℚ) : ℝ) / 2)| ≤
          |(t.c : ℝ)| * ((|(m : ℝ)| + 1) / 2) := by
        rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        linarith
      have h2 : |(t.d : ℝ) * Complex.arg ⟨(t.a : ℝ), (t.b : ℝ)⟩| ≤ |(t.d : ℝ)| * 4 := by
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        linarith [Real.pi_lt_four]
      have h3 := abs_sub ((t.c : ℝ) * (Real.log ((t.a * t.a + t.b * t.b : ℚ) : ℝ) / 2))
        ((t.d : ℝ) * Complex.arg ⟨(t.a : ℝ), (t.b : ℝ)⟩)
      push_cast at h1 h2 h3 ⊢
      linarith
    · split at h
      · simp at h
      · rename_i l el hl
        have hl' : |Real.log ((t.a * t.a + t.b * t.b : ℚ) : ℝ) - (l : ℝ)| ≤ (el : ℝ) := by
          rw [hqy]; exact lnQy_spec hy1 hy2 hl
        set L : ℝ := Real.log ((t.a * t.a + t.b * t.b : ℚ) : ℝ) with hL
        set Ar : ℝ := Complex.arg ⟨(t.a : ℝ), (t.b : ℝ)⟩ with hAr
        split at h
        · rename_i hd
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hd0 : (t.d : ℝ) = 0 := by exact_mod_cast hd
          rw [hval, hd0]
          push_cast
          rw [hqc]
          have e : (t.c : ℝ) * (L / 2) - 0 * Ar -
              (t.c : ℝ) / 2 * (l : ℝ) = ((t.c : ℝ) / 2) * (L - (l : ℝ)) := by ring
          rw [e, abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          have := mul_le_mul_of_nonneg_left hl' (div_nonneg (abs_nonneg (t.c : ℝ)) (by norm_num : (0:ℝ) ≤ 2))
          linarith
        · split at h
          · simp at h
          · rename_i ar ea hA
            have hA' := argQ_spec hA
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [hval]
            push_cast
            rw [hqc, hqd]
            have e : (t.c : ℝ) * (L / 2) - (t.d : ℝ) * Ar -
                ((t.c : ℝ) / 2 * (l : ℝ) - (t.d : ℝ) * (ar : ℝ)) =
                ((t.c : ℝ) / 2) * (L - (l : ℝ)) -
                (t.d : ℝ) * (Ar - (ar : ℝ)) := by ring
            rw [e]
            have h1 : |((t.c : ℝ) / 2) * (L - (l : ℝ))| ≤
                |(t.c : ℝ)| / 2 * (el : ℝ) := by
              rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
              exact mul_le_mul_of_nonneg_left hl' (div_nonneg (abs_nonneg (t.c : ℝ)) (by norm_num : (0:ℝ) ≤ 2))
            have h2 : |(t.d : ℝ) * (Ar - (ar : ℝ))| ≤ |(t.d : ℝ)| * (ea : ℝ) := by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_left hA' (abs_nonneg _)
            have h3 := abs_sub (((t.c : ℝ) / 2) * (L - (l : ℝ)))
              ((t.d : ℝ) * (Ar - (ar : ℝ)))
            linarith

/-- the plain sum of weighted log terms, each rounded to the `2^-128` grid -/
def wTermA (t : LogTerm) : Option (ℚ × ℚ) := wTerm (lenL t.c) (lenA t.d) t

def sumLogsW : List LogTerm → Option (ℚ × ℚ)
  | [] => some (0, 0)
  | t :: l =>
    match wTermA t, sumLogsW l with
    | some (q, e0), some (v, e) => some ((CatalanMeasure.CellCert.encDiv q.num q.den).1 + v,
        e0 + (CatalanMeasure.CellCert.encDiv q.num q.den).2 + e)
    | _, _ => none

theorem sumLogsW_spec {l : List LogTerm} {v e : ℚ}
    (h : sumLogsW l = some (v, e)) : |(l.map LogTerm.val).sum - (v : ℝ)| ≤ (e : ℝ) := by
  induction l generalizing v e with
  | nil =>
    simp only [sumLogsW, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons t l ih =>
    simp only [sumLogsW] at h
    split at h
    · rename_i q e0 v' e' hq hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 := wTerm_spec hq
      have h2 := ih hl
      have h3 := CatalanMeasure.CellCert.encDiv_spec q.num q.den_pos
      have hq' : ((q.num : ℝ) / (q.den : ℝ)) = (q : ℝ) := by rw [Rat.cast_def]
      rw [hq'] at h3
      simp only [List.map_cons, List.sum_cons]
      push_cast
      rw [abs_le] at h1 h2 h3 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    · simp at h


/-! ### integer front end (v2): the same decisions as `findExpY` / `lnQy` / `findOctF` / `atanPos`, with `Nat`/`Int` arithmetic -/

/-- `(m, P, Q)` with `N2 / L2 = 2^m * (P / Q)` and `Q ≤ P ≤ 2 Q` -/
def expPQ (N2 L2 : ℕ) : Option (ℤ × ℕ × ℕ) :=
  if 0 < N2 ∧ 0 < L2 then
    let m0 : ℤ := (N2.log2 : ℤ) - (L2.log2 : ℤ)
    let P0 : ℕ := N2 <<< (-m0).toNat
    let Q0 : ℕ := L2 <<< m0.toNat
    if Q0 ≤ P0 ∧ P0 ≤ 2 * Q0 then some (m0, P0, Q0)
    else if Q0 ≤ 2 * P0 ∧ 2 * P0 ≤ 2 * Q0 then some (m0 - 1, 2 * P0, Q0) else none
  else none

theorem expPQ_core (N2 L2 : ℕ) (hN : 0 < N2) (hL : 0 < L2) (m0 : ℤ) :
    (N2 : ℝ) / (L2 : ℝ) = (2 : ℝ) ^ m0 *
      (((N2 <<< (-m0).toNat : ℕ) : ℝ) / ((L2 <<< m0.toNat : ℕ) : ℝ)) := by
  have hN' : (0 : ℝ) < N2 := by exact_mod_cast hN
  have hL' : (0 : ℝ) < L2 := by exact_mod_cast hL
  rcases Int.eq_nat_or_neg m0 with ⟨t, rfl | rfl⟩
  · have h1 : (-(t : ℤ)).toNat = 0 := by omega
    have h2 : ((t : ℤ)).toNat = t := by omega
    rw [h1, h2, Nat.shiftLeft_eq, Nat.shiftLeft_eq, zpow_natCast]
    push_cast
    field_simp
  · have h1 : (-(-(t : ℤ))).toNat = t := by omega
    have h2 : (-(t : ℤ)).toNat = 0 := by omega
    rw [h1, h2, Nat.shiftLeft_eq, Nat.shiftLeft_eq, zpow_neg, zpow_natCast]
    push_cast
    field_simp

theorem expPQ_spec {N2 L2 P Q : ℕ} {m : ℤ} (h : expPQ N2 L2 = some (m, P, Q)) :
    0 < Q ∧ Q ≤ P ∧ P ≤ 2 * Q ∧ (N2 : ℝ) / (L2 : ℝ) = (2 : ℝ) ^ m * ((P : ℝ) / (Q : ℝ)) := by
  unfold expPQ at h
  simp only at h
  split_ifs at h with h0 h1 h2
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hQ : 0 < (L2 <<< ((N2.log2 : ℤ) - (L2.log2 : ℤ)).toNat) := by
      rw [Nat.shiftLeft_eq]; exact Nat.mul_pos h0.2 (by positivity)
    exact ⟨hQ, h1.1, h1.2, expPQ_core N2 L2 h0.1 h0.2 _⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hQ : 0 < (L2 <<< ((N2.log2 : ℤ) - (L2.log2 : ℤ)).toNat) := by
      rw [Nat.shiftLeft_eq]; exact Nat.mul_pos h0.2 (by positivity)
    refine ⟨hQ, h2.1, h2.2, ?_⟩
    have := expPQ_core N2 L2 h0.1 h0.2 ((N2.log2 : ℤ) - (L2.log2 : ℤ))
    generalize ((N2.log2 : ℤ) - (L2.log2 : ℤ)) = m0 at this hQ ⊢
    have hz : (2 : ℝ) ^ (m0 - 1) = (2 : ℝ) ^ m0 / 2 := by
      rw [zpow_sub₀ (by norm_num), zpow_one]
    rw [this, hz]
    push_cast
    have hQ' : (0 : ℝ) < ((L2 <<< m0.toNat : ℕ) : ℝ) := by exact_mod_cast hQ
    field_simp

/-- `Real.log (2^m * (P/Q))` for `Q ≤ P ≤ 2Q`: node `1 + j/256`, `atanh` series, integer `j, N, D` -/
def lnQP (n : ℕ) (m : ℤ) (P Q : ℕ) : Option (ℚ × ℚ) :=
  let j : ℕ := (P - Q) * 256 / Q
  let N : ℤ := 256 * (P : ℤ) - (256 + (j : ℤ)) * Q
  let D : ℤ := 256 * (P : ℤ) + (256 + (j : ℤ)) * Q
  if j ≤ 256 ∧ 0 ≤ N ∧ 0 < D ∧ 512 * N ≤ D then
    let w : ℚ := Rat.divInt N D
    some ((m : ℚ) * lnTab 256 + lnTab j + 2 * w * serH (w ^ 2) n 1,
      ((qabs (m : ℚ)) + 1) * (1 / 2 ^ 95) + 2 * (1 / 512) ^ (2 * n + 1) / (1 - (1 / 512) ^ 2))
  else none

theorem lnQP_spec {n : ℕ} {P Q : ℕ} {v e : ℚ} {m : ℤ} (hQ : 0 < Q) (hPQ : Q ≤ P) (hP2 : P ≤ 2 * Q)
    (h : lnQP n m P Q = some (v, e)) :
    |Real.log ((2 : ℝ) ^ m * ((P : ℝ) / (Q : ℝ))) - (v : ℝ)| ≤ (e : ℝ) := by
  unfold lnQP at h
  simp only at h
  split_ifs at h with hc
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hj, hN0, hD0, hND⟩ := hc
    set j : ℕ := (P - Q) * 256 / Q with hjdef
    set N : ℤ := 256 * (P : ℤ) - (256 + (j : ℤ)) * Q with hNdef
    set D : ℤ := 256 * (P : ℤ) + (256 + (j : ℤ)) * Q with hDdef
    set w : ℚ := Rat.divInt N D with hwdef
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hPR : (Q : ℝ) ≤ P := by exact_mod_cast hPQ
    set yy : ℝ := (P : ℝ) / (Q : ℝ) with hyy
    have hyR1 : (1 : ℝ) ≤ yy := by rw [hyy, le_div_iff₀ hQR]; linarith
    have hjR : (j : ℝ) ≤ 256 := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := by positivity
    set yj : ℝ := 1 + (j : ℝ) / 256 with hyjdef
    have hyj1 : (1 : ℝ) ≤ yj := by rw [hyjdef]; linarith [div_nonneg hj0 (by norm_num : (0:ℝ) ≤ 256)]
    have hyj0 : yj ≠ 0 := ne_of_gt (by linarith)
    have hlogq : Real.log ((2 : ℝ) ^ m * yy) = (m : ℝ) * Real.log 2 + Real.log yy := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_zpow]
    have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD0
    have hNR : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN0
    have hwc : (w : ℝ) = (N : ℝ) / (D : ℝ) := by
      rw [hwdef, Rat.divInt_eq_div]; push_cast; rfl
    have hw0R : (0 : ℝ) ≤ (w : ℝ) := by
      rw [hwc]; exact div_nonneg hNR hDR.le
    have hw1R : (w : ℝ) ≤ 1 / 512 := by
      rw [hwc, div_le_iff₀ hDR]
      have : (512 : ℝ) * N ≤ D := by exact_mod_cast hND
      linarith
    have hwR : (w : ℝ) = (yy - yj) / (yy + yj) := by
      have h1 : yy + yj ≠ 0 := by linarith
      rw [hwc, div_eq_div_iff (ne_of_gt hDR) h1, hNdef, hDdef, hyy, hyjdef]
      push_cast
      field_simp
    have hratio : (1 + (w : ℝ)) / (1 - (w : ℝ)) = yy / yj := by
      have h3 : (1 : ℝ) - (w : ℝ) ≠ 0 := ne_of_gt (by linarith)
      have h1 : yy + yj ≠ 0 := by linarith
      rw [div_eq_div_iff h3 hyj0, hwR]
      field_simp
      ring
    have hlogy : Real.log yy = Real.log yj + Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) := by
      rw [hratio, ← Real.log_mul hyj0 (by positivity)]
      congr 1
      field_simp
    have hat := atanh_tail hw0R (by linarith) n
    have hS := serH_spec (w ^ 2) n 1
    have hT1 := lnTab_spec hj
    have hT2 := lnTab_spec (le_refl 256)
    rw [← hyjdef] at hT1
    have h2 : (1 : ℝ) + ((256 : ℕ) : ℝ) / 256 = 2 := by norm_num
    rw [h2] at hT2
    have hmono : 2 * (w : ℝ) ^ (2 * n + 1) / (1 - (w : ℝ) ^ 2) ≤
        2 * (1 / 512 : ℝ) ^ (2 * n + 1) / (1 - (1 / 512 : ℝ) ^ 2) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) _
      · have := pow_le_pow_left₀ hw0R hw1R (2 * n + 1); linarith
      · have : (w : ℝ) ^ 2 ≤ (1 / 512 : ℝ) ^ 2 := pow_le_pow_left₀ hw0R hw1R 2
        linarith
    have hm_abs : ((qabs (m : ℚ) : ℚ) : ℝ) = |(m : ℝ)| := by
      rw [qabs_eq]; push_cast; rfl
    push_cast
    rw [hm_abs]
    have hsum : ((serH (w ^ 2) n 1 : ℚ) : ℝ) =
        ∑ i ∈ Finset.range n, ((w : ℝ) ^ 2) ^ i / ((1 + 2 * i : ℕ) : ℝ) := by
      rw [hS]; push_cast; rfl
    have hsum' : (2 : ℝ) * (w : ℝ) * ((serH (w ^ 2) n 1 : ℚ) : ℝ) =
        2 * (w : ℝ) * ∑ i ∈ Finset.range n, ((w : ℝ) ^ 2) ^ i / ((1 + 2 * i : ℕ) : ℝ) := by rw [hsum]
    have hmabs : |(m : ℝ) * (Real.log 2 - (lnTab 256 : ℝ))| ≤ |(m : ℝ)| * (1 / 2 ^ 95) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hT2 (abs_nonneg _)
    have e : Real.log ((2 : ℝ) ^ m * yy) - ((m : ℝ) * (lnTab 256 : ℝ) + (lnTab j : ℝ) +
        2 * (w : ℝ) * ((serH (w ^ 2) n 1 : ℚ) : ℝ)) =
        (m : ℝ) * (Real.log 2 - (lnTab 256 : ℝ)) + (Real.log yj - (lnTab j : ℝ)) +
        (Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) -
          2 * (w : ℝ) * ∑ i ∈ Finset.range n, ((w : ℝ) ^ 2) ^ i / ((1 + 2 * i : ℕ) : ℝ)) := by
      rw [hlogq, hlogy, hsum']; ring
    rw [e]
    have t1 := abs_add_le ((m : ℝ) * (Real.log 2 - (lnTab 256 : ℝ)) + (Real.log yj - (lnTab j : ℝ)))
      (Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) -
          2 * (w : ℝ) * ∑ i ∈ Finset.range n, ((w : ℝ) ^ 2) ^ i / ((1 + 2 * i : ℕ) : ℝ))
    have t2 := abs_add_le ((m : ℝ) * (Real.log 2 - (lnTab 256 : ℝ))) (Real.log yj - (lnTab j : ℝ))
    nlinarith [t1, t2, hmabs, hT1, hat, hmono]


/-- `arctan (S/R)` for `S/R ≥ 0` with integer node arithmetic -/
def atanPosI (n : ℕ) (S R : ℕ) : Option (ℚ × ℚ) :=
  let j : ℕ := S * 128 / R
  let N : ℤ := 128 * (S : ℤ) - (j : ℤ) * R
  let D : ℤ := 128 * (R : ℤ) + (j : ℤ) * S
  if j ≤ 64 ∧ 0 ≤ N ∧ 0 < D ∧ 128 * N ≤ D then
    let s : ℚ := Rat.divInt N D
    some (atTab j + s * serH (-(s ^ 2)) n 1,
      1 / 2 ^ 95 + (1 / 128) ^ (2 * n + 1) / (1 - (1 / 128) ^ 2))
  else none

theorem atanPosI_spec {n S R : ℕ} {v e : ℚ} (hR : 0 < R) (h : atanPosI n S R = some (v, e)) :
    |Real.arctan ((S : ℝ) / (R : ℝ)) - (v : ℝ)| ≤ (e : ℝ) := by
  unfold atanPosI at h
  simp only at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hj, hN0, hD0, hND⟩ := hc
  set j : ℕ := S * 128 / R with hjdef
  set N : ℤ := 128 * (S : ℤ) - (j : ℤ) * R with hNdef
  set D : ℤ := 128 * (R : ℤ) + (j : ℤ) * S with hDdef
  set s : ℚ := Rat.divInt N D with hsdef
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hSR : (0 : ℝ) ≤ S := by positivity
  have htn0 : (0 : ℝ) ≤ (S : ℝ) / (R : ℝ) := by positivity
  set tn : ℝ := (S : ℝ) / (R : ℝ) with htndef
  have hj0 : (0 : ℝ) ≤ j := by positivity
  set tj : ℝ := (j : ℝ) / 128 with htjdef
  have htj0 : (0 : ℝ) ≤ tj := by positivity
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD0
  have hNR : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN0
  have hsc : (s : ℝ) = (N : ℝ) / (D : ℝ) := by
    rw [hsdef, Rat.divInt_eq_div]; push_cast; rfl
  have hs0R : (0 : ℝ) ≤ (s : ℝ) := by rw [hsc]; exact div_nonneg hNR hDR.le
  have hs1R : (s : ℝ) ≤ 1 / 128 := by
    rw [hsc, div_le_iff₀ hDR]
    have : (128 : ℝ) * N ≤ D := by exact_mod_cast hND
    linarith
  have hsR : (s : ℝ) = (tn - tj) / (1 + tn * tj) := by
    have h1 : (1 : ℝ) + tn * tj ≠ 0 := by positivity
    rw [hsc, div_eq_div_iff (ne_of_gt hDR) h1, hNdef, hDdef, htndef, htjdef]
    push_cast
    field_simp
  have hadd := Real.arctan_add (x := tn) (y := -tj) (by nlinarith)
  rw [Real.arctan_neg] at hadd
  have hsq : (tn + -tj) / (1 - tn * -tj) = (s : ℝ) := by
    rw [hsR]; ring_nf
  rw [hsq] at hadd
  have hT := atTab_spec hj
  rw [← htjdef] at hT
  have hat := atan_tail hs0R (by linarith) n
  have hS := serH_spec (-(s ^ 2)) n 1
  have hsum : ((serH (-(s ^ 2)) n 1 : ℚ) : ℝ) =
      ∑ i ∈ Finset.range n, (-((s : ℝ) ^ 2)) ^ i / ((1 + 2 * i : ℕ) : ℝ) := by
    rw [hS]; push_cast; rfl
  have hmono : (s : ℝ) ^ (2 * n + 1) / (1 - (s : ℝ) ^ 2) ≤
      (1 / 128 : ℝ) ^ (2 * n + 1) / (1 - (1 / 128 : ℝ) ^ 2) := by
    apply div_le_div₀ (by positivity) _ (by norm_num) _
    · exact pow_le_pow_left₀ hs0R hs1R (2 * n + 1)
    · have : (s : ℝ) ^ 2 ≤ (1 / 128 : ℝ) ^ 2 := pow_le_pow_left₀ hs0R hs1R 2
      linarith
  push_cast
  rw [hsum]
  have e : Real.arctan tn - ((atTab j : ℝ) + (s : ℝ) * ∑ i ∈ Finset.range n, (-((s : ℝ) ^ 2)) ^ i / ((1 + 2 * i : ℕ) : ℝ)) =
      (Real.arctan tj - (atTab j : ℝ)) +
      (Real.arctan (s : ℝ) - (s : ℝ) * ∑ i ∈ Finset.range n, (-((s : ℝ) ^ 2)) ^ i / ((1 + 2 * i : ℕ) : ℝ)) := by
    linarith [hadd]
  rw [e]
  have := abs_add_le (Real.arctan tj - (atTab j : ℝ))
    (Real.arctan (s : ℝ) - (s : ℝ) * ∑ i ∈ Finset.range n, (-((s : ℝ) ^ 2)) ^ i / ((1 + 2 * i : ℕ) : ℝ))
  linarith [hT, hat, hmono]
  all_goals simp at h

def atanI (n : ℕ) (s r : ℤ) : Option (ℚ × ℚ) :=
  match atanPosI n s.natAbs r.toNat with
  | none => none
  | some (v, e) => some (if s < 0 then -v else v, e)

theorem atanI_spec {n : ℕ} {s r : ℤ} {v e : ℚ} (hr : 0 < r) (h : atanI n s r = some (v, e)) :
    |Real.arctan ((s : ℝ) / (r : ℝ)) - (v : ℝ)| ≤ (e : ℝ) := by
  unfold atanI at h
  split at h
  · simp at h
  · rename_i v' e' hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hrn : (r.toNat : ℝ) = (r : ℝ) := by
      have : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr.le
      exact_mod_cast this
    have hR : 0 < r.toNat := by omega
    have h1 := atanPosI_spec hR hp
    rw [hrn] at h1
    have hsn : ((s.natAbs : ℕ) : ℝ) = |(s : ℝ)| := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    rw [hsn] at h1
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    by_cases hs : s < 0
    · have hsR : (s : ℝ) < 0 := by exact_mod_cast hs
      rw [abs_of_neg hsR] at h1
      rw [if_pos hs]
      have : (s : ℝ) / (r : ℝ) = -(-(s : ℝ) / (r : ℝ)) := by ring
      rw [this, Real.arctan_neg]
      push_cast
      rw [← abs_neg]
      convert h1 using 2
      ring
    · have hsR : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast not_lt.mp hs
      rw [abs_of_nonneg hsR] at h1
      rw [if_neg hs]
      exact h1

def rotCWI : ℕ → ℤ × ℤ → ℤ × ℤ
  | 0, p => p
  | n + 1, p => rotCWI n (p.1 + p.2, p.2 - p.1)

def rotCCWI : ℕ → ℤ × ℤ → ℤ × ℤ
  | 0, p => p
  | n + 1, p => rotCCWI n (p.1 - p.2, p.1 + p.2)

def octRotI (k : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  if 0 ≤ k then rotCWI k.toNat p else rotCCWI (-k).toNat p

theorem rotCW_scale (L : ℚ) : ∀ (n : ℕ) (p : ℤ × ℤ) (x y : ℚ), x = (p.1 : ℚ) / L → y = (p.2 : ℚ) / L →
    rotCW n (x, y) = (((rotCWI n p).1 : ℚ) / L, ((rotCWI n p).2 : ℚ) / L) := by
  intro n
  induction n with
  | zero => intro p x y hx hy; simp [rotCW, rotCWI, hx, hy]
  | succ n ih =>
    intro p x y hx hy
    simp only [rotCW, rotCWI]
    apply ih (p.1 + p.2, p.2 - p.1)
    · simp only [Int.cast_add]; rw [hx, hy]; ring
    · simp only [Int.cast_sub]; rw [hx, hy]; ring

theorem rotCCW_scale (L : ℚ) : ∀ (n : ℕ) (p : ℤ × ℤ) (x y : ℚ), x = (p.1 : ℚ) / L → y = (p.2 : ℚ) / L →
    rotCCW n (x, y) = (((rotCCWI n p).1 : ℚ) / L, ((rotCCWI n p).2 : ℚ) / L) := by
  intro n
  induction n with
  | zero => intro p x y hx hy; simp [rotCCW, rotCCWI, hx, hy]
  | succ n ih =>
    intro p x y hx hy
    simp only [rotCCW, rotCCWI]
    apply ih (p.1 - p.2, p.1 + p.2)
    · simp only [Int.cast_sub]; rw [hx, hy]; ring
    · simp only [Int.cast_add]; rw [hx, hy]; ring

theorem octRot_scale (L : ℚ) (k : ℤ) (p : ℤ × ℤ) :
    octRot k ((p.1 : ℚ) / L, (p.2 : ℚ) / L) =
      (((octRotI k p).1 : ℚ) / L, ((octRotI k p).2 : ℚ) / L) := by
  unfold octRot octRotI
  split_ifs
  · exact rotCW_scale L _ p _ _ rfl rfl
  · exact rotCCW_scale L _ p _ _ rfl rfl

def octOKI (k : ℤ) (p : ℤ × ℤ) : Bool :=
  let q := octRotI k p
  decide (0 < q.1) && decide (2 * (q.2.natAbs : ℤ) ≤ q.1) && (k != 4 || decide (q.2 ≤ 0)) &&
    (k != -4 || decide (0 < q.2))

def octGuessI (a b : ℤ) : ℤ :=
  if 0 < a then
    (if 5 * (b.natAbs : ℤ) ≤ 2 * a then 0 else if 2 * (b.natAbs : ℤ) < 5 * a then (if 0 ≤ b then 1 else -1)
      else (if 0 ≤ b then 2 else -2))
  else
    (if 5 * (b.natAbs : ℤ) ≤ 2 * (a.natAbs : ℤ) then (if 0 ≤ b then 4 else -4)
      else if 2 * (b.natAbs : ℤ) < 5 * (a.natAbs : ℤ) then (if 0 ≤ b then 3 else -3)
      else (if 0 ≤ b then 2 else -2))

def findOctI (p : ℤ × ℤ) : Option ℤ :=
  let k := octGuessI p.1 p.2
  if octOKI k p = true ∧ |k| ≤ 4 then some k else octCandidates.find? (fun k => octOKI k p)

theorem findOctI_spec {p : ℤ × ℤ} {k : ℤ} (h : findOctI p = some k) :
    octOKI k p = true ∧ |k| ≤ 4 := by
  unfold findOctI at h
  simp only at h
  split_ifs at h with hc
  · simp only [Option.some.injEq] at h
    subst h; exact hc
  · have hk' := List.find?_some h
    have hkmem := List.mem_of_find?_eq_some h
    refine ⟨hk', ?_⟩
    simp only [octCandidates, List.mem_cons, List.not_mem_nil, or_false] at hkmem
    rcases hkmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem arg_of_octOKI {A B : ℤ} {L : ℕ} (hL : 0 < L) {k : ℤ} (hk : octOKI k (A, B) = true)
    (hkabs : |k| ≤ 4) :
    Complex.arg ⟨(A : ℝ) / (L : ℝ), (B : ℝ) / (L : ℝ)⟩ = (k : ℝ) * (Real.pi / 4) +
      Real.arctan (((octRotI k (A, B)).2 : ℝ) / ((octRotI k (A, B)).1 : ℝ)) := by
  unfold octOKI at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hk
  obtain ⟨⟨⟨hr, hs⟩, h4⟩, hm4⟩ := hk
  set r := (octRotI k (A, B)).1 with hrdef
  set s := (octRotI k (A, B)).2 with hsdef
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hrot0 := octRot_spec k (((A : ℚ) / L), ((B : ℚ) / L))
  have hsc : octRot k (((A : ℚ) / L), ((B : ℚ) / L)) = ((r : ℚ) / L, (s : ℚ) / L) :=
    octRot_scale (L : ℚ) k (A, B)
  rw [hsc] at hrot0
  have hrot : barrierOctantRotate k ⟨(A : ℝ) / L, (B : ℝ) / L⟩ = ⟨(r : ℝ) / L, (s : ℝ) / L⟩ := by
    have := hrot0
    push_cast at this
    exact this
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsabs : (2 : ℝ) * |(s : ℝ)| ≤ r := by
    have h1 : ((2 * (s.natAbs : ℤ) : ℤ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hs
    push_cast at h1
    exact h1
  have := barrierComplexArg_octant_rational k ⟨(A : ℝ) / L, (B : ℝ) / L⟩ ((r : ℝ) / L) ((s : ℝ) / L) hrot
    (div_pos hrR hLR)
    (by rw [abs_div, abs_of_pos hLR, div_div, div_le_div_iff₀ hLR (by positivity)]
        nlinarith [hsabs, hLR])
    hkabs
    (by intro hk4; rcases h4 with h4 | h4
        · exact absurd hk4 h4
        · exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h4) hLR.le)
    (by intro hk4; rcases hm4 with h4 | h4
        · exact absurd hk4 h4
        · exact div_pos (by exact_mod_cast h4) hLR)
  rw [this]
  congr 2
  field_simp

/-- `Complex.arg ((A + B i)/L)` -/
def argI (n : ℕ) (A B : ℤ) : Option (ℚ × ℚ) :=
  match findOctI (A, B) with
  | none => none
  | some k =>
    match atanI n (octRotI k (A, B)).2 (octRotI k (A, B)).1 with
    | none => none
    | some (v, e) => some ((k : ℚ) * PI4 + v, qabs (k : ℚ) * PI4E + e)

theorem argI_spec {n : ℕ} {A B : ℤ} {L : ℕ} (hL : 0 < L) {v e : ℚ} (h : argI n A B = some (v, e)) :
    |Complex.arg ⟨(A : ℝ) / (L : ℝ), (B : ℝ) / (L : ℝ)⟩ - (v : ℝ)| ≤ (e : ℝ) := by
  unfold argI at h
  split at h
  · simp at h
  · rename_i k hk
    split at h
    · simp at h
    · rename_i v' e' hat
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hok, hkabs⟩ := findOctI_spec hk
      have harg := arg_of_octOKI hL hok hkabs
      have hr : 0 < (octRotI k (A, B)).1 := by
        unfold octOKI at hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        exact hok.1.1.1
      have h1 := atanI_spec hr hat
      have h2 := pi4_spec
      rw [harg]
      have hqk : ((qabs (k : ℚ) : ℚ) : ℝ) = |(k : ℝ)| := by rw [qabs_eq]; push_cast; rfl
      have hc1 : (((k : ℚ) * PI4 + v' : ℚ) : ℝ) = (k : ℝ) * (PI4 : ℝ) + (v' : ℝ) := by push_cast; ring
      have hc2 : ((qabs (k : ℚ) * PI4E + e' : ℚ) : ℝ) = |(k : ℝ)| * (PI4E : ℝ) + (e' : ℝ) := by
        rw [Rat.cast_add, Rat.cast_mul, hqk]
      rw [hc1, hc2]
      have e : (k : ℝ) * (Real.pi / 4) + Real.arctan (((octRotI k (A, B)).2 : ℝ) / ((octRotI k (A, B)).1 : ℝ)) -
          ((k : ℝ) * (PI4 : ℝ) + (v' : ℝ)) =
          (k : ℝ) * (Real.pi / 4 - (PI4 : ℝ)) +
          (Real.arctan (((octRotI k (A, B)).2 : ℝ) / ((octRotI k (A, B)).1 : ℝ)) - (v' : ℝ)) := by ring
      rw [e]
      have t1 := abs_add_le ((k : ℝ) * (Real.pi / 4 - (PI4 : ℝ)))
        (Real.arctan (((octRotI k (A, B)).2 : ℝ) / ((octRotI k (A, B)).1 : ℝ)) - (v' : ℝ))
      have t2 : |(k : ℝ) * (Real.pi / 4 - (PI4 : ℝ))| ≤ |(k : ℝ)| * (PI4E : ℝ) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      linarith [t1, t2, h1]


def wTermI (nL nA : ℕ) (t : LogTerm) : Option (ℚ × ℚ) :=
  let A : ℤ := t.a.num * t.b.den
  let B : ℤ := t.b.num * t.a.den
  let L : ℕ := t.a.den * t.b.den
  match expPQ (A * A + B * B).toNat (L * L) with
  | none => none
  | some (m, P, Q) =>
    let cut := qabs t.c * (qabs (m : ℚ) + 1) / 2 + 4 * qabs t.d
    if t.c.num.natAbs.log2 + 38 ≤ t.c.den.log2 ∧ cut ≤ 1 / 2 ^ 40 then some (0, cut) else
    match lnQP nL m P Q with
    | none => none
    | some (l, el) =>
      if t.d = 0 then some (t.c / 2 * l, qabs t.c / 2 * el)
      else match argI nA A B with
        | none => none
        | some (ar, ea) => some (t.c / 2 * l - t.d * ar, qabs t.c / 2 * el + qabs t.d * ea)

theorem wTermI_spec {nL nA : ℕ} {t : LogTerm} {v e : ℚ} (h : wTermI nL nA t = some (v, e)) :
    |t.val - (v : ℝ)| ≤ (e : ℝ) := by
  have hval : t.val = (t.c : ℝ) * (Real.log ((t.a * t.a + t.b * t.b : ℚ) : ℝ) / 2) -
      (t.d : ℝ) * Complex.arg ⟨(t.a : ℝ), (t.b : ℝ)⟩ := by
    have := barrierComplexLog_weighted_re (barrierComplex t.c t.d) ⟨(t.a : ℝ), (t.b : ℝ)⟩
    have h0 : t.val = (barrierComplex t.c t.d * Complex.log ⟨(t.a : ℝ), (t.b : ℝ)⟩).re := rfl
    rw [h0, this]
    simp only [barrierComplex]
    push_cast
    ring_nf
  have hqc : ((qabs t.c : ℚ) : ℝ) = |(t.c : ℝ)| := by rw [qabs_eq]; push_cast; rfl
  have hqd : ((qabs t.d : ℚ) : ℝ) = |(t.d : ℝ)| := by rw [qabs_eq]; push_cast; rfl
  unfold wTermI at h
  simp only at h
  split at h
  · simp at h
  · rename_i m P Q hmy
    obtain ⟨hQ, hPQ, hP2, hid⟩ := expPQ_spec hmy
    set A : ℤ := t.a.num * t.b.den with hAdef
    set B : ℤ := t.b.num * t.a.den with hBdef
    set L : ℕ := t.a.den * t.b.den with hLdef
    have hLpos : 0 < L := Nat.mul_pos t.a.den_pos t.b.den_pos
    have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
    have hAL : (A : ℝ) / (L : ℝ) = (t.a : ℝ) := by
      rw [hAdef, hLdef, Rat.cast_def t.a]; push_cast; field_simp
    have hBL : (B : ℝ) / (L : ℝ) = (t.b : ℝ) := by
      rw [hBdef, hLdef, Rat.cast_def t.b]; push_cast; field_simp
    have hnn : (0 : ℤ) ≤ A * A + B * B := add_nonneg (mul_self_nonneg A) (mul_self_nonneg B)
    have hN2 : (((A * A + B * B).toNat : ℕ) : ℝ) = (A : ℝ) * A + (B : ℝ) * B := by
      have h2 : (((A * A + B * B).toNat : ℕ) : ℤ) = A * A + B * B := Int.toNat_of_nonneg hnn
      have h3 : (((A * A + B * B).toNat : ℕ) : ℝ) = ((((A * A + B * B).toNat : ℕ) : ℤ) : ℝ) :=
        (Int.cast_natCast _).symm
      rw [h3, h2]; push_cast; ring
    have hqy : ((t.a * t.a + t.b * t.b : ℚ) : ℝ) = (2 : ℝ) ^ m * ((P : ℝ) / (Q : ℝ)) := by
      rw [← hid, hN2]
      push_cast
      rw [← hAL, ← hBL]
      field_simp
    have hyq1 : (1 : ℚ) ≤ (P : ℚ) / (Q : ℚ) := by
      rw [le_div_iff₀ (by exact_mod_cast hQ)]
      exact_mod_cast (by omega : 1 * Q ≤ P)
    have hyq2 : (P : ℚ) / (Q : ℚ) ≤ 2 := by
      rw [div_le_iff₀ (by exact_mod_cast hQ)]
      exact_mod_cast hP2
    have hyc : (((P : ℚ) / (Q : ℚ) : ℚ) : ℝ) = (P : ℝ) / (Q : ℝ) := by push_cast; rfl
    have hz : (⟨(A : ℝ) / (L : ℝ), (B : ℝ) / (L : ℝ)⟩ : ℂ) = ⟨(t.a : ℝ), (t.b : ℝ)⟩ := by
      rw [hAL, hBL]
    have hArAL : Complex.arg ⟨(A : ℝ) / (L : ℝ), (B : ℝ) / (L : ℝ)⟩ =
        Complex.arg ⟨(t.a : ℝ), (t.b : ℝ)⟩ := by rw [hz]
    have hqm : ((qabs (m : ℚ) : ℚ) : ℝ) = |(m : ℝ)| := by rw [qabs_eq]; push_cast; rfl
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hl : |Real.log ((t.a * t.a + t.b * t.b : ℚ) : ℝ)| ≤ |(m : ℝ)| + 1 := by
        rw [hqy]
        have := log_crude' (m := m) hyq1 hyq2
        rw [hyc] at this
        exact this
      have harg := Complex.abs_arg_le_pi (⟨(t.a : ℝ), (t.b : ℝ)⟩ : ℂ)
      have hpi := Real.pi_lt_four
      rw [hval, Rat.cast_zero, sub_zero]
      push_cast
      rw [hqc, hqd, hqm]
      have h1 : |(t.c : ℝ) * (Real.log ((t.a * t.a + t.b * t.b : ℚ) : ℝ) / 2)| ≤
          |(t.c : ℝ)| * ((|(m : ℝ)| + 1) / 2) := by
        rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        linarith
      have h2 : |(t.d : ℝ) * Complex.arg ⟨(t.a : ℝ), (t.b : ℝ)⟩| ≤ |(t.d : ℝ)| * 4 := by
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        linarith [Real.pi_lt_four]
      have h3 := abs_sub ((t.c : ℝ) * (Real.log ((t.a * t.a + t.b * t.b : ℚ) : ℝ) / 2))
        ((t.d : ℝ) * Complex.arg ⟨(t.a : ℝ), (t.b : ℝ)⟩)
      push_cast at h1 h2 h3 ⊢
      linarith
    · split at h
      · simp at h
      · rename_i l el hl
        have hl' : |Real.log ((t.a * t.a + t.b * t.b : ℚ) : ℝ) - (l : ℝ)| ≤ (el : ℝ) := by
          rw [hqy]; exact lnQP_spec hQ hPQ hP2 hl
        set L : ℝ := Real.log ((t.a * t.a + t.b * t.b : ℚ) : ℝ) with hL
        set Ar : ℝ := Complex.arg ⟨(t.a : ℝ), (t.b : ℝ)⟩ with hAr
        split at h
        · rename_i hd
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hd0 : (t.d : ℝ) = 0 := by exact_mod_cast hd
          rw [hval, hd0]
          push_cast
          rw [hqc]
          have e : (t.c : ℝ) * (L / 2) - 0 * Ar -
              (t.c : ℝ) / 2 * (l : ℝ) = ((t.c : ℝ) / 2) * (L - (l : ℝ)) := by ring
          rw [e, abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          have := mul_le_mul_of_nonneg_left hl' (div_nonneg (abs_nonneg (t.c : ℝ)) (by norm_num : (0:ℝ) ≤ 2))
          linarith
        · split at h
          · simp at h
          · rename_i ar ea hA
            have hA' : |Ar - (ar : ℝ)| ≤ (ea : ℝ) := by
              rw [← hArAL]; exact argI_spec hLpos hA
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [hval]
            push_cast
            rw [hqc, hqd]
            have e : (t.c : ℝ) * (L / 2) - (t.d : ℝ) * Ar -
                ((t.c : ℝ) / 2 * (l : ℝ) - (t.d : ℝ) * (ar : ℝ)) =
                ((t.c : ℝ) / 2) * (L - (l : ℝ)) -
                (t.d : ℝ) * (Ar - (ar : ℝ)) := by ring
            rw [e]
            have h1 : |((t.c : ℝ) / 2) * (L - (l : ℝ))| ≤
                |(t.c : ℝ)| / 2 * (el : ℝ) := by
              rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
              exact mul_le_mul_of_nonneg_left hl' (div_nonneg (abs_nonneg (t.c : ℝ)) (by norm_num : (0:ℝ) ≤ 2))
            have h2 : |(t.d : ℝ) * (Ar - (ar : ℝ))| ≤ |(t.d : ℝ)| * (ea : ℝ) := by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_left hA' (abs_nonneg _)
            have h3 := abs_sub (((t.c : ℝ) / 2) * (L - (l : ℝ)))
              ((t.d : ℝ) * (Ar - (ar : ℝ)))
            linarith


def wTermAI (t : LogTerm) : Option (ℚ × ℚ) := wTermI (lenL t.c) (lenA t.d) t

/-- v2 sum (integer front end); same statement as `sumLogsW_spec` -/
def sumLogsWI : List LogTerm → Option (ℚ × ℚ)
  | [] => some (0, 0)
  | t :: l =>
    match wTermAI t, sumLogsWI l with
    | some (q, e0), some (v, e) => some ((CatalanMeasure.CellCert.encDiv q.num q.den).1 + v,
        e0 + (CatalanMeasure.CellCert.encDiv q.num q.den).2 + e)
    | _, _ => none

theorem sumLogsWI_spec {l : List LogTerm} {v e : ℚ}
    (h : sumLogsWI l = some (v, e)) : |(l.map LogTerm.val).sum - (v : ℝ)| ≤ (e : ℝ) := by
  induction l generalizing v e with
  | nil =>
    simp only [sumLogsWI, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons t l ih =>
    simp only [sumLogsWI] at h
    split at h
    · rename_i q e0 v' e' hq hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 := wTermI_spec hq
      have h2 := ih hl
      have h3 := CatalanMeasure.CellCert.encDiv_spec q.num q.den_pos
      have hq' : ((q.num : ℝ) / (q.den : ℝ)) = (q : ℝ) := by rw [Rat.cast_def]
      rw [hq'] at h3
      simp only [List.map_cons, List.sum_cons]
      push_cast
      rw [abs_le] at h1 h2 h3 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    · simp at h

end CatalanMeasure.WLog
