module

public import Submission.CatalanMeasure.CellCert.Scaled

@[expose] public section

/-!
# Series formulas for `trialSeqS`

Scale `2^40` versions of OpenAI's `barrierTrialT_eq_finite_log`, `barrierTrialS_eq_finite_log`,
`barrierTrial_U_hasSum`, `barrierTrial_power_hasSum`.  The tail parts of the OpenAI statements do
not depend on the scale (`barrierTail_T_hasSum`, `barrierTail_S_hasSum`; the `U` and power tail
lemmas are private there and are re-proved here, they are a few lines each).
-/

open OAI.InternalCatalan Polynomial

namespace CatalanMeasure.CellCert
open CatalanMeasure.Cert

theorem trialSeqS_succ (cs : List ℤ) (tail : List TailQ) (k : ℕ) :
    trialSeqS cs tail (k + 1) = (cs.getD k 0 : ℝ) / 1099511627776 +
      (((tail.map TailQ.toC).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum).re := by
  unfold trialSeqS
  rw [if_neg (Nat.succ_ne_zero k), finCoeffS_succ]

theorem finS_hasSum (cs : List ℤ) (g : ℕ → ℝ) :
    HasSum (fun k : ℕ => finCoeffS cs (k + 1) * g k)
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) * g k) := by
  have hs : HasSum (fun k : ℕ => ((cs.getD k 0 : ℝ) / 1099511627776) * g k)
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) * g k) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [List.getD_eq_default cs 0 hlen]
    norm_num
  simpa only [finCoeffS_succ] using hs

private theorem tailRow_power_hasSum (z r : ℂ) (hz : ‖z‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => (r * z ^ (k + 1)).re * x ^ k)
      (r * z / barrierTailLinearDen z x).re := by
  have hratio : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |x| * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
      _ < 1 := by simpa only [one_mul] using hz
  have hc : HasSum (fun k : ℕ => (r * z ^ (k + 1)) * ((x ^ k : ℝ) : ℂ))
      (r * z / barrierTailLinearDen z x) := by
    convert (hasSum_geometric_of_norm_lt_one hratio).mul_left (r * z) using 1
    · funext k
      simp only [Complex.ofReal_pow, mul_pow, pow_succ]
      ring
    · simp only [barrierTailLinearDen, div_eq_mul_inv]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    Complex.hasSum_re hc

theorem tail_power_hasSum (tail : List (ℂ × ℂ)) (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re * x ^ k)
      (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re := by
  revert htail
  induction tail with
  | nil => intro _; simp
  | cons zr tail ih =>
      intro htail
      have hr := tailRow_power_hasSum zr.1 zr.2 (htail zr List.mem_cons_self) hx
      have ht := ih (fun w hw => htail w (List.mem_cons_of_mem _ hw))
      simpa only [List.map_cons, List.sum_cons, Complex.add_re, add_mul] using hr.add ht

private theorem tailRow_U_hasSum (z r : ℂ) (hz : ‖z‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => (r * z ^ (k + 1)).re * (Chebyshev.U ℝ (k : ℤ)).eval x)
      (r * z / barrierTailQuadraticDen z x).re := by
  have hc : HasSum (fun k : ℕ => (r * z ^ (k + 1)) *
        (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ))
      (r * z / barrierTailQuadraticDen z x) := by
    convert (barrierChebyshevU_hasSum hx hz).mul_left (r * z) using 1
    · funext k
      rw [pow_succ]
      ring
    · simp only [barrierTailQuadraticDen, div_eq_mul_inv, one_mul]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    Complex.hasSum_re hc

theorem tail_U_hasSum (tail : List (ℂ × ℂ)) (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re *
        (Chebyshev.U ℝ (k : ℤ)).eval x)
      (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re := by
  revert htail
  induction tail with
  | nil => intro _; simp
  | cons zr tail ih =>
      intro htail
      have hr := tailRow_U_hasSum zr.1 zr.2 (htail zr List.mem_cons_self) hx
      have ht := ih (fun w hw => htail w (List.mem_cons_of_mem _ hw))
      simpa only [List.map_cons, List.sum_cons, Complex.add_re, add_mul] using hr.add ht

/-! ### The four series of `trialSeqS` -/

theorem trialSeqS_T_hasSum (cs : List ℤ) {tail : List TailQ} (h : tailsInDisk tail = true)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => trialSeqS cs tail (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
        ((k + 1 : ℕ) : ℝ))
      ((∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)) -
      ((tail.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2))).sum.re / 2) := by
  have hf := finS_hasSum cs (fun k => (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
    ((k + 1 : ℕ) : ℝ))
  have hh := hf.add (barrierTail_T_hasSum _ (tailsInDisk_spec h) hx)
  have e : (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        ((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ))) =
      ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun k _ => by ring)
  rw [e] at hh
  convert hh using 1
  · funext k
    rw [trialSeqS_succ, finCoeffS_succ]
    ring
  · ring

theorem trialSeqS_T_eq_finite_log (cs : List ℤ) {tail : List TailQ} (h : tailsInDisk tail = true)
    {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialT (trialSeqS cs tail) x =
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)) -
      ((tail.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2))).sum.re / 2 :=
  (trialSeqS_T_hasSum cs h hx).tsum_eq

theorem trialSeqS_S_hasSum (cs : List ℤ) {tail : List TailQ} (h : tailsInDisk tail = true)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => trialSeqS cs tail (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
      ((∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) -
      ((tail.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - (x : ℂ) * zr.1))).sum.re) := by
  have hf := finS_hasSum cs (fun k => x ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
  have hh := hf.add (barrierTail_S_hasSum _ (tailsInDisk_spec h) hx)
  have e : (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        (x ^ (k + 1) / ((k + 1 : ℕ) : ℝ))) =
      ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun k _ => by ring)
  rw [e] at hh
  convert hh using 1
  funext k
  rw [trialSeqS_succ, finCoeffS_succ]
  ring

theorem trialSeqS_S_eq_finite_log (cs : List ℤ) {tail : List TailQ} (h : tailsInDisk tail = true)
    {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialS (trialSeqS cs tail) x =
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) -
      ((tail.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - (x : ℂ) * zr.1))).sum.re :=
  (trialSeqS_S_hasSum cs h hx).tsum_eq

theorem trialSeqS_U_hasSum (cs : List ℤ) {tail : List TailQ} (h : tailsInDisk tail = true)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => trialSeqS cs tail (k + 1) * (Chebyshev.U ℝ (k : ℤ)).eval x)
      ((∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        (Chebyshev.U ℝ (k : ℤ)).eval x) +
      ((tail.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) := by
  have hh := (finS_hasSum cs (fun k => (Chebyshev.U ℝ (k : ℤ)).eval x)).add
    (tail_U_hasSum _ (tailsInDisk_spec h) hx)
  convert hh using 1
  funext k
  rw [trialSeqS_succ, finCoeffS_succ]
  ring

theorem trialSeqS_power_hasSum (cs : List ℤ) {tail : List TailQ} (h : tailsInDisk tail = true)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => trialSeqS cs tail (k + 1) * x ^ k)
      ((∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) * x ^ k) +
      ((tail.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re) := by
  have hh := (finS_hasSum cs (fun k => x ^ k)).add (tail_power_hasSum _ (tailsInDisk_spec h) hx)
  convert hh using 1
  funext k
  rw [trialSeqS_succ, finCoeffS_succ]
  ring

end CatalanMeasure.CellCert
