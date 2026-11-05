module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeC
public import Submission.CatalanMeasure.GenD.Signed.FieldForm

/-!
# D2 constants: absolute sums of a finitely supported trial (`hA`, `hA1`, `hB1`)

* `tsum_abs_bSeq`: `sum' |b_j| = sum_k |bs_k|` (exact rational sum `absq`);
* `abs_barrierTrialS_le`: `|S_b(x)| <= sum_k |bs_k| / (k+1)` for `|x| <= 1` (`absSq`), the crude
  phantom bounds `A1`, `B1` of `SpikeTrialCert`.
* The trial's actual `D.a` is `tseq (bSeq fa) (tail.map TailQ.toC)` (finite part plus a geometric tail, `Data/Trial`):
  `tsum_abs_tseq_le` (`hA`: `sum |a| <= absq fa + tailMaj tail`) and `abs_barrierTrialS_tseq_le`
  (`hA1`: `|S_a(x)| <= absSq fa + 7 tailW tail` for `|x| <= 1023/1024`).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert OAI.InternalCatalan CatalanMeasure.Signed

def absq (as : List ℚ) : ℚ := idxSum (fun _ x => |x|) as 0
def absSq (as : List ℚ) : ℚ := idxSum (fun k x => |x| / ((k : ℚ) + 1)) as 0

theorem bSeq_zero (as : List ℚ) : bSeq as 0 = 0 := by simp [bSeq]

theorem tsum_abs_bSeq (as : List ℚ) : ∑' j : ℕ, |bSeq as j| = (absq as : ℝ) := by
  have hs : Summable (fun j : ℕ => |bSeq as j|) := by
    refine summable_of_ne_finset_zero (s := Finset.range (as.length + 1)) fun j hj => ?_
    have hj' : as.length + 1 ≤ j := by simpa using hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk : as.length ≤ k := by omega
    rw [bSeq_succ, getD_zero_of_le as hk]; simp
  rw [hs.tsum_eq_zero_add, bSeq_zero, abs_zero, zero_add]
  have := tsum_bSeq as (fun _ t => |t|) (fun _ => by simp)
  rw [this, absq, idxSum_cast]
  push_cast
  simp

theorem abs_barrierTrialS_le (as : List ℚ) {x : ℝ} (hx : |x| ≤ 1) :
    |barrierTrialS (bSeq as) x| ≤ (absSq as : ℝ) := by
  unfold barrierTrialS
  have := tsum_bSeq as (fun k t => t * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) (fun _ => by simp)
  rw [this, absSq, idxSum_cast]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  have hj : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hxp : |x| ^ (j + 1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hc0 : 0 ≤ |((as.getD j 0 : ℚ) : ℝ)| := abs_nonneg _
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hj]
  push_cast
  simp only [zero_add]
  have hj' : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  refine div_le_div_of_nonneg_right ?_ hj'.le
  calc |((as.getD j 0 : ℚ) : ℝ)| * |x| ^ (j + 1) ≤ |((as.getD j 0 : ℚ) : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left hxp hc0
    _ = |((as.getD j 0 : ℚ) : ℝ)| := mul_one _

/-- Bool form of the divisibility hypothesis of `De2_of_cov`. -/
theorem divAll {Lc : ℤ} {n : ℕ}
    (h : (List.range n).all (fun i => decide ((((i : ℕ) : ℤ) + 1) ∣ Lc)) = true) :
    ∀ i < n, (((i : ℕ) : ℤ) + 1) ∣ Lc := by
  intro i hi
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa using this


/-! ### The trial sequence with a geometric tail (`tseq`) -/

open CatalanMeasure.Signed.FieldForm
open CatalanMeasure.Cert (TailQ)

/-- `sum |w|` over the tail (`w = rr + i ri`). -/
def tailW (tl : List TailQ) : ℚ := (tl.map fun t => |t.rr| + |t.ri|).sum

/-- `sum |w| |z| / (1 - |z|)` over the tail (`|z| <= |zr| + |zi|`). -/
def tailMaj (tl : List TailQ) : ℚ :=
  (tl.map fun t => (|t.rr| + |t.ri|) * (|t.zr| + |t.zi|) / (1 - (|t.zr| + |t.zi|))).sum

def tailZB (tl : List TailQ) : Bool := tl.all fun t => decide (|t.zr| + |t.zi| < 1)

theorem tailW_cast (tl : List TailQ) :
    ((tailW tl : ℚ) : ℝ) = (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ)).sum := by
  induction tl with
  | nil => simp [tailW]
  | cons t tl ih =>
    rw [tailW, List.map_cons, List.sum_cons, Rat.cast_add,
      show ((List.map (fun t : TailQ => |t.rr| + |t.ri|) tl).sum : ℚ) = tailW tl from rfl, ih]
    simp

theorem tailMaj_cast (tl : List TailQ) :
    ((tailMaj tl : ℚ) : ℝ) = (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ) *
      (((|t.zr| + |t.zi| : ℚ)) : ℝ) * (1 - (((|t.zr| + |t.zi| : ℚ)) : ℝ))⁻¹).sum := by
  induction tl with
  | nil => simp [tailMaj]
  | cons t tl ih =>
    rw [tailMaj, List.map_cons, List.sum_cons, Rat.cast_add,
      show ((List.map (fun t : TailQ => (|t.rr| + |t.ri|) * (|t.zr| + |t.zi|) /
        (1 - (|t.zr| + |t.zi|))) tl).sum : ℚ) = tailMaj tl from rfl, ih]
    simp only [List.map_cons, List.sum_cons]
    push_cast
    simp [div_eq_mul_inv]

theorem tq_norm_z (t : TailQ) : ‖(TailQ.toC t).1‖ ≤ (((|t.zr| + |t.zi| : ℚ)) : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im (TailQ.toC t).1
  simpa [TailQ.toC, OAI.InternalCatalan.barrierComplex] using h

theorem tq_norm_w (t : TailQ) : ‖(TailQ.toC t).2‖ ≤ (((|t.rr| + |t.ri| : ℚ)) : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im (TailQ.toC t).2
  simpa [TailQ.toC, OAI.InternalCatalan.barrierComplex] using h

theorem tail_term_le (tl : List TailQ) (k : ℕ) :
    |(((tl.map TailQ.toC).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum).re| ≤
      (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ) * (((|t.zr| + |t.zi| : ℚ)) : ℝ) ^ k).sum := by
  induction tl with
  | nil => simp
  | cons t tl ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_re]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul (tq_norm_w t) (pow_le_pow_left₀ (norm_nonneg _) (tq_norm_z t) k)
      (by positivity) (by positivity)

theorem tseq_succ_abs_le (fa : List ℚ) (tl : List TailQ) (j : ℕ) :
    |tseq (bSeq fa) (tl.map TailQ.toC) (j + 1)| ≤ |bSeq fa (j + 1)| +
      (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ) *
        (((|t.zr| + |t.zi| : ℚ)) : ℝ) ^ (j + 1)).sum := by
  unfold tseq
  rw [if_neg (Nat.succ_ne_zero j)]
  exact (abs_add_le _ _).trans (add_le_add_right (tail_term_le tl (j + 1)) _)

theorem tailZB_cons {t : TailQ} {tl : List TailQ} (h : tailZB (t :: tl) = true) :
    |t.zr| + |t.zi| < 1 ∧ tailZB tl = true := by
  unfold tailZB at h ⊢
  simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem hasSum_tail_geom (tl : List TailQ) (hZ : tailZB tl = true) :
    HasSum (fun j : ℕ => (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ) *
        (((|t.zr| + |t.zi| : ℚ)) : ℝ) ^ (j + 1)).sum)
      (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ) * (((|t.zr| + |t.zi| : ℚ)) : ℝ) *
        (1 - (((|t.zr| + |t.zi| : ℚ)) : ℝ))⁻¹).sum := by
  induction tl with
  | nil => simpa using hasSum_zero
  | cons t tl ih =>
    obtain ⟨ht, hZ'⟩ := tailZB_cons hZ
    have ht' : (((|t.zr| + |t.zi| : ℚ)) : ℝ) < 1 := by exact_mod_cast ht
    have h0 : (0 : ℝ) ≤ (((|t.zr| + |t.zi| : ℚ)) : ℝ) := by positivity
    have hg := (hasSum_geometric_of_lt_one h0 ht').mul_left
      ((((|t.rr| + |t.ri| : ℚ)) : ℝ) * (((|t.zr| + |t.zi| : ℚ)) : ℝ))
    have hg' : HasSum (fun j : ℕ => (((|t.rr| + |t.ri| : ℚ)) : ℝ) *
        (((|t.zr| + |t.zi| : ℚ)) : ℝ) ^ (j + 1))
        ((((|t.rr| + |t.ri| : ℚ)) : ℝ) * (((|t.zr| + |t.zi| : ℚ)) : ℝ) *
          (1 - (((|t.zr| + |t.zi| : ℚ)) : ℝ))⁻¹) := by
      convert hg using 1
      funext j; rw [pow_succ]; ring
    have := hg'.add (ih hZ')
    simp only [List.map_cons, List.sum_cons]
    exact this

theorem tsum_abs_tseq_le (fa : List ℚ) (tl : List TailQ) (hZ : tailZB tl = true) :
    ∑' j : ℕ, |tseq (bSeq fa) (tl.map TailQ.toC) j| ≤ ((absq fa + tailMaj tl : ℚ) : ℝ) := by
  have hf : Summable (fun j : ℕ => |bSeq fa (j + 1)|) := by
    refine summable_of_ne_finset_zero (s := Finset.range fa.length) fun j hj => ?_
    have hk : fa.length ≤ j := by simpa using hj
    rw [bSeq_succ, getD_zero_of_le fa hk]; simp
  have hfv : ∑' j : ℕ, |bSeq fa (j + 1)| = (absq fa : ℝ) := by
    have := tsum_bSeq fa (fun _ t => |t|) (fun _ => by simp)
    rw [this, absq, idxSum_cast]; push_cast; simp
  have hM := hf.hasSum.add (hasSum_tail_geom tl hZ)
  rw [← tailMaj_cast] at hM
  have hle : ∀ j, |tseq (bSeq fa) (tl.map TailQ.toC) (j + 1)| ≤
      |bSeq fa (j + 1)| + (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ) *
        (((|t.zr| + |t.zi| : ℚ)) : ℝ) ^ (j + 1)).sum := fun j => tseq_succ_abs_le fa tl j
  have hs : Summable (fun j : ℕ => |tseq (bSeq fa) (tl.map TailQ.toC) (j + 1)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle hM.summable
  have hs0 : Summable (fun j : ℕ => |tseq (bSeq fa) (tl.map TailQ.toC) j|) :=
    (summable_nat_add_iff 1).mp hs
  rw [hs0.tsum_eq_zero_add]
  have h0 : tseq (bSeq fa) (tl.map TailQ.toC) 0 = 0 := by simp [tseq]
  rw [h0, abs_zero, zero_add]
  have h1 := hasSum_le hle hs.hasSum hM
  have h2 := hM.tsum_eq
  rw [hfv] at h2
  push_cast
  rw [← hs.hasSum.tsum_eq] at h1 ⊢
  linarith [h1, h2]

theorem hasSum_tail_log (tl : List TailQ) (hZ : tailZB tl = true) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ) *
        ((((|t.zr| + |t.zi| : ℚ)) : ℝ) * |x|) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)).sum)
      (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ) *
        (-Real.log (1 - (((|t.zr| + |t.zi| : ℚ)) : ℝ) * |x|))).sum := by
  induction tl with
  | nil => simpa using hasSum_zero
  | cons t tl ih =>
    obtain ⟨ht, hZ'⟩ := tailZB_cons hZ
    have ht' : (((|t.zr| + |t.zi| : ℚ)) : ℝ) < 1 := by exact_mod_cast ht
    have h0 : (0 : ℝ) ≤ (((|t.zr| + |t.zi| : ℚ)) : ℝ) := by positivity
    have hy : abs ((((|t.zr| + |t.zi| : ℚ)) : ℝ) * |x|) < 1 := by
      rw [abs_of_nonneg (by positivity)]; nlinarith [abs_nonneg x]
    have hl := (Real.hasSum_pow_div_log_of_abs_lt_one hy).mul_left
      (((|t.rr| + |t.ri| : ℚ)) : ℝ)
    have := hl.add (ih hZ')
    simp only [List.map_cons, List.sum_cons]
    convert this using 1
    funext k; push_cast; ring

theorem neg_log_le_seven {y : ℝ} (h0 : 0 ≤ y) (hy : y ≤ 1023 / 1024) : -Real.log (1 - y) ≤ 7 := by
  have hpos : 0 < 1 - y := by linarith
  have h2 : -Real.log (1 - y) ≤ Real.log 1024 := by
    rw [← Real.log_inv]
    exact Real.log_le_log (by positivity) (by rw [inv_le_comm₀ hpos (by norm_num)]; linarith)
  have h3 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

theorem tail_log_le (tl : List TailQ) (hZ : tailZB tl = true) {x : ℝ} (hx : |x| ≤ 1023 / 1024) :
    (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ) *
        (-Real.log (1 - (((|t.zr| + |t.zi| : ℚ)) : ℝ) * |x|))).sum ≤
      7 * (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ)).sum := by
  induction tl with
  | nil => simp
  | cons t tl ih =>
    obtain ⟨ht, hZ'⟩ := tailZB_cons hZ
    have ht' : (((|t.zr| + |t.zi| : ℚ)) : ℝ) ≤ 1 := by exact_mod_cast ht.le
    have h0 : (0 : ℝ) ≤ (((|t.zr| + |t.zi| : ℚ)) : ℝ) := by positivity
    have hw0 : (0 : ℝ) ≤ (((|t.rr| + |t.ri| : ℚ)) : ℝ) := by positivity
    have hy := neg_log_le_seven (y := (((|t.zr| + |t.zi| : ℚ)) : ℝ) * |x|) (by positivity)
      (by nlinarith [abs_nonneg x])
    have := ih hZ'
    simp only [List.map_cons, List.sum_cons]
    nlinarith [mul_le_mul_of_nonneg_left hy hw0]

theorem abs_barrierTrialS_tseq_le (fa : List ℚ) (tl : List TailQ) (hZ : tailZB tl = true) {x : ℝ}
    (hx : |x| ≤ 1023 / 1024) :
    |barrierTrialS (tseq (bSeq fa) (tl.map TailQ.toC)) x| ≤ (absSq fa : ℝ) + 7 * (tailW tl : ℝ) := by
  have hx1 : |x| < 1 := by linarith
  have hlog := hasSum_tail_log tl hZ hx1
  have hfs : Summable (fun k : ℕ => |bSeq fa (k + 1)| / ((k + 1 : ℕ) : ℝ)) := by
    refine summable_of_ne_finset_zero (s := Finset.range fa.length) fun j hj => ?_
    have hk : fa.length ≤ j := by simpa using hj
    rw [bSeq_succ, getD_zero_of_le fa hk]; simp
  have hfv : ∑' k : ℕ, |bSeq fa (k + 1)| / ((k + 1 : ℕ) : ℝ) = (absSq fa : ℝ) := by
    have := tsum_bSeq fa (fun k t => |t| / ((k + 1 : ℕ) : ℝ)) (fun _ => by simp)
    rw [this, absSq, idxSum_cast]; push_cast; simp
  have hgs := hfs.hasSum.add hlog
  rw [hfv] at hgs
  have hterm : ∀ k : ℕ, ‖tseq (bSeq fa) (tl.map TailQ.toC) (k + 1) * x ^ (k + 1) /
      ((k + 1 : ℕ) : ℝ)‖ ≤ |bSeq fa (k + 1)| / ((k + 1 : ℕ) : ℝ) +
        (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ) *
          ((((|t.zr| + |t.zi| : ℚ)) : ℝ) * |x|) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)).sum := by
    intro k
    have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos hk, div_le_iff₀ hk]
    have hb := tseq_succ_abs_le fa tl k
    have hxp : |x| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1.le
    have hxp0 : 0 ≤ |x| ^ (k + 1) := by positivity
    have e1 : (|bSeq fa (k + 1)| / ((k + 1 : ℕ) : ℝ) +
        (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ) *
          ((((|t.zr| + |t.zi| : ℚ)) : ℝ) * |x|) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)).sum) *
          ((k + 1 : ℕ) : ℝ) = |bSeq fa (k + 1)| +
        (tl.map fun t => (((|t.rr| + |t.ri| : ℚ)) : ℝ) *
          (((|t.zr| + |t.zi| : ℚ)) : ℝ) ^ (k + 1)).sum * |x| ^ (k + 1) := by
      rw [add_mul, div_mul_cancel₀ _ hk.ne']
      congr 1
      rw [← List.sum_map_mul_right, ← List.sum_map_mul_right]
      refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
      rw [div_mul_cancel₀ _ hk.ne', mul_pow]; ring
    rw [e1]
    have hf0 : |bSeq fa (k + 1)| * |x| ^ (k + 1) ≤ |bSeq fa (k + 1)| := by
      nlinarith [abs_nonneg (bSeq fa (k + 1))]
    nlinarith [mul_le_mul_of_nonneg_right hb hxp0]
  have hnorm : Summable (fun k : ℕ => ‖tseq (bSeq fa) (tl.map TailQ.toC) (k + 1) * x ^ (k + 1) /
      ((k + 1 : ℕ) : ℝ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hgs.summable
  unfold barrierTrialS
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  refine (hasSum_le hterm hnorm.hasSum hgs).trans ?_
  have := tail_log_le tl hZ hx
  rw [tailW_cast]
  linarith

end CatalanMeasure.Signed.Consts
