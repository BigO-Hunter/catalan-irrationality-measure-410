module

public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierTrialUHasSum
public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierTrialPowerHasSum
public import Submission.CatalanMeasure.Cert.DenominatorBounds
public import Submission.CatalanMeasure.Cert.FieldEval

@[expose] public section

/-!
# Derivatives of the trial fields as quotients of computable polynomials

For trial data `(cs, tail)` with all `|z| < 1`, the derivative of the row field
`W₂ - 4 T(p, ·) - S(v, ·)` (and of the column field `W_s + 2 T(v, ·)`) is a sum of rational
functions with rational coefficients.  `rowFracs` and `colFracs` list them as pairs of
coefficient lists, and `fracSum` combines them into a single quotient `A / Q`.
-/

open OAI.InternalCatalan Polynomial Set

namespace CatalanMeasure.Cert

/-! ### Summability -/

theorem barrierFiniteCoeff_eq_zero {cs : List ℤ} {k : ℕ} (hk : cs.length < k) :
    barrierFiniteCoeff cs k = 0 := by
  unfold barrierFiniteCoeff
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega)]; simp

noncomputable def tailMajorant (tail : List TailQ) (k : ℕ) : ℝ :=
  ((tail.map TailQ.toC).map (fun zr : ℂ × ℂ => ‖zr.2‖ * ‖zr.1‖ ^ k)).sum

theorem majorant_summable (l : List (ℂ × ℂ)) (hd : ∀ zr ∈ l, ‖zr.1‖ < 1) :
    Summable (fun k => (l.map (fun zr : ℂ × ℂ => ‖zr.2‖ * ‖zr.1‖ ^ k)).sum) ∧
      Summable (fun k : ℕ => (k : ℝ) * (l.map (fun zr : ℂ × ℂ => ‖zr.2‖ * ‖zr.1‖ ^ k)).sum) := by
  induction l with
  | nil => simp [summable_zero]
  | cons zr l ih =>
    have hz : ‖zr.1‖ < 1 := hd zr (by simp)
    obtain ⟨h1, h2⟩ := ih (fun w hw => hd w (List.mem_cons_of_mem _ hw))
    simp only [List.map_cons, List.sum_cons]
    have g1 : Summable (fun k : ℕ => ‖zr.2‖ * ‖zr.1‖ ^ k) :=
      (summable_geometric_of_lt_one (norm_nonneg _) hz).mul_left _
    have g2 : Summable (fun k : ℕ => (k : ℝ) * (‖zr.2‖ * ‖zr.1‖ ^ k)) := by
      have := (summable_pow_mul_geometric_of_norm_lt_one 1 (by simpa using hz :
        ‖(‖zr.1‖ : ℝ)‖ < 1)).mul_left ‖zr.2‖
      refine this.congr (fun k => ?_)
      simp; ring
    refine ⟨g1.add h1, ?_⟩
    refine (g2.add h2).congr (fun k => ?_)
    ring

theorem tailMajorant_summable {tail : List TailQ} (h : tailsInDisk tail = true) :
    Summable (fun k => tailMajorant tail k) ∧
      Summable (fun k : ℕ => (k : ℝ) * tailMajorant tail k) :=
  majorant_summable _ (tailsInDisk_spec h)

theorem tailMajorant_nonneg (tail : List TailQ) (k : ℕ) : 0 ≤ tailMajorant tail k := by
  unfold tailMajorant
  apply List.sum_nonneg
  intro a ha
  obtain ⟨zr, _, rfl⟩ := List.mem_map.mp ha
  positivity

theorem listNorm_sum_le (l : List ℂ) : ‖l.sum‖ ≤ (l.map norm).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.sum_cons, List.map_cons]; exact (norm_add_le _ _).trans (by linarith)

theorem trialSeq_abs_le (cs : List ℤ) (tail : List TailQ) (k : ℕ) :
    |trialSeq cs tail k| ≤ |barrierFiniteCoeff cs k| + tailMajorant tail k := by
  have hm := tailMajorant_nonneg tail k
  unfold trialSeq barrierTrial
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

theorem finiteCoeff_summable (cs : List ℤ) :
    Summable (fun k => |barrierFiniteCoeff cs k|) ∧
      Summable (fun k : ℕ => (k : ℝ) * |barrierFiniteCoeff cs k|) := by
  constructor
  · apply summable_of_ne_finset_zero (s := Finset.range (cs.length + 1))
    intro k hk
    rw [barrierFiniteCoeff_eq_zero (by simp at hk; omega)]; simp
  · apply summable_of_ne_finset_zero (s := Finset.range (cs.length + 1))
    intro k hk
    rw [barrierFiniteCoeff_eq_zero (by simp at hk; omega)]; simp

theorem trialSeq_summable {cs : List ℤ} {tail : List TailQ} (h : tailsInDisk tail = true) :
    Summable (fun k => |trialSeq cs tail k|) ∧
      Summable (fun k : ℕ => (k : ℝ) * |trialSeq cs tail k|) := by
  obtain ⟨f1, f2⟩ := finiteCoeff_summable cs
  obtain ⟨g1, g2⟩ := tailMajorant_summable h
  refine ⟨(f1.add g1).of_nonneg_of_le (fun k => abs_nonneg _) (trialSeq_abs_le cs tail),
    (f2.add g2).of_nonneg_of_le (fun k => by positivity) (fun k => ?_)⟩
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (trialSeq_abs_le cs tail k) (Nat.cast_nonneg k)

/-! ### Computable polynomial forms of the finite parts -/

def chebUPair : ℕ → List ℚ × List ℚ
  | 0 => ([1], [0, 2])
  | n + 1 => ((chebUPair n).2,
      lpAdd (lpMul [0, 2] (chebUPair n).2) (lpSmul (-1) (chebUPair n).1))

def chebUList (n : ℕ) : List ℚ := (chebUPair n).1

theorem chebUPair_spec (n : ℕ) (x : ℝ) :
    lpEval (chebUPair n).1 x = (Chebyshev.U ℝ (n : ℤ)).eval x ∧
      lpEval (chebUPair n).2 x = (Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x := by
  induction n with
  | zero =>
    refine ⟨by simp [chebUPair, Chebyshev.U_zero], ?_⟩
    simp [chebUPair, Chebyshev.U_one]; ring
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h := Chebyshev.U_add_two ℝ (n : ℤ)
    have e : ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have e' : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, h]
    simp only [chebUPair, lpEval_add, lpEval_mul, lpEval_smul, lpEval_cons, lpEval_nil,
      eval_sub, eval_mul, eval_X, eval_ofNat]
    rw [ih.1, ih.2, e']
    push_cast
    ring

def lpSumList : List (List ℚ) → List ℚ
  | [] => []
  | p :: l => lpAdd p (lpSumList l)

theorem lpEval_sumList (l : List (List ℚ)) (x : ℝ) :
    lpEval (lpSumList l) x = (l.map (fun p => lpEval p x)).sum := by
  induction l with
  | nil => simp [lpSumList]
  | cons p l ih => simp [lpSumList, ih]

def finUPoly (cs : List ℤ) : List ℚ :=
  lpSumList ((List.range cs.length).map
    (fun k => lpSmul ((cs.getD k 0 : ℚ) / 100000000) (chebUList k)))

def finPowPoly (cs : List ℤ) : List ℚ := cs.map (fun c : ℤ => (c : ℚ) / 100000000)

theorem finUPoly_spec (cs : List ℤ) (x : ℝ) :
    lpEval (finUPoly cs) x = (barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x := by
  unfold finUPoly barrierFiniteUDerivative
  rw [lpEval_sumList, List.map_map, list_range_map_sum, eval₂_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Function.comp_apply, lpEval_smul, eval₂_mul, eval₂_C]
  rw [chebUList, (chebUPair_spec k x).1, ← eval_map, Chebyshev.map_U]
  simp

theorem lpEval_map_div (cs : List ℤ) (x : ℝ) :
    lpEval (cs.map (fun c : ℤ => (c : ℚ) / 100000000)) x =
      ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℚ) / 100000000 : ℝ) * x ^ k := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, lpEval_cons, ih, List.length_cons, Finset.sum_range_succ',
      Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    · push_cast; ring

theorem finPowPoly_spec (cs : List ℤ) (x : ℝ) :
    lpEval (finPowPoly cs) x = (barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x := by
  unfold finPowPoly barrierFinitePowerDerivative
  rw [lpEval_map_div, eval₂_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp

/-! ### Tail fractions -/

/-- `Re (r z / (1 - 2 x z + z²))` as numerator and denominator. -/
def tailTFrac (t : TailQ) : List ℚ × List ℚ :=
  let P := t.rr * t.zr - t.ri * t.zi
  let Q := t.rr * t.zi + t.ri * t.zr
  if t.zi = 0 ∧ t.ri = 0 then ([P], [1 + t.zr * t.zr, -2 * t.zr])
  else
    let al := 1 + t.zr * t.zr - t.zi * t.zi
    let be := 2 * t.zr * t.zi
    ([P * al + Q * be, -2 * (P * t.zr + Q * t.zi)],
      lpAdd (lpMul [al, -2 * t.zr] [al, -2 * t.zr]) (lpMul [be, -2 * t.zi] [be, -2 * t.zi]))

/-- `Re (r z / (1 - x z))` as numerator and denominator. -/
def tailSFrac (t : TailQ) : List ℚ × List ℚ :=
  let P := t.rr * t.zr - t.ri * t.zi
  let Q := t.rr * t.zi + t.ri * t.zr
  if t.zi = 0 ∧ t.ri = 0 then ([P], [1, -t.zr])
  else ([P, -(P * t.zr + Q * t.zi)],
      lpAdd (lpMul [1, -t.zr] [1, -t.zr]) (lpMul [0, t.zi] [0, t.zi]))

theorem tailTFrac_spec (t : TailQ) (ht : ‖(TailQ.toC t).1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    lpEval (tailTFrac t).2 x ≠ 0 ∧
      ((TailQ.toC t).2 * (TailQ.toC t).1 / barrierTailQuadraticDen (TailQ.toC t).1 x).re =
        lpEval (tailTFrac t).1 x / lpEval (tailTFrac t).2 x := by
  have hw := quadratic_den_norm_lower hx ht.le
  have hpos : 0 < ‖barrierTailQuadraticDen (TailQ.toC t).1 x‖ :=
    lt_of_lt_of_le (by nlinarith [norm_nonneg (TailQ.toC t).1]) hw
  have hw0 : barrierTailQuadraticDen (TailQ.toC t).1 x ≠ 0 := norm_pos_iff.mp hpos
  have hre : (barrierTailQuadraticDen (TailQ.toC t).1 x).re =
      1 + t.zr * t.zr - t.zi * t.zi - 2 * t.zr * x := by
    simp [barrierTailQuadraticDen, TailQ.toC, barrierComplex, pow_two]; ring
  have him : (barrierTailQuadraticDen (TailQ.toC t).1 x).im = 2 * t.zr * t.zi - 2 * t.zi * x := by
    simp [barrierTailQuadraticDen, TailQ.toC, barrierComplex, pow_two]; ring
  have hns : Complex.normSq (barrierTailQuadraticDen (TailQ.toC t).1 x) ≠ 0 :=
    (Complex.normSq_pos.mpr hw0).ne'
  unfold tailTFrac
  split_ifs with hr
  · obtain ⟨hzi, hri⟩ := hr
    have hre' : (barrierTailQuadraticDen (TailQ.toC t).1 x) =
        ((1 + t.zr * t.zr - 2 * t.zr * x : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [hre]; simp [hzi]
      · rw [him]; simp [hzi]
    have hd : (1 + t.zr * t.zr - 2 * t.zr * x : ℝ) ≠ 0 := by
      intro h0; rw [hre', h0] at hw0; simp at hw0
    have hrz : (TailQ.toC t).2 * (TailQ.toC t).1 = ((t.rr * t.zr : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [TailQ.toC, barrierComplex, hzi, hri]
    have hd' : lpEval [1 + t.zr * t.zr, -2 * t.zr] x = 1 + t.zr * t.zr - 2 * t.zr * x := by
      simp; ring
    refine ⟨by rw [hd']; exact hd, ?_⟩
    rw [hre', hrz, ← Complex.ofReal_div, Complex.ofReal_re, hd']
    simp [hzi, hri]
  · refine ⟨?_, ?_⟩
    · intro h0
      apply hns
      rw [Complex.normSq_apply, hre, him]
      simp [lpEval_add, lpEval_mul] at h0
      push_cast at h0
      linarith
    · rw [Complex.div_re, hre, him]
      rw [Complex.normSq_apply, hre, him]
      simp [TailQ.toC, barrierComplex, Complex.mul_re, Complex.mul_im, lpEval_add, lpEval_mul]
      push_cast
      field_simp
      ring

theorem tailSFrac_spec (t : TailQ) (ht : ‖(TailQ.toC t).1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    lpEval (tailSFrac t).2 x ≠ 0 ∧
      ((TailQ.toC t).2 * (TailQ.toC t).1 / barrierTailLinearDen (TailQ.toC t).1 x).re =
        lpEval (tailSFrac t).1 x / lpEval (tailSFrac t).2 x := by
  have hw := linear_den_norm_lower hx (z := (TailQ.toC t).1)
  have hpos : 0 < ‖barrierTailLinearDen (TailQ.toC t).1 x‖ := lt_of_lt_of_le (by linarith) hw
  have hw0 : barrierTailLinearDen (TailQ.toC t).1 x ≠ 0 := norm_pos_iff.mp hpos
  have hre : (barrierTailLinearDen (TailQ.toC t).1 x).re = 1 - t.zr * x := by
    simp [barrierTailLinearDen, TailQ.toC, barrierComplex]; ring
  have him : (barrierTailLinearDen (TailQ.toC t).1 x).im = -(t.zi * x) := by
    simp [barrierTailLinearDen, TailQ.toC, barrierComplex]; ring
  have hns : Complex.normSq (barrierTailLinearDen (TailQ.toC t).1 x) ≠ 0 :=
    (Complex.normSq_pos.mpr hw0).ne'
  unfold tailSFrac
  split_ifs with hr
  · obtain ⟨hzi, hri⟩ := hr
    have hre' : (barrierTailLinearDen (TailQ.toC t).1 x) = ((1 - t.zr * x : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [hre]; simp
      · rw [him]; simp [hzi]
    have hd : (1 - t.zr * x : ℝ) ≠ 0 := by
      intro h0; rw [hre', h0] at hw0; simp at hw0
    have hrz : (TailQ.toC t).2 * (TailQ.toC t).1 = ((t.rr * t.zr : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [TailQ.toC, barrierComplex, hzi, hri]
    have hd' : lpEval [1, -t.zr] x = 1 - t.zr * x := by simp; ring
    refine ⟨by rw [hd']; exact hd, ?_⟩
    rw [hre', hrz, ← Complex.ofReal_div, Complex.ofReal_re, hd']
    simp [hzi, hri]
  · refine ⟨?_, ?_⟩
    · intro h0
      apply hns
      rw [Complex.normSq_apply, hre, him]
      simp [lpEval_add, lpEval_mul] at h0
      push_cast at h0
      linarith
    · rw [Complex.div_re, hre, him]
      rw [Complex.normSq_apply, hre, him]
      simp [TailQ.toC, barrierComplex, Complex.mul_re, Complex.mul_im, lpEval_add, lpEval_mul]
      push_cast
      field_simp
      ring

/-! ### Sums of fractions -/

def fracSum : List (List ℚ × List ℚ) → List ℚ × List ℚ
  | [] => ([0], [1])
  | f :: l => (lpAdd (lpMul (fracSum l).1 f.2) (lpMul f.1 (fracSum l).2),
      lpMul (fracSum l).2 f.2)

theorem fracSum_spec (l : List (List ℚ × List ℚ)) (x : ℝ)
    (h : ∀ f ∈ l, lpEval f.2 x ≠ 0) :
    lpEval (fracSum l).2 x ≠ 0 ∧
      lpEval (fracSum l).1 x / lpEval (fracSum l).2 x =
        (l.map (fun f => lpEval f.1 x / lpEval f.2 x)).sum := by
  induction l with
  | nil => simp [fracSum]
  | cons f l ih =>
    obtain ⟨h0, h1⟩ := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    have hf := h f List.mem_cons_self
    simp only [fracSum, lpEval_add, lpEval_mul, List.map_cons, List.sum_cons]
    refine ⟨mul_ne_zero h0 hf, ?_⟩
    rw [← h1]
    field_simp
    ring

/-! ### The derivative fractions of the two fields -/

def rowFracs (Pc Vc : List ℤ) (P V : List TailQ) : List (List ℚ × List ℚ) :=
  [([19 / 48], [0, 1]), ([-1 / 12], [1, -1]), ([0, -65 / 24], [1, 0, 1]),
    (lpAdd (lpSmul (-4) (finUPoly Pc)) (lpSmul (-1) (finPowPoly Vc)), [1])] ++
  P.map (fun t => (lpSmul (-4) (tailTFrac t).1, (tailTFrac t).2)) ++
  V.map (fun t => (lpSmul (-1) (tailSFrac t).1, (tailSFrac t).2))

def colFracs (Vc : List ℤ) (V : List TailQ) : List (List ℚ × List ℚ) :=
  [([7 / 48], [0, 1]), ([-1 / 12], [1, -1]), (lpSmul 2 (finUPoly Vc), [1])] ++
  V.map (fun t => (lpSmul 2 (tailTFrac t).1, (tailTFrac t).2))

theorem re_list_sum_map {α : Type*} (l : List α) (f : α → ℂ) :
    (l.map f).sum.re = (l.map (fun a => (f a).re)).sum := by
  rw [re_list_sum, List.map_map]; rfl

theorem rowField_hasDerivAt {Pc Vc : List ℤ} {P V : List TailQ} (hP : tailsInDisk P = true)
    (hV : tailsInDisk V = true) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    lpEval (fracSum (rowFracs Pc Vc P V)).2 x ≠ 0 ∧
    HasDerivAt (realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V))
      (lpEval (fracSum (rowFracs Pc Vc P V)).1 x / lpEval (fracSum (rowFracs Pc Vc P V)).2 x)
      x := by
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  have hx1 : x ≠ 1 := hx.2.ne
  have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  have hdP := tailsInDisk_spec hP
  have hdV := tailsInDisk_spec hV
  have hden : ∀ f ∈ rowFracs Pc Vc P V, lpEval f.2 x ≠ 0 := by
    intro f hf
    simp only [rowFracs, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
      or_false] at hf
    rcases hf with ((rfl | rfl | rfl | rfl) | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
    · simpa using hx0
    · simp only [lpEval_cons, lpEval_nil]; push_cast; intro h; apply h1x; linarith
    · simp only [lpEval_cons, lpEval_nil]; push_cast
      exact ne_of_gt (by nlinarith [mul_self_nonneg x])
    · simp
    · exact (tailTFrac_spec t (hdP _ (List.mem_map_of_mem ht)) hxa).1
    · exact (tailSFrac_spec t (hdV _ (List.mem_map_of_mem ht)) hxa).1
  obtain ⟨hQ, hAQ⟩ := fracSum_spec _ x hden
  refine ⟨hQ, ?_⟩
  rw [hAQ]
  -- derivatives of the pieces
  have hl0 : HasDerivAt (fun y : ℝ => Real.log |y|) (1 / x) x := by
    simpa only [Real.log_abs, one_div] using Real.hasDerivAt_log hx0
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x :=
    ((hasDerivAt_id x).const_sub (1 : ℝ)).log h1x
  have hp : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add (1 : ℝ)
  have hW := ((hl0.const_mul (19 / 48 : ℝ)).add (hl1.const_mul (1 / 12 : ℝ))).sub
    ((hp.log hd).const_mul ((2 : ℝ) / 2 + 17 / 48))
  obtain ⟨sP1, sP2⟩ := trialSeq_summable (cs := Pc) hP
  obtain ⟨sV1, -⟩ := trialSeq_summable (cs := Vc) hV
  have hT := barrierTrialT_hasDerivAt_series (barrierTrial Pc (P.map TailQ.toC)) sP1 sP2 hx
  rw [(barrierTrial_U_hasSum Pc _ hdP hxa).tsum_eq] at hT
  have hS := barrierTrialS_hasDerivAt_series (barrierTrial Vc (V.map TailQ.toC)) sV1 hx
  rw [(barrierTrial_power_hasSum Vc _ hdV hxa).tsum_eq] at hS
  have hC : HasDerivAt (fun y => (0 : ℝ) * realEnergyCaseField y) 0 x := by
    simpa using hasDerivAt_const x (0 : ℝ)
  have hall := ((hW.add hC).sub (hT.const_mul (2 * 2 : ℝ))).sub hS
  unfold realEnergyRowTrialField realEnergyField trialSeq
  refine hall.congr_deriv ?_
  -- the sum of fractions
  simp only [rowFracs, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.map_map]
  have eT : (P.map ((fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x) ∘ TailQ.toC)).sum.re =
      (P.map (fun t => lpEval (tailTFrac t).1 x / lpEval (tailTFrac t).2 x)).sum := by
    rw [re_list_sum_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact (tailTFrac_spec t (hdP _ (List.mem_map_of_mem ht)) hxa).2
  have eS : (V.map ((fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailLinearDen zr.1 x) ∘ TailQ.toC)).sum.re =
      (V.map (fun t => lpEval (tailSFrac t).1 x / lpEval (tailSFrac t).2 x)).sum := by
    rw [re_list_sum_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact (tailSFrac_spec t (hdV _ (List.mem_map_of_mem ht)) hxa).2
  rw [eT, eS, ← finUPoly_spec, ← finPowPoly_spec]
  have e1 : (P.map ((fun f : List ℚ × List ℚ => lpEval f.1 x / lpEval f.2 x) ∘
      fun t => (lpSmul (-4) (tailTFrac t).1, (tailTFrac t).2))).sum =
      -4 * (P.map (fun t => lpEval (tailTFrac t).1 x / lpEval (tailTFrac t).2 x)).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, lpEval_smul]
    push_cast
    ring
  have e2 : (V.map ((fun f : List ℚ × List ℚ => lpEval f.1 x / lpEval f.2 x) ∘
      fun t => (lpSmul (-1) (tailSFrac t).1, (tailSFrac t).2))).sum =
      -1 * (V.map (fun t => lpEval (tailSFrac t).1 x / lpEval (tailSFrac t).2 x)).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, lpEval_smul]
    push_cast
    ring
  rw [e1, e2]
  have f1 : lpEval [19 / 48] x / lpEval [0, 1] x = 19 / 48 * (1 / x) := by
    simp only [lpEval_cons, lpEval_nil]; push_cast; ring
  have f2 : lpEval [-1 / 12] x / lpEval [1, -1] x = 1 / 12 * (-1 / (1 - x)) := by
    simp only [lpEval_cons, lpEval_nil]; push_cast
    rw [show (1 : ℝ) + x * (-1 + x * 0) = 1 - x by ring]; ring
  have f3 : lpEval [0, -65 / 24] x / lpEval [1, 0, 1] x =
      -((2 / 2 + 17 / 48) * (2 * x / (1 + x ^ 2))) := by
    simp only [lpEval_cons, lpEval_nil]; push_cast
    rw [show (1 : ℝ) + x * (0 + x * (1 + x * 0)) = 1 + x ^ 2 by ring]; ring
  have f4 : lpEval (lpAdd (lpSmul (-4) (finUPoly Pc)) (lpSmul (-1) (finPowPoly Vc))) x /
      lpEval [1] x = -4 * lpEval (finUPoly Pc) x - lpEval (finPowPoly Vc) x := by
    simp only [lpEval_add, lpEval_smul, lpEval_cons, lpEval_nil]; push_cast; ring
  rw [f1, f2, f3, f4]
  ring

theorem colField_hasDerivAt {Vc : List ℤ} {V : List TailQ} (hV : tailsInDisk V = true)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    lpEval (fracSum (colFracs Vc V)).2 x ≠ 0 ∧
    HasDerivAt (realEnergyColumnTrialField (trialSeq Vc V))
      (lpEval (fracSum (colFracs Vc V)).1 x / lpEval (fracSum (colFracs Vc V)).2 x) x := by
  have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx'.1.le, hx.2.le⟩
  have hx0 : x ≠ 0 := hx.1.ne'
  have h1x : 1 - x ≠ 0 := by linarith [hx.2]
  have hdV := tailsInDisk_spec hV
  have hden : ∀ f ∈ colFracs Vc V, lpEval f.2 x ≠ 0 := by
    intro f hf
    simp only [colFracs, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
      or_false] at hf
    rcases hf with (rfl | rfl | rfl) | ⟨t, ht, rfl⟩
    · simpa using hx0
    · simp only [lpEval_cons, lpEval_nil]; push_cast; intro h; apply h1x; linarith
    · simp
    · exact (tailTFrac_spec t (hdV _ (List.mem_map_of_mem ht)) hxa).1
  obtain ⟨hQ, hAQ⟩ := fracSum_spec _ x hden
  refine ⟨hQ, ?_⟩
  rw [hAQ]
  have hl0 : HasDerivAt Real.log (1 / x) x := by
    simpa only [one_div] using Real.hasDerivAt_log hx0
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x :=
    ((hasDerivAt_id x).const_sub (1 : ℝ)).log h1x
  obtain ⟨sV1, sV2⟩ := trialSeq_summable (cs := Vc) hV
  have hT := barrierTrialT_hasDerivAt_series (barrierTrial Vc (V.map TailQ.toC)) sV1 sV2 hx'
  rw [(barrierTrial_U_hasSum Vc _ hdV hxa).tsum_eq] at hT
  have hall := ((hl0.const_mul (7 / 48 : ℝ)).add (hl1.const_mul (1 / 12 : ℝ))).add
    (hT.const_mul (2 : ℝ))
  unfold realEnergyColumnTrialField realEnergyColumnField trialSeq
  refine hall.congr_deriv ?_
  simp only [colFracs, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.map_map]
  have eT : (V.map ((fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x) ∘ TailQ.toC)).sum.re =
      (V.map (fun t => lpEval (tailTFrac t).1 x / lpEval (tailTFrac t).2 x)).sum := by
    rw [re_list_sum_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact (tailTFrac_spec t (hdV _ (List.mem_map_of_mem ht)) hxa).2
  rw [eT, ← finUPoly_spec]
  have e1 : (V.map ((fun f : List ℚ × List ℚ => lpEval f.1 x / lpEval f.2 x) ∘
      fun t => (lpSmul 2 (tailTFrac t).1, (tailTFrac t).2))).sum =
      2 * (V.map (fun t => lpEval (tailTFrac t).1 x / lpEval (tailTFrac t).2 x)).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, lpEval_smul]
    push_cast
    ring
  rw [e1]
  have f1 : lpEval [7 / 48] x / lpEval [0, 1] x = 7 / 48 * (1 / x) := by
    simp only [lpEval_cons, lpEval_nil]; push_cast; ring
  have f2 : lpEval [-1 / 12] x / lpEval [1, -1] x = 1 / 12 * (-1 / (1 - x)) := by
    simp only [lpEval_cons, lpEval_nil]; push_cast
    rw [show (1 : ℝ) + x * (-1 + x * 0) = 1 - x by ring]; ring
  have f4 : lpEval (lpSmul 2 (finUPoly Vc)) x / lpEval [1] x = 2 * lpEval (finUPoly Vc) x := by
    simp only [lpEval_smul, lpEval_cons, lpEval_nil]; push_cast; ring
  rw [f1, f2, f4]
  ring

end CatalanMeasure.Cert
