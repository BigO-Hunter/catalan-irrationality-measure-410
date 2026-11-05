module

public import Submission.CatalanMeasure.GenD.Signed.FieldForm
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.PolyPos

/-!
# Trial data in rational form and the identification `hid` (Theorem A, Phase 2 trial assembly)

The three endpoint trials are given by exact rational data (`TrialQ`): the sequences `v, a, p, R`
(finite part `f` plus a geometric tail of rational complex pairs, `SeqQ`), the split parameter `η`,
the particle sup `Sup` and the polynomial-density species of the signed reference `P - N`: `qT, qF` (`P`)
and `qTn, qFn` (`N`) (`PieceQ`).  `TrialQ.form` is the `TrialForm` of FieldForm.

For every field class the Lean limit field is an explicit cell field plus an explicit constant:

* `hid_sn` (`fNegLim`), `hid_sp` (`fPosLim`, with the dilated block as a Laurent field),
  `hid_sc` (column), `hid_sm` (`fNegMLim`), `hid_spm` (`fPosMSLim` + the Lemma R′ remainder),
  `hid_near` (`fNearMSLim`), `hid_fr` (the Frostman field `frLim`, τ = 1);
* each states `field x = fieldTower fq (poleFn fq.poles) 0 x [+ lfieldTower lts 0 x] + κ`, where
  `fq` is any `FieldQ` equal to the generic builder (a data module proves that equality by
  `decide +kernel` on literals) and `κ` is the exact Lean constant (`sConst`, `tConst`, `log 2`, `Sup`).

The polynomial parts enter through block equalities (`polyS f = vS`, `polyT f = pT`, …), each a
literal equality checked once per trial.  `poleFn` is definitionally `Data.Cells.poleF`.

`TrialQ.spec` builds `TrialForm.Spec` from the definitional equations of the family member and
the data checks (`tailOKB`, the range of `η`, `PieceOK` by `nnCov`, `BD` by `nnCov`).
-/

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Trial

open Set MeasureTheory Finset
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
open CatalanMeasure.Cert (TailQ lpEval)
open OAI.InternalCatalan (barrierComplex)

noncomputable section

deriving instance DecidableEq for CatalanMeasure.CellCert.PoleR
deriving instance DecidableEq for CatalanMeasure.GenD.Signed.TaylorCell.FieldQ
deriving instance DecidableEq for CatalanMeasure.Signed.FieldForm.PieceQ

/-! ### 1. Rational trial data -/

/-- The finite part `k ↦ f_{k-1}` (`0` at `k = 0` and beyond the list). -/
def fQ (f : List ℚ) (k : ℕ) : ℝ := if k = 0 then 0 else ((f.getD (k - 1) 0 : ℚ) : ℝ)

theorem fQ_supp (f : List ℚ) : ∀ k, f.length < k → fQ f k = 0 := by
  intro k hk
  unfold fQ
  rw [if_neg (by omega), List.getD_eq_default _ _ (by omega)]
  simp

theorem fQ_succ (f : List ℚ) (k : ℕ) : fQ f (k + 1) = ((f.getD k 0 : ℚ) : ℝ) := by
  simp [fQ]

/-- A rational sequence form: finite part `f_1, …, f_L` and a geometric tail. -/
structure SeqQ where
  f : List ℚ
  tail : List TailQ

def SeqQ.form (d : SeqQ) : SeqForm := ⟨fQ d.f, d.f.length, d.tail.map TailQ.toC⟩

/-- The rational data of one trial. -/
structure TrialQ where
  v : SeqQ
  a : SeqQ
  p : SeqQ
  R : SeqQ
  η : ℚ
  Sup : ℚ
  qT : List PieceQ
  qF : List PieceQ
  /-- The negative part `N` of the signed reference `P - N` (`P` has `qT`, `qF`). -/
  qTn : List PieceQ
  qFn : List PieceQ

def TrialQ.form (T : TrialQ) : TrialForm :=
  ⟨T.v.form, T.a.form, T.p.form, (T.η : ℝ), T.R.form, (T.Sup : ℝ), T.qT.map PieceQ.toPiece,
    T.qF.map PieceQ.toPiece, T.qTn.map PieceQ.toPiece, T.qFn.map PieceQ.toPiece⟩

/-! ### Literal helpers (data modules emit `raw_ints%` integer lists) -/

/-- `[n₀, d₀, n₁, d₁, …] ↦ [n₀/d₀, n₁/d₁, …]`. -/
def qlist : List ℤ → List ℚ
  | n :: d :: r => ((n : ℚ) / (d : ℚ)) :: qlist r
  | _ => []

/-- Groups of four rationals as tail entries `(zr, zi, rr, ri)`. -/
def mkTail : List ℚ → List TailQ
  | a :: b :: c :: d :: r => ⟨a, b, c, d⟩ :: mkTail r
  | _ => []

/-- Groups of four rationals as poles `(rr, ri, pr, pi)`. -/
def mkPolesQ : List ℚ → List PoleR
  | a :: b :: c :: d :: r => ⟨a, b, c, d⟩ :: mkPolesQ r
  | _ => []

/-! ### 2. Field values -/

/-- The pole potential `Σ_q Re[ρ_q log (y - p_q)]` (definitionally `Data.Cells.poleF`). -/
def poleFn (ps : List PoleR) (y : ℝ) : ℝ :=
  (ps.map (fun q => (q.rho * Complex.log ((y : ℂ) - q.pc)).re)).sum

theorem poleFn_eq (ps : List PoleR) (y : ℝ) : poleFn ps y = poleSum (ps.map poleC) y := by
  rw [poleSum_poleC]; rfl

theorem poleFn_nil (y : ℝ) : poleFn [] y = 0 := by simp [poleFn]

theorem poleFn_cons (q : PoleR) (ps : List PoleR) (y : ℝ) :
    poleFn (q :: ps) y = (q.rho * Complex.log ((y : ℂ) - q.pc)).re + poleFn ps y := by
  simp [poleFn]

theorem poleFn_append (a b : List PoleR) (y : ℝ) : poleFn (a ++ b) y = poleFn a y + poleFn b y := by
  simp [poleFn, List.map_append, List.sum_append]

/-- The value of a `FieldQ` field with its own pole potential. -/
def fval (f : FieldQ) (x : ℝ) : ℝ :=
  polyTow f.poly 0 x + plogSumTower f.plogs 0 x + poleFn f.poles x

theorem fieldTower_poleFn (f : FieldQ) (x : ℝ) : fieldTower f (poleFn f.poles) 0 x = fval f x := rfl

theorem plogSumTower_zero (l : List (List ℚ × ℚ)) (x : ℝ) :
    plogSumTower l 0 x = (l.map (fun t => polyTow t.1 0 x * Real.log |x - (t.2 : ℝ)|)).sum := by
  simp [plogSumTower, mulTower_zero, logTower]

theorem fval_add (a b : FieldQ) (x : ℝ) : fval (fqAdd a b) x = fval a x + fval b x := by
  simp only [fval, fqAdd, polyTow_zero_vecAdd, plogSumTower, List.map_append, List.sum_append,
    poleFn_append]
  ring

def fqZero : FieldQ := ⟨[], [], []⟩

theorem fval_zero (x : ℝ) : fval fqZero x = 0 := by
  simp [fval, fqZero, polyTow_zero_nil, plogSumTower, poleFn_nil]

/-- Sum of a list of fields. -/
def fqSum : List FieldQ → FieldQ
  | [] => fqZero
  | f :: fs => fqAdd f (fqSum fs)

theorem fval_sum (fs : List FieldQ) (x : ℝ) : fval (fqSum fs) x = (fs.map (fun f => fval f x)).sum := by
  induction fs with
  | nil => simp [fqSum, fval_zero]
  | cons f fs ih => simp [fqSum, fval_add, ih]

def scaleP (c : ℚ) (q : PoleR) : PoleR := ⟨c * q.rr, c * q.ri, q.pr, q.pi⟩

/-- A rational multiple of a field. -/
def fqScale (c : ℚ) (f : FieldQ) : FieldQ :=
  ⟨f.poly.map (fun t => c * t), f.plogs.map (fun t => (t.1.map (fun s => c * s), t.2)),
    f.poles.map (scaleP c)⟩

theorem poleFn_scale (c : ℚ) (ps : List PoleR) (y : ℝ) :
    poleFn (ps.map (scaleP c)) y = (c : ℝ) * poleFn ps y := by
  induction ps with
  | nil => simp [poleFn_nil]
  | cons q qs ih =>
    rw [List.map_cons, poleFn_cons, poleFn_cons, ih, mul_add]
    congr 1
    have e : (scaleP c q).rho = ((c : ℝ) : ℂ) * q.rho := by
      apply Complex.ext <;> simp [scaleP, PoleR.rho]
    have e2 : (scaleP c q).pc = q.pc := rfl
    rw [e, e2, mul_assoc, Complex.re_ofReal_mul]

theorem plogSumTower_scale (c : ℚ) (l : List (List ℚ × ℚ)) (x : ℝ) :
    plogSumTower (l.map (fun t => (t.1.map (fun s => c * s), t.2))) 0 x =
      (c : ℝ) * plogSumTower l 0 x := by
  rw [plogSumTower_zero, plogSumTower_zero]
  induction l with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, polyTow_zero_map_mul]
    ring

theorem fval_scale (c : ℚ) (f : FieldQ) (x : ℝ) : fval (fqScale c f) x = (c : ℝ) * fval f x := by
  simp only [fval, fqScale, polyTow_zero_map_mul, plogSumTower_scale, poleFn_scale]
  ring

/-- A pure polynomial. -/
def fqPoly (L : List ℚ) : FieldQ := ⟨L, [], []⟩

theorem fval_poly (L : List ℚ) (x : ℝ) : fval (fqPoly L) x = polyTow L 0 x := by
  simp [fval, fqPoly, plogSumTower, poleFn_nil]

/-- `c log|x - e|`. -/
def logFQ (c e : ℚ) : FieldQ := ⟨[], [([c], e)], []⟩

theorem fval_log (c e : ℚ) (x : ℝ) : fval (logFQ c e) x = (c : ℝ) * Real.log |x - (e : ℝ)| := by
  simp [fval, logFQ, plogSumTower_zero, polyTow_zero_nil, polyTow_zero_cons, poleFn_nil]

/-- `-c log (1 + x²)` as the pole `Re[(-2c) log (x - i)]`. -/
def sqFQ (c : ℚ) : FieldQ := ⟨[], [], [⟨-2 * c, 0, 0, 1⟩]⟩

theorem fval_sq (c : ℚ) (x : ℝ) : fval (sqFQ c) x = -(c : ℝ) * Real.log (1 + x ^ 2) := by
  simp only [fval, sqFQ, polyTow_zero_nil, plogSumTower, List.map_nil, List.sum_nil, poleFn_cons,
    poleFn_nil]
  have e1 : ((⟨-2 * c, 0, 0, 1⟩ : PoleR).rho) = (((-2 * c : ℚ) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [PoleR.rho]
  have e2 : ((⟨-2 * c, 0, 0, 1⟩ : PoleR).pc) = Complex.I := by
    apply Complex.ext <;> simp [PoleR.pc]
  rw [e1, e2, Complex.re_ofReal_mul, Complex.log_re]
  have hn : ‖(x : ℂ) - Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp
    ring
  rw [hn, Real.log_sqrt (by positivity)]
  push_cast
  ring

/-- `-log |x - 1| - log |x + 1|` (`= -log (1 - x²)` on `(-1, 1)`). -/
def m1sqFQ : FieldQ := ⟨[], [([-1], 1), ([-1], -1)], []⟩

theorem fval_m1sq {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    fval m1sqFQ x = -Real.log (1 - x ^ 2) := by
  simp only [fval, m1sqFQ, plogSumTower_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, polyTow_zero_nil, polyTow_zero_cons, poleFn_nil]
  have h1 : (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) := by ring
  have ha : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
  have hb : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
  rw [h1, Real.log_mul ha hb]
  have e1 : Real.log |x - ((1 : ℚ) : ℝ)| = Real.log (1 - x) := by
    rw [← Real.log_abs (1 - x)]; push_cast; rw [abs_sub_comm]
  have e2 : Real.log |x - ((-1 : ℚ) : ℝ)| = Real.log (1 + x) := by
    rw [← Real.log_abs (1 + x)]; push_cast; ring_nf
  rw [e1, e2]
  push_cast
  ring

/-! ### 3. Poles of the sequence tails -/

/-- The S-pole of a tail entry: `ρ = -r`, `p = 1/z`. -/
def sPoleQ (t : TailQ) : PoleR :=
  ⟨-t.rr, -t.ri, t.zr / (t.zr * t.zr + t.zi * t.zi), -t.zi / (t.zr * t.zr + t.zi * t.zi)⟩

/-- The T-pole of a tail entry: `ρ = -r/2`, `p = (1 + z²)/(2z)`. -/
def tPoleQ (t : TailQ) : PoleR :=
  let nr := 1 + t.zr * t.zr - t.zi * t.zi
  let ni := 2 * t.zr * t.zi
  let dr := 2 * t.zr
  let di := 2 * t.zi
  let dn := dr * dr + di * di
  ⟨-t.rr / 2, -t.ri / 2, (nr * dr + ni * di) / dn, (ni * dr - nr * di) / dn⟩

/-- Reflection `x ↦ -x` of a pole with a real weight. -/
def reflP (q : PoleR) : PoleR := ⟨q.rr, q.ri, -q.pr, -q.pi⟩

theorem poleC_sPoleQ (t : TailQ) : poleC (sPoleQ t) = (-(TailQ.toC t).2, (TailQ.toC t).1⁻¹) := by
  simp only [poleC, sPoleQ, TailQ.toC, PoleR.rho, PoleR.pc, barrierComplex]
  refine Prod.ext ?_ ?_
  · apply Complex.ext <;> simp
  · apply Complex.ext <;> simp [Complex.inv_re, Complex.inv_im, Complex.normSq_apply] <;> ring

theorem poleC_tPoleQ (t : TailQ) : poleC (tPoleQ t) = (-(TailQ.toC t).2 / 2, tPole (TailQ.toC t).1) := by
  simp only [poleC, tPoleQ, TailQ.toC, PoleR.rho, PoleR.pc, barrierComplex, tPole]
  refine Prod.ext ?_ ?_
  · apply Complex.ext <;> simp
  · apply Complex.ext <;>
      simp [Complex.div_re, Complex.div_im, Complex.normSq_apply, pow_two] <;> ring

theorem sPoles_map (tl : List TailQ) : sPoles (tl.map TailQ.toC) = (tl.map sPoleQ).map poleC := by
  simp only [sPoles, List.map_map]
  exact List.map_congr_left (fun t _ => (poleC_sPoleQ t).symm)

theorem tPoles_map (tl : List TailQ) : tPoles (tl.map TailQ.toC) = (tl.map tPoleQ).map poleC := by
  simp only [tPoles, List.map_map]
  exact List.map_congr_left (fun t _ => (poleC_tPoleQ t).symm)

theorem poleFn_reflP (ps : List PoleR) (hr : ∀ q ∈ ps, q.ri = 0) (x : ℝ) :
    poleFn (ps.map reflP) x = poleFn ps (-x) := by
  induction ps with
  | nil => simp [poleFn_nil]
  | cons q qs ih =>
    rw [List.map_cons, poleFn_cons, poleFn_cons,
      ih (fun r hr' => hr r (List.mem_cons_of_mem _ hr'))]
    congr 1
    have hq : q.ri = 0 := hr q List.mem_cons_self
    have e1 : (reflP q).rho = ((q.rr : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [reflP, PoleR.rho, hq]
    have e2 : q.rho = ((q.rr : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [PoleR.rho, hq]
    rw [e1, e2, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.log_re, Complex.log_re]
    congr 2
    have : ((x : ℂ) - (reflP q).pc) = -(((-x : ℝ) : ℂ) - q.pc) := by
      apply Complex.ext <;> simp [reflP, PoleR.pc] <;> ring
    rw [this, norm_neg]

/-! ### 4. Polynomial blocks -/

/-- Coefficients `c_k / (n + k + 1)`. -/
def divIdx : ℕ → List ℚ → List ℚ
  | _, [] => []
  | n, c :: cs => c / ((n : ℚ) + 1) :: divIdx (n + 1) cs

/-- The coefficient list of `Σ_{k ≥ 1} f_k x^k / k`. -/
def polyS (f : List ℚ) : List ℚ := 0 :: divIdx 0 f

theorem polyTow_divIdx : ∀ (cs : List ℚ) (n : ℕ) (x : ℝ),
    polyTow (divIdx n cs) 0 x =
      ∑ k ∈ range cs.length, ((cs.getD k 0 : ℚ) : ℝ) / (((n + k : ℕ) : ℝ) + 1) * x ^ k
  | [], n, x => by simp [divIdx, polyTow_zero_nil]
  | c :: cs, n, x => by
    rw [divIdx, polyTow_zero_cons, polyTow_divIdx cs (n + 1) x, List.length_cons,
      Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, add_zero]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      have e : ((n + 1 + k : ℕ) : ℝ) = ((n + (k + 1) : ℕ) : ℝ) := by push_cast; ring
      rw [e, pow_succ]
      ring
    · push_cast; ring

theorem polyTow_polyS (f : List ℚ) (x : ℝ) : polyTow (polyS f) 0 x = finS (fQ f) f.length x := by
  rw [polyS, polyTow_zero_cons, polyTow_divIdx, finS, Finset.mul_sum]
  push_cast
  rw [zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fQ_succ]
  push_cast
  rw [pow_succ]
  ring

/-- One step `C_{k+2} = y C_{k+1} - C_k` of the scaled Chebyshev polynomials `C_k(y) = 2 T_k(y/2)`
(integer coefficients without the `2^j` growth of `T_k`). -/
def cStep (Tp Tc : List ℚ) : List ℚ := vecAdd (0 :: Tc) (Tp.map (fun t => -1 * t))

/-- `acc + Σ_j c_j/(k+j+1) C_{k+j+1}` along the list. -/
def chebAcc : List ℚ → ℕ → List ℚ → List ℚ → List ℚ → List ℚ
  | [], _, _, _, acc => acc
  | c :: cs, k, Tp, Tc, acc =>
      chebAcc cs (k + 1) Tc (cStep Tp Tc) (vecAdd acc (Tc.map (fun t => c / ((k : ℚ) + 1) * t)))

/-- `a_j s 2^j`: the coefficients of `s · q(2x)`. -/
def dil2 : ℚ → List ℚ → List ℚ
  | _, [] => []
  | s, a :: as => a * s :: dil2 (2 * s) as

/-- The coefficient list of `Σ_{k ≥ 1} f_k T_k(x) / k`. -/
def polyT (f : List ℚ) : List ℚ := dil2 (1 / 2) (chebAcc f 0 [2] [0, 1] [])

/-- The state `(Tp, Tc, acc)` of `chebAcc` after a list (for chunked certificates). -/
def chebSt : List ℚ → ℕ → List ℚ → List ℚ → List ℚ → List ℚ × List ℚ × List ℚ
  | [], _, Tp, Tc, acc => (Tp, Tc, acc)
  | c :: cs, k, Tp, Tc, acc =>
      chebSt cs (k + 1) Tc (cStep Tp Tc) (vecAdd acc (Tc.map (fun t => c / ((k : ℚ) + 1) * t)))

theorem chebAcc_append : ∀ (l1 l2 : List ℚ) (k : ℕ) (Tp Tc acc : List ℚ),
    chebAcc (l1 ++ l2) k Tp Tc acc =
      chebAcc l2 (k + l1.length) (chebSt l1 k Tp Tc acc).1 (chebSt l1 k Tp Tc acc).2.1
        (chebSt l1 k Tp Tc acc).2.2
  | [], l2, k, Tp, Tc, acc => by simp [chebSt]
  | c :: cs, l2, k, Tp, Tc, acc => by
    rw [List.cons_append, chebAcc, chebAcc_append cs l2 (k + 1), chebSt, List.length_cons,
      show k + 1 + cs.length = k + (cs.length + 1) by ring]

/-- One chunk of a chunked `chebAcc` evaluation with a literal state `S`. -/
theorem chebAcc_chunk {l1 l2 : List ℚ} {k k' : ℕ} {Tp Tc acc : List ℚ} {S : List ℚ × List ℚ × List ℚ}
    (h : chebSt l1 k Tp Tc acc = S) (hk : k + l1.length = k') :
    chebAcc (l1 ++ l2) k Tp Tc acc = chebAcc l2 k' S.1 S.2.1 S.2.2 := by
  rw [chebAcc_append, h, hk]

theorem chebAcc_nil (k : ℕ) (Tp Tc acc : List ℚ) : chebAcc [] k Tp Tc acc = acc := rfl

theorem polyTow_dil2 : ∀ (L : List ℚ) (s : ℚ) (x : ℝ),
    polyTow (dil2 s L) 0 x = (s : ℝ) * polyTow L 0 (2 * x)
  | [], s, x => by simp [dil2, polyTow_zero_nil]
  | a :: as, s, x => by
    rw [dil2, polyTow_zero_cons, polyTow_zero_cons, polyTow_dil2 as (2 * s) x]
    push_cast
    ring

theorem polyTow_cStep (Tp Tc : List ℚ) (y : ℝ) :
    polyTow (cStep Tp Tc) 0 y = y * polyTow Tc 0 y - polyTow Tp 0 y := by
  rw [cStep, polyTow_zero_vecAdd, polyTow_zero_cons, polyTow_zero_map_mul]
  push_cast
  ring

theorem chebT_eval_add_two (k : ℕ) (z : ℝ) :
    (Polynomial.Chebyshev.T ℝ ((k + 2 : ℕ) : ℤ)).eval z =
      2 * z * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval z -
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval z := by
  have e : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
  have e' : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  rw [e, e', Polynomial.Chebyshev.T_add_two]
  simp

theorem polyTow_chebAcc (y : ℝ) : ∀ (cs : List ℚ) (k : ℕ) (Tp Tc acc : List ℚ),
    polyTow Tp 0 y = 2 * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (y / 2) →
    polyTow Tc 0 y = 2 * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (y / 2) →
    polyTow (chebAcc cs k Tp Tc acc) 0 y = polyTow acc 0 y +
      ∑ j ∈ range cs.length, ((cs.getD j 0 : ℚ) : ℝ) / (((k + j : ℕ) : ℝ) + 1) *
        (2 * (Polynomial.Chebyshev.T ℝ ((k + j + 1 : ℕ) : ℤ)).eval (y / 2))
  | [], k, Tp, Tc, acc, _, _ => by simp [chebAcc]
  | c :: cs, k, Tp, Tc, acc, hp, hc => by
    have hn : polyTow (cStep Tp Tc) 0 y =
        2 * (Polynomial.Chebyshev.T ℝ ((k + 1 + 1 : ℕ) : ℤ)).eval (y / 2) := by
      rw [polyTow_cStep, hp, hc, show k + 1 + 1 = k + 2 by ring, chebT_eval_add_two]
      ring
    rw [chebAcc, polyTow_chebAcc y cs (k + 1) Tc (cStep Tp Tc) _ hc hn, polyTow_zero_vecAdd,
      polyTow_zero_map_mul, hc, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    have e1 : ∀ j : ℕ, ((k + 1 + j : ℕ) : ℝ) = ((k + (j + 1) : ℕ) : ℝ) := fun j => by push_cast; ring
    have e2 : ∀ j : ℕ, k + 1 + j + 1 = k + (j + 1) + 1 := fun j => by ring
    simp only [e1, e2]
    push_cast
    ring

theorem polyTow_polyT (f : List ℚ) (x : ℝ) : polyTow (polyT f) 0 x = finT (fQ f) f.length x := by
  rw [polyT, polyTow_dil2]
  rw [polyTow_chebAcc (2 * x) f 0 [2] [0, 1] [] (by simp [polyTow_zero_cons, polyTow_zero_nil])
    (by simp [polyTow_zero_cons, polyTow_zero_nil])]
  rw [polyTow_zero_nil, zero_add, finT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fQ_succ, show 2 * x / 2 = x by ring, show (0 + j + 1 : ℕ) = j + 1 by ring]
  push_cast
  ring

/-- Alternating signs `(-1)^j f_j`. -/
def altGo : ℚ → List ℚ → List ℚ
  | _, [] => []
  | s, c :: cs => s * c :: altGo (-s) cs

def altL (f : List ℚ) : List ℚ := altGo 1 f

theorem altGo_length : ∀ (s : ℚ) (f : List ℚ), (altGo s f).length = f.length
  | _, [] => rfl
  | s, c :: cs => by simp [altGo, altGo_length (-s) cs]

theorem altGo_getD : ∀ (s : ℚ) (f : List ℚ) (k : ℕ), (altGo s f).getD k 0 = s * (-1) ^ k * f.getD k 0
  | _, [], k => by simp [altGo]
  | s, c :: cs, 0 => by simp [altGo]
  | s, c :: cs, k + 1 => by
    simp only [altGo, List.getD_cons_succ]
    rw [altGo_getD (-s) cs k]
    ring

/-! ### 5. Block values -/

/-- The S-closed form of a sequence form with the given polynomial block. -/
def seqSFQ (L : List ℚ) (tl : List TailQ) : FieldQ := ⟨L, [], tl.map sPoleQ⟩
/-- The T-closed form. -/
def seqTFQ (L : List ℚ) (tl : List TailQ) : FieldQ := ⟨L, [], tl.map tPoleQ⟩
/-- The S-closed form at `-x` (real tail weights). -/
def seqSnFQ (L : List ℚ) (tl : List TailQ) : FieldQ := ⟨negX L, [], (tl.map sPoleQ).map reflP⟩

theorem fval_seqS (d : SeqQ) (x : ℝ) :
    fval (seqSFQ (polyS d.f) d.tail) x = d.form.Sform x - sConst (d.tail.map TailQ.toC) := by
  simp only [fval, seqSFQ, plogSumTower, List.map_nil, List.sum_nil, polyTow_polyS, poleFn_eq,
    SeqQ.form, SeqForm.Sform, sPoles_map]
  ring

theorem fval_seqT (d : SeqQ) (x : ℝ) :
    fval (seqTFQ (polyT d.f) d.tail) x = d.form.Tform x - tConst (d.tail.map TailQ.toC) := by
  simp only [fval, seqTFQ, plogSumTower, List.map_nil, List.sum_nil, polyTow_polyT, poleFn_eq,
    SeqQ.form, SeqForm.Tform, tPoles_map]
  ring

theorem fval_seqSn (d : SeqQ) (hr : ∀ t ∈ d.tail, t.ri = 0) (x : ℝ) :
    fval (seqSnFQ (polyS d.f) d.tail) x = d.form.Sform (-x) - sConst (d.tail.map TailQ.toC) := by
  have hr' : ∀ q ∈ d.tail.map sPoleQ, q.ri = 0 := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
    simp [sPoleQ, hr t ht]
  simp only [fval, seqSnFQ, plogSumTower, List.map_nil, List.sum_nil, polyTow_zero_negX,
    polyTow_polyS, poleFn_reflP _ hr', poleFn_eq, SeqQ.form, SeqForm.Sform, sPoles_map]
  ring

theorem fval_rS (d : SeqQ) (ht : d.tail = []) (x : ℝ) :
    fval (fqPoly (polyS d.f)) x = rLim d.form x := by
  rw [fval_poly, polyTow_polyS, rLim, SeqQ.form, ht]
  simp [geoLim]

theorem fval_refRow (qT qF : List PieceQ) (x : ℝ) :
    fval (refRowFieldQ qT qF) x = refRowForm (qT.map PieceQ.toPiece) (qF.map PieceQ.toPiece) x := by
  rw [refRowForm_eq_fieldTower]
  have hp : (refRowFieldQ qT qF).poles = [] := by simp [refRowFieldQ, fqAdd, fqNeg]
  simp only [fval, fieldTower, poleTower_zero, hp, poleFn_nil]

/-- The reference row of the signed reference `P - N` as one `FieldQ`
(`refRowFieldQ qT qF - refRowFieldQ qTn qFn`; no poles). -/
def refRowSFQ (qT qF qTn qFn : List PieceQ) : FieldQ :=
  fqSum [refRowFieldQ qT qF, fqScale (-1) (refRowFieldQ qTn qFn)]

theorem fval_refRowS (qT qF qTn qFn : List PieceQ) (x : ℝ) :
    fval (refRowSFQ qT qF qTn qFn) x =
      refRowForm (qT.map PieceQ.toPiece) (qF.map PieceQ.toPiece) x -
        refRowForm (qTn.map PieceQ.toPiece) (qFn.map PieceQ.toPiece) x := by
  simp only [refRowSFQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fval_scale,
    fval_refRow]
  push_cast
  ring

/-- The Laurent terms of the dilated potential of the signed species `P - N`:
`dilTermsQ qs ++ scaleL (-1) (dilTermsQ qn)`. -/
def dilTermsS (qs qn : List PieceQ) : List LTerm := dilTermsQ qs ++ scaleL (-1) (dilTermsQ qn)

theorem dilS_eq (qs qn : List PieceQ) (x : ℝ) (hx : x ≠ 0) :
    dilPot (qs.map PieceQ.toPiece) x - dilPot (qn.map PieceQ.toPiece) x =
      lfieldTower (dilTermsS qs qn) 0 x := by
  rw [dilTermsS, lfieldTower_append, lfieldTower_scaleL_zero, ← dilPot_eq_lfieldTower qs x hx,
    ← dilPot_eq_lfieldTower qn x hx]
  push_cast
  ring

theorem denPoly_fQ (bs : List ℚ) (x : ℝ) :
    denPoly (fQ bs) bs.length x = 2 * polyTow (negX (polyS bs)) 0 x := by
  rw [polyTow_zero_negX, polyTow_polyS, denPoly, finS]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### 6. The limit fields of the problem -/

/-- `c₁ log|x| + c₂ log(1 - x) - c₃ log(1 + x²)` (the free-row field `rfLim`). -/
def rfQ (c1 c2 c3 : ℚ) (x : ℝ) : ℝ :=
  (c1 : ℝ) * Real.log |x| + (c2 : ℝ) * Real.log (1 - x) - (c3 : ℝ) * Real.log (1 + x ^ 2)

def rfFQ (c1 c2 c3 : ℚ) : FieldQ := fqSum [logFQ c1 0, logFQ c2 1, sqFQ c3]

theorem fval_rf (c1 c2 c3 : ℚ) (x : ℝ) : fval (rfFQ c1 c2 c3) x = rfQ c1 c2 c3 x := by
  simp only [rfFQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fval_log,
    fval_sq, rfQ]
  have e : Real.log |x - ((1 : ℚ) : ℝ)| = Real.log (1 - x) := by
    rw [← Real.log_abs (1 - x)]; push_cast; rw [abs_sub_comm]
  rw [e]
  push_cast
  simp only [sub_zero]
  ring

theorem rfLim_eq (P : CatalanMeasure.Parametric.Parameters) :
    rfLim P = rfQ (((P.b0 + P.q0 + 2 * P.g0 : ℕ) : ℚ) / P.n0) (2 * (P.h0 : ℚ) / P.n0)
      (((P.n0 + P.b0 + P.q0 + P.g0 + P.h0 : ℕ) : ℚ) / P.n0) := by
  funext x
  simp only [rfLim, rfQ]
  push_cast
  ring

/-- `c₁ log s + c₂ log(1 - s)` (the column field `cfLim`). -/
def cfQ (c1 c2 : ℚ) (s : ℝ) : ℝ := (c1 : ℝ) * Real.log s + (c2 : ℝ) * Real.log (1 - s)

def cfFQ (c1 c2 : ℚ) : FieldQ := fqSum [logFQ c1 0, logFQ c2 1]

theorem fval_cf (c1 c2 : ℚ) (s : ℝ) : fval (cfFQ c1 c2) s = cfQ c1 c2 s := by
  simp only [cfFQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fval_log, cfQ]
  have e : Real.log |s - ((1 : ℚ) : ℝ)| = Real.log (1 - s) := by
    rw [← Real.log_abs (1 - s)]; push_cast; rw [abs_sub_comm]
  have e0 : Real.log |s - ((0 : ℚ) : ℝ)| = Real.log s := by
    rw [← Real.log_abs s]; push_cast; rw [sub_zero]
  rw [e, e0]
  ring

theorem cfLim_eq (P : CatalanMeasure.Parametric.Parameters) :
    cfLim P = cfQ ((P.b0 : ℚ) / P.n0) ((P.q0 : ℚ) / P.n0) := by
  funext s
  simp only [cfLim, cfQ]
  push_cast
  ring

/-- The fixed-row limit field `-c log (1 + x²)`. -/
def rmQ (c : ℚ) (x : ℝ) : ℝ := -(c : ℝ) * Real.log (1 + x ^ 2)

theorem fval_rm (c : ℚ) (x : ℝ) : fval (sqFQ c) x = rmQ c x := fval_sq c x

/-- The near-row limit field `-c log (1 + x²) + c' log |x|`. -/
def rnQ (c c' : ℚ) (x : ℝ) : ℝ := -(c : ℝ) * Real.log (1 + x ^ 2) + (c' : ℝ) * Real.log |x|

def rnFQ (c c' : ℚ) : FieldQ := fqSum [sqFQ c, logFQ c' 0]

theorem fval_rn (c c' : ℚ) (x : ℝ) : fval (rnFQ c c') x = rnQ c c' x := by
  simp only [rnFQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fval_log,
    fval_sq, rnQ]
  push_cast
  simp only [sub_zero]
  ring

/-! ### 7. The identifications -/

section Ident

variable (T : TrialQ)

/-- Constant of the S-form of `v`, `p`'s T-form, `a`'s S-form. -/
def cSv : ℝ := sConst (T.v.tail.map TailQ.toC)
def cTv : ℝ := tConst (T.v.tail.map TailQ.toC)
def cTp : ℝ := tConst (T.p.tail.map TailQ.toC)
def cSa : ℝ := sConst (T.a.tail.map TailQ.toC)
def cTa : ℝ := tConst (T.a.tail.map TailQ.toC)

/-- **SN**: the free negative-row field. -/
def snFQ (rf : FieldQ) (vS pT aS rS : List ℚ) (rr : FieldQ) : FieldQ :=
  fqSum [rf, fqScale (-1) (seqSFQ vS T.v.tail), fqScale (-2 * (1 - T.η)) rr,
    fqScale (-4 * T.η) (seqTFQ pT T.p.tail), fqScale (-2) (seqSnFQ aS T.a.tail),
    fqScale (-1) (fqPoly rS)]

def snK : ℝ := -cSv T - 4 * (T.η : ℝ) * cTp T - 2 * cSa T

theorem hid_sn {RfL : ℝ → ℝ} {rf : FieldQ} (hrf : ∀ x, RfL x = fval rf x)
    {vS pT aS rS : List ℚ} {rr : FieldQ}
    (hv : polyS T.v.f = vS) (hp : polyT T.p.f = pT) (ha : polyS T.a.f = aS)
    (hRs : polyS T.R.f = rS) (hrr : refRowSFQ T.qT T.qF T.qTn T.qFn = rr)
    (hRt : T.R.tail = []) (har : ∀ t ∈ T.a.tail, t.ri = 0)
    {fq : FieldQ} (hfq : fq = snFQ T rf vS pT aS rS rr) (x : ℝ) :
    fNegLim T.form RfL x = fieldTower fq (poleFn fq.poles) 0 x + snK T := by
  subst hv hp ha hRs hrr hfq
  rw [fieldTower_poleFn]
  simp only [snFQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fval_scale,
    fval_seqS, fval_seqT, fval_seqSn _ har, fval_rS _ hRt, fval_refRowS, ← hrf]
  simp only [fNegLim, snK, cSv, cTp, cSa, TrialForm.refRow, TrialQ.form]
  push_cast
  ring

/-- **SP**: the free positive-row field (spike cost kept as the indicator). -/
def spFQ (rf : FieldQ) (vS pT aS rS bS : List ℚ) (rr : FieldQ) (σ : ℚ) : FieldQ :=
  fqSum [rf, fqScale (-1) (seqSFQ vS T.v.tail), fqScale (-2 * (1 - T.η)) rr,
    fqScale (-4 * T.η) (seqTFQ pT T.p.tail), fqScale 2 (seqSnFQ aS T.a.tail),
    fqScale (-2 * σ) (fqPoly (negX bS)), fqPoly rS]

def spK : ℝ := -cSv T - 4 * (T.η : ℝ) * cTp T + 2 * cSa T + 2 * (T.Sup : ℝ)

theorem hid_sp {RfL : ℝ → ℝ} {rf : FieldQ} (hrf : ∀ x, RfL x = fval rf x)
    {vS pT aS rS bS : List ℚ} {rr : FieldQ} {bs : List ℚ} {σ : ℚ} {csL θL : ℝ}
    (hv : polyS T.v.f = vS) (hp : polyT T.p.f = pT) (ha : polyS T.a.f = aS)
    (hRs : polyS T.R.f = rS) (hb : polyS bs = bS) (hrr : refRowSFQ T.qT T.qF T.qTn T.qFn = rr)
    (hRt : T.R.tail = []) (har : ∀ t ∈ T.a.tail, t.ri = 0)
    {fq : FieldQ} (hfq : fq = spFQ T rf vS pT aS rS bS rr σ) {x : ℝ} (hx : x ≠ 0) :
    fPosLim T.form RfL σ (fQ bs) bs.length csL θL x =
      fieldTower fq (poleFn fq.poles) 0 x + lfieldTower (dilTermsS T.qT T.qTn) 0 x + spK T +
        csL * (if 1 - θL < x then 1 else 0) := by
  subst hv hp ha hRs hb hrr hfq
  rw [fieldTower_poleFn, ← dilS_eq _ _ x hx]
  simp only [spFQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fval_scale,
    fval_seqS, fval_seqT, fval_seqSn _ har, fval_rS _ hRt, fval_refRowS, fval_poly, ← hrf]
  simp only [fPosLim, spK, cSv, cTp, cSa, TrialForm.refRow, TrialForm.dilT, TrialQ.form, denPoly_fQ]
  push_cast
  ring

/-- **SC**: the column field. -/
def scFQ (cf : FieldQ) (vT : List ℚ) : FieldQ := fqSum [cf, fqScale 2 (seqTFQ vT T.v.tail)]

def scK : ℝ := 2 * cTv T

theorem hid_sc {CfL : ℝ → ℝ} {cf : FieldQ} (hcf : ∀ s, CfL s = fval cf s) {vT : List ℚ}
    (hv : polyT T.v.f = vT) {fq : FieldQ} (hfq : fq = scFQ T cf vT) (s : ℝ) :
    CfL s + 2 * T.form.v.Tform s = fieldTower fq (poleFn fq.poles) 0 s + scK T := by
  subst hv hfq
  rw [fieldTower_poleFn]
  simp only [scFQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fval_scale,
    fval_seqT, ← hcf]
  simp only [scK, cTv, TrialQ.form]
  push_cast
  ring

/-- **σ⁻**: the first-kind fixed negative-node field. -/
def smFQ (rm : FieldQ) (pT aS rS : List ℚ) (rr : FieldQ) : FieldQ :=
  fqSum [rm, fqScale (-(1 - T.η)) rr, fqScale (-2 * T.η) (seqTFQ pT T.p.tail),
    fqScale (-2) (seqSnFQ aS T.a.tail), fqScale (-1) (fqPoly rS)]

def smK : ℝ := -2 * (T.η : ℝ) * cTp T - 2 * cSa T

theorem hid_sm {RmL : ℝ → ℝ} {rm : FieldQ} (hrm : ∀ x, RmL x = fval rm x)
    {pT aS rS : List ℚ} {rr : FieldQ}
    (hp : polyT T.p.f = pT) (ha : polyS T.a.f = aS) (hRs : polyS T.R.f = rS)
    (hrr : refRowSFQ T.qT T.qF T.qTn T.qFn = rr) (hRt : T.R.tail = []) (har : ∀ t ∈ T.a.tail, t.ri = 0)
    {fq : FieldQ} (hfq : fq = smFQ T rm pT aS rS rr) (x : ℝ) :
    fNegMLim T.form RmL x = fieldTower fq (poleFn fq.poles) 0 x + smK T := by
  subst hp ha hRs hrr hfq
  rw [fieldTower_poleFn]
  simp only [smFQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fval_scale,
    fval_seqT, fval_seqSn _ har, fval_rS _ hRt, fval_refRowS, ← hrm]
  simp only [fNegMLim, smK, cTp, cSa, TrialForm.refRow, TrialQ.form]
  push_cast
  ring

/-- **σ⁺**: the first-kind fixed positive-node field with the Lemma R′ remainder. -/
def spmFQ (rm : FieldQ) (pT aS rS bS : List ℚ) (rr : FieldQ) (σ rc α : ℚ) : FieldQ :=
  fqSum [rm, fqScale (-(1 - T.η)) rr, fqScale (-2 * T.η) (seqTFQ pT T.p.tail),
    fqScale 2 (seqSnFQ aS T.a.tail), fqScale (-2 * σ) (fqPoly (negX bS)), fqPoly rS,
    fqScale (rc * α) m1sqFQ]

def spmK : ℝ := -2 * (T.η : ℝ) * cTp T + 2 * cSa T + 2 * (T.Sup : ℝ)

theorem hid_spm {RmL : ℝ → ℝ} {rm : FieldQ} (hrm : ∀ x, RmL x = fval rm x)
    {pT aS rS bS : List ℚ} {rr : FieldQ} {bs : List ℚ} {σ rc α : ℚ} {csL θL : ℝ}
    (hp : polyT T.p.f = pT) (ha : polyS T.a.f = aS) (hRs : polyS T.R.f = rS)
    (hb : polyS bs = bS) (hrr : refRowSFQ T.qT T.qF T.qTn T.qFn = rr) (hRt : T.R.tail = [])
    (har : ∀ t ∈ T.a.tail, t.ri = 0)
    {fq : FieldQ} (hfq : fq = spmFQ T rm pT aS rS bS rr σ rc α) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    fPosMSLim T.form RmL σ (fQ bs) bs.length csL θL x + rc * α * (-Real.log (1 - x ^ 2)) =
      fieldTower fq (poleFn fq.poles) 0 x + lfieldTower (dilTermsS T.qT T.qTn) 0 x + spmK T +
        csL * (if 1 - θL < x then 1 else 0) := by
  subst hp ha hRs hb hrr hfq
  rw [fieldTower_poleFn, ← dilS_eq _ _ x hx.1.ne']
  simp only [spmFQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fval_scale,
    fval_seqT, fval_seqSn _ har, fval_rS _ hRt, fval_refRowS, fval_poly,
    fval_m1sq ⟨by linarith [hx.1], hx.2⟩, ← hrm]
  simp only [fPosMSLim, spmK, cTp, cSa, TrialForm.refRow, TrialForm.dilT, TrialQ.form, denPoly_fQ]
  push_cast
  ring

/-- **Near-type** fixed nodes. -/
def nearFQ (rn : FieldQ) (aS rS bS : List ℚ) (σ α β : ℚ) : FieldQ :=
  fqSum [rn, fqScale 2 (seqSnFQ aS T.a.tail), fqScale (-2 * σ) (fqPoly (negX bS)), fqPoly rS,
    fqScale (α / 2) (logFQ 1 (-1)), fqScale (β / (4 * (1 - T.η))) m1sqFQ]

def nearK (α β : ℚ) : ℝ :=
  2 * cSa T + remC (1 - 2 * (T.η : ℝ)) * (β : ℝ) * (2 * Real.log 2) +
    ((T.η : ℝ) + (α : ℝ) / 2) * Real.log 2 + 2 * (T.Sup : ℝ)

theorem hid_near {RnL : ℝ → ℝ} {rn : FieldQ} (hrn : ∀ x, RnL x = fval rn x)
    {aS rS bS : List ℚ} {bs : List ℚ} {σ α β : ℚ} {csL θL : ℝ}
    (ha : polyS T.a.f = aS) (hRs : polyS T.R.f = rS) (hb : polyS bs = bS) (hRt : T.R.tail = [])
    (har : ∀ t ∈ T.a.tail, t.ri = 0)
    {fq : FieldQ} (hfq : fq = nearFQ T rn aS rS bS σ α β) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    fNearMSLim T.form RnL α β σ (fQ bs) bs.length csL θL x =
      fieldTower fq (poleFn fq.poles) 0 x +
        lfieldTower (scaleL (-1) (reflL (dilTermsS T.qF T.qFn))) 0 x + nearK T α β +
        csL * (if 1 - θL < x then 1 else 0) := by
  subst ha hRs hb hfq
  rw [fieldTower_poleFn, lfieldTower_scaleL_zero, lfieldTower_reflL_zero, ← dilS_eq _ _ (-x) (neg_ne_zero.mpr hx.1.ne')]
  have e1 : Real.log |x - ((-1 : ℚ) : ℝ)| = Real.log (1 + x) := by
    rw [← Real.log_abs (1 + x)]; push_cast; ring_nf
  simp only [nearFQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fval_scale,
    fval_seqSn _ har, fval_rS _ hRt, fval_poly, fval_log, e1,
    fval_m1sq ⟨by linarith [hx.1], hx.2⟩, ← hrn]
  simp only [fNearMSLim, nearK, cSa, TrialForm.dilF, TrialQ.form, denPoly_fQ]
  push_cast
  ring

/-- The Frostman field (`h_ℓ` of SpikeDischarge) at `τ = 1`:
`Σ_k (-1)^k R_{k+1} T_{k+1}(x)/(k+1) - 2 T_a(x)`. -/
def frLim (F : TrialForm) (x : ℝ) : ℝ :=
  ∑ k ∈ range F.R.L, (-1 : ℝ) ^ k * F.R.f (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ) -
    2 * F.a.Tform x

def frFQ (rT aT : List ℚ) : FieldQ := fqSum [fqPoly rT, fqScale (-2) (seqTFQ aT T.a.tail)]

def frK : ℝ := -2 * cTa T

theorem hid_fr {rT aT : List ℚ} (hr : polyT (altL T.R.f) = rT) (ha : polyT T.a.f = aT)
    {fq : FieldQ} (hfq : fq = frFQ T rT aT) (x : ℝ) :
    frLim T.form x = fieldTower fq (poleFn fq.poles) 0 x + frK T := by
  subst hr ha hfq
  rw [fieldTower_poleFn]
  simp only [frFQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fval_scale,
    fval_seqT, fval_poly, polyTow_polyT]
  simp only [frLim, frK, cTa, TrialQ.form, SeqQ.form, finT, altL, altGo_length]
  have e : ∀ k ∈ range T.R.f.length,
      fQ (altGo 1 T.R.f) (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
          ((k + 1 : ℕ) : ℝ) =
        (-1 : ℝ) ^ k * fQ T.R.f (k + 1) *
          (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ) := by
    intro k _
    rw [fQ_succ, fQ_succ, altGo_getD]
    push_cast
    ring
  rw [Finset.sum_congr rfl e]
  push_cast
  ring

end Ident

/-! ### 8. Polynomial rounding (for cell data with rounded polynomial parts) -/

theorem polyTow_zero_eq_sum (p : List ℚ) (x : ℝ) :
    polyTow p 0 x = ∑ k ∈ range p.length, ((p.getD k 0 : ℚ) : ℝ) * x ^ k := by
  induction p with
  | nil => simp [polyTow_zero_nil]
  | cons a as ih =>
    rw [polyTow_zero_cons, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ]; ring

/-- `Σ |p_k - q_k|` over the longer list. -/
def l1Diff : List ℚ → List ℚ → ℚ
  | a :: as, b :: bs => |a - b| + l1Diff as bs
  | [], bs => (bs.map (fun t => |t|)).sum
  | as, [] => (as.map (fun t => |t|)).sum

theorem polyTow_abs_le (p : List ℚ) {x : ℝ} (hx : |x| ≤ 1) :
    |polyTow p 0 x| ≤ (((p.map (fun t => |t|)).sum : ℚ) : ℝ) := by
  induction p with
  | nil => simp [polyTow_zero_nil]
  | cons a as ih =>
    rw [polyTow_zero_cons]
    simp only [List.map_cons, List.sum_cons]
    rw [Rat.cast_add, Rat.cast_abs]
    have h1 : |x * polyTow as 0 x| ≤ |polyTow as 0 x| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hx
    calc |(a : ℝ) + x * polyTow as 0 x| ≤ |(a : ℝ)| + |x * polyTow as 0 x| := abs_add_le _ _
      _ ≤ _ := by linarith [ih, h1]

theorem polyTow_sub_le : ∀ (p q : List ℚ) {x : ℝ}, |x| ≤ 1 →
    |polyTow p 0 x - polyTow q 0 x| ≤ ((l1Diff p q : ℚ) : ℝ)
  | a :: as, b :: bs, x, hx => by
    have ih := polyTow_sub_le as bs hx
    have h1 : |x * (polyTow as 0 x - polyTow bs 0 x)| ≤ |polyTow as 0 x - polyTow bs 0 x| := by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hx
    have h2 : |((a : ℝ) - b) + x * (polyTow as 0 x - polyTow bs 0 x)| ≤
        |(a : ℝ) - b| + |x * (polyTow as 0 x - polyTow bs 0 x)| := abs_add_le _ _
    have e : polyTow (a :: as) 0 x - polyTow (b :: bs) 0 x =
        ((a : ℝ) - b) + x * (polyTow as 0 x - polyTow bs 0 x) := by
      rw [polyTow_zero_cons, polyTow_zero_cons]; ring
    have e2 : ((l1Diff (a :: as) (b :: bs) : ℚ) : ℝ) = |(a : ℝ) - b| + ((l1Diff as bs : ℚ) : ℝ) := by
      rw [l1Diff, Rat.cast_add, Rat.cast_abs, Rat.cast_sub]
    rw [e, e2]
    linarith
  | [], bs, x, hx => by
    rw [polyTow_zero_nil, zero_sub, abs_neg]
    have := polyTow_abs_le bs hx
    cases bs <;> simpa [l1Diff] using this
  | a :: as, [], x, hx => by
    rw [polyTow_zero_nil, sub_zero]
    simpa [l1Diff] using polyTow_abs_le (a :: as) hx

/-- **Rounding transfer**: a cell field `fr` with the same logarithmic and pole parts as `fq` and a
rounded polynomial part bounds `fq` up to the `ℓ¹` distance of the polynomial parts, on `|x| ≤ 1`. -/
theorem fieldTower_le_round (fq fr : FieldQ) (hpl : fq.plogs = fr.plogs) (hpo : fq.poles = fr.poles)
    {x : ℝ} (hx : |x| ≤ 1) :
    fieldTower fq (poleFn fq.poles) 0 x ≤
      fieldTower fr (poleFn fr.poles) 0 x + ((l1Diff fq.poly fr.poly : ℚ) : ℝ) := by
  rw [fieldTower_poleFn, fieldTower_poleFn]
  simp only [fval, hpl, hpo]
  have := (abs_le.mp (polyTow_sub_le fq.poly fr.poly hx)).2
  linarith

/-! ### 9. The `Spec` of a trial: data checks -/

/-- Tail admissibility (`TailOK`) as a Boolean check. -/
def tailOKB (tl : List TailQ) : Bool :=
  tl.all (fun t => decide (t.zr * t.zr + t.zi * t.zi < 1) && decide (t.zr ≠ 0 ∨ t.zi ≠ 0) &&
    decide (t.zi ≠ 0 ∨ t.ri = 0))

theorem tailOK_of (tl : List TailQ) (h : tailOKB tl = true) : TailOK (tl.map TailQ.toC) := by
  intro zr hzr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hzr
  have h1 := List.all_eq_true.mp h t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨hd, hnz⟩, him⟩ := h1
  refine ⟨?_, ?_, ?_⟩
  · have h2 : ‖(TailQ.toC t).1‖ ^ 2 < 1 := by
      simp only [TailQ.toC]
      rw [CatalanMeasure.Cert.norm_barrierComplex_sq]
      exact_mod_cast hd
    nlinarith [norm_nonneg (TailQ.toC t).1]
  · simp only [TailQ.toC, barrierComplex]
    intro h0
    have hr := congrArg Complex.re h0
    have hi := congrArg Complex.im h0
    simp at hr hi
    rcases hnz with h | h
    · exact h hr
    · exact h hi
  · simp only [TailQ.toC, barrierComplex]
    rcases him with h | h
    · left; simpa using h
    · right; simpa using h

theorem lpEval_eq_polyTow (p : List ℚ) (x : ℝ) : lpEval p x = polyTow p 0 x := by
  induction p with
  | nil => simp [polyTow_zero_nil]
  | cons a as ih => rw [CatalanMeasure.Cert.lpEval_cons, polyTow_zero_cons, ih]

theorem dens_toPiece (q : PieceQ) (y : ℝ) : q.toPiece.dens y = lpEval q.p y := by
  rw [lpEval_eq_polyTow, polyTow_zero_eq_sum]
  simp only [Piece.dens, PieceQ.toPiece, pc]

/-- `PieceOK` from a positivity cover. -/
theorem pieceOK_of (q : PieceQ) (cs : List ℚ) (hle : q.lo ≤ q.hi)
    (h : CatalanMeasure.Signed.Consts.nnCov q.p q.lo cs q.hi = true) : PieceOK q.toPiece := by
  refine ⟨by simp only [PieceQ.toPiece]; exact_mod_cast hle, fun y hy => ?_⟩
  rw [dens_toPiece]
  exact CatalanMeasure.Signed.Consts.nnCov_sound q.p cs q.lo q.hi h y hy.1 hy.2

/-- `C - p` as a coefficient list. -/
def capL (C : ℚ) (p : List ℚ) : List ℚ := vecAdd [C] (p.map (fun t => -1 * t))

theorem lpEval_capL (C : ℚ) (p : List ℚ) (x : ℝ) : lpEval (capL C p) x = (C : ℝ) - lpEval p x := by
  rw [lpEval_eq_polyTow, lpEval_eq_polyTow, capL, polyTow_zero_vecAdd, polyTow_zero_map_mul,
    polyTow_zero_cons, polyTow_zero_nil]
  push_cast; ring

open CatalanMeasure.Signed.ReflectionEnergy in
/-- One piece inside `[0, 1]` with density at most `C` has a `BD` bound `C`. -/
theorem piece_BD (q : Piece) (hlo : 0 ≤ q.lo) (hhi : q.hi ≤ 1) {C : ℝ}
    (hC : ∀ y ∈ Icc q.lo q.hi, q.dens y ≤ C) : BD q.meas C := by
  unfold BD Piece.meas
  have h1 : (volume.restrict (Ioc q.lo q.hi)).withDensity (fun y => ENNReal.ofReal (q.dens y)) ≤
      (volume.restrict (Ioc q.lo q.hi)).withDensity (fun _ => ENNReal.ofReal C) := by
    apply withDensity_mono
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
    exact ENNReal.ofReal_le_ofReal (hC y ⟨hy.1.le, hy.2⟩)
  rw [withDensity_const] at h1
  refine h1.trans ?_
  have h2 : volume.restrict (Ioc q.lo q.hi) ≤ volume.restrict (Ioo (0 : ℝ) 1) := by
    calc volume.restrict (Ioc q.lo q.hi) ≤ volume.restrict (Ioc (0 : ℝ) 1) :=
          Measure.restrict_mono (Ioc_subset_Ioc hlo hhi) le_rfl
      _ = volume.restrict (Ioo (0 : ℝ) 1) := Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  rw [Measure.le_iff']
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  have := Measure.le_iff'.mp h2 s
  gcongr

open CatalanMeasure.Signed.ReflectionEnergy in
theorem BD_add {m m' : Measure ℝ} {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (h : BD m C) (h' : BD m' C') :
    BD (m + m') (C + C') := by
  unfold BD at *
  rw [Measure.le_iff'] at *
  intro s
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at *
  rw [ENNReal.ofReal_add hC hC', add_mul]
  exact add_le_add (h s) (h' s)

open CatalanMeasure.Signed.ReflectionEnergy in
theorem BD_mono {m : Measure ℝ} {C C' : ℝ} (h : BD m C) (hle : C ≤ C') : BD m C' := by
  unfold BD at *
  rw [Measure.le_iff'] at *
  intro s
  simp only [Measure.smul_apply, smul_eq_mul] at *
  refine (h s).trans ?_
  gcongr

/-- A piece checked against a rational density cap. -/
def pieceCapOK (q : PieceQ) (C : ℚ) (cs : List ℚ) : Bool :=
  decide (0 ≤ q.lo) && decide (q.hi ≤ 1) && decide (0 ≤ C) &&
    CatalanMeasure.Signed.Consts.nnCov (capL C q.p) q.lo cs q.hi

/-- One cap per piece. -/
def capsOK : List PieceQ → List (ℚ × List ℚ) → Bool
  | [], [] => true
  | q :: qs, c :: cs => pieceCapOK q c.1 c.2 && capsOK qs cs
  | _, _ => false

open CatalanMeasure.Signed.ReflectionEnergy in
/-- `BD` of the measure of a list of rational pieces, from one cap per piece. -/
theorem polyMeas_BD : ∀ (qs : List PieceQ) (caps : List (ℚ × List ℚ)), capsOK qs caps = true →
    0 ≤ (caps.map Prod.fst).sum ∧
      BD (polyMeas (qs.map PieceQ.toPiece)) (((caps.map Prod.fst).sum : ℚ) : ℝ)
  | [], [], _ => by
    refine ⟨by simp, ?_⟩
    unfold BD
    simp [polyMeas]
  | q :: qs, c :: cs, h => by
    simp only [capsOK, pieceCapOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hlo, hhi⟩, hC0⟩, hcov⟩, hrest⟩ := h
    obtain ⟨hS, ih⟩ := polyMeas_BD qs cs hrest
    have hp : BD q.toPiece.meas (c.1 : ℝ) := by
      refine piece_BD q.toPiece (by simp [PieceQ.toPiece]; exact_mod_cast hlo)
        (by simp [PieceQ.toPiece]; exact_mod_cast hhi) fun y hy => ?_
      have := CatalanMeasure.Signed.Consts.nnCov_sound _ c.2 q.lo q.hi hcov y hy.1 hy.2
      rw [lpEval_capL] at this
      rw [dens_toPiece]; linarith
    have hm : polyMeas ((q :: qs).map PieceQ.toPiece) =
        q.toPiece.meas + polyMeas (qs.map PieceQ.toPiece) := by
      simp [polyMeas]
    have hc : (((c :: cs).map Prod.fst).sum : ℚ) = c.1 + (cs.map Prod.fst).sum := by simp
    refine ⟨by rw [hc]; linarith, ?_⟩
    rw [hm, hc, Rat.cast_add]
    exact BD_add (by exact_mod_cast hC0) (by exact_mod_cast hS) hp ih
  | [], _ :: _, h => by simp [capsOK] at h
  | _ :: _, [], h => by simp [capsOK] at h

/-- The data checks of a trial (all decidable except through the covers). -/
structure TrialQ.DataOK (T : TrialQ) (Cb : ℝ) : Prop where
  hvT : tailOKB T.v.tail = true
  haT : tailOKB T.a.tail = true
  hpT : tailOKB T.p.tail = true
  hη0 : 0 ≤ T.η
  hη1 : T.η < 1 / 2
  hRt : T.R.tail = []
  pT : ∀ q ∈ T.qT, PieceOK q.toPiece
  pF : ∀ q ∈ T.qF, PieceOK q.toPiece
  bdT : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas (T.qT.map PieceQ.toPiece)) Cb
  bdF : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas (T.qF.map PieceQ.toPiece)) Cb
  /-- The negative part `N` of `P - N`: nonnegative pieces on `(0, 1/8]`, density `≤ Cb`, mass `≤ 1`. -/
  pTn : ∀ q ∈ T.qTn, PieceOK q.toPiece
  pFn : ∀ q ∈ T.qFn, PieceOK q.toPiece
  hTn : ∀ q ∈ T.qTn, q.hi ≤ 1 / 8
  bdTn : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas (T.qTn.map PieceQ.toPiece)) Cb
  bdFn : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas (T.qFn.map PieceQ.toPiece)) Cb
  nm : (T.qTn.map PieceQ.massQ).sum + (T.qFn.map PieceQ.massQ).sum ≤ 1

/-- **`TrialForm.Spec` of a trial**: the definitional equations of the family member plus the
data checks. -/
theorem TrialQ.spec (T : TrialQ) (D : SignedData) (hτ : D.τ ∈ Ioo (0 : ℝ) 1)
    (hv : D.v = tseq (fQ T.v.f) (T.v.tail.map TailQ.toC))
    (ha : D.a = tseq (fQ T.a.f) (T.a.tail.map TailQ.toC))
    (hp : D.p = tseq (fQ T.p.f) (T.p.tail.map TailQ.toC))
    (hη : D.η = T.η) (hR : D.R = fun n => fQ T.R.f (n + 1)) (hSup : D.Sup = T.Sup)
    (ht : D.t = mneg D.μ D.τ)
    (hμT : D.μ.P true = polyMeas (T.qT.map PieceQ.toPiece))
    (hμF : D.μ.P false = polyMeas (T.qF.map PieceQ.toPiece))
    (hμTn : D.μ.N true = polyMeas (T.qTn.map PieceQ.toPiece))
    (hμFn : D.μ.N false = polyMeas (T.qFn.map PieceQ.toPiece))
    (hok : T.DataOK D.Cb) : T.form.Spec D where
  hτ := hτ
  hv := hv
  hvf := fQ_supp T.v.f
  hvT := tailOK_of _ hok.hvT
  ha := ha
  haf := fQ_supp T.a.f
  haT := tailOK_of _ hok.haT
  hp := hp
  hpf := fQ_supp T.p.f
  hpT := tailOK_of _ hok.hpT
  hη := hη
  hηI := by
    show ((T.η : ℚ) : ℝ) ∈ Ico (0 : ℝ) (1 / 2)
    have h0 : ((0 : ℚ) : ℝ) ≤ (T.η : ℝ) := Rat.cast_le.mpr hok.hη0
    have h1 : (T.η : ℝ) < ((1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr hok.hη1
    push_cast at h0 h1
    exact ⟨h0, h1⟩
  hR := by
    rw [hR]; funext n
    simp [TrialQ.form, SeqQ.form, tseq, hok.hRt]
  hRf := fQ_supp T.R.f
  hRok := by simp [TrialQ.form, SeqQ.form, hok.hRt]
  hRgT := ⟨0, fun n => by simp [TrialQ.form, SeqQ.form, hok.hRt, gseq]⟩
  hSup := hSup
  ht := ht
  hμT := hμT
  hμF := hμF
  hμTn := hμTn
  hμFn := hμFn
  pT := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact hok.pT r hr
  pF := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact hok.pF r hr
  pTn := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact hok.pTn r hr
  pFn := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact hok.pFn r hr
  hTn := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    have h := hok.hTn r hr
    show ((r.hi : ℚ) : ℝ) ≤ 1 / 8
    have h2 : ((r.hi : ℚ) : ℝ) ≤ (((1 / 8 : ℚ)) : ℝ) := Rat.cast_le.mpr h
    have h3 : (((1 / 8 : ℚ)) : ℝ) = 1 / 8 := by norm_num
    exact h2.trans_eq h3
  bd :=
    { hP := fun b => by
        cases b
        · rw [hμF]; exact hok.bdF
        · rw [hμT]; exact hok.bdT
      hN := fun b => by
        cases b
        · rw [hμFn]; exact hok.bdFn
        · rw [hμTn]; exact hok.bdTn
      hNm := by
        rw [Fintype.sum_bool, hμTn, hμFn]
        have hm : ∀ qs : List PieceQ, (∀ q ∈ qs, PieceOK q.toPiece) →
            (polyMeas (qs.map PieceQ.toPiece)).real univ = (((qs.map PieceQ.massQ).sum : ℚ) : ℝ) := by
          intro qs hqs
          have hq' : ∀ q ∈ qs.map PieceQ.toPiece, PieceOK q := by
            intro q hq
            obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
            exact hqs r hr
          have := integral_const_polyMeas hq'
          rw [integral_const, smul_eq_mul, mul_one] at this
          rw [this, polyMass_cast]
        rw [hm _ hok.pTn, hm _ hok.pFn]
        exact_mod_cast hok.nm }

/-- The total mass of the species of a trial (the contract's `mass μ`), as a rational. -/
theorem polyMass_trial (qs : List PieceQ) :
    polyMass (qs.map PieceQ.toPiece) = (((qs.map PieceQ.massQ).sum : ℚ) : ℝ) := polyMass_cast qs

/-! ### 10. The phantom bound `BR` of `RefTrial` (finite moments) -/

/-- `Σ_k |f_k| / (k + 1)` (a rational bound for `RefTrial.hBR`). -/
def brQ (f : List ℚ) : ℚ := ∑ k ∈ range f.length, |f.getD k 0| / ((k : ℚ) + 1)

theorem fld_fQ_abs_le (f : List ℚ) {y : ℝ} (hy : |y| ≤ 1) :
    |∑' n : ℕ, fQ f (n + 1) * y ^ (n + 1) / ((n : ℝ) + 1)| ≤ ((brQ f : ℚ) : ℝ) := by
  rw [tsum_eq_sum (s := range f.length) (fun n hn => by
    rw [Finset.mem_range, not_lt] at hn
    rw [fQ_supp f (n + 1) (by omega)]; ring)]
  unfold brQ
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [fQ_succ, abs_div, abs_mul, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
  have h1 : |y| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hy
  have h2 : |((f.getD k 0 : ℚ) : ℝ)| * |y| ^ (k + 1) ≤ |((f.getD k 0 : ℚ) : ℝ)| :=
    mul_le_of_le_one_right (abs_nonneg _) h1
  exact div_le_div_of_nonneg_right h2 (by positivity)

/-- `RefTrial.hBR` for a trial with finite moments `R = fQ f`, at `|τ (1 - θ)| ≤ 1`. -/
theorem hBR_of (D : SignedData) (f : List ℚ) (hR : D.R = fun n => fQ f (n + 1))
    (hy : |D.τ * (1 - D.θ)| ≤ 1) {BR : ℝ} (hBR : ((brQ f : ℚ) : ℝ) ≤ BR) :
    |∑' n : ℕ, D.R n * (D.τ * (1 - D.θ)) ^ (n + 1) / ((n : ℝ) + 1)| ≤ BR := by
  rw [hR]
  exact (fld_fQ_abs_le f hy).trans hBR

/-- The spike-count range of `hcert_form` for `N ≥ 1` (a choice of `Mmax`). -/
theorem mmax_bound {N M : ℕ} (hM : M + 1 ≤ 57 * N / 50) : 50 * (M + 1) ≤ 57 * N := by
  have := Nat.div_mul_le_self (57 * N) 50
  omega

end

end CatalanMeasure.GenD.Signed.Data.Trial
