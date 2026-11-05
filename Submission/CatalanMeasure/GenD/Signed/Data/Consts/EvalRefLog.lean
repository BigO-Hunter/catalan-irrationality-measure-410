module

public import Submission.CatalanMeasure.GenD.Signed.FieldForm
public import Submission.CatalanMeasure.GenD.Signed.Interp
public import Submission.CatalanMeasure.GenD.Signed.LogEval

@[expose] public section

/-!
# The reference bilinear energy `refBil` of two piecewise-polynomial references (Theorem A, lane E1b, item 15)

For signed references `μ = P − N`, `ν = P' − N'` whose four parts are `polyMeas` of lists of rational
polynomial pieces (`RefQ`; the form `TrialQ.qT/qF/qTn/qFn` of `FieldForm.Spec` takes after the step-4
regeneration), `refBil μ ν = ∬ Kt dμ dν` is an exact rational combination of values `log |r|` at
rational points `r` (breakpoint differences and sums such as `log (401/2500)`):

* `LF` (log form `c₀ + Σ cₖ log |rₖ|`), `LF.enc n f` rational enclosure (merge equal arguments, then `logAbsQ`);
* the inner potential of a piece is a pole-free `FieldQ` (`PieceQ.pot_eq_fieldTower`, reflected by
  `fqReflect` for the opposite-species kernel `-log (x + y)`), the outer integral against a piece of
  density `p` is again `polyPot` of the polynomial `p · c` (`int_dens_field`);
* `pairLF qa qb r` is the value for ONE pair of pieces (the unit of sharding); `refPlan R S` lists the
  `Job`s `(qa, qb, r, sign)` of `refBil`; `refBil_enc` consumes a `List.Forall₂` of per-job literal
  equalities `j.lf = l` (one `decide +kernel` per job) and one enclosure check of the summed literal.

Lemmas about `tsum`, `ip`, moments: `EvalRefMom`; limit glue (`hrA`, `hrB`, `hκ`): `EvalRefGlue`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.Cert (qabs)
open MeasureTheory Set

noncomputable section

/-! ### 1. Log forms -/

/-- `c₀ + Σ cₖ log |rₖ|` with rational `c₀, cₖ, rₖ`. -/
structure LF where
  c0 : ℚ
  ts : List (ℚ × ℚ)

/-- `Σ cₖ log |rₖ|`. -/
def termsEval : List (ℚ × ℚ) → ℝ
  | [] => 0
  | t :: l => (t.1 : ℝ) * Real.log |(t.2 : ℝ)| + termsEval l

def LF.eval (f : LF) : ℝ := (f.c0 : ℝ) + termsEval f.ts

theorem termsEval_append (l m : List (ℚ × ℚ)) :
    termsEval (l ++ m) = termsEval l + termsEval m := by
  induction l with
  | nil => simp [termsEval]
  | cons t l ih => simp only [List.cons_append, termsEval, ih]; ring

theorem termsEval_smul (a : ℚ) (l : List (ℚ × ℚ)) :
    termsEval (l.map (fun t => (a * t.1, t.2))) = (a : ℝ) * termsEval l := by
  induction l with
  | nil => simp [termsEval]
  | cons t l ih => simp only [List.map_cons, termsEval, ih]; push_cast; ring

def LF.add (f g : LF) : LF := ⟨f.c0 + g.c0, f.ts ++ g.ts⟩
def LF.smul (a : ℚ) (f : LF) : LF := ⟨a * f.c0, f.ts.map (fun t => (a * t.1, t.2))⟩
def LF.const (c : ℚ) : LF := ⟨c, []⟩
def LF.sumL : List LF → LF
  | [] => ⟨0, []⟩
  | f :: l => f.add (LF.sumL l)

theorem LF.eval_add (f g : LF) : (f.add g).eval = f.eval + g.eval := by
  simp only [LF.eval, LF.add, termsEval_append]; push_cast; ring

theorem LF.eval_smul (a : ℚ) (f : LF) : (f.smul a).eval = (a : ℝ) * f.eval := by
  simp only [LF.eval, LF.smul, termsEval_smul]; push_cast; ring

theorem LF.eval_const (c : ℚ) : (LF.const c).eval = (c : ℝ) := by
  simp [LF.eval, LF.const, termsEval]

theorem LF.eval_sumL : ∀ l : List LF, (LF.sumL l).eval = (l.map LF.eval).sum
  | [] => by simp [LF.sumL, LF.eval, termsEval]
  | f :: l => by
    simp only [LF.sumL, LF.eval_add, List.map_cons, List.sum_cons, LF.eval_sumL l]

theorem LF.eval_sumL_append (l m : List LF) :
    (LF.sumL (l ++ m)).eval = (LF.sumL l).eval + (LF.sumL m).eval := by
  simp only [LF.eval_sumL, List.map_append, List.sum_append]

/-! ### 2. Enclosure of a log form: merge equal arguments, then `logAbsQ` -/

theorem log_abs_cast_abs (r : ℚ) : Real.log |((|r| : ℚ) : ℝ)| = Real.log |(r : ℝ)| := by
  rw [Rat.cast_abs, abs_abs]

/-- Add `c log |r|` to a list of terms with positive arguments, merging an equal argument. -/
def addT (c r : ℚ) : List (ℚ × ℚ) → List (ℚ × ℚ)
  | [] => [(c, |r|)]
  | t :: l => if |r| = t.2 then (c + t.1, t.2) :: l else t :: addT c r l

theorem termsEval_addT (c r : ℚ) : ∀ l : List (ℚ × ℚ),
    termsEval (addT c r l) = (c : ℝ) * Real.log |(r : ℝ)| + termsEval l
  | [] => by simp [addT, termsEval, log_abs_cast_abs]
  | t :: l => by
    unfold addT
    split_ifs with h
    · have h' : Real.log |(t.2 : ℝ)| = Real.log |(r : ℝ)| := by
        rw [← h]; exact log_abs_cast_abs r
      simp only [termsEval, h']; push_cast; ring
    · simp only [termsEval, termsEval_addT c r l]; ring

/-- Merge terms with equal `|r|`; terms with `r = 0` vanish (`log 0 = 0`). -/
def mergeT : List (ℚ × ℚ) → List (ℚ × ℚ)
  | [] => []
  | t :: l => if t.2 = 0 then mergeT l else addT t.1 t.2 (mergeT l)

theorem termsEval_mergeT : ∀ l : List (ℚ × ℚ), termsEval (mergeT l) = termsEval l
  | [] => rfl
  | t :: l => by
    unfold mergeT
    split_ifs with h
    · simp [termsEval, h, termsEval_mergeT l]
    · simp only [termsEval, termsEval_addT, termsEval_mergeT l]

def encTerms (n : ℕ) : List (ℚ × ℚ) → Option (ℚ × ℚ)
  | [] => some (0, 0)
  | t :: l =>
    match logAbsQ n t.2, encTerms n l with
    | some p, some p' => some (t.1 * p.1 + p'.1, qabs t.1 * p.2 + p'.2)
    | _, _ => none

theorem encTerms_spec (n : ℕ) : ∀ (l : List (ℚ × ℚ)) (p : ℚ × ℚ),
    encTerms n l = some p → Enc (termsEval l) p
  | [], p, h => by
    simp only [encTerms, Option.some.injEq] at h
    subst h
    simp [termsEval, Enc]
  | t :: l, p, h => by
    rcases h1 : logAbsQ n t.2 with _ | ⟨v, e⟩
    · simp [encTerms, h1] at h
    · rcases h2 : encTerms n l with _ | ⟨v', e'⟩
      · simp [encTerms, h1, h2] at h
      · simp only [encTerms, h1, h2, Option.some.injEq] at h
        subst h
        have hl := (logAbsQ_spec h1).2
        have ih := encTerms_spec n l (v', e') h2
        have := (hl.mulQ t.1).add ih
        simpa only [termsEval] using this

/-- Rational enclosure `Enc f.eval p`, `p = (value, error)`, from `logAbsQ n` (about `2^-127` per
distinct argument for `n ≥ 7`). -/
def LF.enc (n : ℕ) (f : LF) : Option (ℚ × ℚ) :=
  match encTerms n (mergeT f.ts) with
  | some p => some (f.c0 + p.1, p.2)
  | none => none

theorem LF.enc_spec (n : ℕ) (f : LF) (p : ℚ × ℚ) (h : f.enc n = some p) : Enc f.eval p := by
  unfold LF.enc at h
  rcases h1 : encTerms n (mergeT f.ts) with _ | q
  · simp [h1] at h
  · simp only [h1, Option.some.injEq] at h
    subst h
    have h2 := encTerms_spec n _ q h1
    rw [termsEval_mergeT] at h2
    have := (Enc.const f.c0).add h2
    simpa [LF.eval] using this

/-! ### 3. Rational polynomials: evaluation, product, the density of a piece -/

/-- Horner evaluation of rational coefficients at a rational point. -/
def evalH (l : List ℚ) (w : ℚ) : ℚ := l.foldr (fun a acc => a + w * acc) 0

theorem evalH_cast (l : List ℚ) (w : ℚ) : ((evalH l w : ℚ) : ℝ) = polyTow l 0 (w : ℝ) := by
  induction l with
  | nil => simp [evalH, polyTow_zero_nil]
  | cons a l ih =>
    simp only [evalH, List.foldr_cons] at ih ⊢
    rw [polyTow_zero_cons, ← ih, Rat.cast_add, Rat.cast_mul]

/-- Product of coefficient lists. -/
def pmul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: as, b => vecAdd (b.map (fun t => a * t)) (0 :: pmul as b)

theorem polyTow_zero_pmul : ∀ (a b : List ℚ) (x : ℝ),
    polyTow (pmul a b) 0 x = polyTow a 0 x * polyTow b 0 x
  | [], b, x => by simp [pmul, polyTow_zero_nil]
  | a :: as, b, x => by
    simp only [pmul, polyTow_zero_vecAdd, polyTow_zero_map_mul, polyTow_zero_cons,
      polyTow_zero_pmul as b x]
    push_cast
    ring

theorem polyTow_zero_eq_sum : ∀ (l : List ℚ) (y : ℝ),
    polyTow l 0 y = ∑ m ∈ Finset.range l.length, ((l.getD m 0 : ℚ) : ℝ) * y ^ m
  | [], y => by simp [polyTow_zero_nil]
  | a :: as, y => by
    have ih := polyTow_zero_eq_sum as y
    rw [polyTow_zero_cons, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    have h1 : ∀ m ∈ Finset.range as.length, y * (((as.getD m 0 : ℚ) : ℝ) * y ^ m) =
        (((a :: as).getD (m + 1) 0 : ℚ) : ℝ) * y ^ (m + 1) := fun m _ => by
      simp only [List.getD_cons_succ]; ring
    rw [Finset.sum_congr rfl h1]
    simp only [List.getD_cons_zero, pow_zero, mul_one]
    ring

/-- The density of a rational piece is the Horner polynomial of its coefficients. -/
theorem dens_eq (q : PieceQ) (y : ℝ) : q.toPiece.dens y = polyTow q.p 0 y := by
  rw [polyTow_zero_eq_sum]; rfl

theorem pieceOK_le_rat {q : PieceQ} (h : PieceOK q.toPiece) : q.lo ≤ q.hi := by
  have : (q.lo : ℝ) ≤ q.hi := h.1
  exact_mod_cast this

theorem continuous_polyTow0 : ∀ l : List ℚ, Continuous (fun y : ℝ => polyTow l 0 y)
  | [] => by simp only [polyTow_zero_nil]; exact continuous_const
  | a :: as => by
    have ih := continuous_polyTow0 as
    have h : (fun y : ℝ => polyTow (a :: as) 0 y) = fun y => (a : ℝ) + y * polyTow as 0 y := by
      funext y; exact polyTow_zero_cons a as y
    rw [h]
    exact continuous_const.add (continuous_id.mul ih)

/-! ### 4. Fields at rational points as log forms -/

/-- The log form of a (pole-free) `FieldQ` at a rational point. -/
def fqLF (F : FieldQ) (w : ℚ) : LF :=
  ⟨evalH F.poly w, F.plogs.map (fun t => (evalH t.1 w, w - t.2))⟩

theorem plogSumTower_zero_eq (L : List (List ℚ × ℚ)) (y : ℝ) :
    plogSumTower L 0 y = (L.map (fun s => polyTow s.1 0 y * Real.log |y - (s.2 : ℝ)|)).sum := by
  unfold plogSumTower
  congr 1
  refine List.map_congr_left (fun s _ => ?_)
  simp only [mulTower_zero, logTower]

theorem fieldTower_zero_eq (F : FieldQ) (y : ℝ) :
    fieldTower F (fun _ => 0) 0 y = polyTow F.poly 0 y +
      (F.plogs.map (fun s => polyTow s.1 0 y * Real.log |y - (s.2 : ℝ)|)).sum := by
  unfold fieldTower
  rw [plogSumTower_zero_eq]
  simp [poleTower_zero]

theorem termsEval_plogs (w : ℚ) : ∀ L : List (List ℚ × ℚ),
    termsEval (L.map (fun t => (evalH t.1 w, w - t.2))) =
      (L.map (fun s => polyTow s.1 0 (w : ℝ) * Real.log |(w : ℝ) - (s.2 : ℝ)|)).sum
  | [] => by simp [termsEval]
  | t :: L => by
    simp only [List.map_cons, termsEval, List.sum_cons, termsEval_plogs w L, evalH_cast,
      Rat.cast_sub]

theorem fqLF_eval (F : FieldQ) (w : ℚ) :
    (fqLF F w).eval = fieldTower F (fun _ => 0) 0 (w : ℝ) := by
  rw [fieldTower_zero_eq]
  show (↑(evalH F.poly w) : ℝ) + termsEval (F.plogs.map (fun t => (evalH t.1 w, w - t.2))) = _
  rw [evalH_cast, termsEval_plogs]

/-! ### 5. Integrals of a piece density against a pole-free field -/

theorem ii_plogs (a b : ℝ) : ∀ L : List (List ℚ × ℚ),
    IntervalIntegrable (fun y => (L.map (fun s => polyTow s.1 0 y *
      Real.log |y - (s.2 : ℝ)|)).sum) volume a b
  | [] => by
    simp only [List.map_nil, List.sum_nil]
    exact intervalIntegrable_const
  | s :: L => by
    simp only [List.map_cons, List.sum_cons]
    exact (intervalIntegrable_mul_log_abs_sub (continuous_polyTow0 s.1) (s.2 : ℝ) a b).add
      (ii_plogs a b L)

theorem ii_field (F : FieldQ) (a b : ℝ) :
    IntervalIntegrable (fun y => fieldTower F (fun _ => 0) 0 y) volume a b := by
  have : (fun y => fieldTower F (fun _ => 0) 0 y) = fun y => polyTow F.poly 0 y +
      (F.plogs.map (fun s => polyTow s.1 0 y * Real.log |y - (s.2 : ℝ)|)).sum :=
    funext (fieldTower_zero_eq F)
  rw [this]
  exact ((continuous_polyTow0 F.poly).intervalIntegrable a b).add (ii_plogs a b F.plogs)

/-- `∫_{lo}^{hi} (density) = massQ`. -/
theorem int_polyTow (q : PieceQ) :
    ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t = ((q.massQ : ℚ) : ℝ) := by
  rw [PieceQ.massQ_cast]
  calc ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t
      = ∫ t in (q.lo : ℝ)..(q.hi : ℝ), pc q.toPiece.n q.toPiece.p t :=
        intervalIntegral.integral_congr (fun t _ => (dens_eq q t).symm)
    _ = q.toPiece.mass :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hasDerivAt_potG q.toPiece.n q.toPiece.p t)
          ((continuous_pc q.toPiece.n q.toPiece.p).intervalIntegrable _ _)

/-- `∫_{lo}^{hi} p(t) log |t - a| dt` as the log form of the piece's own potential field. -/
theorem int_polyTow_log (q : PieceQ) (hle : q.lo ≤ q.hi) (a : ℚ) :
    ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * Real.log |t - (a : ℝ)| =
      (fqLF q.fieldQ a).eval := by
  rw [fqLF_eval, ← PieceQ.pot_eq_fieldTower]
  have h := polyPot q.toPiece.n q.toPiece.p (Rat.cast_le.mpr hle : (q.lo : ℝ) ≤ q.hi) (a : ℝ)
  calc ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * Real.log |t - (a : ℝ)|
      = ∫ t in (q.lo : ℝ)..(q.hi : ℝ), pc q.toPiece.n q.toPiece.p t * Real.log |t - (a : ℝ)| :=
        intervalIntegral.integral_congr (fun t _ => by
          show polyTow q.p 0 t * _ = q.toPiece.dens t * _
          rw [dens_eq])
    _ = q.toPiece.pot (a : ℝ) := h

/-- The log form of `∫ dens(t) · fieldTower F t dt` over the piece. -/
def pieceFieldLF (q : PieceQ) (F : FieldQ) : LF :=
  (LF.const (PieceQ.massQ ⟨q.lo, q.hi, pmul q.p F.poly⟩)).add
    (LF.sumL (F.plogs.map (fun s => fqLF (PieceQ.fieldQ ⟨q.lo, q.hi, pmul q.p s.1⟩) s.2)))

theorem int_mul_plogs (q : PieceQ) (hle : q.lo ≤ q.hi) : ∀ L : List (List ℚ × ℚ),
    ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * (L.map (fun s => polyTow s.1 0 t *
        Real.log |t - (s.2 : ℝ)|)).sum =
      (LF.sumL (L.map (fun s => fqLF (PieceQ.fieldQ ⟨q.lo, q.hi, pmul q.p s.1⟩) s.2))).eval
  | [] => by simp [LF.sumL, LF.eval, termsEval]
  | s :: L => by
    have e : ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * ((s :: L).map (fun s => polyTow s.1 0 t *
        Real.log |t - (s.2 : ℝ)|)).sum =
        ∫ t in (q.lo : ℝ)..(q.hi : ℝ), (polyTow (pmul q.p s.1) 0 t * Real.log |t - (s.2 : ℝ)| +
          polyTow q.p 0 t * (L.map (fun s => polyTow s.1 0 t * Real.log |t - (s.2 : ℝ)|)).sum) :=
      intervalIntegral.integral_congr (fun t _ => by
        simp only [List.map_cons, List.sum_cons]
        rw [polyTow_zero_pmul]
        ring)
    have ii1 : IntervalIntegrable (fun t => polyTow (pmul q.p s.1) 0 t * Real.log |t - (s.2 : ℝ)|)
        volume (q.lo : ℝ) (q.hi : ℝ) :=
      intervalIntegrable_mul_log_abs_sub (continuous_polyTow0 _) _ _ _
    have ii2 : IntervalIntegrable (fun t => polyTow q.p 0 t * (L.map (fun s => polyTow s.1 0 t *
        Real.log |t - (s.2 : ℝ)|)).sum) volume (q.lo : ℝ) (q.hi : ℝ) :=
      (ii_plogs _ _ L).continuousOn_mul (continuous_polyTow0 q.p).continuousOn
    have h1 : ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow (pmul q.p s.1) 0 t * Real.log |t - (s.2 : ℝ)| =
        (fqLF (PieceQ.fieldQ ⟨q.lo, q.hi, pmul q.p s.1⟩) s.2).eval :=
      int_polyTow_log ⟨q.lo, q.hi, pmul q.p s.1⟩ hle s.2
    rw [e, intervalIntegral.integral_add ii1 ii2, h1, int_mul_plogs q hle L]
    simp only [List.map_cons, LF.sumL, LF.eval_add]

theorem int_dens_field (q : PieceQ) (hle : q.lo ≤ q.hi) (F : FieldQ) :
    ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * fieldTower F (fun _ => 0) 0 t =
      (pieceFieldLF q F).eval := by
  have e : ∀ t : ℝ, polyTow q.p 0 t * fieldTower F (fun _ => 0) 0 t =
      polyTow (pmul q.p F.poly) 0 t + polyTow q.p 0 t *
        (F.plogs.map (fun s => polyTow s.1 0 t * Real.log |t - (s.2 : ℝ)|)).sum := by
    intro t
    rw [fieldTower_zero_eq, polyTow_zero_pmul]
    ring
  have h1 : ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * fieldTower F (fun _ => 0) 0 t =
      ∫ t in (q.lo : ℝ)..(q.hi : ℝ), (polyTow (pmul q.p F.poly) 0 t + polyTow q.p 0 t *
        (F.plogs.map (fun s => polyTow s.1 0 t * Real.log |t - (s.2 : ℝ)|)).sum) :=
    intervalIntegral.integral_congr (fun t _ => e t)
  have ii1 : IntervalIntegrable (fun t => polyTow (pmul q.p F.poly) 0 t) volume (q.lo : ℝ) (q.hi : ℝ) :=
    (continuous_polyTow0 _).intervalIntegrable _ _
  have ii2 : IntervalIntegrable (fun t => polyTow q.p 0 t *
      (F.plogs.map (fun s => polyTow s.1 0 t * Real.log |t - (s.2 : ℝ)|)).sum)
      volume (q.lo : ℝ) (q.hi : ℝ) :=
    (ii_plogs _ _ F.plogs).continuousOn_mul (continuous_polyTow0 q.p).continuousOn
  have h2 : ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow (pmul q.p F.poly) 0 t =
      ((PieceQ.massQ ⟨q.lo, q.hi, pmul q.p F.poly⟩ : ℚ) : ℝ) :=
    int_polyTow ⟨q.lo, q.hi, pmul q.p F.poly⟩
  rw [h1, intervalIntegral.integral_add ii1 ii2, h2, int_mul_plogs q hle F.plogs]
  simp only [pieceFieldLF, LF.eval_add, LF.eval_const]

/-! ### 6. Sums over the pieces of the inner measure; reflection for the opposite species -/

/-- The field of a piece in the inner potential: `fieldQ` (`r = false`: `x ↦ pot x`) or its
reflection (`r = true`: `x ↦ pot (-x)`, the kernel `-log (x + y)`). -/
def fieldOf : Bool → PieceQ → FieldQ
  | false, q => q.fieldQ
  | true, q => fqReflect q.fieldQ

/-- `x ↦ Σ_{qb ∈ B} fieldTower (fieldOf r qb) x`. -/
def Gsum (r : Bool) (B : List PieceQ) (x : ℝ) : ℝ :=
  (B.map (fun q => fieldTower (fieldOf r q) (fun _ => 0) 0 x)).sum

theorem Gsum_cons (r : Bool) (q : PieceQ) (B : List PieceQ) (x : ℝ) :
    Gsum r (q :: B) x = fieldTower (fieldOf r q) (fun _ => 0) 0 x + Gsum r B x := by
  simp [Gsum]

theorem ii_Gsum (r : Bool) (a b : ℝ) : ∀ B : List PieceQ,
    IntervalIntegrable (fun x => Gsum r B x) volume a b
  | [] => by
    simp only [Gsum, List.map_nil, List.sum_nil]
    exact intervalIntegrable_const
  | q :: B => by
    have : (fun x => Gsum r (q :: B) x) =
        fun x => fieldTower (fieldOf r q) (fun _ => 0) 0 x + Gsum r B x :=
      funext (Gsum_cons r q B)
    rw [this]
    exact (ii_field _ a b).add (ii_Gsum r a b B)

theorem logPot_Gsum0 (B : List PieceQ) (x : ℝ) :
    logPot (B.map PieceQ.toPiece) x = Gsum false B x := by
  induction B with
  | nil => simp [logPot, Gsum]
  | cons q B ih =>
    simp only [logPot, Gsum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [fieldOf]
    rw [PieceQ.pot_eq_fieldTower]

theorem logPot_Gsum1 (B : List PieceQ) (x : ℝ) :
    logPot (B.map PieceQ.toPiece) (-x) = Gsum true B x := by
  induction B with
  | nil => simp [logPot, Gsum]
  | cons q B ih =>
    simp only [logPot, Gsum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [fieldOf]
    rw [PieceQ.pot_eq_fieldTower, fieldTower_reflect q.fieldQ rfl]

/-- The log form of one pair of pieces (outer `qa`, inner `qb`, reflection flag `r`):
`∫_{qa} dens_a(x) · fieldTower (fieldOf r qb) x dx`.  This is the unit of sharding. -/
def pairLF (qa qb : PieceQ) (r : Bool) : LF := pieceFieldLF qa (fieldOf r qb)

def rowLF (qa : PieceQ) (B : List PieceQ) (r : Bool) : LF :=
  LF.sumL (B.map (fun qb => pairLF qa qb r))

def entLF (A B : List PieceQ) (r : Bool) : LF :=
  LF.sumL (A.map (fun qa => rowLF qa B r))

theorem int_dens_Gsum (q : PieceQ) (hle : q.lo ≤ q.hi) (r : Bool) : ∀ B : List PieceQ,
    ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * Gsum r B t = (rowLF q B r).eval
  | [] => by simp [Gsum, rowLF, LF.sumL, LF.eval, termsEval]
  | qb :: B => by
    have e : ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * Gsum r (qb :: B) t =
        ∫ t in (q.lo : ℝ)..(q.hi : ℝ), (polyTow q.p 0 t * fieldTower (fieldOf r qb) (fun _ => 0) 0 t +
          polyTow q.p 0 t * Gsum r B t) :=
      intervalIntegral.integral_congr (fun t _ => by
        simp only [Gsum_cons]; ring)
    have ii1 : IntervalIntegrable (fun t => polyTow q.p 0 t *
        fieldTower (fieldOf r qb) (fun _ => 0) 0 t) volume (q.lo : ℝ) (q.hi : ℝ) :=
      (ii_field (fieldOf r qb) _ _).continuousOn_mul (continuous_polyTow0 q.p).continuousOn
    have ii2 : IntervalIntegrable (fun t => polyTow q.p 0 t * Gsum r B t) volume
        (q.lo : ℝ) (q.hi : ℝ) :=
      (ii_Gsum r _ _ B).continuousOn_mul (continuous_polyTow0 q.p).continuousOn
    rw [e, intervalIntegral.integral_add ii1 ii2, int_dens_field q hle, int_dens_Gsum q hle r B]
    simp only [rowLF, List.map_cons, LF.sumL, LF.eval_add, pairLF]

theorem int_piece_eq (qa : PieceQ) (G : ℝ → ℝ) :
    (∫ t in qa.toPiece.lo..qa.toPiece.hi, qa.toPiece.dens t * G t) =
      ∫ t in (qa.lo : ℝ)..(qa.hi : ℝ), polyTow qa.p 0 t * G t := by
  simp only [dens_eq]
  all_goals rfl

/-- The outer integral over the pieces of `A`. -/
theorem int_core (A B : List PieceQ) (hA : ∀ q ∈ A, PieceOK q.toPiece) (r : Bool) :
    ∫ x, Gsum r B x ∂(polyMeas (A.map PieceQ.toPiece)) = (entLF A B r).eval := by
  have hgs : ∀ q ∈ A.map PieceQ.toPiece, PieceOK q ∧ IntegrableOn (Gsum r B) (Icc q.lo q.hi) := by
    intro q hq
    obtain ⟨qa, hqa, rfl⟩ := List.mem_map.mp hq
    refine ⟨hA qa hqa, ?_⟩
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (hA qa hqa).1).mp (ii_Gsum r _ _ B)
  rw [(integrable_polyMeas hgs).2]
  simp only [entLF, LF.eval_sumL, List.map_map]
  congr 1
  refine List.map_congr_left (fun qa hqa => ?_)
  simp only [Function.comp_apply]
  rw [int_piece_eq, int_dens_Gsum qa (pieceOK_le_rat (hA qa hqa)) r B]

/-! ### 7. The kernel `Kt` -/

theorem mem_toPiece_ok {B : List PieceQ} (hB : ∀ q ∈ B, PieceOK q.toPiece) :
    ∀ q ∈ B.map PieceQ.toPiece, PieceOK q := by
  intro q hq
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact hB q0 hq0

theorem inner_same (B : List PieceQ) (hB : ∀ q ∈ B, PieceOK q.toPiece) (s : Bool) (x : ℝ) :
    ∫ y, Kt s s x y ∂(polyMeas (B.map PieceQ.toPiece)) = -Gsum false B x := by
  have e : ∀ y, Kt s s x y = -Real.log |y - x| := fun y => by
    unfold Kt; rw [if_pos rfl, abs_sub_comm]
  simp_rw [e]
  rw [integral_neg, integral_log_polyMeas (mem_toPiece_ok hB) x, logPot_Gsum0]

theorem inner_opp (B : List PieceQ) (hB : ∀ q ∈ B, PieceOK q.toPiece) (s t : Bool) (hst : s ≠ t)
    (x : ℝ) :
    ∫ y, Kt s t x y ∂(polyMeas (B.map PieceQ.toPiece)) = -Gsum true B x := by
  have e : ∀ y, Kt s t x y = -Real.log |y - (-x)| := fun y => by
    unfold Kt
    rw [if_neg hst, Real.log_abs]
    congr 2
    ring
  simp_rw [e]
  rw [integral_neg, integral_log_polyMeas (mem_toPiece_ok hB) (-x), logPot_Gsum1]

theorem kt_same (A B : List PieceQ) (hA : ∀ q ∈ A, PieceOK q.toPiece)
    (hB : ∀ q ∈ B, PieceOK q.toPiece) (s : Bool) :
    ∫ x, ∫ y, Kt s s x y ∂(polyMeas (B.map PieceQ.toPiece)) ∂(polyMeas (A.map PieceQ.toPiece)) =
      -(entLF A B false).eval := by
  simp_rw [inner_same B hB s]
  rw [integral_neg, int_core A B hA false]

theorem kt_opp (A B : List PieceQ) (hA : ∀ q ∈ A, PieceOK q.toPiece)
    (hB : ∀ q ∈ B, PieceOK q.toPiece) (s t : Bool) (hst : s ≠ t) :
    ∫ x, ∫ y, Kt s t x y ∂(polyMeas (B.map PieceQ.toPiece)) ∂(polyMeas (A.map PieceQ.toPiece)) =
      -(entLF A B true).eval := by
  simp_rw [inner_opp B hB s t hst]
  rw [integral_neg, int_core A B hA true]

/-- The log form of `pairI μ ν Kt` is `-bilLF`: `A1, A0` are the pieces of `μ true/false`,
`B1, B0` those of `ν true/false`. -/
def bilLF (A1 A0 B1 B0 : List PieceQ) : LF :=
  (entLF A1 B1 false).add ((entLF A1 B0 true).add ((entLF A0 B1 true).add (entLF A0 B0 false)))

theorem pairI_Kt (μ ν : Bool → Measure ℝ) (A1 A0 B1 B0 : List PieceQ)
    (hA1 : ∀ q ∈ A1, PieceOK q.toPiece) (hA0 : ∀ q ∈ A0, PieceOK q.toPiece)
    (hB1 : ∀ q ∈ B1, PieceOK q.toPiece) (hB0 : ∀ q ∈ B0, PieceOK q.toPiece)
    (hμ1 : μ true = polyMeas (A1.map PieceQ.toPiece)) (hμ0 : μ false = polyMeas (A0.map PieceQ.toPiece))
    (hν1 : ν true = polyMeas (B1.map PieceQ.toPiece)) (hν0 : ν false = polyMeas (B0.map PieceQ.toPiece)) :
    pairI μ ν Kt = -(bilLF A1 A0 B1 B0).eval := by
  unfold pairI
  simp only [Fintype.sum_bool, hμ1, hμ0, hν1, hν0]
  rw [kt_same A1 B1 hA1 hB1, kt_opp A1 B0 hA1 hB0 true false (by decide),
    kt_opp A0 B1 hA0 hB1 false true (by decide), kt_same A0 B0 hA0 hB0]
  simp only [bilLF, LF.eval_add]
  ring

/-! ### 8. Signed references and `refBil` -/

/-- Four lists of rational pieces: the positive part `P` (species `true`, `false`) and the negative part `N`. -/
structure RefQ where
  pT : List PieceQ
  pF : List PieceQ
  nT : List PieceQ
  nF : List PieceQ

def RefQ.OK (R : RefQ) : Prop :=
  (∀ q ∈ R.pT, PieceOK q.toPiece) ∧ (∀ q ∈ R.pF, PieceOK q.toPiece) ∧
  (∀ q ∈ R.nT, PieceOK q.toPiece) ∧ (∀ q ∈ R.nF, PieceOK q.toPiece)

/-- The signed reference `μ` is the one given by the lists of `R` (the equations of `TrialForm.Spec`
`hμT hμF hμTn hμFn` for `F.qT = R.pT.map toPiece` etc.). -/
def IsRefQ (μ : SRef) (R : RefQ) : Prop :=
  μ.P true = polyMeas (R.pT.map PieceQ.toPiece) ∧ μ.P false = polyMeas (R.pF.map PieceQ.toPiece) ∧
  μ.N true = polyMeas (R.nT.map PieceQ.toPiece) ∧ μ.N false = polyMeas (R.nF.map PieceQ.toPiece)

/-- `refBil μ ν = -bil(PP) + bil(PN) + bil(NP) - bil(NN)` as a log form. -/
def refBilLF (R S : RefQ) : LF :=
  LF.sumL [(bilLF R.pT R.pF S.pT S.pF).smul (-1), bilLF R.pT R.pF S.nT S.nF,
    bilLF R.nT R.nF S.pT S.pF, (bilLF R.nT R.nF S.nT S.nF).smul (-1)]

theorem refBil_eval (μ ν : SRef) (R S : RefQ) (hμ : IsRefQ μ R) (hν : IsRefQ ν S) (hR : R.OK) (hS : S.OK) :
    refBil μ ν = (refBilLF R S).eval := by
  obtain ⟨hμ1, hμ0, hμn1, hμn0⟩ := hμ
  obtain ⟨hν1, hν0, hνn1, hνn0⟩ := hν
  obtain ⟨hR1, hR0, hRn1, hRn0⟩ := hR
  obtain ⟨hS1, hS0, hSn1, hSn0⟩ := hS
  have h1 := pairI_Kt μ.P ν.P R.pT R.pF S.pT S.pF hR1 hR0 hS1 hS0 hμ1 hμ0 hν1 hν0
  have h2 := pairI_Kt μ.P ν.N R.pT R.pF S.nT S.nF hR1 hR0 hSn1 hSn0 hμ1 hμ0 hνn1 hνn0
  have h3 := pairI_Kt μ.N ν.P R.nT R.nF S.pT S.pF hRn1 hRn0 hS1 hS0 hμn1 hμn0 hν1 hν0
  have h4 := pairI_Kt μ.N ν.N R.nT R.nF S.nT S.nF hRn1 hRn0 hSn1 hSn0 hμn1 hμn0 hνn1 hνn0
  unfold refBil refBilM
  rw [h1, h2, h3, h4]
  simp only [refBilLF, LF.eval_sumL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LF.eval_smul]
  push_cast
  ring

/-- `refEnergy μ = refBil μ μ`. -/
theorem refEnergy_eval (μ : SRef) (R : RefQ) (hμ : IsRefQ μ R) (hR : R.OK) :
    refEnergy μ = (refBilLF R R).eval := by
  rw [refEnergy_eq_refBil]
  exact refBil_eval μ μ R R hμ hμ hR hR

/-! ### 9. Jobs: one literal per pair of pieces -/

/-- One `±pairLF qa qb r` of the expansion of `refBil`. -/
structure Job where
  qa : PieceQ
  qb : PieceQ
  r : Bool
  sg : ℚ

def Job.lf (j : Job) : LF := (pairLF j.qa j.qb j.r).smul j.sg

def jobsRow (sg : ℚ) (r : Bool) (qa : PieceQ) : List PieceQ → List Job
  | [] => []
  | qb :: l => ⟨qa, qb, r, sg⟩ :: jobsRow sg r qa l

def jobsEnt (sg : ℚ) (r : Bool) (B : List PieceQ) : List PieceQ → List Job
  | [] => []
  | qa :: l => jobsRow sg r qa B ++ jobsEnt sg r B l

def jobsBil (sg : ℚ) (A1 A0 B1 B0 : List PieceQ) : List Job :=
  jobsEnt sg false B1 A1 ++ jobsEnt sg true B0 A1 ++ jobsEnt sg true B1 A0 ++ jobsEnt sg false B0 A0

/-- The jobs of `refBil μ ν` for `μ ~ R`, `ν ~ S`, in the order of `refBilLF`. -/
def refPlan (R S : RefQ) : List Job :=
  jobsBil (-1) R.pT R.pF S.pT S.pF ++ jobsBil 1 R.pT R.pF S.nT S.nF ++
    jobsBil 1 R.nT R.nF S.pT S.pF ++ jobsBil (-1) R.nT R.nF S.nT S.nF

theorem eval_jobsRow (sg : ℚ) (r : Bool) (qa : PieceQ) : ∀ B : List PieceQ,
    (LF.sumL ((jobsRow sg r qa B).map Job.lf)).eval = (sg : ℝ) * (rowLF qa B r).eval
  | [] => by simp [jobsRow, rowLF, LF.sumL, LF.eval, termsEval]
  | qb :: B => by
    simp only [jobsRow, rowLF, List.map_cons, LF.sumL, LF.eval_add, Job.lf, LF.eval_smul]
    have := eval_jobsRow sg r qa B
    simp only [rowLF] at this
    rw [this]
    ring

theorem eval_jobsEnt (sg : ℚ) (r : Bool) (B : List PieceQ) : ∀ A : List PieceQ,
    (LF.sumL ((jobsEnt sg r B A).map Job.lf)).eval = (sg : ℝ) * (entLF A B r).eval
  | [] => by simp [jobsEnt, entLF, LF.sumL, LF.eval, termsEval]
  | qa :: A => by
    simp only [jobsEnt, entLF, List.map_cons, LF.sumL, LF.eval_add, List.map_append,
      LF.eval_sumL_append]
    have h1 := eval_jobsRow sg r qa B
    have h2 := eval_jobsEnt sg r B A
    simp only [entLF] at h2
    rw [h1, h2]
    ring

theorem eval_jobsBil (sg : ℚ) (A1 A0 B1 B0 : List PieceQ) :
    (LF.sumL ((jobsBil sg A1 A0 B1 B0).map Job.lf)).eval = (sg : ℝ) * (bilLF A1 A0 B1 B0).eval := by
  simp only [jobsBil, List.map_append, LF.eval_sumL_append, eval_jobsEnt, bilLF, LF.eval_add]
  ring

theorem eval_refPlan (R S : RefQ) :
    (LF.sumL ((refPlan R S).map Job.lf)).eval = (refBilLF R S).eval := by
  simp only [refPlan, List.map_append, LF.eval_sumL_append, eval_jobsBil]
  simp only [refBilLF, LF.eval_sumL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LF.eval_smul]
  push_cast
  ring

theorem map_lf_eq {js : List Job} {ls : List LF}
    (h : List.Forall₂ (fun (j : Job) (l : LF) => j.lf = l) js ls) : js.map Job.lf = ls := by
  induction h with
  | nil => rfl
  | cons h1 h2 ih => simp [h1, ih]

/-- **The `refBil` evaluator.**  `lits` are the per-job literal log forms (`j.lf = l` one
`decide +kernel` each; `refPlan R S` fixes the order); if the summed literal has an enclosure
`p = (value, error)` at precision `n` (`LF.enc`), then `|refBil μ ν − value| ≤ error`. -/
theorem refBil_enc (μ ν : SRef) (R S : RefQ) (hμ : IsRefQ μ R) (hν : IsRefQ ν S) (hR : R.OK) (hS : S.OK)
    {lits : List LF} (hl : List.Forall₂ (fun (j : Job) (l : LF) => j.lf = l) (refPlan R S) lits) (n : ℕ)
    {p : ℚ × ℚ} (h : (LF.sumL lits).enc n = some p) : Enc (refBil μ ν) p := by
  have hv := LF.enc_spec n _ p h
  rw [← map_lf_eq hl, eval_refPlan] at hv
  rwa [refBil_eval μ ν R S hμ hν hR hS]

/-- `refEnergy μ` (the constant of the reference in `constTotal`). -/
theorem refEnergy_enc (μ : SRef) (R : RefQ) (hμ : IsRefQ μ R) (hR : R.OK)
    {lits : List LF} (hl : List.Forall₂ (fun (j : Job) (l : LF) => j.lf = l) (refPlan R R) lits) (n : ℕ)
    {p : ℚ × ℚ} (h : (LF.sumL lits).enc n = some p) : Enc (refEnergy μ) p := by
  rw [refEnergy_eq_refBil]
  exact refBil_enc μ μ R R hμ hμ hR hR hl n h

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef

#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.refBil_enc
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.refEnergy_enc
