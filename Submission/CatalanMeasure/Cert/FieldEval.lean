module

public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierChebyshevLogFormula
public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierPowerLogFormula
public import Submission.OAI.NumberTheory.Catalan.Estimates.RealEnergySupDual
public import Submission.CatalanMeasure.Cert.LogApprox

@[expose] public section

/-!
# Certified values of the energy trial fields at rational points

A trial sequence is given by a list `cs` of integers (its first coefficients times `10⁸`) and
a list of rational complex pairs `(z, r)`; it is OpenAI's `barrierTrial cs tail`,
`u_k = cs_{k-1} / 10⁸ + Re Σ r z^k`.  At a rational point the row and column fields are a
rational number plus a sum of terms `Re ((c + d i) log w)` with rational `c, d, w`.  The
functions `rowApprox` and `colApprox` compute a rational approximation together with an error
bound, and `rowApprox_spec`, `colApprox_spec` prove the bound.
-/

open OAI.InternalCatalan Polynomial

namespace CatalanMeasure.Cert

/-- A geometric tail `Re (r z^k)` with `z = zr + zi i`, `r = rr + ri i`. -/
structure TailQ where
  zr : ℚ
  zi : ℚ
  rr : ℚ
  ri : ℚ
deriving DecidableEq

def TailQ.toC (t : TailQ) : ℂ × ℂ := (barrierComplex t.zr t.zi, barrierComplex t.rr t.ri)

/-- The trial sequence of `cs` and `tail`. -/
noncomputable def trialSeq (cs : List ℤ) (tail : List TailQ) : ℕ → ℝ :=
  barrierTrial cs (tail.map TailQ.toC)

def tailsInDisk (tail : List TailQ) : Bool :=
  tail.all (fun t => decide (t.zr * t.zr + t.zi * t.zi < 1))

theorem norm_barrierComplex_sq (a b : ℚ) :
    ‖barrierComplex a b‖ ^ 2 = ((a * a + b * b : ℚ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [barrierComplex]

theorem tailsInDisk_spec {tail : List TailQ} (h : tailsInDisk tail = true) :
    ∀ zr ∈ tail.map TailQ.toC, ‖zr.1‖ < 1 := by
  intro zr hzr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hzr
  have h1 : t.zr * t.zr + t.zi * t.zi < 1 := by
    unfold tailsInDisk at h
    simpa using List.all_eq_true.mp h t ht
  have h2 : ‖(TailQ.toC t).1‖ ^ 2 < 1 := by
    simp only [TailQ.toC]
    rw [norm_barrierComplex_sq]
    exact_mod_cast h1
  nlinarith [norm_nonneg (TailQ.toC t).1]

/-! ### Chebyshev polynomials and finite sums at rational points -/

def chebTPair : ℕ → ℚ → ℚ × ℚ
  | 0, x => (1, x)
  | n + 1, x => ((chebTPair n x).2, 2 * x * (chebTPair n x).2 - (chebTPair n x).1)

def chebTQ (n : ℕ) (x : ℚ) : ℚ := (chebTPair n x).1

theorem chebTPair_spec (n : ℕ) (x : ℚ) :
    (((chebTPair n x).1 : ℚ) : ℝ) = (Chebyshev.T ℝ (n : ℤ)).eval (x : ℝ) ∧
      (((chebTPair n x).2 : ℚ) : ℝ) = (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval (x : ℝ) := by
  induction n with
  | zero => simp [chebTPair, Chebyshev.T_zero, Chebyshev.T_one]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h := Chebyshev.T_add_two ℝ (n : ℤ)
    have e : ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have e' : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, h]
    simp only [chebTPair, eval_sub, eval_mul, eval_X, eval_ofNat]
    push_cast
    rw [ih.1, ih.2, e']

theorem chebTQ_spec (n : ℕ) (x : ℚ) :
    ((chebTQ n x : ℚ) : ℝ) = (Chebyshev.T ℝ (n : ℤ)).eval (x : ℝ) :=
  (chebTPair_spec n x).1

theorem list_range_map_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

def finTQ (cs : List ℤ) (x : ℚ) : ℚ :=
  ((List.range cs.length).map
    (fun k => (cs.getD k 0 : ℚ) / 100000000 * chebTQ (k + 1) x / (k + 1 : ℕ))).sum

def finSQ (cs : List ℤ) (x : ℚ) : ℚ :=
  ((List.range cs.length).map
    (fun k => (cs.getD k 0 : ℚ) / 100000000 * x ^ (k + 1) / (k + 1 : ℕ))).sum

theorem finTQ_spec (cs : List ℤ) (x : ℚ) :
    ((finTQ cs x : ℚ) : ℝ) = ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (x : ℝ) / ((k + 1 : ℕ) : ℝ) := by
  unfold finTQ
  rw [list_range_map_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← chebTQ_spec]
  push_cast
  ring

theorem finSQ_spec (cs : List ℤ) (x : ℚ) :
    ((finSQ cs x : ℚ) : ℝ) = ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (x : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  unfold finSQ
  rw [list_range_map_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast
  ring

/-! ### Sums of logarithm terms -/

/-- A term `Re ((c + d i) log (a + b i))`. -/
structure LogTerm where
  c : ℚ
  d : ℚ
  a : ℚ
  b : ℚ

noncomputable def LogTerm.val (t : LogTerm) : ℝ :=
  (barrierComplex t.c t.d * Complex.log (barrierComplex t.a t.b)).re

def sumLogs : List LogTerm → Option (ℚ × ℚ)
  | [] => some (0, 0)
  | t :: l =>
    match cLog t.c t.d t.a t.b, sumLogs l with
    | some q, some (v, e) => some (q + v, (wPieces t.c t.d : ℚ) / 1000000000000 + e)
    | _, _ => none

theorem sumLogs_spec {l : List LogTerm} {v e : ℚ} (h : sumLogs l = some (v, e)) :
    |(l.map LogTerm.val).sum - (v : ℝ)| ≤ (e : ℝ) := by
  induction l generalizing v e with
  | nil =>
    simp only [sumLogs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons t l ih =>
    simp only [sumLogs] at h
    split at h
    · rename_i q v' e' hq hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 := cLog_spec hq
      have h2 := ih hl
      simp only [List.map_cons, List.sum_cons]
      have hv : t.val = (barrierComplex t.c t.d * Complex.log ⟨(t.a : ℝ), (t.b : ℝ)⟩).re := rfl
      rw [hv]
      push_cast
      calc |(barrierComplex t.c t.d * Complex.log ⟨(t.a : ℝ), (t.b : ℝ)⟩).re +
              (l.map LogTerm.val).sum - ((q : ℝ) + v')|
          ≤ |(barrierComplex t.c t.d * Complex.log ⟨(t.a : ℝ), (t.b : ℝ)⟩).re - q| +
              |(l.map LogTerm.val).sum - v'| := by
            rw [show (barrierComplex t.c t.d * Complex.log ⟨(t.a : ℝ), (t.b : ℝ)⟩).re +
              (l.map LogTerm.val).sum - ((q : ℝ) + v') =
              ((barrierComplex t.c t.d * Complex.log ⟨(t.a : ℝ), (t.b : ℝ)⟩).re - q) +
              ((l.map LogTerm.val).sum - v') by ring]
            exact abs_add_le _ _
        _ ≤ _ := add_le_add h1 h2
    · simp at h

/-! ### The fields as logarithm sums -/

/-- `1 - 2 x z + z²` as a rational complex number. -/
def quadArg (x : ℚ) (t : TailQ) : ℚ × ℚ :=
  (1 - 2 * x * t.zr + t.zr * t.zr - t.zi * t.zi, -2 * x * t.zi + 2 * t.zr * t.zi)

/-- `1 - x z`. -/
def linArg (x : ℚ) (t : TailQ) : ℚ × ℚ := (1 - x * t.zr, -(x * t.zi))

theorem quadArg_spec (x : ℚ) (t : TailQ) :
    1 - 2 * ((x : ℝ) : ℂ) * (TailQ.toC t).1 + (TailQ.toC t).1 ^ 2 =
      barrierComplex (quadArg x t).1 (quadArg x t).2 := by
  apply Complex.ext <;>
    simp [TailQ.toC, barrierComplex, quadArg, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem linArg_spec (x : ℚ) (t : TailQ) :
    1 - ((x : ℝ) : ℂ) * (TailQ.toC t).1 = barrierComplex (linArg x t).1 (linArg x t).2 := by
  apply Complex.ext <;>
    simp [TailQ.toC, barrierComplex, linArg, Complex.mul_re, Complex.mul_im]

/-- The terms of `-4 T(p, x) - S(v, x)` beyond the finite parts, and of `W₂`. -/
def rowTerms (P V : List TailQ) (x : ℚ) : List LogTerm :=
  [⟨19 / 48, 0, x, 0⟩, ⟨1 / 12, 0, 1 - x, 0⟩, ⟨-(65 / 48), 0, 1 + x * x, 0⟩] ++
    P.map (fun t => ⟨2 * t.rr, 2 * t.ri, (quadArg x t).1, (quadArg x t).2⟩) ++
    V.map (fun t => ⟨t.rr, t.ri, (linArg x t).1, (linArg x t).2⟩)

def rowRat (Pc Vc : List ℤ) (x : ℚ) : ℚ := -4 * finTQ Pc x - finSQ Vc x

def colTerms (V : List TailQ) (s : ℚ) : List LogTerm :=
  [⟨7 / 48, 0, s, 0⟩, ⟨1 / 12, 0, 1 - s, 0⟩] ++
    V.map (fun t => ⟨-t.rr, -t.ri, (quadArg s t).1, (quadArg s t).2⟩)

def colRat (Vc : List ℤ) (s : ℚ) : ℚ := 2 * finTQ Vc s

theorem re_list_sum (l : List ℂ) : l.sum.re = (l.map Complex.re).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem realLogTerm (c a : ℚ) (_ha : (a : ℝ) ≠ 0) :
    LogTerm.val ⟨c, 0, a, 0⟩ = (c : ℝ) * Real.log |(a : ℝ)| := by
  simp only [LogTerm.val, barrierComplex, Complex.mul_re, Complex.log_re]
  have : ‖(⟨(a : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ)‖ = |(a : ℝ)| := by
    rw [show (⟨(a : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = ((a : ℝ) : ℂ) by apply Complex.ext <;> simp]
    exact Complex.norm_real _
  rw [this]
  simp

theorem tailTerm_T (t : TailQ) (x : ℚ) :
    (2 * ((TailQ.toC t).2 * Complex.log (1 - 2 * ((x : ℝ) : ℂ) * (TailQ.toC t).1 +
        (TailQ.toC t).1 ^ 2))).re =
      LogTerm.val ⟨2 * t.rr, 2 * t.ri, (quadArg x t).1, (quadArg x t).2⟩ := by
  rw [quadArg_spec]
  simp only [LogTerm.val, TailQ.toC, barrierComplex, Complex.mul_re, Complex.mul_im]
  push_cast
  simp
  ring

theorem tailTerm_S (t : TailQ) (x : ℚ) :
    ((TailQ.toC t).2 * Complex.log (1 - ((x : ℝ) : ℂ) * (TailQ.toC t).1)).re =
      LogTerm.val ⟨t.rr, t.ri, (linArg x t).1, (linArg x t).2⟩ := by
  rw [linArg_spec]
  rfl

theorem tailTerm_colT (t : TailQ) (x : ℚ) :
    -((TailQ.toC t).2 * Complex.log (1 - 2 * ((x : ℝ) : ℂ) * (TailQ.toC t).1 +
        (TailQ.toC t).1 ^ 2)).re =
      LogTerm.val ⟨-t.rr, -t.ri, (quadArg x t).1, (quadArg x t).2⟩ := by
  rw [quadArg_spec]
  simp only [LogTerm.val, TailQ.toC, barrierComplex, Complex.mul_re]
  push_cast
  ring

theorem rowField_eq (Pc Vc : List ℤ) (P V : List TailQ) (hP : tailsInDisk P = true)
    (hV : tailsInDisk V = true) {x : ℚ} (hx : |(x : ℝ)| ≤ 1) (hx0 : (x : ℝ) ≠ 0)
    (hx1 : (x : ℝ) ≠ 1) :
    realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V) x =
      ((rowTerms P V x).map LogTerm.val).sum + (rowRat Pc Vc x : ℝ) := by
  have hT : (P.map (LogTerm.val ∘ fun t => (⟨2 * t.rr, 2 * t.ri, (quadArg x t).1,
      (quadArg x t).2⟩ : LogTerm))).sum = 2 * (List.map ((fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * ((x : ℝ) : ℂ) * zr.1 + zr.1 ^ 2)) ∘ TailQ.toC) P).sum.re := by
    rw [re_list_sum, List.map_map, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    rw [← tailTerm_T]
    simp [Complex.mul_re]
  have hS : (V.map (LogTerm.val ∘ fun t => (⟨t.rr, t.ri, (linArg x t).1,
      (linArg x t).2⟩ : LogTerm))).sum = (List.map ((fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - ((x : ℝ) : ℂ) * zr.1)) ∘ TailQ.toC) V).sum.re := by
    rw [re_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    exact (tailTerm_S t x).symm
  unfold realEnergyRowTrialField realEnergyField trialSeq
  rw [barrierTrialT_eq_finite_log Pc _ (tailsInDisk_spec hP) hx,
    barrierTrialS_eq_finite_log Vc _ (tailsInDisk_spec hV) hx]
  simp only [rowTerms, rowRat, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.map_map]
  have h1 : (((1 - x : ℚ)) : ℝ) ≠ 0 := by push_cast; exact sub_ne_zero.mpr hx1.symm
  have hxx : (0 : ℝ) < 1 + (x : ℝ) * x := by nlinarith [mul_self_nonneg (x : ℝ)]
  have h2 : (((1 + x * x : ℚ)) : ℝ) ≠ 0 := by push_cast; exact hxx.ne'
  rw [realLogTerm _ _ hx0, realLogTerm _ _ h1, realLogTerm _ _ h2, hT, hS]
  push_cast
  rw [finTQ_spec, finSQ_spec]
  push_cast
  have hx1' : (0 : ℝ) < 1 - x := by
    rcases lt_or_gt_of_ne hx1 with h | h
    · linarith
    · exfalso; have := (abs_le.mp hx).2; linarith
  rw [abs_of_pos hx1', abs_of_pos hxx, pow_two]
  ring

theorem colField_eq (Vc : List ℤ) (V : List TailQ) (hV : tailsInDisk V = true) {s : ℚ}
    (hs : (s : ℝ) ∈ Set.Ioo (0 : ℝ) 1) :
    realEnergyColumnTrialField (trialSeq Vc V) s =
      ((colTerms V s).map LogTerm.val).sum + (colRat Vc s : ℝ) := by
  have hx : |(s : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2.le⟩
  have hT : (V.map (LogTerm.val ∘ fun t => (⟨-t.rr, -t.ri, (quadArg s t).1,
      (quadArg s t).2⟩ : LogTerm))).sum = -1 * (List.map ((fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * ((s : ℝ) : ℂ) * zr.1 + zr.1 ^ 2)) ∘ TailQ.toC) V).sum.re := by
    rw [re_list_sum, List.map_map, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    rw [← tailTerm_colT]
    ring
  unfold realEnergyColumnTrialField realEnergyColumnField trialSeq
  rw [barrierTrialT_eq_finite_log Vc _ (tailsInDisk_spec hV) hx]
  simp only [colTerms, colRat, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.map_map]
  have h0 : (s : ℝ) ≠ 0 := hs.1.ne'
  have h1 : (((1 - s : ℚ)) : ℝ) ≠ 0 := by push_cast; linarith [hs.2]
  rw [realLogTerm _ _ h0, realLogTerm _ _ h1, hT]
  push_cast
  rw [finTQ_spec]
  push_cast
  rw [abs_of_pos hs.1, abs_of_pos (by linarith [hs.2] : (0 : ℝ) < 1 - s)]
  ring

/-! ### Certified approximations -/

def rowApprox (Pc Vc : List ℤ) (P V : List TailQ) (x : ℚ) : Option (ℚ × ℚ) :=
  (sumLogs (rowTerms P V x)).map (fun ve => (ve.1 + rowRat Pc Vc x, ve.2))

def colApprox (Vc : List ℤ) (V : List TailQ) (s : ℚ) : Option (ℚ × ℚ) :=
  (sumLogs (colTerms V s)).map (fun ve => (ve.1 + colRat Vc s, ve.2))

theorem rowApprox_spec {Pc Vc : List ℤ} {P V : List TailQ} (hP : tailsInDisk P = true)
    (hV : tailsInDisk V = true) {x v e : ℚ} (h : rowApprox Pc Vc P V x = some (v, e))
    (hx : |(x : ℝ)| ≤ 1) (hx0 : (x : ℝ) ≠ 0) (hx1 : (x : ℝ) ≠ 1) :
    realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V) x ≤ v + e := by
  unfold rowApprox at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v', e'⟩, h1, rfl, rfl⟩ := h
  have := sumLogs_spec h1
  rw [rowField_eq Pc Vc P V hP hV hx hx0 hx1]
  push_cast
  linarith [(abs_le.mp this).2]

theorem colApprox_spec {Vc : List ℤ} {V : List TailQ} (hV : tailsInDisk V = true)
    {s v e : ℚ} (h : colApprox Vc V s = some (v, e)) (hs : (s : ℝ) ∈ Set.Ioo (0 : ℝ) 1) :
    realEnergyColumnTrialField (trialSeq Vc V) s ≤ v + e := by
  unfold colApprox at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v', e'⟩, h1, rfl, rfl⟩ := h
  have := sumLogs_spec h1
  rw [colField_eq Vc V hV hs]
  push_cast
  linarith [(abs_le.mp this).2]

end CatalanMeasure.Cert
