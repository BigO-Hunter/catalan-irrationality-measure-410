module

public import Submission.CatalanMeasure.Cert.Norm
public import Submission.CatalanMeasure.CellCert.Scaled
public import Submission.CatalanMeasure.GenD.D58.Cert590.NormV
public import Submission.CatalanMeasure.GenD.D58.Cert590.NormP
public import Submission.CatalanMeasure.GenD.Signed.TaylorCell

@[expose] public section

/-!
# The norm split `u = finite + tail` (Theorem A, lane E1, item 10)

`‖u‖² = Σ_{k ≥ 1} u_k² / k` (`barrierTrialNormSq`).  For `u = u₀ + h` with `h` finitely supported,

  `‖u₀ + h‖² = ‖u₀‖² + 2 Σ_{k ≤ L} u₀(k) h(k) / k + Σ_{k ≤ L} h(k)² / k`   (`normSq_add_fin`).

* For the trial sequences `v = v₅₉₀ + dv`, `p = p₅₉₀ + dp`: `u₀ = trialSeqS Vc V` (resp. `Pc P`),
  `‖u₀‖² ≤ NV` (resp. `NP`) by `Cert590.normV_le`/`normP_le`; `h = dv` (`dp`);
  `u₀(k) = Vc_k/2^40 + tailValQ V k`, so the cross term is `qDot Vc dv + qCross dv V` — an exact
  rational (`qCross` by Horner's rule in every pole, `qCross_eq`, mirroring `CellCert.nCross`).
* For `a` (`u₀` = pure tail, 20 poles, `h = aF`): `‖u₀‖² ≤ B` by `Cert.normOK [] tail B`
  (the scale `2^40` is irrelevant for `cs = []`; `trialSeqS_nil_eq`).

`normChkP` is the Boolean check; `norm_perturb_le` and `norm_tail_le` are the theorems, stated for
`tseqE (fQE f) (tl.map TailQ.toC)`, which is `FieldForm.tseq (Hid.fQ f) …` by `rfl` (EvalNormT).
-/

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalNorm
open CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.CellCert (trialSeqS finCoeffS finCoeffS_succ finCoeffS_eq_zero)
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd vecAdd_getD)

/-! ### 1. Local copies of `FieldForm.tseq` and `Hid.fQ` (so this module does not import them) -/

/-- Same body as `FieldForm.tseq` for the tail `tl.map TailQ.toC`. -/
noncomputable def tseqE (f : ℕ → ℝ) (tail : List (ℂ × ℂ)) (k : ℕ) : ℝ :=
  if k = 0 then 0 else f k + (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re

/-- Same body as `Hid.fQ`. -/
def fQE (f : List ℚ) (k : ℕ) : ℝ := if k = 0 then 0 else ((f.getD (k - 1) 0 : ℚ) : ℝ)

theorem fQE_supp (f : List ℚ) {k : ℕ} (hk : f.length ≤ k) : fQE f (k + 1) = 0 := by
  simp [fQE, List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

/-! ### 2. The bilinear identity -/

theorem summable_add_fin (u h : ℕ → ℝ) (L : ℕ)
    (hu : Summable (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)))
    (hh : ∀ k, L ≤ k → h (k + 1) = 0) :
    Summable (fun k : ℕ => (u (k + 1) + h (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
  set g : ℕ → ℝ := fun k => 2 * (u (k + 1) * h (k + 1) / ((k + 1 : ℕ) : ℝ)) +
    h (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) with hg
  have hg0 : ∀ k ∉ Finset.range L, g k = 0 := by
    intro k hk
    have : L ≤ k := by simpa using hk
    simp [hg, hh k this]
  have hgs : Summable g := summable_of_ne_finset_zero hg0
  have e : (fun k : ℕ => (u (k + 1) + h (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ)) =
      fun k => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) + g k := by
    funext k; simp only [hg]; ring
  rw [e]
  exact hu.add hgs

theorem normSq_add_fin (u h : ℕ → ℝ) (L : ℕ)
    (hu : Summable (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)))
    (hh : ∀ k, L ≤ k → h (k + 1) = 0) :
    barrierTrialNormSq (fun k => u k + h k) = barrierTrialNormSq u +
      2 * ∑ k ∈ Finset.range L, u (k + 1) * h (k + 1) / ((k + 1 : ℕ) : ℝ) +
      ∑ k ∈ Finset.range L, h (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) := by
  set g : ℕ → ℝ := fun k => 2 * (u (k + 1) * h (k + 1) / ((k + 1 : ℕ) : ℝ)) +
    h (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) with hg
  have hg0 : ∀ k ∉ Finset.range L, g k = 0 := by
    intro k hk
    have : L ≤ k := by simpa using hk
    simp [hg, hh k this]
  have hgs : Summable g := summable_of_ne_finset_zero hg0
  have e : (fun k : ℕ => (u (k + 1) + h (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ)) =
      fun k => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) + g k := by
    funext k; simp only [hg]; ring
  have key : ∑' k : ℕ, (u (k + 1) + h (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ) =
      (∑' k : ℕ, u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) + ∑ k ∈ Finset.range L, g k := by
    rw [e, hu.tsum_add hgs, tsum_eq_sum hg0]
  unfold barrierTrialNormSq
  show (∑' k : ℕ, (u (k + 1) + h (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ)) = _
  rw [key, hg, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-! ### 3. Exact rational pieces and Horner's rule -/

/-- `Σ_k f_k² / (i + k + 1)`. -/
def qSq : List ℚ → ℕ → ℚ
  | [], _ => 0
  | f :: fs, i => f ^ 2 / ((i + 1 : ℕ) : ℚ) + qSq fs (i + 1)

/-- `Σ_k f_k · (tail value at i+k+1) / (i + k + 1)`. -/
def qTailRec (tl : List TailQ) : List ℚ → ℕ → ℚ
  | [], _ => 0
  | f :: fs, i => f * tailValQ tl (i + 1) / ((i + 1 : ℕ) : ℚ) + qTailRec tl fs (i + 1)

/-- `Σ_k f_k · (c_{i+k}/2^40) / (i + k + 1)`. -/
def qDot (cs : List ℤ) : List ℚ → ℕ → ℚ
  | [], _ => 0
  | f :: fs, i => f * ((cs.getD i 0 : ℚ) / 2 ^ 40) / ((i + 1 : ℕ) : ℚ) + qDot cs fs (i + 1)

/-- `Σ_k (f_k / (i + k + 1)) z^(k+1)` by Horner's rule. -/
def hornQ (z : ℚ × ℚ) : List ℚ → ℕ → ℚ × ℚ
  | [], _ => (0, 0)
  | f :: fs, i =>
    cmulQ z (f / ((i + 1 : ℕ) : ℚ) + (hornQ z fs (i + 1)).1, (hornQ z fs (i + 1)).2)

/-- `Re (r Σ_k (f_k / k) z^k)` for one tail entry. -/
def crossH (fs : List ℚ) (t : TailQ) : ℚ := (cmulQ (t.rr, t.ri) (hornQ (t.zr, t.zi) fs 0)).1

def qCross (fs : List ℚ) (tl : List TailQ) : ℚ := (tl.map (crossH fs)).sum

def qCrossRec (t : TailQ) : List ℚ → ℕ → ℚ
  | [], _ => 0
  | f :: fs, i =>
    f / ((i + 1 : ℕ) : ℚ) * (cmulQ (t.rr, t.ri) (cpowQ (t.zr, t.zi) (i + 1))).1 +
      qCrossRec t fs (i + 1)

theorem qCrossRec_eq (t : TailQ) (fs : List ℚ) (i : ℕ) :
    qCrossRec t fs i =
      (cmulQ (cmulQ (t.rr, t.ri) (cpowQ (t.zr, t.zi) i)) (hornQ (t.zr, t.zi) fs i)).1 := by
  induction fs generalizing i with
  | nil => simp [qCrossRec, hornQ, cmulQ]
  | cons f fs ih =>
    rw [qCrossRec, ih (i + 1)]
    simp only [hornQ, cpowQ, cmulQ]
    ring

theorem sum_qCrossRec (tl : List TailQ) (fs : List ℚ) (i : ℕ) :
    (tl.map (fun t => qCrossRec t fs i)).sum = qTailRec tl fs i := by
  induction fs generalizing i with
  | nil => simp [qCrossRec, qTailRec]
  | cons f fs ih =>
    have h1 : (tl.map (fun t => qCrossRec t (f :: fs) i)).sum =
        f / ((i + 1 : ℕ) : ℚ) * tailValQ tl (i + 1) +
          (tl.map (fun t => qCrossRec t fs (i + 1))).sum := by
      simp only [qCrossRec, List.sum_map_add, tailValQ, List.sum_map_mul_left]
    rw [h1, ih (i + 1), qTailRec]
    ring

theorem qCross_eq (fs : List ℚ) (tl : List TailQ) : qCross fs tl = qTailRec tl fs 0 := by
  rw [← sum_qCrossRec]
  unfold qCross
  congr 1
  apply List.map_congr_left
  intro t _
  rw [qCrossRec_eq]
  simp [crossH, cpowQ, cmulQ]

/-! ### 4. The recursions as sums -/

theorem qSq_eq_sum (fs : List ℚ) (i : ℕ) :
    qSq fs i = ∑ k ∈ Finset.range fs.length, (fs.getD k 0) ^ 2 / ((i + k + 1 : ℕ) : ℚ) := by
  induction fs generalizing i with
  | nil => simp [qSq]
  | cons f fs ih =>
    rw [qSq, ih (i + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : i + 1 + k + 1 = i + (k + 1) + 1 := by omega
    rw [this]

theorem qTailRec_eq_sum (tl : List TailQ) (fs : List ℚ) (i : ℕ) :
    qTailRec tl fs i = ∑ k ∈ Finset.range fs.length,
      fs.getD k 0 * tailValQ tl (i + k + 1) / ((i + k + 1 : ℕ) : ℚ) := by
  induction fs generalizing i with
  | nil => simp [qTailRec]
  | cons f fs ih =>
    rw [qTailRec, ih (i + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : i + 1 + k + 1 = i + (k + 1) + 1 := by omega
    rw [this]

theorem qDot_eq_sum (cs : List ℤ) (fs : List ℚ) (i : ℕ) :
    qDot cs fs i = ∑ k ∈ Finset.range fs.length,
      fs.getD k 0 * ((cs.getD (i + k) 0 : ℚ) / 2 ^ 40) / ((i + k + 1 : ℕ) : ℚ) := by
  induction fs generalizing i with
  | nil => simp [qDot]
  | cons f fs ih =>
    rw [qDot, ih (i + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : i + 1 + k = i + (k + 1) := by omega
    rw [this]

/-! ### 5. Sequences -/

theorem trialSeqS_nil_eq (tl : List TailQ) : trialSeqS [] tl = trialSeq [] tl := by
  funext k
  unfold trialSeqS trialSeq barrierTrial barrierFiniteCoeff finCoeffS
  simp

/-- The weighted squares of a pure tail are summable. -/
theorem summable_tail (tl : List TailQ) (hd : tailsInDisk tl = true) :
    Summable (fun k : ℕ => trialSeq [] tl (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
  have := (tail_sq_hasSum (tl.map TailQ.toC) (tailsInDisk_spec hd)).summable
  refine this.congr (fun k => ?_)
  unfold trialSeq barrierTrial barrierFiniteCoeff
  simp

theorem trialSeqS_succ (cs : List ℤ) (tl : List TailQ) (k : ℕ) :
    trialSeqS cs tl (k + 1) = (cs.getD k 0 : ℝ) / 2 ^ 40 + ((tailValQ tl (k + 1) : ℚ) : ℝ) := by
  rw [tailValQ_spec]
  unfold trialSeqS
  rw [if_neg (Nat.succ_ne_zero k), finCoeffS_succ]
  norm_num

theorem trialSeqS_eq_add (cs : List ℤ) (tl : List TailQ) :
    trialSeqS cs tl = fun k => trialSeq [] tl k + finCoeffS cs k := by
  funext k
  rcases k with _ | k
  · simp [trialSeqS, trialSeq, barrierTrial, finCoeffS]
  · rw [trialSeqS_succ]
    unfold trialSeq barrierTrial barrierFiniteCoeff
    rw [tailValQ_spec, finCoeffS_succ]
    simp
    norm_num
    ring

theorem summable_trialSeqS (cs : List ℤ) (tl : List TailQ) (hd : tailsInDisk tl = true) :
    Summable (fun k : ℕ => trialSeqS cs tl (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
  rw [trialSeqS_eq_add]
  exact summable_add_fin (trialSeq [] tl) (finCoeffS cs) cs.length (summable_tail tl hd)
    (fun k hk => finCoeffS_eq_zero (by omega))

theorem getD_map_div (cs : List ℤ) (k : ℕ) :
    ((cs.map (fun n : ℤ => (n : ℚ) / 2 ^ 40)).getD k 0) = (cs.getD k 0 : ℚ) / 2 ^ 40 := by
  induction cs generalizing k with
  | nil => simp
  | cons c cs ih =>
    cases k with
    | zero => simp
    | succ k => simpa using ih k

/-- The sequence `v₅₉₀ + dv`: finite part `Cs/2^40 + dl`, same tail. -/
theorem perturb_seq (cs : List ℤ) (dl : List ℚ) (tl : List TailQ) :
    tseqE (fQE (vecAdd (cs.map (fun n : ℤ => (n : ℚ) / 2 ^ 40)) dl)) (tl.map TailQ.toC) =
      fun k => trialSeqS cs tl k + fQE dl k := by
  funext k
  rcases k with _ | k
  · simp [tseqE, trialSeqS, fQE]
  · unfold tseqE trialSeqS
    simp only [Nat.succ_ne_zero, if_false]
    rw [finCoeffS_succ]
    unfold fQE
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [vecAdd_getD, getD_map_div]
    push_cast
    norm_num
    ring

/-! ### 6. The checks -/

/-- `‖v‖² ≤ Bf` for `v = (cs/2^40 + dl) + tail`, given `‖trialSeqS cs tl‖² ≤ B0`. -/
def normChkP (cs : List ℤ) (dl : List ℚ) (tl : List TailQ) (B0 Bf : ℚ) : Bool :=
  tailsInDisk tl && decide (B0 + 2 * (qCross dl tl + qDot cs dl 0) + qSq dl 0 ≤ Bf)

theorem norm_perturb_le {cs : List ℤ} {dl : List ℚ} {tl : List TailQ} {B0 Bf : ℚ}
    (h0 : barrierTrialNormSq (trialSeqS cs tl) ≤ (B0 : ℝ))
    (h : normChkP cs dl tl B0 Bf = true) :
    barrierTrialNormSq (tseqE (fQE (vecAdd (cs.map (fun n : ℤ => (n : ℚ) / 2 ^ 40)) dl))
        (tl.map TailQ.toC)) ≤ (Bf : ℝ) := by
  unfold normChkP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hd, hB⟩ := h
  rw [perturb_seq]
  have hs := summable_trialSeqS cs tl hd
  rw [normSq_add_fin (trialSeqS cs tl) (fQE dl) dl.length hs (fun k hk => fQE_supp dl hk)]
  have e1 : ∑ k ∈ Finset.range dl.length,
      trialSeqS cs tl (k + 1) * fQE dl (k + 1) / ((k + 1 : ℕ) : ℝ) =
        ((qCross dl tl + qDot cs dl 0 : ℚ) : ℝ) := by
    rw [qCross_eq, qTailRec_eq_sum, qDot_eq_sum]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [trialSeqS_succ]
    simp only [fQE, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, zero_add]
    push_cast
    ring
  have e2 : ∑ k ∈ Finset.range dl.length, fQE dl (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) =
      ((qSq dl 0 : ℚ) : ℝ) := by
    rw [qSq_eq_sum]
    push_cast
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [fQE, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, zero_add]
  rw [e1, e2]
  have hB' : ((B0 + 2 * (qCross dl tl + qDot cs dl 0) + qSq dl 0 : ℚ) : ℝ) ≤ (Bf : ℝ) := by
    exact_mod_cast hB
  push_cast at hB' ⊢
  linarith

theorem vecAdd_nil_left (l : List ℚ) : vecAdd [] l = l := by cases l <;> rfl

/-- A pure tail plus a finite part `fl`: `‖tail‖² ≤ Bt` from `normOK [] tl Bt`. -/
theorem norm_tail_le {fl : List ℚ} {tl : List TailQ} {Bt Bf : ℚ}
    (hB : normOK [] tl Bt = true) (h : normChkP [] fl tl Bt Bf = true) :
    barrierTrialNormSq (tseqE (fQE fl) (tl.map TailQ.toC)) ≤ (Bf : ℝ) := by
  have h0 : barrierTrialNormSq (trialSeqS [] tl) ≤ (Bt : ℝ) := by
    rw [trialSeqS_nil_eq]; exact normOK_spec hB
  have h1 := norm_perturb_le (cs := ([] : List ℤ)) h0 h
  rw [List.map_nil, vecAdd_nil_left] at h1
  exact h1

/-! ### 7. The Cert590 caps -/

/-- `‖v‖² ≤ Bf` for `v = v₅₉₀ + dv`. -/
theorem norm_v_le {dl : List ℚ} {Bf : ℚ}
    (h : normChkP CatalanMeasure.GenD.D58.Cert590.Vc dl CatalanMeasure.GenD.D58.Cert590.V
      CatalanMeasure.GenD.D58.Cert590.NV Bf = true) :
    barrierTrialNormSq (tseqE (fQE (vecAdd (CatalanMeasure.GenD.D58.Cert590.Vc.map
      (fun n : ℤ => (n : ℚ) / 2 ^ 40)) dl)) (CatalanMeasure.GenD.D58.Cert590.V.map TailQ.toC))
      ≤ (Bf : ℝ) :=
  norm_perturb_le CatalanMeasure.GenD.D58.Cert590.normV_le h

theorem norm_p_le {dl : List ℚ} {Bf : ℚ}
    (h : normChkP CatalanMeasure.GenD.D58.Cert590.Pc dl CatalanMeasure.GenD.D58.Cert590.P
      CatalanMeasure.GenD.D58.Cert590.NP Bf = true) :
    barrierTrialNormSq (tseqE (fQE (vecAdd (CatalanMeasure.GenD.D58.Cert590.Pc.map
      (fun n : ℤ => (n : ℚ) / 2 ^ 40)) dl)) (CatalanMeasure.GenD.D58.Cert590.P.map TailQ.toC))
      ≤ (Bf : ℝ) :=
  norm_perturb_le CatalanMeasure.GenD.D58.Cert590.normP_le h

end CatalanMeasure.GenD.Signed.Data.Consts.EvalNorm
