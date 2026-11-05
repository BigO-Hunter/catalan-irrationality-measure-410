module

public import Submission.CatalanMeasure.CellCert.Scaled
public import Submission.CatalanMeasure.Cert.Norm
public import Submission.CatalanMeasure.Cert.SplitNorm

@[expose] public section

/-!
# The weighted norm of a scale-`2^40` trial sequence in closed form

`barrierTrialNormSq (trialSeqS cs tail) = finNormQS cs tail + Re Σ pair logs`, where the finite
part is the exact rational

  `finNormQS cs tail = Σ_k f_k² / k + 2 Σ_j Re (r_j Σ_k (f_k / k) z_j^k)`,   `f_k = cs[k-1] / 2^40`,

evaluated by a Horner scheme over `ℚ × ℚ` (linear in the number of modes, instead of
recomputing `z^k` for every `k` as `Cert.finNormQ` does).  The log part reuses `Cert.pairTerms`
and `Cert.sumLogs`.  Sharding lemmas (`sum_le_of_chunks`, `pair_le_of_row_chunks`) let the
finite part and the log part be certified by many small `decide +kernel` checks.
-/

open OAI.InternalCatalan

namespace CatalanMeasure.CellCert
open CatalanMeasure.Cert

/-! ### Horner evaluation of the cross term -/

/-- `f / k` for the coefficient `c / 2^40` at index `k = i + 1`. -/
def nCoef (c : ℤ) (i : ℕ) : ℚ := (c : ℚ) / 1099511627776 / ((i + 1 : ℕ) : ℚ)

def cadd1 (c : ℚ) (a : ℚ × ℚ) : ℚ × ℚ := (c + a.1, a.2)

/-- `Σ_k nCoef c_k (i + k) z^(k+1)` by Horner's rule. -/
def nHorner (z : ℚ × ℚ) : List ℤ → ℕ → ℚ × ℚ
  | [], _ => (0, 0)
  | c :: cs, i => cmulQ z (cadd1 (nCoef c i) (nHorner z cs (i + 1)))

/-- `Re (r Σ_k (f_k / k) z^k)` for one tail. -/
def nCross (cs : List ℤ) (t : TailQ) : ℚ :=
  (cmulQ (t.rr, t.ri) (nHorner (t.zr, t.zi) cs 0)).1

/-- `Σ_k f_k² / k`. -/
def nSq : List ℤ → ℕ → ℚ
  | [], _ => 0
  | c :: cs, i => ((c : ℚ) / 1099511627776) ^ 2 / ((i + 1 : ℕ) : ℚ) + nSq cs (i + 1)

/-- The finite part of the weighted norm. -/
def finNormQS (cs : List ℤ) (tail : List TailQ) : ℚ :=
  nSq cs 0 + 2 * (tail.map (nCross cs)).sum

/-! ### Correctness of the finite part -/

theorem cmulQ_assoc (a b c : ℚ × ℚ) : cmulQ (cmulQ a b) c = cmulQ a (cmulQ b c) := by
  simp only [cmulQ]; ext <;> ring

def crossRec (t : TailQ) : List ℤ → ℕ → ℚ
  | [], _ => 0
  | c :: cs, i =>
    nCoef c i * (cmulQ (t.rr, t.ri) (cpowQ (t.zr, t.zi) (i + 1))).1 + crossRec t cs (i + 1)

theorem crossRec_eq (t : TailQ) (cs : List ℤ) (i : ℕ) :
    crossRec t cs i =
      (cmulQ (cmulQ (t.rr, t.ri) (cpowQ (t.zr, t.zi) i)) (nHorner (t.zr, t.zi) cs i)).1 := by
  induction cs generalizing i with
  | nil => simp [crossRec, nHorner, cmulQ]
  | cons c cs ih =>
    rw [crossRec, ih (i + 1)]
    simp only [nHorner, cadd1, cpowQ, cmulQ]
    ring

/-- `Σ_k (f_k² + 2 f_k t_k) / k`, the definition of the finite part. -/
def nRec (tail : List TailQ) : List ℤ → ℕ → ℚ
  | [], _ => 0
  | c :: cs, i =>
    ((((c : ℚ) / 1099511627776) ^ 2 + 2 * ((c : ℚ) / 1099511627776) * tailValQ tail (i + 1)) /
        ((i + 1 : ℕ) : ℚ)) + nRec tail cs (i + 1)

theorem nRec_eq (tail : List TailQ) (cs : List ℤ) (i : ℕ) :
    nRec tail cs i = nSq cs i + 2 * (tail.map (fun t => crossRec t cs i)).sum := by
  induction cs generalizing i with
  | nil => simp [nRec, nSq, crossRec]
  | cons c cs ih =>
    rw [nRec, ih (i + 1), nSq]
    have h1 : (tail.map (fun t => crossRec t (c :: cs) i)).sum =
        nCoef c i * tailValQ tail (i + 1) + (tail.map (fun t => crossRec t cs (i + 1))).sum := by
      simp only [crossRec, List.sum_map_add, tailValQ, List.sum_map_mul_left]
    rw [h1]
    unfold nCoef
    ring

theorem finNormQS_eq_nRec (cs : List ℤ) (tail : List TailQ) :
    finNormQS cs tail = nRec tail cs 0 := by
  rw [nRec_eq]
  unfold finNormQS
  congr 2
  apply congrArg
  apply List.map_congr_left
  intro t _
  rw [crossRec_eq]
  simp [nCross, cpowQ, cmulQ]

theorem nRec_eq_sum (tail : List TailQ) (cs : List ℤ) (i : ℕ) :
    nRec tail cs i = ∑ k ∈ Finset.range cs.length,
      (((((cs.getD k 0 : ℤ) : ℚ) / 1099511627776) ^ 2 +
        2 * (((cs.getD k 0 : ℤ) : ℚ) / 1099511627776) * tailValQ tail (i + k + 1)) /
          ((i + k + 1 : ℕ) : ℚ)) := by
  induction cs generalizing i with
  | nil => simp [nRec]
  | cons c cs ih =>
    rw [nRec, ih (i + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : i + 1 + k + 1 = i + (k + 1) + 1 := by omega
    rw [this]

theorem finNormQS_eq_sum (cs : List ℤ) (tail : List TailQ) :
    finNormQS cs tail = ∑ k ∈ Finset.range cs.length,
      (((((cs.getD k 0 : ℤ) : ℚ) / 1099511627776) ^ 2 +
        2 * (((cs.getD k 0 : ℤ) : ℚ) / 1099511627776) * tailValQ tail (k + 1)) /
          ((k + 1 : ℕ) : ℚ)) := by
  rw [finNormQS_eq_nRec, nRec_eq_sum]
  simp only [zero_add]

/-! ### The closed form -/

theorem trialSeqS_normSq {cs : List ℤ} {tail : List TailQ} (h : tailsInDisk tail = true) :
    barrierTrialNormSq (trialSeqS cs tail) =
      (finNormQS cs tail : ℝ) + ((pairsOf (tail.map TailQ.toC)).map pairVal).sum.re := by
  have hl := tailsInDisk_spec h
  have hB := tail_sq_hasSum _ hl
  have hA : HasSum (fun k : ℕ =>
      (finCoeffS cs (k + 1) ^ 2 + 2 * finCoeffS cs (k + 1) *
        ((tail.map TailQ.toC).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re) /
          ((k + 1 : ℕ) : ℝ)) (finNormQS cs tail : ℝ) := by
    have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
      (s := Finset.range cs.length)
      (f := fun k : ℕ => (finCoeffS cs (k + 1) ^ 2 + 2 * finCoeffS cs (k + 1) *
        ((tail.map TailQ.toC).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re) /
          ((k + 1 : ℕ) : ℝ)) (by
        intro k hk
        rw [finCoeffS_eq_zero (by simp at hk; omega)]
        simp)
    convert this using 1
    rw [finNormQS_eq_sum, Rat.cast_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [finCoeffS_succ, ← tailValQ_spec]
    push_cast
    ring
  have hsum := hA.add hB
  unfold barrierTrialNormSq
  rw [← hsum.tsum_eq]
  congr 1
  funext k
  unfold trialSeqS
  simp only [Nat.add_one_ne_zero, ite_false]
  ring

/-! ### Approximation and the one-shot certificate -/

def normApproxS (cs : List ℤ) (tail : List TailQ) : Option (ℚ × ℚ) :=
  (sumLogs (pairTerms tail)).map (fun ve => (ve.1 + finNormQS cs tail, ve.2))

theorem normApproxS_spec {cs : List ℤ} {tail : List TailQ} (h : tailsInDisk tail = true)
    {v e : ℚ} (hn : normApproxS cs tail = some (v, e)) :
    barrierTrialNormSq (trialSeqS cs tail) ≤ v + e := by
  unfold normApproxS at hn
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hn
  obtain ⟨⟨v', e'⟩, h1, rfl, rfl⟩ := hn
  have := sumLogs_spec h1
  rw [trialSeqS_normSq h, ← pairTerms_val]
  push_cast
  linarith [(abs_le.mp this).2]

def normOKS (cs : List ℤ) (tail : List TailQ) (B : ℚ) : Bool :=
  tailsInDisk tail &&
    match normApproxS cs tail with
    | some ve => decide (ve.1 + ve.2 ≤ B)
    | none => false

theorem normOKS_spec {cs : List ℤ} {tail : List TailQ} {B : ℚ} (h : normOKS cs tail B = true) :
    barrierTrialNormSq (trialSeqS cs tail) ≤ B := by
  unfold normOKS at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hd, h⟩ := h
  split at h
  · rename_i ve hve
    simp only [decide_eq_true_eq] at h
    have := normApproxS_spec hd (v := ve.1) (e := ve.2) (by rw [hve])
    have hB : ((ve.1 + ve.2 : ℚ) : ℝ) ≤ B := by exact_mod_cast h
    push_cast at hB
    linarith
  · simp at h

/-! ### Sharding -/

/-- Cutting a list into consecutive blocks of `n` and bounding each block's sum. -/
theorem sum_le_of_chunks {α β : Type*} [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    (f : α → β) (n : ℕ) (ubs : List β) :
    ∀ (L : List α), L.length ≤ n * ubs.length →
      (∀ g < ubs.length, (((L.drop (n * g)).take n).map f).sum ≤ ubs.getD g 0) →
      (L.map f).sum ≤ ubs.sum := by
  induction ubs with
  | nil =>
    intro L hL _
    have : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hL)
    subst this; simp
  | cons u ubs ih =>
    intro L hL h
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, List.drop_zero, List.getD_cons_zero] at h0
    have hsplit : (L.map f).sum = ((L.take n).map f).sum + ((L.drop n).map f).sum := by
      rw [← List.sum_append, ← List.map_append, List.take_append_drop]
    rw [hsplit, List.sum_cons]
    refine add_le_add h0 (ih (L.drop n) ?_ ?_)
    · rw [List.length_drop]
      simp only [List.length_cons] at hL
      rw [Nat.mul_succ] at hL
      omega
    · intro g hg
      have := h (g + 1) (by simpa using hg)
      rw [List.drop_drop, show n + n * g = n * (g + 1) by ring]
      simpa using this

/-- One row of `pairTerms`: all terms with first index `a`. -/
def rowTerms (tail : List TailQ) (a : TailQ) : List LogTerm :=
  tail.flatMap (fun b =>
    let w1 := cmulQ (a.rr, a.ri) (b.rr, b.ri)
    let w2 := cmulQ (a.rr, a.ri) (b.rr, -b.ri)
    let y1 := cmulQ (a.zr, a.zi) (b.zr, b.zi)
    let y2 := cmulQ (a.zr, a.zi) (b.zr, -b.zi)
    [⟨-(w1.1 / 2), -(w1.2 / 2), 1 - y1.1, -y1.2⟩, ⟨-(w2.1 / 2), -(w2.2 / 2), 1 - y2.1, -y2.2⟩])

theorem pairTerms_eq_rows (tail : List TailQ) :
    pairTerms tail = tail.flatMap (rowTerms tail) := rfl

theorem pair_le_of_row_chunks (tail : List TailQ) (n : ℕ) (bs : List ℚ)
    (hlen : tail.length ≤ n * bs.length)
    (h : ∀ g < bs.length,
      logUpperOK (((tail.drop (n * g)).take n).flatMap (rowTerms tail)) (bs.getD g 0) = true) :
    ((pairTerms tail).map LogTerm.val).sum ≤ ((bs.sum : ℚ) : ℝ) := by
  have key : ((pairTerms tail).map LogTerm.val).sum =
      (tail.map (fun a => ((rowTerms tail a).map LogTerm.val).sum)).sum := by
    rw [pairTerms_eq_rows, List.map_flatMap, lsum_flatMap]
  rw [key]
  have hget : ∀ g, ((bs.map (Rat.cast : ℚ → ℝ)).getD g 0) = ((bs.getD g 0 : ℚ) : ℝ) := by
    intro g
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases bs[g]? <;> simp
  have := sum_le_of_chunks (fun a => ((rowTerms tail a).map LogTerm.val).sum) n
    (bs.map (Rat.cast : ℚ → ℝ)) tail (by simpa using hlen) (by
      intro g hg
      rw [List.length_map] at hg
      have hh := logUpper_le (h g hg)
      rw [List.map_flatMap, lsum_flatMap] at hh
      rw [hget]
      simpa [List.map_map, Function.comp_def] using hh)
  rw [Rat.cast_list_sum]
  exact this

/-- The weighted norm of a trial is bounded by the finite part and the log chunk bounds. -/
theorem normSq_le_of_shards {cs : List ℤ} {tail : List TailQ} (hd : tailsInDisk tail = true)
    {B : ℚ} (nf : ℕ) (fubs : List ℚ) (sqUb : ℚ) (nl : ℕ) (bs : List ℚ)
    (hsq : nSq cs 0 ≤ sqUb)
    (hlenF : tail.length ≤ nf * fubs.length)
    (hF : ∀ g < fubs.length,
      (((tail.drop (nf * g)).take nf).map (nCross cs)).sum ≤ fubs.getD g 0)
    (hlenL : tail.length ≤ nl * bs.length)
    (hL : ∀ g < bs.length,
      logUpperOK (((tail.drop (nl * g)).take nl).flatMap (rowTerms tail)) (bs.getD g 0) = true)
    (hB : sqUb + 2 * fubs.sum + bs.sum ≤ B) :
    barrierTrialNormSq (trialSeqS cs tail) ≤ (B : ℝ) := by
  rw [trialSeqS_normSq hd, ← pairTerms_val]
  have h1 : (tail.map (nCross cs)).sum ≤ fubs.sum :=
    sum_le_of_chunks (nCross cs) nf fubs tail hlenF hF
  have h2 := pair_le_of_row_chunks tail nl bs hlenL hL
  have hfin : finNormQS cs tail ≤ sqUb + 2 * fubs.sum := by
    unfold finNormQS; linarith
  have hr := (Rat.cast_le (K := ℝ)).2 hB
  rw [Rat.cast_add] at hr
  have hf := (Rat.cast_le (K := ℝ)).2 hfin
  linarith

end CatalanMeasure.CellCert
