module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierFinitePotentialRat
public import Submission.CatalanMeasure.Cert.FieldDeriv

@[expose] public section

/-!
# The weighted norm `Σ u_k² / k` of a trial sequence in closed form

For `u_k = f_k + Re Σ_j r_j z_j^k` with finitely many `f_k`,
`Σ_k u_k² / k = Σ_k (f_k² + 2 f_k t_k) / k + ½ Re Σ_{j,l} (-r_j r_l log (1 - z_j z_l)
- r_j conj r_l log (1 - z_j conj z_l))`, where `t_k = Re Σ_j r_j z_j^k`.  The first sum is
finite and rational; the second is a sum of logarithm terms, approximated by `sumLogs`.
-/

open OAI.InternalCatalan

namespace CatalanMeasure.Cert

/-! ### Rational complex arithmetic -/

def cmulQ (a b : ℚ × ℚ) : ℚ × ℚ := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

def cpowQ (a : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => cmulQ (cpowQ a n) a

noncomputable def toCQ (a : ℚ × ℚ) : ℂ := barrierComplex a.1 a.2

theorem toCQ_mul (a b : ℚ × ℚ) : toCQ (cmulQ a b) = toCQ a * toCQ b := by
  apply Complex.ext <;> simp [toCQ, cmulQ, barrierComplex, Complex.mul_re, Complex.mul_im]

theorem toCQ_pow (a : ℚ × ℚ) (n : ℕ) : toCQ (cpowQ a n) = toCQ a ^ n := by
  induction n with
  | zero => apply Complex.ext <;> simp [toCQ, cpowQ, barrierComplex]
  | succ n ih => rw [cpowQ, toCQ_mul, ih, pow_succ]

theorem TailQ.toC_eq (t : TailQ) : t.toC = (toCQ (t.zr, t.zi), toCQ (t.rr, t.ri)) := rfl

/-- `Re Σ_j r_j z_j^k`, exactly. -/
def tailValQ (tail : List TailQ) (k : ℕ) : ℚ :=
  (tail.map (fun t => (cmulQ (t.rr, t.ri) (cpowQ (t.zr, t.zi) k)).1)).sum

theorem tailValQ_spec (tail : List TailQ) (k : ℕ) :
    ((tailValQ tail k : ℚ) : ℝ) =
      ((tail.map TailQ.toC).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re := by
  unfold tailValQ
  rw [re_list_sum_map, List.map_map, Rat.cast_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, TailQ.toC_eq]
  rw [← toCQ_pow, ← toCQ_mul]
  simp [toCQ, barrierComplex]

/-- The finite part `Σ_{k ≤ K} (f_k² + 2 f_k t_k) / k`. -/
def finNormQ (cs : List ℤ) (tail : List TailQ) : ℚ :=
  ((List.range cs.length).map (fun k =>
    let f : ℚ := (cs.getD k 0 : ℚ) / 100000000
    (f * f + 2 * f * tailValQ tail (k + 1)) / (k + 1 : ℕ))).sum

/-- The logarithm terms `-½ r_j r_l log (1 - z_j z_l)` and `-½ r_j conj r_l log (1 - z_j conj z_l)`. -/
def pairTerms (tail : List TailQ) : List LogTerm :=
  tail.flatMap (fun a => tail.flatMap (fun b =>
    let w1 := cmulQ (a.rr, a.ri) (b.rr, b.ri)
    let w2 := cmulQ (a.rr, a.ri) (b.rr, -b.ri)
    let y1 := cmulQ (a.zr, a.zi) (b.zr, b.zi)
    let y2 := cmulQ (a.zr, a.zi) (b.zr, -b.zi)
    [⟨-(w1.1 / 2), -(w1.2 / 2), 1 - y1.1, -y1.2⟩, ⟨-(w2.1 / 2), -(w2.2 / 2), 1 - y2.1, -y2.2⟩]))

def normApprox (cs : List ℤ) (tail : List TailQ) : Option (ℚ × ℚ) :=
  (sumLogs (pairTerms tail)).map (fun ve => (ve.1 + finNormQ cs tail, ve.2))

/-! ### The closed form -/

theorem hasSum_list_sum {α : Type*} (L : List α) (F : α → ℕ → ℂ) (s : α → ℂ)
    (h : ∀ a ∈ L, HasSum (F a) (s a)) :
    HasSum (fun k => (L.map (fun a => F a k)).sum) (L.map s).sum := by
  induction L with
  | nil => simpa using hasSum_zero
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-- All ordered pairs from a list. -/
def pairsOf {α : Type*} (L : List α) : List (α × α) := L.flatMap (fun a => L.map (fun b => (a, b)))

theorem mem_pairsOf {α : Type*} {L : List α} {p : α × α} (hp : p ∈ pairsOf L) :
    p.1 ∈ L ∧ p.2 ∈ L := by
  simp only [pairsOf, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨a, ha, b, hb, rfl⟩ := hp
  exact ⟨ha, hb⟩

theorem lsum_flatMap {α β : Type*} [AddCommMonoid β] (L : List α) (f : α → List β) :
    (L.flatMap f).sum = (L.map (fun a => (f a).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_pairsOf {α β : Type*} [AddCommMonoid β] (L : List α) (h : α × α → β) :
    ((pairsOf L).map h).sum = (L.map (fun a => (L.map (fun b => h (a, b))).sum)).sum := by
  unfold pairsOf
  rw [List.map_flatMap, lsum_flatMap]
  simp [List.map_map, Function.comp_def]

theorem sum_pairsOf_mul {α : Type*} (L : List α) (f g : α → ℂ) :
    ((pairsOf L).map (fun p => f p.1 * g p.2)).sum = (L.map f).sum * (L.map g).sum := by
  rw [sum_pairsOf, ← List.sum_map_mul_right]
  congr 1
  apply List.map_congr_left
  intro a _
  dsimp only
  rw [List.sum_map_mul_left]

theorem star_list_sum {α : Type*} (L : List α) (f : α → ℂ) :
    star (L.map f).sum = (L.map (fun a => star (f a))).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem norm_mul_lt_one {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) : ‖z * w‖ < 1 := by
  rw [norm_mul]
  calc ‖z‖ * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hz.le (norm_nonneg _)
    _ < 1 := by rw [one_mul]; exact hw

noncomputable def pairVal (p : (ℂ × ℂ) × (ℂ × ℂ)) : ℂ :=
  -(p.1.2 * p.2.2) / 2 * Complex.log (1 - p.1.1 * p.2.1) +
    -(p.1.2 * star p.2.2) / 2 * Complex.log (1 - p.1.1 * star p.2.1)

theorem tail_sq_hasSum (l : List (ℂ × ℂ)) (hl : ∀ zr ∈ l, ‖zr.1‖ < 1) :
    HasSum (fun k : ℕ => ((l.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re) ^ 2 /
        ((k + 1 : ℕ) : ℝ)) ((pairsOf l).map pairVal).sum.re := by
  set F : (ℂ × ℂ) × (ℂ × ℂ) → ℕ → ℂ := fun p k =>
    (p.1.2 * p.2.2 * (p.1.1 * p.2.1) ^ (k + 1) +
      p.1.2 * star p.2.2 * (p.1.1 * star p.2.1) ^ (k + 1)) * (1 / (2 * ((k + 1 : ℕ) : ℂ)))
  have hpair : ∀ p ∈ pairsOf l, HasSum (F p) (pairVal p) := by
    intro p hp
    obtain ⟨ha, hb⟩ := mem_pairsOf hp
    have h1 := Complex.hasSum_taylorSeries_neg_log' (norm_mul_lt_one (hl _ ha) (hl _ hb))
    have h2 := Complex.hasSum_taylorSeries_neg_log'
      (norm_mul_lt_one (hl _ ha) (by rw [norm_star]; exact hl _ hb))
    have := ((h1.mul_left (p.1.2 * p.2.2)).add (h2.mul_left (p.1.2 * star p.2.2))).div_const 2
    convert this using 1
    · funext k; simp only [F]; push_cast; field_simp
    · unfold pairVal; ring
  have hs := hasSum_list_sum _ _ _ hpair
  have hre := Complex.reCLM.hasSum hs
  simp only [Complex.reCLM_apply] at hre
  convert hre using 1
  funext k
  set S : ℂ := (l.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum with hS
  have hstar : star S = (l.map (fun zr : ℂ × ℂ => star zr.2 * star zr.1 ^ (k + 1))).sum := by
    rw [hS, star_list_sum]
    congr 1
    apply List.map_congr_left
    intro zr _
    simp [star_pow]
  set c : ℂ := 1 / (2 * ((k + 1 : ℕ) : ℂ)) with hc
  have e1 : (pairsOf l).map (fun p => F p k) = (pairsOf l).map (fun p =>
      ((p.1.2 * p.1.1 ^ (k + 1)) * (p.2.2 * p.2.1 ^ (k + 1)) +
        (p.1.2 * p.1.1 ^ (k + 1)) * (star p.2.2 * star p.2.1 ^ (k + 1))) * c) := by
    apply List.map_congr_left
    intro p _
    simp only [F, hc]
    rw [mul_pow, mul_pow]
    ring
  have hsum : ((pairsOf l).map (fun p => F p k)).sum = (S * S + S * star S) * c := by
    have m1 := sum_pairsOf_mul l (fun a => a.2 * a.1 ^ (k + 1)) (fun b => b.2 * b.1 ^ (k + 1))
    have m2 := sum_pairsOf_mul l (fun a => a.2 * a.1 ^ (k + 1))
      (fun b => star b.2 * star b.1 ^ (k + 1))
    simp only at m1 m2
    rw [e1, List.sum_map_mul_right, List.sum_map_add, m1, m2, ← hS, ← hstar]
  rw [hsum]
  have hk : (1 / (2 * ((k + 1 : ℕ) : ℂ))) = (((1 / (2 * ((k + 1 : ℕ) : ℝ))) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hc, hk, Complex.re_mul_ofReal]
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.star_def]
  field_simp
  ring

theorem barrierFiniteCoeff_succ (cs : List ℤ) (k : ℕ) :
    barrierFiniteCoeff cs (k + 1) = ((cs.getD k 0 : ℚ) / 100000000 : ℚ) := by
  unfold barrierFiniteCoeff
  simp

theorem trialSeq_normSq {cs : List ℤ} {tail : List TailQ} (h : tailsInDisk tail = true) :
    barrierTrialNormSq (trialSeq cs tail) =
      (finNormQ cs tail : ℝ) + ((pairsOf (tail.map TailQ.toC)).map pairVal).sum.re := by
  have hl := tailsInDisk_spec h
  have hB := tail_sq_hasSum _ hl
  have hA : HasSum (fun k : ℕ =>
      (barrierFiniteCoeff cs (k + 1) ^ 2 + 2 * barrierFiniteCoeff cs (k + 1) *
        ((tail.map TailQ.toC).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re) /
          ((k + 1 : ℕ) : ℝ)) (finNormQ cs tail : ℝ) := by
    have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
      (s := Finset.range cs.length)
      (f := fun k : ℕ => (barrierFiniteCoeff cs (k + 1) ^ 2 + 2 * barrierFiniteCoeff cs (k + 1) *
        ((tail.map TailQ.toC).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re) /
          ((k + 1 : ℕ) : ℝ)) (by
        intro k hk
        rw [barrierFiniteCoeff_eq_zero (by simp at hk; omega)]
        simp)
    convert this using 1
    unfold finNormQ
    rw [Rat.cast_list_sum, List.map_map, list_range_map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Function.comp_apply]
    rw [barrierFiniteCoeff_succ, ← tailValQ_spec]
    push_cast
    ring
  have hsum := hA.add hB
  unfold barrierTrialNormSq
  rw [← hsum.tsum_eq]
  congr 1
  funext k
  unfold trialSeq barrierTrial
  simp only [Nat.add_one_ne_zero, if_false]
  ring

/-! ### Evaluation of the pair terms -/

theorem pw1 (a b : TailQ) :
    barrierComplex (-((cmulQ (a.rr, a.ri) (b.rr, b.ri)).1 / 2))
      (-((cmulQ (a.rr, a.ri) (b.rr, b.ri)).2 / 2)) = -((TailQ.toC a).2 * (TailQ.toC b).2) / 2 := by
  apply Complex.ext <;> simp [TailQ.toC, barrierComplex, cmulQ, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem pw2 (a b : TailQ) :
    barrierComplex (-((cmulQ (a.rr, a.ri) (b.rr, -b.ri)).1 / 2))
      (-((cmulQ (a.rr, a.ri) (b.rr, -b.ri)).2 / 2)) =
      -((TailQ.toC a).2 * star (TailQ.toC b).2) / 2 := by
  apply Complex.ext <;> simp [TailQ.toC, barrierComplex, cmulQ, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem pa1 (a b : TailQ) :
    barrierComplex (1 - (cmulQ (a.zr, a.zi) (b.zr, b.zi)).1) (-(cmulQ (a.zr, a.zi) (b.zr, b.zi)).2) =
      1 - (TailQ.toC a).1 * (TailQ.toC b).1 := by
  apply Complex.ext <;> simp [TailQ.toC, barrierComplex, cmulQ, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem pa2 (a b : TailQ) :
    barrierComplex (1 - (cmulQ (a.zr, a.zi) (b.zr, -b.zi)).1)
      (-(cmulQ (a.zr, a.zi) (b.zr, -b.zi)).2) = 1 - (TailQ.toC a).1 * star (TailQ.toC b).1 := by
  apply Complex.ext <;> simp [TailQ.toC, barrierComplex, cmulQ, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem pairTerms_val (tail : List TailQ) :
    ((pairTerms tail).map LogTerm.val).sum = ((pairsOf (tail.map TailQ.toC)).map pairVal).sum.re := by
  rw [re_list_sum_map, sum_pairsOf, List.map_map]
  unfold pairTerms
  rw [List.map_flatMap, lsum_flatMap]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [List.map_flatMap, lsum_flatMap]
  simp only [Function.comp_apply, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, pairVal, Complex.add_re, LogTerm.val]
  rw [pw1, pw2, pa1, pa2]

theorem normApprox_spec {cs : List ℤ} {tail : List TailQ} (h : tailsInDisk tail = true)
    {v e : ℚ} (hn : normApprox cs tail = some (v, e)) :
    barrierTrialNormSq (trialSeq cs tail) ≤ v + e := by
  unfold normApprox at hn
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hn
  obtain ⟨⟨v', e'⟩, h1, rfl, rfl⟩ := hn
  have := sumLogs_spec h1
  rw [trialSeq_normSq h, ← pairTerms_val]
  push_cast
  linarith [(abs_le.mp this).2]

end CatalanMeasure.Cert

namespace CatalanMeasure.Cert

def normOK (cs : List ℤ) (tail : List TailQ) (B : ℚ) : Bool :=
  tailsInDisk tail &&
    match normApprox cs tail with
    | some ve => decide (ve.1 + ve.2 ≤ B)
    | none => false

theorem normOK_spec {cs : List ℤ} {tail : List TailQ} {B : ℚ} (h : normOK cs tail B = true) :
    barrierTrialNormSq (trialSeq cs tail) ≤ B := by
  unfold normOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hd, h⟩ := h
  split at h
  · rename_i ve hve
    simp only [decide_eq_true_eq] at h
    have := normApprox_spec hd (v := ve.1) (e := ve.2) (by rw [hve])
    have hB : ((ve.1 + ve.2 : ℚ) : ℝ) ≤ B := by exact_mod_cast h
    push_cast at hB
    linarith
  · simp at h

end CatalanMeasure.Cert
