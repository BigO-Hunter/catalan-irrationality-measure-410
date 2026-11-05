module

public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierComplexOctantRange
public import Submission.CatalanMeasure.Cert.ListPoly

@[expose] public section

/-!
# Kernel-computable approximations of `Re ((c + d i) log z)`

OpenAI's lemma `barrierWeightedComplexLogRat_error` approximates `Re ((c + d i) log z)` to
`10⁻¹²` for rational `c, d` and a rational complex `z`, given an exponent `m`, a mantissa `y`
and an octant rotation `k` with explicit side conditions.  Here the hints are computed from
`z` by a function the kernel can evaluate, and the side conditions are checked by the same
function, so that a single `decide +kernel` certifies a whole sum of such approximations.
-/

open OAI.InternalCatalan

namespace CatalanMeasure.Cert

/-- Rotation by `(1 - i)^n`. -/
def rotCW : ℕ → ℚ × ℚ → ℚ × ℚ
  | 0, p => p
  | n + 1, p => rotCW n (p.1 + p.2, p.2 - p.1)

/-- Rotation by `(1 + i)^n`. -/
def rotCCW : ℕ → ℚ × ℚ → ℚ × ℚ
  | 0, p => p
  | n + 1, p => rotCCW n (p.1 - p.2, p.1 + p.2)

def octRot (k : ℤ) (p : ℚ × ℚ) : ℚ × ℚ :=
  if 0 ≤ k then rotCW k.toNat p else rotCCW (-k).toNat p

theorem rotCW_spec (n : ℕ) (p : ℚ × ℚ) :
    (1 - Complex.I) ^ n * (⟨(p.1 : ℝ), (p.2 : ℝ)⟩ : ℂ) =
      ⟨((rotCW n p).1 : ℝ), ((rotCW n p).2 : ℝ)⟩ := by
  induction n generalizing p with
  | zero => simp [rotCW]
  | succ n ih =>
    rw [pow_succ, mul_assoc]
    have h : (1 - Complex.I) * (⟨(p.1 : ℝ), (p.2 : ℝ)⟩ : ℂ) =
        ⟨((p.1 + p.2 : ℚ) : ℝ), ((p.2 - p.1 : ℚ) : ℝ)⟩ := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
    rw [h]
    exact ih (p.1 + p.2, p.2 - p.1)

theorem rotCCW_spec (n : ℕ) (p : ℚ × ℚ) :
    (1 + Complex.I) ^ n * (⟨(p.1 : ℝ), (p.2 : ℝ)⟩ : ℂ) =
      ⟨((rotCCW n p).1 : ℝ), ((rotCCW n p).2 : ℝ)⟩ := by
  induction n generalizing p with
  | zero => simp [rotCCW]
  | succ n ih =>
    rw [pow_succ, mul_assoc]
    have h : (1 + Complex.I) * (⟨(p.1 : ℝ), (p.2 : ℝ)⟩ : ℂ) =
        ⟨((p.1 - p.2 : ℚ) : ℝ), ((p.1 + p.2 : ℚ) : ℝ)⟩ := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
    rw [h]
    exact ih (p.1 - p.2, p.1 + p.2)

theorem octRot_spec (k : ℤ) (p : ℚ × ℚ) :
    barrierOctantRotate k ⟨(p.1 : ℝ), (p.2 : ℝ)⟩ =
      ⟨((octRot k p).1 : ℝ), ((octRot k p).2 : ℝ)⟩ := by
  unfold barrierOctantRotate barrierOctantMultiplier octRot
  split_ifs with hk
  · exact rotCW_spec _ _
  · exact rotCCW_spec _ _

/-- Candidate octants, in order of preference. -/
def octCandidates : List ℤ := [0, 1, -1, 2, -2, 3, -3, 4, -4]

def octOK (k : ℤ) (p : ℚ × ℚ) : Bool :=
  let q := octRot k p
  decide (0 < q.1) && decide (2 * qabs q.2 ≤ q.1) && (k != 4 || decide (q.2 ≤ 0)) &&
    (k != -4 || decide (0 < q.2))

def findOct (p : ℚ × ℚ) : Option ℤ := octCandidates.find? (fun k => octOK k p)

/-- An exponent `m` with `q / 2^m ∈ [1, 2]`, for `q > 0`. -/
def findExp (q : ℚ) : Option ℤ :=
  let m0 : ℤ := (q.num.natAbs.log2 : ℤ) - (q.den.log2 : ℤ)
  [m0, m0 - 1, m0 + 1].find? (fun m => decide (1 ≤ q / 2 ^ m) && decide (q / 2 ^ m ≤ 2))

/-- `Re ((c + d i) log (a + b i))` to within `10⁻¹²`, when the weights satisfy `|c|, |d| ≤ 1`. -/
def cLog1 (c d a b : ℚ) : Option ℚ :=
  match findExp (a * a + b * b), findOct (a, b) with
  | some m, some k =>
    if qabs c ≤ 1 ∧ qabs d ≤ 1 ∧ qabs m ≤ 100 then
      some (barrierWeightedComplexLogRat c d m k ((a * a + b * b) / 2 ^ m)
        ((octRot k (a, b)).2 / (octRot k (a, b)).1))
    else none
  | _, _ => none

theorem cLog1_spec {c d a b q : ℚ} (h : cLog1 c d a b = some q) :
    |(barrierComplex c d * Complex.log ⟨(a : ℝ), (b : ℝ)⟩).re - (q : ℝ)| <
      1 / 1000000000000 := by
  unfold cLog1 at h
  split at h
  · rename_i m k hm hk
    split_ifs at h with hw
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hc, hd, hmm⟩ := hw
    rw [qabs_eq] at hc hd hmm
    -- the exponent
    unfold findExp at hm
    have hm' := List.find?_some hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm'
    obtain ⟨hy1, hy2⟩ := hm'
    -- the octant
    unfold findOct at hk
    have hk' := List.find?_some hk
    have hkmem := List.mem_of_find?_eq_some hk
    unfold octOK at hk'
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hk'
    obtain ⟨⟨⟨hr, hs⟩, h4⟩, hm4⟩ := hk'
    set r := (octRot k (a, b)).1
    set s := (octRot k (a, b)).2
    have hn2 : a * a + b * b = 2 ^ m * ((a * a + b * b) / 2 ^ m) := by
      have : (2 : ℚ) ^ m ≠ 0 := zpow_ne_zero _ (by norm_num)
      field_simp
    have hnorm : (⟨(a : ℝ), (b : ℝ)⟩ : ℂ).re ^ 2 + (⟨(a : ℝ), (b : ℝ)⟩ : ℂ).im ^ 2 =
        (2 : ℝ) ^ m * (((a * a + b * b) / 2 ^ m : ℚ) : ℝ) := by
      have := congrArg (fun t : ℚ => (t : ℝ)) hn2
      simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_zpow, Rat.cast_ofNat] at this
      simp only [pow_two]
      rw [this]
    have hkabs : |k| ≤ 4 := by
      simp only [octCandidates, List.mem_cons, List.not_mem_nil, or_false] at hkmem
      rcases hkmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hrot := octRot_spec k (a, b)
    have herr := barrierWeightedComplexLogRat_error c d ⟨(a : ℝ), (b : ℝ)⟩ m k
      ((a * a + b * b) / 2 ^ m) r s
      (by exact_mod_cast hc) (by exact_mod_cast hd)
      (by have : ((|m| : ℤ) : ℚ) ≤ 100 := by exact_mod_cast hmm
          rw [← Int.cast_abs]; exact_mod_cast this)
      hnorm
      ⟨by exact_mod_cast hy1, by exact_mod_cast hy2⟩
      hrot (by exact_mod_cast hr)
      (by have : 2 * |s| ≤ r := by rw [← qabs_eq]; exact hs
          have h' : ((2 * |s| : ℚ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast this
          push_cast at h'
          linarith)
      hkabs
      (by intro hk4; rcases h4 with h4 | h4
          · exact absurd hk4 h4
          · exact_mod_cast h4)
      (by intro hk4; rcases hm4 with h4 | h4
          · exact absurd hk4 h4
          · exact_mod_cast h4)
    simpa using herr
  · simp at h

/-- The weight split into `n` pieces of size at most one. -/
def wPieces (c d : ℚ) : ℕ := max 1 (max (qabs c).ceil.toNat (qabs d).ceil.toNat)

/-- `Re ((c + d i) log (a + b i))` to within `n · 10⁻¹²`, `n = wPieces c d`. -/
def cLog (c d a b : ℚ) : Option ℚ :=
  let n := wPieces c d
  (cLog1 (c / n) (d / n) a b).map (fun q => n * q)

theorem cLog_spec {c d a b q : ℚ} (h : cLog c d a b = some q) :
    |(barrierComplex c d * Complex.log ⟨(a : ℝ), (b : ℝ)⟩).re - (q : ℝ)| ≤
      (wPieces c d : ℝ) / 1000000000000 := by
  unfold cLog at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨q1, h1, rfl⟩ := h
  have hs := cLog1_spec h1
  set n := wPieces c d
  have hn : (0 : ℝ) < n := by
    have : 1 ≤ n := le_max_left _ _
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hsplit : (barrierComplex c d * Complex.log ⟨(a : ℝ), (b : ℝ)⟩).re =
      n * (barrierComplex (c / n) (d / n) * Complex.log ⟨(a : ℝ), (b : ℝ)⟩).re := by
    simp only [barrierComplex, Complex.mul_re]
    push_cast
    field_simp
  rw [hsplit]
  push_cast
  rw [← mul_sub, abs_mul, abs_of_pos hn]
  calc (n : ℝ) * |_| ≤ n * (1 / 1000000000000) := mul_le_mul_of_nonneg_left hs.le hn.le
    _ = _ := by ring

end CatalanMeasure.Cert
