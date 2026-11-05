module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Computable polynomials for kernel-checked certificates

Polynomials with rational coefficients are represented as coefficient lists, constant term
first, so that the Lean kernel can compute with them (`decide +kernel`).  We prove once and
for all that the list operations are compatible with evaluation in `ℝ`, and we give two
certificates:

* `lpNoRootCheck p a b`: after the substitution `x = a + (b - a) / (1 + y)`, all coefficients
  of `(1 + y)^d p(x)` have the same strict sign; then `p` has no root in `(a, b)`
  (the zero-variation case of Descartes's rule, proved directly);
* `lpRatioBound A Q l w`: an upper bound for `|A t / Q t|` on `[l, l + w]`, from the Taylor
  coefficients of `A` and `Q` at `l`.
-/

open Set

namespace CatalanMeasure.Cert

/-- Horner evaluation of a coefficient list (constant term first) in `ℝ`. -/
def lpEval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: p, x => (c : ℝ) + x * lpEval p x

@[simp] theorem lpEval_nil (x : ℝ) : lpEval [] x = 0 := rfl
@[simp] theorem lpEval_cons (c : ℚ) (p : List ℚ) (x : ℝ) :
    lpEval (c :: p) x = (c : ℝ) + x * lpEval p x := rfl

def lpAdd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: lpAdd p q

@[simp] theorem lpEval_add (p q : List ℚ) (x : ℝ) :
    lpEval (lpAdd p q) x = lpEval p x + lpEval q x := by
  induction p generalizing q with
  | nil => simp [lpAdd]
  | cons a p ih =>
    cases q with
    | nil => simp [lpAdd]
    | cons b q => simp [lpAdd, ih]; ring

def lpSmul (c : ℚ) (p : List ℚ) : List ℚ := p.map (c * ·)

@[simp] theorem lpEval_smul (c : ℚ) (p : List ℚ) (x : ℝ) :
    lpEval (lpSmul c p) x = c * lpEval p x := by
  induction p with
  | nil => simp [lpSmul]
  | cons a p ih =>
    simp only [lpSmul, List.map_cons, lpEval_cons] at ih ⊢
    rw [ih]; push_cast; ring

def lpMul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => lpAdd (lpSmul a q) (0 :: lpMul p q)

@[simp] theorem lpEval_mul (p q : List ℚ) (x : ℝ) :
    lpEval (lpMul p q) x = lpEval p x * lpEval q x := by
  induction p with
  | nil => simp [lpMul]
  | cons a p ih => simp [lpMul, ih]; ring

/-- `p (a + h X)`. -/
def lpCompAff (a h : ℚ) : List ℚ → List ℚ
  | [] => []
  | c :: p => lpAdd [c] (lpMul [a, h] (lpCompAff a h p))

@[simp] theorem lpEval_compAff (a h : ℚ) (p : List ℚ) (u : ℝ) :
    lpEval (lpCompAff a h p) u = lpEval p (a + h * u) := by
  induction p with
  | nil => simp [lpCompAff]
  | cons c p ih =>
    simp only [lpCompAff, lpEval_add, lpEval_mul, lpEval_cons, lpEval_nil, ih]
    ring

theorem lpEval_append_single (p : List ℚ) (c : ℚ) (z : ℝ) :
    lpEval (p ++ [c]) z = lpEval p z + c * z ^ p.length := by
  induction p with
  | nil => simp
  | cons a p ih => simp [ih]; ring

theorem lpEval_reverse (p : List ℚ) (z : ℝ) (hz : z ≠ 0) :
    z * lpEval p.reverse z = z ^ p.length * lpEval p z⁻¹ := by
  induction p with
  | nil => simp
  | cons c q ih =>
    rw [List.reverse_cons, lpEval_append_single, List.length_reverse, List.length_cons,
      lpEval_cons, mul_add, ih]
    field_simp
    ring

/-! ### Sign certificates -/

theorem lpEval_nonneg {p : List ℚ} (h : p.all (fun c => decide (0 ≤ c)) = true) {y : ℝ}
    (hy : 0 ≤ y) : 0 ≤ lpEval p y := by
  induction p with
  | nil => simp
  | cons c p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have hc : (0 : ℝ) ≤ c := by exact_mod_cast h.1
    have := ih h.2
    simp only [lpEval_cons]
    positivity

theorem lpEval_pos {p : List ℚ} (h : p.all (fun c => decide (0 ≤ c)) = true)
    (h' : p.any (fun c => decide (0 < c)) = true) {y : ℝ} (hy : 0 < y) :
    0 < lpEval p y := by
  induction p with
  | nil => simp at h'
  | cons c p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.any_cons, Bool.or_eq_true, decide_eq_true_eq] at h'
    have hc : (0 : ℝ) ≤ c := by exact_mod_cast h.1
    have hq := lpEval_nonneg h.2 hy.le
    simp only [lpEval_cons]
    rcases h' with h' | h'
    · have : (0 : ℝ) < c := by exact_mod_cast h'
      positivity
    · have := ih h.2 h'
      positivity

def lpNeg (p : List ℚ) : List ℚ := lpSmul (-1) p

/-- The polynomial `(1 + y)^d p(a + (b - a) / (1 + y))`, `d + 1 = p.length`. -/
def lpMobius (p : List ℚ) (a b : ℚ) : List ℚ :=
  lpCompAff 1 1 (lpCompAff a (b - a) p).reverse

def lpSignCheck (T : List ℚ) : Bool :=
  (T.all (fun c => decide (0 ≤ c)) && T.any (fun c => decide (0 < c))) ||
    (T.all (fun c => decide (c ≤ 0)) && T.any (fun c => decide (c < 0)))

/-- No root of `p` in `(a, b)`: a zero-sign-variation certificate. -/
def lpNoRootCheck (p : List ℚ) (a b : ℚ) : Bool :=
  decide (a < b) && lpSignCheck (lpMobius p a b)

theorem lpEval_ne_zero_of_signCheck {T : List ℚ} (h : lpSignCheck T = true) {y : ℝ}
    (hy : 0 < y) : lpEval T y ≠ 0 := by
  unfold lpSignCheck at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (lpEval_pos h1 h2 hy).ne'
  · have e : lpEval T y = -lpEval (lpNeg T) y := by simp [lpNeg]
    have h1' : (lpNeg T).all (fun c => decide (0 ≤ c)) = true := by
      simp only [lpNeg, lpSmul, List.all_map, List.all_eq_true, Function.comp_apply,
        decide_eq_true_eq] at h1 ⊢
      intro c hc; linarith [h1 c hc]
    have h2' : (lpNeg T).any (fun c => decide (0 < c)) = true := by
      simp only [lpNeg, lpSmul, List.any_map, List.any_eq_true, Function.comp_apply,
        decide_eq_true_eq] at h2 ⊢
      obtain ⟨c, hc, hc'⟩ := h2
      exact ⟨c, hc, by linarith⟩
    rw [e]
    exact neg_ne_zero.mpr (lpEval_pos h1' h2' hy).ne'

theorem lpEval_ne_zero_of_noRootCheck {p : List ℚ} {a b : ℚ}
    (h : lpNoRootCheck p a b = true) {x : ℝ} (hx : x ∈ Ioo (a : ℝ) b) :
    lpEval p x ≠ 0 := by
  unfold lpNoRootCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hab, hs⟩ := h
  have hab' : (0 : ℝ) < (b : ℝ) - a := by
    have : (a : ℝ) < b := by exact_mod_cast hab
    linarith
  set u : ℝ := (x - a) / ((b : ℝ) - a) with hu
  have hu0 : 0 < u := div_pos (by linarith [hx.1]) hab'
  have hu1 : u < 1 := (div_lt_one hab').mpr (by linarith [hx.2])
  set y : ℝ := u⁻¹ - 1 with hy
  have hy0 : 0 < y := by
    have : 1 < u⁻¹ := one_lt_inv_iff₀.mpr ⟨hu0, hu1⟩
    linarith
  have hT := lpEval_ne_zero_of_signCheck hs hy0
  unfold lpMobius at hT
  rw [lpEval_compAff] at hT
  have hz : ((1 : ℚ) : ℝ) + ((1 : ℚ) : ℝ) * y = u⁻¹ := by push_cast; rw [hy]; ring
  rw [hz] at hT
  have hrev := lpEval_reverse (lpCompAff a (b - a) p) u⁻¹ (inv_ne_zero hu0.ne')
  rw [inv_inv, lpEval_compAff] at hrev
  have hx' : (a : ℝ) + ((b - a : ℚ) : ℝ) * u = x := by
    rw [hu]; push_cast; field_simp; ring
  rw [hx'] at hrev
  intro hp
  rw [hp, mul_zero] at hrev
  exact hT ((mul_eq_zero.mp hrev).resolve_left (inv_ne_zero hu0.ne'))

/-! ### Ratio bounds on short intervals -/

/-- `|c|`, written so that the kernel reduces it. -/
def qabs (c : ℚ) : ℚ := if c < 0 then -c else c

theorem qabs_eq (c : ℚ) : qabs c = |c| := by
  unfold qabs; split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (not_lt.mp h)).symm

def lpAbsSum (p : List ℚ) : ℚ := (p.map qabs).sum

theorem lpAbsSum_cons (c : ℚ) (p : List ℚ) : lpAbsSum (c :: p) = |c| + lpAbsSum p := by
  simp [lpAbsSum, qabs_eq]

theorem lpAbsSum_nonneg (p : List ℚ) : 0 ≤ lpAbsSum p := by
  induction p with
  | nil => simp [lpAbsSum]
  | cons c p ih => rw [lpAbsSum_cons]; positivity

theorem abs_lpEval_le {p : List ℚ} {u : ℝ} (hu : |u| ≤ 1) :
    |lpEval p u| ≤ (lpAbsSum p : ℝ) := by
  induction p with
  | nil => simp [lpAbsSum]
  | cons c p ih =>
    rw [lpEval_cons, lpAbsSum_cons]
    push_cast
    calc |(c : ℝ) + u * lpEval p u| ≤ |(c : ℝ)| + |u| * |lpEval p u| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(c : ℝ)| + 1 * (lpAbsSum p : ℝ) := by
          gcongr
      _ = _ := by rw [one_mul]

theorem abs_lpEval_ge {c : ℚ} {p : List ℚ} {u : ℝ} (hu : |u| ≤ 1) :
    (|c| : ℝ) - (lpAbsSum p : ℝ) ≤ |lpEval (c :: p) u| := by
  rw [lpEval_cons]
  have h1 := abs_lpEval_le (p := p) hu
  have h2 : |u * lpEval p u| ≤ (lpAbsSum p : ℝ) := by
    rw [abs_mul]
    calc |u| * |lpEval p u| ≤ 1 * (lpAbsSum p : ℝ) :=
          mul_le_mul hu h1 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h3 := abs_sub_abs_le_abs_sub (c : ℝ) (-(u * lpEval p u))
  rw [sub_neg_eq_add] at h3
  have h4 : |(-(u * lpEval p u))| = |u * lpEval p u| := abs_neg _
  rw [h4] at h3
  linarith

/-- An upper bound for `|A t / Q t|` on `[l, l + w]`, or `none`. -/
def lpRatioBound (A Q : List ℚ) (l w : ℚ) : Option ℚ :=
  match lpCompAff l w Q with
  | [] => none
  | c :: q =>
    if 0 < qabs c - lpAbsSum q then some (lpAbsSum (lpCompAff l w A) / (qabs c - lpAbsSum q))
    else none

theorem lpRatioBound_spec {A Q : List ℚ} {l w B : ℚ} (hw : 0 < w)
    (h : lpRatioBound A Q l w = some B) {t : ℝ} (ht : t ∈ Icc (l : ℝ) (l + w)) :
    lpEval Q t ≠ 0 ∧ |lpEval A t / lpEval Q t| ≤ B := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  set u : ℝ := (t - l) / w with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith [ht.1]) hw'.le
  have hu1 : u ≤ 1 := (div_le_one hw').mpr (by linarith [ht.2])
  have hua : |u| ≤ 1 := abs_le.mpr ⟨by linarith, hu1⟩
  have ht' : (l : ℝ) + (w : ℝ) * u = t := by rw [hu]; field_simp; ring
  have hA : lpEval A t = lpEval (lpCompAff l w A) u := by rw [lpEval_compAff, ht']
  have hQ : lpEval Q t = lpEval (lpCompAff l w Q) u := by rw [lpEval_compAff, ht']
  unfold lpRatioBound at h
  split at h
  · simp at h
  · rename_i c q hcq
    split_ifs at h with hpos
    simp only [Option.some.injEq] at h
    subst h
    rw [qabs_eq] at hpos ⊢
    have hlow := abs_lpEval_ge (c := c) (p := q) hua
    rw [← hcq, ← hQ] at hlow
    have hpos' : (0 : ℝ) < (|c| : ℝ) - (lpAbsSum q : ℝ) := by
      have : ((|c| - lpAbsSum q : ℚ) : ℝ) > 0 := by exact_mod_cast hpos
      push_cast at this; exact this
    have hQ0 : 0 < |lpEval Q t| := lt_of_lt_of_le hpos' hlow
    refine ⟨abs_pos.mp hQ0, ?_⟩
    have hupp := abs_lpEval_le (p := lpCompAff l w A) hua
    rw [← hA] at hupp
    rw [abs_div]
    push_cast
    rw [div_le_div_iff₀ hQ0 hpos']
    calc |lpEval A t| * ((|c| : ℝ) - (lpAbsSum q : ℝ))
        ≤ (lpAbsSum (lpCompAff l w A) : ℝ) * ((|c| : ℝ) - (lpAbsSum q : ℝ)) :=
          mul_le_mul_of_nonneg_right hupp hpos'.le
      _ ≤ (lpAbsSum (lpCompAff l w A) : ℝ) * |lpEval Q t| :=
          mul_le_mul_of_nonneg_left hlow (by exact_mod_cast lpAbsSum_nonneg _)

end CatalanMeasure.Cert
