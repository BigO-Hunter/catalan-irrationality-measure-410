module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Data.Rat.Floor
public import Submission.CatalanMeasure.Cert.ListPoly
public import Submission.CatalanMeasure.Cert.FieldDeriv
public import Submission.CatalanMeasure.Cert.ShiftedFields
@[expose] public section
/-! # Taylor-cell tower: derivative towers, exact pole towers, `ptZ`/`ftZ`, row poles.

Generalised from the pilot (`Pilot7.BridgeLib`, `Pilot729.{Tower,Val,RowLink}`): the polynomial part of the
derivative is `Z(x) / 2^40` (not `/10^8`), and there is no bound on `Z.length`. -/
namespace CatalanMeasure.CellCert
open Set Nat CatalanMeasure.Cert OAI.InternalCatalan

/-! ### Taylor theorem with remainder for a derivative tower (derivatives on the open interval only) -/
theorem tower_step_right' (ph ph' : ℝ → ℝ) (c H M : ℝ) (m : ℕ)
    (hc : ContinuousOn ph (Icc c (c + H)))
    (hd : ∀ x ∈ Ioo c (c + H), HasDerivAt ph (ph' x) x)
    (hb : ∀ x ∈ Ioo c (c + H), |ph' x| ≤ M * (x - c) ^ m / (m ! : ℝ))
    (h0 : ph c = 0) :
    ∀ x ∈ Icc c (c + H), |ph x| ≤ M * (x - c) ^ (m + 1) / ((m + 1)! : ℝ) := by
  intro x hx
  set B : ℝ → ℝ := fun y => M * (y - c) ^ (m + 1) / ((m + 1)! : ℝ) with hB
  have hBd : ∀ y, HasDerivAt B (M * (y - c) ^ m / (m ! : ℝ)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (y - c) ^ (m + 1)) (((m + 1 : ℕ) : ℝ) * (y - c) ^ m * 1) y :=
      ((hasDerivAt_id y).sub_const c).pow (m + 1)
    have h2 := (h1.const_mul M).div_const ((m + 1)! : ℝ)
    refine h2.congr_deriv ?_
    rw [Nat.factorial_succ]
    push_cast
    have : (m ! : ℝ) ≠ 0 := by positivity
    field_simp
  have hBc : B c = 0 := by simp [hB]
  have hx' : c ≤ x := hx.1
  have hmono : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      MonotoneOn (fun y => B y + s * ph y) (Icc c (c + H)) := by
    intro s hs
    have hdd : ∀ y ∈ Ioo c (c + H),
        HasDerivAt (fun y => B y + s * ph y) (M * (y - c) ^ m / (m ! : ℝ) + s * ph' y) y :=
      fun y hy => (hBd y).add ((hd y hy).const_mul s)
    refine monotoneOn_of_deriv_nonneg (convex_Icc c (c + H)) ?_ ?_ ?_
    · exact ((continuous_iff_continuousAt.mpr (fun y => (hBd y).continuousAt)).continuousOn).add (continuousOn_const.mul hc)
    · intro y hy
      rw [interior_Icc] at hy
      exact (hdd y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hdd y hy).deriv]
      have := hb y hy
      rcases hs with rfl | rfl
      · have := (abs_le.mp this).1
        linarith
      · have := (abs_le.mp this).2
        linarith
  have hc0 : c ∈ Icc c (c + H) := ⟨le_refl c, by linarith [hx.1, hx.2]⟩
  have m1 := hmono 1 (Or.inl rfl) hc0 hx hx'
  have m2 := hmono (-1) (Or.inr rfl) hc0 hx hx'
  simp only [hBc, h0, mul_zero, add_zero] at m1 m2
  rw [abs_le]
  constructor <;> simp only [hB] at m1 m2 ⊢ <;> linarith

theorem tower_step' (ph ph' : ℝ → ℝ) (c H M : ℝ) (m : ℕ)
    (hc : ContinuousOn ph (Icc (c - H) (c + H)))
    (hd : ∀ x ∈ Ioo (c - H) (c + H), HasDerivAt ph (ph' x) x)
    (hb : ∀ x ∈ Ioo (c - H) (c + H), |ph' x| ≤ M * |x - c| ^ m / (m ! : ℝ))
    (h0 : ph c = 0) :
    ∀ x ∈ Icc (c - H) (c + H), |ph x| ≤ M * |x - c| ^ (m + 1) / ((m + 1)! : ℝ) := by
  intro x hx
  rcases le_total c x with h | h
  · have hH : c ≤ c + H := by linarith [hx.2]
    have := tower_step_right' ph ph' c H M m
      (hc.mono (Icc_subset_Icc (by linarith [hx.2]) le_rfl))
      (fun y hy => hd y ⟨by linarith [hy.1, hy.2], hy.2⟩)
      (fun y hy => by
        have := hb y ⟨by linarith [hy.1, hy.2], hy.2⟩
        rwa [abs_of_nonneg (sub_nonneg.mpr hy.1.le)] at this) h0 x ⟨h, hx.2⟩
    rwa [abs_of_nonneg (sub_nonneg.mpr h)]
  · have hH : c - H ≤ c := by linarith [hx.1]
    let ps : ℝ → ℝ := fun y => ph (2 * c - y)
    have hpsc : ContinuousOn ps (Icc c (c + H)) := by
      have h1 : ContinuousOn (fun y : ℝ => 2 * c - y) (Icc c (c + H)) :=
        (continuous_const.sub continuous_id).continuousOn
      refine hc.comp h1 (fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩)
    have hpsd : ∀ y ∈ Ioo c (c + H), HasDerivAt ps (-(ph' (2 * c - y))) y := by
      intro y hy
      have h1 : HasDerivAt (fun y : ℝ => 2 * c - y) (-1) y := by
        simpa using (hasDerivAt_id y).const_sub (2 * c)
      exact ((hd (2 * c - y) ⟨by linarith [hy.2], by linarith [hy.1]⟩).comp y h1).congr_deriv (by ring)
    have := tower_step_right' ps (fun y => -(ph' (2 * c - y))) c H M m hpsc hpsd
      (fun y hy => by
        have := hb (2 * c - y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
        have e : |2 * c - y - c| = y - c := by
          rw [show 2 * c - y - c = -(y - c) by ring, abs_neg]; exact abs_of_nonneg (sub_nonneg.mpr hy.1.le)
        rw [e] at this
        rwa [abs_neg])
      (by show ph (2 * c - c) = 0; rw [show 2 * c - c = c by ring]; exact h0) (2 * c - x) ⟨by linarith, by linarith [hx.1]⟩
    have e2 : |x - c| = 2 * c - x - c := by
      rw [abs_of_nonpos (sub_nonpos.mpr h)]; ring
    rw [e2]
    have e3 : ps (2 * c - x) = ph x := by
      show ph (2 * c - (2 * c - x)) = ph x
      rw [show 2 * c - (2 * c - x) = x by ring]
    rw [e3] at this
    exact this

theorem taylor_tower' (c H M : ℝ) :
    ∀ (m : ℕ) (f : ℕ → ℝ → ℝ),
    (∀ j ≤ m, ContinuousOn (f j) (Icc (c - H) (c + H))) →
    (∀ j < m, ∀ x ∈ Ioo (c - H) (c + H), HasDerivAt (f j) (f (j + 1) x) x) →
    (∀ x ∈ Icc (c - H) (c + H), |f m x| ≤ M) →
    ∀ x ∈ Icc (c - H) (c + H),
      |f 0 x - ∑ j ∈ Finset.range m, f j c * (x - c) ^ j / (j ! : ℝ)| ≤ M * |x - c| ^ m / (m ! : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro f _ _ hM x hx
    simpa using hM x hx
  | succ m ih =>
    intro f hcont hder hM x hx
    have ih' := ih (fun j => f (j + 1)) (fun j hj => hcont (j + 1) (by omega))
      (fun j hj y hy => hder (j + 1) (by omega) y hy)
      (by simpa using hM)
    set ph : ℝ → ℝ := fun y => f 0 y - ∑ j ∈ Finset.range (m + 1), f j c * (y - c) ^ j / (j ! : ℝ) with hph
    set ph' : ℝ → ℝ := fun y => f 1 y - ∑ j ∈ Finset.range m, f (j + 1) c * (y - c) ^ j / (j ! : ℝ) with hph'
    have hphc : ContinuousOn ph (Icc (c - H) (c + H)) := by
      refine (hcont 0 (by omega)).sub ?_
      refine continuousOn_finsetSum _ (fun j _ => ?_)
      exact ((continuousOn_const.mul ((continuous_id.sub continuous_const).pow j).continuousOn)).div_const _
    have hphd : ∀ y ∈ Ioo (c - H) (c + H), HasDerivAt ph (ph' y) y := by
      intro y hy
      have hs : HasDerivAt (fun y : ℝ => ∑ j ∈ Finset.range (m + 1), f j c * (y - c) ^ j / (j ! : ℝ))
          (∑ j ∈ Finset.range (m + 1), f j c * (((j : ℕ) : ℝ) * (y - c) ^ (j - 1) * 1) / (j ! : ℝ)) y := by
        apply HasDerivAt.fun_sum
        intro j _
        have h1 : HasDerivAt (fun y : ℝ => (y - c) ^ j) (((j : ℕ) : ℝ) * (y - c) ^ (j - 1) * 1) y :=
          ((hasDerivAt_id y).sub_const c).pow j
        exact (h1.const_mul (f j c)).div_const _
      have hs' : (∑ j ∈ Finset.range (m + 1), f j c * (((j : ℕ) : ℝ) * (y - c) ^ (j - 1) * 1) / (j ! : ℝ))
          = ∑ j ∈ Finset.range m, f (j + 1) c * (y - c) ^ j / (j ! : ℝ) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_mul, mul_zero, zero_div, add_zero, Nat.factorial_zero]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Nat.factorial_succ]
        push_cast
        have : (j ! : ℝ) ≠ 0 := by positivity
        have : ((j : ℝ) + 1) ≠ 0 := by positivity
        try simp only [Nat.add_sub_cancel]
        field_simp
      rw [hs'] at hs
      exact (hder 0 (by omega) y hy).sub hs
    have h0 : ph c = 0 := by
      simp only [hph]
      rw [Finset.sum_range_succ']
      have hz : ∀ j ∈ Finset.range m, f (j + 1) c * (c - c) ^ (j + 1) / (((j + 1)! : ℕ) : ℝ) = 0 :=
        fun j _ => by simp
      rw [Finset.sum_eq_zero hz]
      simp
    exact (tower_step' ph ph' c H M m hphc hphd (fun y hy => ih' y ⟨hy.1.le, hy.2.le⟩) h0) x hx


/-! ### BridgeLib: integer helpers, exact polynomial lists, pole towers -/
/-! ### integer helpers -/
def zabs (a : ℤ) : ℤ := if a < 0 then -a else a
def qabs' (a : ℚ) : ℚ := if a < 0 then -a else a
def qfloor (a : ℚ) : ℤ := a.num / (a.den : ℤ)
def qceil (a : ℚ) : ℤ := -((-a).num / (a.den : ℤ))
def cdiv (a b : ℤ) : ℤ := (a + (b - 1)) / b

theorem zabs_cast (a : ℤ) : ((zabs a : ℤ) : ℝ) = |(a : ℝ)| := by
  unfold zabs
  split_ifs with h
  · push_cast; rw [abs_of_neg (by exact_mod_cast h)]
  · push_cast; rw [abs_of_nonneg (by exact_mod_cast (not_lt.mp h))]

theorem qabs'_cast (a : ℚ) : ((qabs' a : ℚ) : ℝ) = |(a : ℝ)| := by
  unfold qabs'
  split_ifs with h
  · push_cast; rw [abs_of_neg (by exact_mod_cast h)]
  · push_cast; rw [abs_of_nonneg (by exact_mod_cast (not_lt.mp h))]

theorem qfloor_le (a : ℚ) : ((qfloor a : ℤ) : ℚ) ≤ a := by
  have : qfloor a = ⌊a⌋ := by rw [Rat.floor_def']; rfl
  rw [this]; exact Int.floor_le a

theorem lt_qfloor_add_one (a : ℚ) : a < ((qfloor a : ℤ) : ℚ) + 1 := by
  have : qfloor a = ⌊a⌋ := by rw [Rat.floor_def']; rfl
  rw [this]; exact Int.lt_floor_add_one a

theorem le_qceil (a : ℚ) : a ≤ ((qceil a : ℤ) : ℚ) := by
  have h := qfloor_le (-a)
  have e : qceil a = -(qfloor (-a)) := rfl
  rw [e]; push_cast; linarith

theorem qceil_lt_add_one (a : ℚ) : ((qceil a : ℤ) : ℚ) < a + 1 := by
  have h := lt_qfloor_add_one (-a)
  have e : qceil a = -(qfloor (-a)) := rfl
  rw [e]; push_cast; linarith

theorem cdiv_ge (a b : ℤ) (hb : 0 < b) : a ≤ b * cdiv a b := by
  unfold cdiv
  have h1 := Int.emod_add_mul_ediv (a + (b - 1)) b   -- (x % b) + b * (x / b) = x
  have h2 := Int.emod_lt_of_pos (a + (b - 1)) hb
  have h3 := Int.emod_nonneg (a + (b - 1)) hb.ne'
  nlinarith

theorem cdiv_cast_ge (a b : ℤ) (hb : 0 < b) : (a : ℝ) ≤ (b : ℝ) * (cdiv a b : ℤ) := by
  exact_mod_cast cdiv_ge a b hb

theorem zdiv_le (a b : ℤ) (hb : 0 < b) : b * (a / b) ≤ a := Int.mul_ediv_self_le hb.ne'
theorem lt_zdiv_add_one (a b : ℤ) (hb : 0 < b) : a < b * (a / b + 1) := by
  have h := Int.lt_ediv_add_one_mul_self a hb
  linarith

/-! ### list sums over `range` -/
theorem list_range_map_sum {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-! ### integer polynomial lists: derivative and homogeneous Horner -/
def zl (Z : List ℤ) : List ℚ := Z.map (fun z : ℤ => (z : ℚ))

def lderAux : ℕ → List ℤ → List ℤ
  | _, [] => []
  | k, a :: t => ((k : ℤ) * a) :: lderAux (k + 1) t

def lder (l : List ℤ) : List ℤ := (lderAux 0 l).tail

theorem lderAux_length (k : ℕ) (l : List ℤ) : (lderAux k l).length = l.length := by
  induction l generalizing k with
  | nil => rfl
  | cons a t ih => simp [lderAux, ih]

theorem lder_length (l : List ℤ) : (lder l).length = l.length - 1 := by
  unfold lder
  rw [List.length_tail, lderAux_length]

theorem lder_iter_length (n : ℕ) (l : List ℤ) : (lder^[n] l).length = l.length - n := by
  induction n generalizing l with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply, ih, lder_length]; omega

theorem lder_iter_nil (n : ℕ) (l : List ℤ) (h : l.length ≤ n) : lder^[n] l = [] := by
  have := lder_iter_length n l
  rw [Nat.sub_eq_zero_of_le h] at this
  exact List.length_eq_zero_iff.mp this

theorem lpEval_zl_lderAux_succ (u : List ℤ) (k : ℕ) (x : ℝ) :
    lpEval (zl (lderAux (k + 1) u)) x = lpEval (zl (lderAux k u)) x + lpEval (zl u) x := by
  induction u generalizing k with
  | nil => simp [zl, lderAux]
  | cons a u ih =>
    have := ih (k + 1)
    simp only [zl, lderAux, List.map_cons, lpEval_cons] at this ⊢
    push_cast at this ⊢
    rw [this]; ring

theorem lpEval_zl_lder_cons (a : ℤ) (t : List ℤ) (x : ℝ) :
    lpEval (zl (lder (a :: t))) x = lpEval (zl t) x + x * lpEval (zl (lder t)) x := by
  unfold lder
  simp only [lderAux, List.tail_cons]
  rw [lpEval_zl_lderAux_succ t 0 x]
  cases t with
  | nil => simp [zl, lderAux]
  | cons b u =>
    simp only [lderAux, List.tail_cons, zl, List.map_cons, lpEval_cons]
    push_cast
    ring

theorem hasDerivAt_lpEval_zl (l : List ℤ) (x : ℝ) :
    HasDerivAt (fun y => lpEval (zl l) y) (lpEval (zl (lder l)) x) x := by
  induction l with
  | nil => simpa [zl, lder, lderAux] using hasDerivAt_const x (0 : ℝ)
  | cons a t ih =>
    rw [lpEval_zl_lder_cons]
    have h1 := (hasDerivAt_id x).mul ih
    have h2 := h1.const_add (a : ℝ)
    simp only [zl, List.map_cons, lpEval_cons]
    simpa [zl, add_comm] using h2

/-- identity, but forces the kernel to normalise the value to a literal -/
def forceZ : ℤ → ℤ
  | Int.ofNat n => match n with | 0 => 0 | k + 1 => Int.ofNat (k + 1)
  | Int.negSucc n => match n with | 0 => -1 | k + 1 => Int.negSucc (k + 1)

@[simp] theorem forceZ_eq (a : ℤ) : forceZ a = a := by
  cases a with
  | ofNat n => cases n <;> rfl
  | negSucc n => cases n <;> rfl

/-- homogeneous Horner: with `tp = T^N`, `hv cc T tp l = Σ l_i cc^i T^(N-i)` -/
def hv (cc T : ℤ) : ℤ → List ℤ → ℤ
  | _, [] => 0
  | tp, a :: t => forceZ (a * tp + cc * hv cc T (forceZ (tp / T)) t)

theorem hv_spec (cc T : ℤ) (hT : 0 < T) (l : List ℤ) :
    ∀ N : ℕ, l.length ≤ N + 1 →
      ((hv cc T (T ^ N) l : ℤ) : ℝ) = (T : ℝ) ^ N * lpEval (zl l) ((cc : ℝ) / T) := by
  induction l with
  | nil => intro N _; simp [hv, zl]
  | cons a t ih =>
    intro N hN
    cases N with
    | zero =>
      have : t = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hN; omega)
      subst this
      simp [hv, zl]
    | succ N =>
      have hdiv : T ^ (N + 1) / T = T ^ N := by
        rw [pow_succ, Int.mul_ediv_cancel _ hT.ne']
      have := ih N (by simp at hN; omega)
      simp only [hv, forceZ_eq, hdiv]
      push_cast
      rw [this]
      simp only [zl, List.map_cons, lpEval_cons]
      have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
      push_cast
      field_simp
      ring

/-- values of all derivative levels -/
def polyVals (cc T tp : ℤ) : ℕ → List ℤ → List ℤ
  | 0, _ => []
  | n + 1, l => hv cc T tp l :: polyVals cc T tp n (lder l)

theorem polyVals_getD (cc T tp : ℤ) (n : ℕ) :
    ∀ (l : List ℤ) (j : ℕ), j < n → (polyVals cc T tp n l).getD j 0 = hv cc T tp (lder^[j] l) := by
  induction n with
  | zero => intro l j hj; omega
  | succ n ih =>
    intro l j hj
    cases j with
    | zero => simp [polyVals]
    | succ j =>
      simp only [polyVals, List.getD_cons_succ]
      rw [ih (lder l) j (by omega), Function.iterate_succ_apply]

/-! ### poles -/
structure PoleR where
  rr : ℚ
  ri : ℚ
  pr : ℚ
  pi : ℚ

def PoleR.rho (q : PoleR) : ℂ := ⟨q.rr, q.ri⟩
def PoleR.pc (q : PoleR) : ℂ := ⟨q.pr, q.pi⟩

def cmulQ (x y : ℚ × ℚ) : ℚ × ℚ := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def cpowQ (u : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => cmulQ (cpowQ u n) u
/-- 1/(c - p) -/
def uOf (q : PoleR) (c : ℚ) : ℚ × ℚ :=
  let a := c - q.pr
  let b := -q.pi
  (a / (a * a + b * b), -b / (a * a + b * b))
def poleVal (q : PoleR) (c : ℚ) (j : ℕ) : ℚ :=
  let w := cpowQ (uOf q c) (j + 1)
  ((-1 : ℚ) ^ j * ((j ! : ℕ) : ℚ)) * (q.rr * w.1 - q.ri * w.2)

/-- real tower of the pole `Re[ρ/(x-p)]` -/
noncomputable def qe (q : PoleR) (j : ℕ) (w : ℂ) : ℂ :=
  q.rho * ((-1 : ℂ) ^ j * ((j ! : ℕ) : ℂ)) * ((w - q.pc)⁻¹) ^ (j + 1)
noncomputable def qt (q : PoleR) (j : ℕ) (x : ℝ) : ℝ := (qe q j (x : ℂ)).re

theorem hasDerivAt_qe (q : PoleR) (j : ℕ) (w : ℂ) (hw : w ≠ q.pc) :
    HasDerivAt (qe q j) (qe q (j + 1) w) w := by
  have hne : w - q.pc ≠ 0 := sub_ne_zero.mpr hw
  have h1 : HasDerivAt (fun y : ℂ => y - q.pc) 1 w := (hasDerivAt_id w).sub_const _
  have h2 := h1.inv hne
  have h3 := h2.pow (j + 1)
  have h4 := h3.const_mul (q.rho * ((-1 : ℂ) ^ j * ((j ! : ℕ) : ℂ)))
  have e : (-1 / (w - q.pc) ^ 2 : ℂ) = -((w - q.pc)⁻¹) ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]; ring
  refine h4.congr_deriv ?_
  simp only [qe, Pi.inv_apply, Nat.add_sub_cancel, e, Nat.factorial_succ]
  push_cast
  ring

theorem hasDerivAt_qt (q : PoleR) (j : ℕ) (x : ℝ) (hx : (x : ℂ) ≠ q.pc) :
    HasDerivAt (qt q j) (qt q (j + 1) x) x :=
  (hasDerivAt_qe q j (x : ℂ) hx).real_of_complex

theorem uOf_spec (q : PoleR) (c : ℚ) :
    (((uOf q c).1 : ℝ) : ℂ) + (((uOf q c).2 : ℝ) : ℂ) * Complex.I = ((c : ℂ) - q.pc)⁻¹ := by
  have hz : ((c : ℂ) - q.pc) = ⟨(c : ℝ) - q.pr, -(q.pi : ℝ)⟩ := by
    apply Complex.ext <;> simp [PoleR.pc]
  rw [hz]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one, add_zero, Complex.inv_re,
      Complex.normSq_apply]
    unfold uOf
    push_cast
    ring
  · simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, zero_mul, zero_add, mul_one, add_zero, Complex.inv_im,
      Complex.normSq_apply]
    unfold uOf
    push_cast
    ring

theorem cpowQ_spec (q : PoleR) (c : ℚ) (n : ℕ) :
    (((cpowQ (uOf q c) n).1 : ℝ) : ℂ) + (((cpowQ (uOf q c) n).2 : ℝ) : ℂ) * Complex.I =
      (((c : ℂ) - q.pc)⁻¹) ^ n := by
  induction n with
  | zero => simp [cpowQ]
  | succ n ih =>
    rw [pow_succ, ← ih, ← uOf_spec q c]
    simp only [cpowQ, cmulQ]
    push_cast
    apply Complex.ext <;> simp <;> ring

theorem poleVal_spec (q : PoleR) (c : ℚ) (j : ℕ) :
    ((poleVal q c j : ℚ) : ℝ) = qt q j (c : ℝ) := by
  unfold poleVal qt qe
  have h := cpowQ_spec q c (j + 1)
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
    Complex.mul_im, zero_add] at hre him
  set w := cpowQ (uOf q c) (j + 1)
  have hcast : (((c : ℝ) : ℂ)) = (c : ℂ) := by simp
  have hcf : ((-1 : ℂ) ^ j * ((j ! : ℕ) : ℂ)) = ((((-1 : ℝ) ^ j * (j ! : ℝ) : ℝ)) : ℂ) := by
    push_cast; ring
  rw [hcast, ← h, hcf]
  have e : q.rho * ((((-1 : ℝ) ^ j * (j ! : ℝ) : ℝ)) : ℂ) *
      (((w.1 : ℝ) : ℂ) + ((w.2 : ℝ) : ℂ) * Complex.I) =
      ((((-1 : ℝ) ^ j * (j ! : ℝ) : ℝ)) : ℂ) *
      (q.rho * (((w.1 : ℝ) : ℂ) + ((w.2 : ℝ) : ℂ) * Complex.I)) := by ring
  rw [e, Complex.re_ofReal_mul, Complex.mul_re]
  simp only [PoleR.rho, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
  push_cast
  ring


/-! ### the field-derivative tower `ftZ`: `F' = Z(x)/2^40 + Σ_q Re[ρ_q/(x-p_q)]` -/
theorem hasDerivAt_listsum_qt (L : List PoleR) (j : ℕ) (x : ℝ) (hx : ∀ q ∈ L, (x : ℂ) ≠ q.pc) :
    HasDerivAt (fun y => (L.map (fun q => qt q j y)).sum) ((L.map (fun q => qt q (j + 1) x)).sum) x := by
  induction L with
  | nil => simpa using hasDerivAt_const x (0 : ℝ)
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hasDerivAt_qt q j x (hx q (by simp))).add (ih (fun r hr => hx r (by simp [hr])))

/-- the data scale `2^40` of the polynomial part -/
def K40 : ℤ := 1099511627776

noncomputable def ptZ (Z : List ℤ) (j : ℕ) (x : ℝ) : ℝ := lpEval (zl (lder^[j] Z)) x / 1099511627776
noncomputable def ftZ (Z : List ℤ) (poles : List PoleR) (j : ℕ) (x : ℝ) : ℝ :=
  ptZ Z j x + (poles.map (fun q => qt q j x)).sum

theorem hasDerivAt_ptZ (Z : List ℤ) (j : ℕ) (x : ℝ) : HasDerivAt (ptZ Z j) (ptZ Z (j + 1) x) x := by
  have h := (hasDerivAt_lpEval_zl (lder^[j] Z) x).div_const (1099511627776 : ℝ)
  have e : ptZ Z (j + 1) x = lpEval (zl (lder (lder^[j] Z))) x / 1099511627776 := by
    simp [ptZ, Function.iterate_succ_apply']
  rw [e]; exact h

theorem hasDerivAt_ftZ (Z : List ℤ) (poles : List PoleR) (j : ℕ) (x : ℝ)
    (hx : ∀ q ∈ poles, (x : ℂ) ≠ q.pc) : HasDerivAt (ftZ Z poles j) (ftZ Z poles (j + 1) x) x :=
  (hasDerivAt_ptZ Z j x).add (hasDerivAt_listsum_qt poles j x hx)

/-! ### pole lists of the trial fields -/
theorem qt_scale (k : ℚ) (q : PoleR) (j : ℕ) (x : ℝ) :
    qt ⟨k * q.rr, k * q.ri, q.pr, q.pi⟩ j x = (k : ℝ) * qt q j x := by
  unfold qt qe
  have h : (PoleR.rho ⟨k * q.rr, k * q.ri, q.pr, q.pi⟩) = ((k : ℝ) : ℂ) * q.rho := by
    apply Complex.ext <;> simp [PoleR.rho]
  have h2 : (PoleR.pc ⟨k * q.rr, k * q.ri, q.pr, q.pi⟩) = q.pc := rfl
  rw [h, h2]
  have : ((k : ℝ) : ℂ) * q.rho * ((-1 : ℂ) ^ j * ((j ! : ℕ) : ℂ)) * ((x : ℂ) - q.pc)⁻¹ ^ (j + 1) =
      ((k : ℝ) : ℂ) * (q.rho * ((-1 : ℂ) ^ j * ((j ! : ℕ) : ℂ)) * ((x : ℂ) - q.pc)⁻¹ ^ (j + 1)) := by ring
  rw [this, Complex.re_ofReal_mul]

theorem qt_real (c p : ℚ) (x : ℝ) : qt ⟨c, 0, p, 0⟩ 0 x = (c : ℝ) / (x - p) := by
  have h : (x : ℂ) - (PoleR.pc ⟨c, 0, p, 0⟩) = ((x - p : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [PoleR.pc]
  have h2 : (PoleR.rho ⟨c, 0, p, 0⟩) = ((c : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [PoleR.rho]
  unfold qt qe
  rw [h, h2]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, zero_add, pow_one]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re, div_eq_mul_inv]

theorem qt_i (c : ℚ) (x : ℝ) : qt ⟨c, 0, 0, 1⟩ 0 x = (c : ℝ) * x / (x ^ 2 + 1) := by
  have h1 : (x : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  simp only [qt, qe, PoleR.rho, PoleR.pc]
  simp [Complex.inv_re, Complex.normSq_apply, Complex.mul_re]
  field_simp

def poleOfTail (t : TailQ) : PoleR :=
  ⟨t.rr, t.ri, t.zr * (1 + (t.zr * t.zr + t.zi * t.zi)) / (2 * (t.zr * t.zr + t.zi * t.zi)),
    t.zi * ((t.zr * t.zr + t.zi * t.zi) - 1) / (2 * (t.zr * t.zr + t.zi * t.zi))⟩

theorem tail_pole (t : TailQ) (ht : ‖(TailQ.toC t).1‖ < 1) (hz : t.zr ≠ 0 ∨ t.zi ≠ 0)
    (x : ℝ) (hx : |x| ≤ 1) :
    lpEval (lpSmul (-2) (tailTFrac t).1) x / lpEval (tailTFrac t).2 x =
      qt (poleOfTail t) 0 x := by
  obtain ⟨hden, hre⟩ := tailTFrac_spec t ht hx
  have hw := quadratic_den_norm_lower hx ht.le
  have hwpos : 0 < ‖barrierTailQuadraticDen (TailQ.toC t).1 x‖ :=
    lt_of_lt_of_le (by nlinarith [norm_nonneg (TailQ.toC t).1]) hw
  have hw0 : barrierTailQuadraticDen (TailQ.toC t).1 x ≠ 0 := norm_pos_iff.mp hwpos
  rw [lpEval_smul, mul_div_assoc, ← hre]
  set z : ℂ := (TailQ.toC t).1 with hzdef
  set r : ℂ := (TailQ.toC t).2 with hrdef
  have hzc : z ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    have h2 := congrArg Complex.im h0
    simp [hzdef, TailQ.toC, barrierComplex] at h1 h2
    rcases hz with h | h
    · exact h h1
    · exact h h2
  have hn : (t.zr : ℝ) * t.zr + (t.zi : ℝ) * t.zi ≠ 0 := by
    intro h0
    rcases hz with h | h
    · have : (t.zr : ℝ) ≠ 0 := by exact_mod_cast h
      nlinarith [mul_self_nonneg (t.zr : ℝ), mul_self_nonneg (t.zi : ℝ), sq_pos_of_ne_zero this]
    · have : (t.zi : ℝ) ≠ 0 := by exact_mod_cast h
      nlinarith [mul_self_nonneg (t.zr : ℝ), mul_self_nonneg (t.zi : ℝ), sq_pos_of_ne_zero this]
  have hn' : (t.zr : ℝ) ^ 2 + (t.zi : ℝ) ^ 2 ≠ 0 := by
    intro h; apply hn; nlinarith
  have hn'' : (t.zi : ℝ) ^ 2 + (t.zr : ℝ) ^ 2 ≠ 0 := by rw [add_comm]; exact hn'
  set p : ℂ := (poleOfTail t).pc with hpdef
  have hw : barrierTailQuadraticDen z x = -2 * z * ((x : ℂ) - p) := by
    apply Complex.ext
    · simp [barrierTailQuadraticDen, hzdef, TailQ.toC, barrierComplex, hpdef, poleOfTail,
        PoleR.pc, pow_two]
      field_simp
      ring
    · simp [barrierTailQuadraticDen, hzdef, TailQ.toC, barrierComplex, hpdef, poleOfTail,
        PoleR.pc, pow_two]
      field_simp
      ring
  have hxp : (x : ℂ) - p ≠ 0 := by
    intro h0
    apply hw0
    rw [hw, h0]; ring
  have key : r * z / barrierTailQuadraticDen z x = -(1 / 2 : ℂ) * (r * ((x : ℂ) - p)⁻¹) := by
    rw [hw]
    field_simp
  unfold qt qe
  rw [key]
  have hrho : (poleOfTail t).rho = r := by
    simp [PoleR.rho, poleOfTail, hrdef, TailQ.toC, barrierComplex]
  rw [hrho]
  have e : r * ((-1 : ℂ) ^ 0 * ((0 ! : ℕ) : ℂ)) * ((x : ℂ) - p)⁻¹ ^ (0 + 1) = r * ((x : ℂ) - p)⁻¹ := by
    simp
  rw [e]
  have e2 : -(1 / 2 : ℂ) * (r * ((x : ℂ) - p)⁻¹) = ((-(1 / 2) : ℝ) : ℂ) * (r * ((x : ℂ) - p)⁻¹) := by
    push_cast; ring
  rw [e2, Complex.re_ofReal_mul]
  ring


def poleP (t : TailQ) : PoleR := ⟨2 * (poleOfTail t).rr, 2 * (poleOfTail t).ri, (poleOfTail t).pr, (poleOfTail t).pi⟩

def poleOfTailS (t : TailQ) : PoleR :=
  ⟨t.rr, t.ri, t.zr / (t.zr * t.zr + t.zi * t.zi), -t.zi / (t.zr * t.zr + t.zi * t.zi)⟩

theorem tailT4_pole (t : TailQ) (ht : ‖(TailQ.toC t).1‖ < 1) (hz : t.zr ≠ 0 ∨ t.zi ≠ 0)
    (x : ℝ) (hx : |x| ≤ 1) :
    lpEval (lpSmul (-4) (tailTFrac t).1) x / lpEval (tailTFrac t).2 x = qt (poleP t) 0 x := by
  have h := tail_pole t ht hz x hx
  have e : lpEval (lpSmul (-4) (tailTFrac t).1) x = 2 * lpEval (lpSmul (-2) (tailTFrac t).1) x := by
    simp only [lpEval_smul]; push_cast; ring
  rw [e, mul_div_assoc, h]
  unfold poleP
  rw [qt_scale 2 (poleOfTail t) 0 x]
  push_cast; ring

theorem tailS_pole (t : TailQ) (ht : ‖(TailQ.toC t).1‖ < 1) (hz : t.zr ≠ 0 ∨ t.zi ≠ 0)
    (x : ℝ) (hx : |x| ≤ 1) :
    lpEval (lpSmul (-1) (tailSFrac t).1) x / lpEval (tailSFrac t).2 x = qt (poleOfTailS t) 0 x := by
  obtain ⟨hden, hre⟩ := tailSFrac_spec t ht hx
  have hw0 : barrierTailLinearDen (TailQ.toC t).1 x ≠ 0 := barrierTailLinearDen_ne_zero hx ht
  rw [lpEval_smul, mul_div_assoc, ← hre]
  set z : ℂ := (TailQ.toC t).1 with hzdef
  set r : ℂ := (TailQ.toC t).2 with hrdef
  have hzc : z ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    have h2 := congrArg Complex.im h0
    simp [hzdef, TailQ.toC, barrierComplex] at h1 h2
    rcases hz with h | h
    · exact h h1
    · exact h h2
  have hn : (t.zr : ℝ) * t.zr + (t.zi : ℝ) * t.zi ≠ 0 := by
    intro h0
    rcases hz with h | h
    · have : (t.zr : ℝ) ≠ 0 := by exact_mod_cast h
      nlinarith [mul_self_nonneg (t.zr : ℝ), mul_self_nonneg (t.zi : ℝ), sq_pos_of_ne_zero this]
    · have : (t.zi : ℝ) ≠ 0 := by exact_mod_cast h
      nlinarith [mul_self_nonneg (t.zr : ℝ), mul_self_nonneg (t.zi : ℝ), sq_pos_of_ne_zero this]
  set p : ℂ := (poleOfTailS t).pc with hpdef
  have hpz : p = z⁻¹ := by
    rw [hpdef, hzdef]
    apply Complex.ext
    · simp [poleOfTailS, PoleR.pc, TailQ.toC, barrierComplex, Complex.inv_re, Complex.normSq_apply]
    · simp [poleOfTailS, PoleR.pc, TailQ.toC, barrierComplex, Complex.inv_im, Complex.normSq_apply]
  have hw : barrierTailLinearDen z x = -z * ((x : ℂ) - p) := by
    unfold barrierTailLinearDen
    rw [hpz]
    field_simp
    ring
  have hxp : (x : ℂ) - p ≠ 0 := by
    intro h0
    apply hw0
    rw [hw, h0]; ring
  have key : r * z / barrierTailLinearDen z x = -(r * ((x : ℂ) - p)⁻¹) := by
    rw [hw]
    field_simp
  unfold qt qe
  rw [key]
  have hrho : (poleOfTailS t).rho = r := by
    simp [PoleR.rho, poleOfTailS, hrdef, TailQ.toC, barrierComplex]
  rw [hrho]
  have e : r * ((-1 : ℂ) ^ 0 * ((0 ! : ℕ) : ℂ)) * ((x : ℂ) - p)⁻¹ ^ (0 + 1) = r * ((x : ℂ) - p)⁻¹ := by
    simp
  rw [e]
  simp

/-- the poles of the (scaled) row field derivative (with `lam = 0`) -/
def rowPoles (R : RowWeights) (P V : List TailQ) : List PoleR :=
  [⟨R.alpha, 0, 0, 0⟩, ⟨R.beta, 0, 1, 0⟩, ⟨-2 * R.gamma, 0, 0, 1⟩] ++ P.map poleP ++ V.map poleOfTailS

end CatalanMeasure.CellCert
