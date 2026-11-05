module
public import Submission.CatalanMeasure.CellCert.Tower
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
@[expose] public section
/-! # Sound Taylor value cells

Generalised from `Pilot7.GapBridge4`, `Pilot729.Val`: `cellVal_sound` gives `F x ≤ cap` on a whole cell
from the centre enclosure `ev`, the literal level tables of `PolyData` (2-adic rescaling `lam`), and a
global Chebyshev-T l1 constant `MG` for the `m`-th derivative of the polynomial part. -/
namespace CatalanMeasure.CellCert
open Set Nat CatalanMeasure.Cert
set_option maxRecDepth 100000

/-! ### Chebyshev-T l1 bound -/
def lev (l : List ℤ) (y : ℝ) : ℝ := lpEval (zl l) y
@[simp] theorem lev_nil (y : ℝ) : lev [] y = 0 := rfl
@[simp] theorem lev_cons (a : ℤ) (l : List ℤ) (y : ℝ) : lev (a :: l) y = (a : ℝ) + y * lev l y := by
  simp [lev, zl]

def zsub : List ℤ → List ℤ → List ℤ
  | [], b => b.map (fun x => -x)
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a - b) :: zsub as bs

def zadd : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: zadd as bs

theorem lev_neg_map (b : List ℤ) (y : ℝ) : lev (b.map (fun x => -x)) y = - lev b y := by
  induction b with
  | nil => simp
  | cons a b ih => simp [ih]; ring

theorem lev_zsub (a b : List ℤ) (y : ℝ) : lev (zsub a b) y = lev a y - lev b y := by
  induction a generalizing b with
  | nil => simp [zsub, lev_neg_map]
  | cons a as ih =>
    cases b with
    | nil => simp [zsub]
    | cons b bs => simp [zsub, ih]; ring

theorem lev_zadd (a b : List ℤ) (y : ℝ) : lev (zadd a b) y = lev a y + lev b y := by
  induction a generalizing b with
  | nil => simp [zadd]
  | cons a as ih =>
    cases b with
    | nil => simp [zadd]
    | cons b bs => simp [zadd, ih]; ring

def zsc (c : ℤ) (l : List ℤ) : List ℤ := l.map (fun x => c * x)
theorem lev_zsc (c : ℤ) (l : List ℤ) (y : ℝ) : lev (zsc c l) y = c * lev l y := by
  induction l with
  | nil => simp [zsc]
  | cons a l ih => simp only [zsc, List.map_cons, lev_cons] at ih ⊢; rw [ih]; push_cast; ring

/-- `2 x · l` -/
def t2x (l : List ℤ) : List ℤ := 0 :: zsc 2 l
theorem lev_t2x (l : List ℤ) (y : ℝ) : lev (t2x l) y = 2 * y * lev l y := by
  simp [t2x, lev_zsc]; ring

def zl1 : List ℤ → ℝ
  | [] => 0
  | b :: bs => |(b : ℝ)| + zl1 bs

theorem zl1_eq (bs : List ℤ) : zl1 bs = (((bs.map zabs).sum : ℤ) : ℝ) := by
  induction bs with
  | nil => simp [zl1]
  | cons b bs ih => simp [zl1, ih, zabs_cast]

/-- fold: `Σ_i b_i T_{k+i}` given `(T_k, T_{k+1})` -/
def tfold : List ℤ → List ℤ × List ℤ → List ℤ → List ℤ
  | [], _, acc => acc
  | b :: bs, (t, t'), acc => tfold bs (t', zsub (t2x t') t) (zadd acc (zsc b t))

/-- cos-evaluation of the T recurrence -/
theorem tfold_ev (θ : ℝ) : ∀ (bs : List ℤ) (k : ℕ) (t t' acc : List ℤ),
    lev t (Real.cos θ) = Real.cos (k * θ) → lev t' (Real.cos θ) = Real.cos ((k + 1 : ℕ) * θ) →
    ∃ s : ℝ, lev (tfold bs (t, t') acc) (Real.cos θ) = lev acc (Real.cos θ) + s ∧
      |s| ≤ zl1 bs := by
  intro bs
  induction bs with
  | nil => intro k t t' acc _ _; exact ⟨0, by simp [tfold], by simp [zl1]⟩
  | cons b bs ih =>
    intro k t t' acc h1 h2
    have h3 : lev (zsub (t2x t') t) (Real.cos θ) = Real.cos ((k + 2 : ℕ) * θ) := by
      rw [lev_zsub, lev_t2x, h1, h2]
      push_cast
      have e1 : ((k : ℝ) + 2) * θ = ((k : ℝ) + 1) * θ + θ := by ring
      have e2 : (k : ℝ) * θ = ((k : ℝ) + 1) * θ - θ := by ring
      rw [e1, e2, Real.cos_add, Real.cos_sub]
      ring
    obtain ⟨s, hs, hsb⟩ := ih (k + 1) t' (zsub (t2x t') t) (zadd acc (zsc b t)) h2 (by
      rw [h3])
    refine ⟨b * Real.cos (k * θ) + s, ?_, ?_⟩
    · simp only [tfold]
      rw [hs, lev_zadd, lev_zsc, h1]; ring
    · rw [zl1]
      have hb : |(b : ℝ) * Real.cos (k * θ)| ≤ |(b : ℝ)| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      linarith [abs_add_le ((b : ℝ) * Real.cos (k * θ)) s]

def tcomb (bs : List ℤ) : List ℤ := tfold bs ([1], [0, 1]) []

theorem tcomb_bound (bs : List ℤ) (y : ℝ) (hy : |y| ≤ 1) :
    |lev (tcomb bs) y| ≤ zl1 bs := by
  have hy' := abs_le.mp hy
  obtain ⟨θ, hθ⟩ : ∃ θ, Real.cos θ = y := ⟨Real.arccos y, Real.cos_arccos hy'.1 hy'.2⟩
  obtain ⟨s, hs, hsb⟩ := tfold_ev θ bs 0 [1] [0, 1] [] (by simp) (by simp [hθ])
  unfold tcomb
  rw [← hθ] at *
  have : lev (tfold bs ([1], [0, 1]) []) (Real.cos θ) = s := by rw [hs]; simp
  rw [this]; exact hsb



/-! ### sign-split Horner over literal level tables -/
def zval (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - p.2

def hP (neg : Bool) (y T : ℕ) : ℕ → List (ℕ × ℕ) → ℕ × ℕ
  | _, [] => (0, 0)
  | tp, a :: t =>
    match hP neg y T (tp / T) t with
    | (u, v) =>
      if neg then (a.1 * tp + y * v, a.2 * tp + y * u) else (a.1 * tp + y * u, a.2 * tp + y * v)

theorem hP_spec (neg : Bool) (y T : ℕ) : ∀ (lp : List (ℕ × ℕ)) (tp : ℕ),
    zval (hP neg y T tp lp) = hv (if neg then -(y : ℤ) else (y : ℤ)) (T : ℤ) (tp : ℤ) (lp.map zval) := by
  intro lp
  induction lp with
  | nil => intro tp; simp [hP, hv, zval]
  | cons a t ih =>
    intro tp
    have h := ih (tp / T)
    simp only [hP]
    rcases hr : hP neg y T (tp / T) t with ⟨u, v⟩
    rw [hr] at h
    rw [Int.natCast_div] at h
    simp only [hv, List.map_cons, forceZ_eq]
    unfold zval at h ⊢
    cases neg
    · simp only [Bool.false_eq_true, ite_false] at h ⊢
      push_cast at h ⊢
      rw [← h]; ring
    · simp only [ite_true] at h ⊢
      push_cast at h ⊢
      rw [← h]; ring

/-! ### constants -/
def TT : ℤ := 1099511627776
def SC : ℤ := 340282366920938463463374607431768211456
/-- `TT ^ N` as a natural-number power (kernel-fast) -/
def TPN (N : ℕ) : ℤ := (((1099511627776 : ℕ) ^ N : ℕ) : ℤ)
def zpw (a : ℤ) (n : ℕ) : ℤ := ((a.toNat ^ n : ℕ) : ℤ)
def tf (i : ℕ) : ℤ := (((1099511627776 : ℕ) ^ i * i ! : ℕ) : ℤ)

theorem TT_pos : (0 : ℤ) < TT := by unfold TT; norm_num
theorem SC_pos : (0 : ℤ) < SC := by unfold SC; norm_num
theorem TPN_eq (N : ℕ) : TPN N = TT ^ N := by unfold TPN TT; push_cast; rfl
theorem TPN_pos (N : ℕ) : (0 : ℤ) < TPN N := by rw [TPN_eq]; exact pow_pos TT_pos _
theorem zpw_eq (a : ℤ) (n : ℕ) (ha : 0 ≤ a) : zpw a n = a ^ n := by
  unfold zpw; push_cast; rw [Int.toNat_of_nonneg ha]
theorem tf_eq (i : ℕ) : tf i = TT ^ i * ((i ! : ℕ) : ℤ) := by
  unfold tf TT; push_cast; rfl

/-! ### level tables: `wlist j B` is the list of coefficients of the `j`-th derivative -/
def ffp (i : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => (i + j + 1) * ffp i j

theorem ffp_eq (i j : ℕ) : ffp i j = (i + j).descFactorial j := by
  induction j with
  | zero => simp [ffp]
  | succ j ih =>
    rw [ffp, ih, show i + (j + 1) = (i + j) + 1 by omega, Nat.succ_descFactorial_succ]

def wl (j : ℕ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | i, a :: t => (a * (ffp i j : ℤ)) :: wl j (i + 1) t

def wlist (j : ℕ) (l : List ℤ) : List ℤ := wl j 0 (l.drop j)

theorem wl_length (j : ℕ) : ∀ (l : List ℤ) (i : ℕ), (wl j i l).length = l.length := by
  intro l
  induction l with
  | nil => intro i; rfl
  | cons a t ih => intro i; simp [wl, ih]

theorem wl_getD (j : ℕ) : ∀ (l : List ℤ) (i n : ℕ),
    (wl j i l).getD n 0 = l.getD n 0 * (ffp (i + n) j : ℤ) := by
  intro l
  induction l with
  | nil => intro i n; simp [wl]
  | cons a t ih =>
    intro i n
    cases n with
    | zero => simp [wl]
    | succ n =>
      simp only [wl, List.getD_cons_succ, ih]
      congr 3; omega

theorem wlist_getD (j : ℕ) (l : List ℤ) (i : ℕ) :
    (wlist j l).getD i 0 = l.getD (i + j) 0 * (ffp i j : ℤ) := by
  unfold wlist
  rw [wl_getD, zero_add]
  have hdZ : (l.drop j).getD i 0 = l.getD (i + j) 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, add_comm]
  rw [hdZ]

theorem wlist_length (j : ℕ) (l : List ℤ) : (wlist j l).length = l.length - j := by
  unfold wlist; rw [wl_length, List.length_drop]

theorem lderAux_getD (L : List ℤ) : ∀ (k i : ℕ),
    (lderAux k L).getD i 0 = ((k + i : ℕ) : ℤ) * L.getD i 0 := by
  induction L with
  | nil => intro k i; simp [lderAux]
  | cons a L ih =>
    intro k i
    cases i with
    | zero => simp [lderAux]
    | succ i =>
      simp only [lderAux, List.getD_cons_succ, ih]
      congr 2; omega

theorem lder_getD (L : List ℤ) (i : ℕ) :
    (lder L).getD i 0 = ((i + 1 : ℕ) : ℤ) * L.getD (i + 1) 0 := by
  unfold lder
  have := lderAux_getD L 0 (i + 1)
  rw [List.getD_eq_getElem?_getD] at this ⊢
  rw [List.getElem?_tail] at *
  simpa [List.getD_eq_getElem?_getD] using this

theorem lder_iter_getD (l : List ℤ) : ∀ (j i : ℕ),
    (lder^[j] l).getD i 0 = l.getD (i + j) 0 * (((i + j).descFactorial j : ℕ) : ℤ) := by
  intro j
  induction j with
  | zero => intro i; simp
  | succ j ih =>
    intro i
    rw [Function.iterate_succ_apply', lder_getD, ih]
    have e : (i + 1 + j).descFactorial (j + 1) = (i + 1) * (i + 1 + j).descFactorial j := by
      rw [Nat.descFactorial_succ]; congr 1; omega
    have e2 : i + 1 + j = i + (j + 1) := by omega
    rw [e2] at e ⊢
    rw [e]; push_cast; ring


theorem wlist_eq (j : ℕ) (l : List ℤ) : wlist j l = lder^[j] l := by
  apply List.ext_getElem
  · rw [wlist_length, lder_iter_length]
  · intro i h1 h2
    have e1 := (List.getD_eq_getElem (wlist j l) 0 h1).symm
    have e2 := (List.getD_eq_getElem (lder^[j] l) 0 h2).symm
    rw [e1, e2, wlist_getD, lder_iter_getD, ffp_eq]

/-! ### 2-adic rescaling of the level tables: `Z = shl lam B`, `Z_i = lam^i B_i` -/
theorem zsc_getD (c : ℤ) (l : List ℤ) (i : ℕ) : (zsc c l).getD i 0 = c * l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [zsc]
  | cons a t ih =>
    cases i with
    | zero => simp [zsc]
    | succ i => simpa [zsc] using ih i

def shl (lam : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: t => a :: zsc lam (shl lam t)

theorem shl_length (lam : ℤ) (l : List ℤ) : (shl lam l).length = l.length := by
  induction l with
  | nil => simp [shl]
  | cons a t ih => simp [shl, zsc, ih]

theorem lev_shl (lam : ℤ) (l : List ℤ) (x : ℝ) : lev (shl lam l) x = lev l ((lam : ℝ) * x) := by
  induction l with
  | nil => simp [shl]
  | cons a t ih => simp only [shl, lev_cons, lev_zsc, ih]; ring

theorem shl_getD (lam : ℤ) (l : List ℤ) (i : ℕ) : (shl lam l).getD i 0 = lam ^ i * l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [shl]
  | cons a t ih =>
    cases i with
    | zero => simp [shl]
    | succ i =>
      simp only [shl, List.getD_cons_succ, zsc_getD, ih]
      ring

theorem wlist_shl (lam : ℤ) (j : ℕ) (l : List ℤ) :
    wlist j (shl lam l) = zsc (lam ^ j) (shl lam (wlist j l)) := by
  apply List.ext_getElem
  · simp only [zsc, List.length_map, shl_length, wlist_length]
  · intro i h1 h2
    have e1 := (List.getD_eq_getElem (wlist j (shl lam l)) 0 h1).symm
    have e2 := (List.getD_eq_getElem (zsc (lam ^ j) (shl lam (wlist j l))) 0 h2).symm
    rw [e1, e2, wlist_getD, zsc_getD, shl_getD, shl_getD, wlist_getD]
    ring

/-! ### polynomial data of a field: `Z = shl lam B`, level tables over `T' = Tb = 2^40 / lam` -/
structure PolyData where
  B : List ℤ
  LV : List (List (ℕ × ℕ))
  lam : ℕ
  Tb : ℕ

namespace PolyData
def Z (D : PolyData) : List ℤ := shl (D.lam : ℤ) D.B
def N (D : PolyData) : ℕ := D.B.length - 1

/-- the one-off checks: `lam * Tb = 2^40`, and the literal tables are the derivative levels of `B` -/
structure Ok (D : PolyData) : Prop where
  hT : D.lam * D.Tb = 1099511627776
  hlam : 0 < D.lam
  hchk : ∀ j < D.LV.length, wlist j D.B = (D.LV.getD j []).map zval

theorem Z_length (D : PolyData) : D.Z.length = D.N + 1 ∨ D.B = [] := by
  unfold Z N
  rw [shl_length]
  cases D.B with
  | nil => right; rfl
  | cons a t => left; simp

theorem Z_length_le (D : PolyData) : D.Z.length ≤ D.N + 1 := by
  unfold Z N; rw [shl_length]; omega
end PolyData

/-- the exact integer value `lam^(N+j) * zval(hP ...)` of the `j`-th polynomial level at `cc` -/
def polyValsD (D : PolyData) (cc : ℤ) (m : ℕ) : List ℤ :=
  (List.range m).map (fun j => ((D.lam ^ (D.N + j) : ℕ) : ℤ) *
    zval (hP (decide (cc < 0)) cc.natAbs D.Tb (D.Tb ^ D.N) (D.LV.getD j [])))

theorem lpEval_zl_eq_lev (l : List ℤ) (y : ℝ) : lpEval (zl l) y = lev l y := rfl

theorem polyVal_eq (D : PolyData) (hD : D.Ok) (cc : ℤ) (j : ℕ) (hj : j < D.LV.length) :
    ((D.lam ^ (D.N + j) : ℕ) : ℤ) *
      zval (hP (decide (cc < 0)) cc.natAbs D.Tb (D.Tb ^ D.N) (D.LV.getD j [])) =
      hv cc TT (TT ^ D.N) (lder^[j] D.Z) := by
  rw [hP_spec]
  have h1 : (if decide (cc < 0) = true then -(cc.natAbs : ℤ) else (cc.natAbs : ℤ)) = cc := by
    by_cases h : cc < 0
    · rw [decide_eq_true h]; simp only [ite_true]
      have := Int.ofNat_natAbs_of_nonpos h.le; omega
    · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ite_false]
      have := Int.natAbs_of_nonneg (not_lt.mp h); omega
  have h3 : ((D.Tb ^ D.N : ℕ) : ℤ) = ((D.Tb : ℕ) : ℤ) ^ D.N := by push_cast; rfl
  rw [h1, h3]
  set L : List ℤ := (D.LV.getD j []).map zval with hL
  have hchk := hD.hchk j hj
  rw [← hL] at hchk
  have hw : wlist j D.Z = lder^[j] D.Z := wlist_eq j D.Z
  have hLlen : L.length ≤ D.N + 1 := by
    have h0 := congrArg List.length hchk
    rw [wlist_length] at h0
    unfold PolyData.N; omega
  have hlam : (0 : ℤ) < (D.lam : ℤ) := by exact_mod_cast hD.hlam
  have hTb : (0 : ℤ) < (D.Tb : ℤ) := by
    rcases Nat.eq_zero_or_pos D.Tb with h | h
    · have := hD.hT; rw [h] at this; omega
    · exact_mod_cast h
  have hTTlam : (TT : ℝ) = (D.lam : ℝ) * (D.Tb : ℝ) := by
    unfold TT; exact_mod_cast hD.hT.symm
  have hTbR : (D.Tb : ℝ) ≠ 0 := by exact_mod_cast hTb.ne'
  have hlamR : (D.lam : ℝ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hTTR : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_mul, hv_spec cc (D.Tb : ℤ) hTb L D.N hLlen]
  have hZl : (lder^[j] D.Z).length ≤ D.N + 1 := by
    rw [lder_iter_length]; have := D.Z_length_le; omega
  rw [hv_spec cc TT TT_pos _ D.N hZl, ← hw]
  unfold PolyData.Z
  rw [lpEval_zl_eq_lev, lpEval_zl_eq_lev, wlist_shl, hchk, lev_zsc, lev_shl]
  have e : ((D.lam : ℤ) : ℝ) * ((cc : ℝ) / TT) = (cc : ℝ) / (D.Tb : ℝ) := by
    rw [hTTlam]; push_cast; field_simp
  rw [e, hTTlam]
  push_cast
  ring

theorem polyValsD_getD (D : PolyData) (hD : D.Ok) (cc : ℤ) (m j : ℕ) (hm : m ≤ D.LV.length)
    (hj : j < m) : (polyValsD D cc m).getD j 0 = hv cc TT (TT ^ D.N) (lder^[j] D.Z) := by
  rw [← polyVal_eq D hD cc j (by omega)]
  simp [polyValsD, List.getD_eq_getElem?_getD, List.getElem?_range hj]

/-! ### poles: distance and tower bounds -/
def qmax (a b : ℚ) : ℚ := if a ≤ b then b else a
def poleDl (q : PoleR) (lo hi : ℚ) : ℚ :=
  qmax (qmax 0 (qmax (lo - q.pr) (q.pr - hi))) (qabs' q.pi)

theorem qmax_cast_le (a b : ℚ) (r : ℝ) (ha : (a : ℝ) ≤ r) (hb : (b : ℝ) ≤ r) :
    ((qmax a b : ℚ) : ℝ) ≤ r := by
  unfold qmax; split_ifs <;> assumption

theorem dl_le_norm (q : PoleR) (lo hi : ℚ) (y : ℝ) (h1 : (lo : ℝ) ≤ y) (h2 : y ≤ (hi : ℝ)) :
    ((poleDl q lo hi : ℚ) : ℝ) ≤ ‖(y : ℂ) - q.pc‖ := by
  have hre : |y - q.pr| ≤ ‖(y : ℂ) - q.pc‖ := by
    have := Complex.abs_re_le_norm ((y : ℂ) - q.pc)
    simpa [PoleR.pc] using this
  have him : |(q.pi : ℝ)| ≤ ‖(y : ℂ) - q.pc‖ := by
    have := Complex.abs_im_le_norm ((y : ℂ) - q.pc)
    simpa [PoleR.pc, abs_neg] using this
  unfold poleDl
  refine qmax_cast_le _ _ _ (qmax_cast_le _ _ _ ?_ (qmax_cast_le _ _ _ ?_ ?_)) ?_
  · rw [Rat.cast_zero]; exact norm_nonneg _
  · push_cast; linarith [le_abs_self (y - q.pr)]
  · push_cast; linarith [neg_abs_le (y - q.pr)]
  · rw [qabs'_cast]; exact him

theorem qt_bound (q : PoleR) (m : ℕ) (y dl : ℝ) (hdl : 0 < dl) (hy : dl ≤ ‖(y : ℂ) - q.pc‖) :
    |qt q m y| ≤ (|(q.rr : ℝ)| + |(q.ri : ℝ)|) * (m ! : ℝ) / dl ^ (m + 1) := by
  unfold qt qe
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, norm_pow, norm_mul, norm_pow, norm_inv]
  have h1 : ‖q.rho‖ ≤ |(q.rr : ℝ)| + |(q.ri : ℝ)| := by
    have := Complex.norm_le_abs_re_add_abs_im q.rho
    simpa [PoleR.rho] using this
  have h2 : ‖(-1 : ℂ)‖ ^ m * ‖((m ! : ℕ) : ℂ)‖ = (m ! : ℝ) := by
    simp
  have h3 : (‖(y : ℂ) - q.pc‖⁻¹) ^ (m + 1) ≤ 1 / dl ^ (m + 1) := by
    rw [one_div, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hdl hy) _
  have h4 : (0 : ℝ) ≤ ‖q.rho‖ := norm_nonneg _
  rw [mul_assoc, h2, div_eq_mul_one_div ((|(q.rr : ℝ)| + |(q.ri : ℝ)|) * (m ! : ℝ))]
  rw [← mul_assoc]
  calc ‖q.rho‖ * (m ! : ℝ) * ‖(y : ℂ) - q.pc‖⁻¹ ^ (m + 1)
      ≤ (|(q.rr : ℝ)| + |(q.ri : ℝ)|) * (m ! : ℝ) * (1 / dl ^ (m + 1)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h3 (by positivity)
          (by positivity)
    _ = _ := by ring

theorem abs_list_sum_le {α : Type*} (L : List α) (f : α → ℝ) :
    |(L.map f).sum| ≤ (L.map (fun a => |f a|)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (by linarith)

theorem cast_list_sum_map {α : Type*} (L : List α) (g : α → ℤ) :
    (((L.map g).sum : ℤ) : ℝ) = (L.map (fun a => (g a : ℝ))).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem list_sum_floor {α : Type*} (L : List α) (f : α → ℝ) (g : α → ℤ)
    (h : ∀ a ∈ L, (g a : ℝ) ≤ f a ∧ f a < (g a : ℝ) + 1) :
    (((L.map g).sum : ℤ) : ℝ) ≤ (L.map f).sum ∧ (L.map f).sum ≤ (((L.map g).sum : ℤ) : ℝ) + L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨h1, h2⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons, Int.cast_add, Nat.cast_add, Nat.cast_one]
    constructor <;> linarith [ha.1, ha.2]

theorem list_sum_le_cast {α : Type*} (L : List α) (f : α → ℝ) (g : α → ℤ)
    (h : ∀ a ∈ L, f a ≤ (g a : ℝ)) : (L.map f).sum ≤ (((L.map g).sum : ℤ) : ℝ) := by
  rw [cast_list_sum_map]
  exact List.sum_le_sum h

/-! ### floor-scaled derivative levels -/
def fhatV (N : ℕ) (poles : List PoleR) (cc : ℤ) (V : List ℤ) (j : ℕ) : ℤ :=
  (V.getD j 0 * SC) / (K40 * TPN N) +
    (poles.map (fun q => qfloor (SC * poleVal q ((cc : ℚ) / (TT : ℚ)) j))).sum

def EcntV (poles : List PoleR) : ℤ := 1 + (poles.length : ℤ)

def BsumV (N : ℕ) (poles : List PoleR) (cc hh : ℤ) (V : List ℤ) (m : ℕ) : ℤ :=
  ((List.range m).map (fun j =>
    cdiv ((zabs (fhatV N poles cc V j) + EcntV poles) * zpw hh (j + 1)) (tf (j + 1)))).sum

def MpoleV (poles : List PoleR) (m : ℕ) (lo hi : ℚ) : ℤ :=
  (poles.map (fun q => qceil (SC * (qabs' q.rr + qabs' q.ri) * ((m ! : ℕ) : ℚ) /
    (poleDl q lo hi) ^ (m + 1)))).sum

/-- scaled bound for `sup |P^(m)|` on the cell `[c-h, c+h]` from the Taylor tower of `P^(m)`
to order `L` (values at the centre, floors with `+1`) and the global constant `MGL` at level `m+L` -/
def PbV (N : ℕ) (cc hh : ℤ) (V : List ℤ) (m L : ℕ) (MGL : ℤ) : ℤ :=
  ((List.range L).map (fun k =>
    cdiv ((zabs (V.getD (m + k) 0 * SC / (K40 * TPN N)) + 1) * zpw hh k) (tf k))).sum +
    cdiv (MGL * zpw hh L) (tf L)

/-- the pole `pe` (if any) must not lie inside the open cell -/
def peOK (pe : Option ℚ) (lo hi : ℚ) : Bool :=
  match pe with
  | none => true
  | some p => decide (p ≤ lo) || decide (hi ≤ p)

/-- The Taylor value cell `(cc, hh)` (centre / half width in units of `2^-40`), order `m`:
`F x ≤ cap` on the cell, where `ev` encloses `F` at the centre. -/
def cellVal (ev : ℚ → Option (ℚ × ℚ)) (D : PolyData) (poles : List PoleR) (m L : ℕ) (MGL : ℤ)
    (pe : Option ℚ) (cap : ℚ) (cell : ℤ × ℤ) : Bool :=
  let cc := cell.1
  let hh := cell.2
  let lo : ℚ := ((cc - hh : ℤ) : ℚ) / (TT : ℚ)
  let hi : ℚ := ((cc + hh : ℤ) : ℚ) / (TT : ℚ)
  let V := polyValsD D cc (m + L)
  match ev ((cc : ℚ) / (TT : ℚ)) with
  | none => false
  | some ve =>
    decide (m + L ≤ D.LV.length) && decide (0 ≤ hh) &&
      decide (-TT ≤ cc - hh) && decide (cc + hh ≤ TT) && peOK pe lo hi &&
      poles.all (fun q => decide (0 < poleDl q lo hi)) &&
      decide (qceil (SC * (ve.1 + ve.2)) + BsumV D.N poles cc hh V m +
        cdiv ((MpoleV poles m lo hi + PbV D.N cc hh V m L MGL) * zpw hh (m + 1)) (tf (m + 1)) ≤ qfloor (SC * cap))

/-! ### real side -/
theorem hv_real (D : PolyData) (cc : ℤ) (j : ℕ) :
    ((hv cc TT (TT ^ D.N) (lder^[j] D.Z) : ℤ) : ℝ) =
      (TT : ℝ) ^ D.N * lpEval (zl (lder^[j] D.Z)) ((cc : ℝ) / TT) :=
  hv_spec cc TT TT_pos (lder^[j] D.Z) D.N
    (by rw [lder_iter_length]; have := D.Z_length_le; omega)

theorem fhatV_err (D : PolyData) (hD : D.Ok) (poles : List PoleR) (cc : ℤ) (m j : ℕ)
    (hm : m ≤ D.LV.length) (hj : j < m) :
    (fhatV D.N poles cc (polyValsD D cc m) j : ℝ) ≤
        (SC : ℝ) * ftZ D.Z poles j ((cc : ℝ) / TT) ∧
    (SC : ℝ) * ftZ D.Z poles j ((cc : ℝ) / TT) ≤
        (fhatV D.N poles cc (polyValsD D cc m) j : ℝ) + EcntV poles := by
  have hT : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  have hP : (0 : ℝ) < TPN D.N := by exact_mod_cast TPN_pos D.N
  have hK40 : (0 : ℤ) < K40 := by unfold K40; norm_num
  have hS : (0 : ℝ) < SC := by exact_mod_cast SC_pos
  have hpt : ptZ D.Z j ((cc : ℝ) / TT) =
      (hv cc TT (TT ^ D.N) (lder^[j] D.Z) : ℝ) / TPN D.N / 1099511627776 := by
    have := hv_real D cc j
    unfold ptZ
    have hTP : (TPN D.N : ℝ) = (TT : ℝ) ^ D.N := by rw [TPN_eq]; push_cast; rfl
    rw [hTP, this]
    field_simp
  set a : ℤ := hv cc TT (TT ^ D.N) (lder^[j] D.Z) * SC with ha
  set b : ℤ := K40 * TPN D.N with hb
  have hbpos : (0 : ℤ) < b := mul_pos hK40 (TPN_pos _)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have e1 : (SC : ℝ) * ptZ D.Z j ((cc : ℝ) / TT) = (a : ℝ) / b := by
    rw [hpt, ha, hb]; push_cast
    have : (K40 : ℝ) = 1099511627776 := by unfold K40; norm_num
    rw [this]; field_simp
  have f1 := zdiv_le a b hbpos
  have f2 := lt_zdiv_add_one a b hbpos
  have f1R : (b : ℝ) * ((a / b : ℤ) : ℝ) ≤ a := by exact_mod_cast f1
  have f2R : (a : ℝ) < b * (((a / b : ℤ) : ℝ) + 1) := by exact_mod_cast f2
  have g1 : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
    rw [le_div_iff₀ hbR]; linarith
  have g2 : (a : ℝ) / b < ((a / b : ℤ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hbR]; linarith
  have hpoles := list_sum_floor poles
    (fun q => (SC : ℝ) * qt q j ((cc : ℝ) / TT))
    (fun q => qfloor (SC * poleVal q ((cc : ℚ) / (TT : ℚ)) j))
    (by
      intro q _
      have hv' : ((poleVal q ((cc : ℚ) / (TT : ℚ)) j : ℚ) : ℝ) = qt q j ((cc : ℝ) / TT) := by
        have := poleVal_spec q ((cc : ℚ) / (TT : ℚ)) j
        rw [this]; push_cast; rfl
      have l1 := qfloor_le (SC * poleVal q ((cc : ℚ) / (TT : ℚ)) j)
      have l2 := lt_qfloor_add_one (SC * poleVal q ((cc : ℚ) / (TT : ℚ)) j)
      have l1R : (((qfloor (SC * poleVal q ((cc : ℚ) / (TT : ℚ)) j) : ℤ) : ℚ) : ℝ) ≤
          ((SC * poleVal q ((cc : ℚ) / (TT : ℚ)) j : ℚ) : ℝ) := by exact_mod_cast l1
      have l2R : ((SC * poleVal q ((cc : ℚ) / (TT : ℚ)) j : ℚ) : ℝ) <
          (((qfloor (SC * poleVal q ((cc : ℚ) / (TT : ℚ)) j) : ℤ) : ℚ) : ℝ) + 1 := by exact_mod_cast l2
      push_cast at l1R l2R
      rw [hv'] at l1R l2R
      exact ⟨by exact_mod_cast l1R, by exact_mod_cast l2R⟩)
  have hlen : (poles.length : ℝ) + 1 = EcntV poles := by unfold EcntV; push_cast; ring
  have hsum : (SC : ℝ) * (poles.map (fun q => qt q j ((cc : ℝ) / TT))).sum =
      (poles.map (fun q => (SC : ℝ) * qt q j ((cc : ℝ) / TT))).sum := by
    rw [List.sum_map_mul_left]
  unfold ftZ fhatV
  rw [mul_add, e1, hsum, polyValsD_getD D hD cc m j hm hj, TPN_eq]
  simp only [Int.cast_add]
  have : ((hv cc TT (TT ^ D.N) (lder^[j] D.Z) * SC) / (K40 * TT ^ D.N) : ℤ) = a / b := by
    rw [hb, TPN_eq]
  rw [this]
  rw [TPN_eq] at hb
  constructor <;> linarith [hpoles.1, hpoles.2, g1, g2]

theorem ptZ_scaled (D : PolyData) (hD : D.Ok) (cc : ℤ) (m' j : ℕ) (hm : m' ≤ D.LV.length)
    (hj : j < m') :
    ((((polyValsD D cc m').getD j 0 * SC) / (K40 * TPN D.N) : ℤ) : ℝ) ≤
        (SC : ℝ) * ptZ D.Z j ((cc : ℝ) / TT) ∧
    (SC : ℝ) * ptZ D.Z j ((cc : ℝ) / TT) <
        ((((polyValsD D cc m').getD j 0 * SC) / (K40 * TPN D.N) : ℤ) : ℝ) + 1 := by
  have hT : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  have hP : (0 : ℝ) < TPN D.N := by exact_mod_cast TPN_pos D.N
  have hK40 : (0 : ℤ) < K40 := by unfold K40; norm_num
  have hS : (0 : ℝ) < SC := by exact_mod_cast SC_pos
  have hpt : ptZ D.Z j ((cc : ℝ) / TT) =
      (hv cc TT (TT ^ D.N) (lder^[j] D.Z) : ℝ) / TPN D.N / 1099511627776 := by
    have := hv_real D cc j
    unfold ptZ
    have hTP : (TPN D.N : ℝ) = (TT : ℝ) ^ D.N := by rw [TPN_eq]; push_cast; rfl
    rw [hTP, this]
    field_simp
  rw [polyValsD_getD D hD cc m' j hm hj]
  set a : ℤ := hv cc TT (TT ^ D.N) (lder^[j] D.Z) * SC with ha
  set b : ℤ := K40 * TPN D.N with hb
  have hbpos : (0 : ℤ) < b := mul_pos hK40 (TPN_pos _)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have e1 : (SC : ℝ) * ptZ D.Z j ((cc : ℝ) / TT) = (a : ℝ) / b := by
    rw [hpt, ha, hb]; push_cast
    have : (K40 : ℝ) = 1099511627776 := by unfold K40; norm_num
    rw [this]; field_simp
  have f1 := zdiv_le a b hbpos
  have f2 := lt_zdiv_add_one a b hbpos
  have f1R : (b : ℝ) * ((a / b : ℤ) : ℝ) ≤ a := by exact_mod_cast f1
  have f2R : (a : ℝ) < b * (((a / b : ℤ) : ℝ) + 1) := by exact_mod_cast f2
  have g1 : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
    rw [le_div_iff₀ hbR]; linarith
  have g2 : (a : ℝ) / b < ((a / b : ℤ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hbR]; linarith
  rw [e1]
  exact ⟨g1, g2⟩

/-- local bound of `SC * |P^(m)|` on a cell: Taylor tower of the polynomial part with the global
constant `MGL` only at level `m + L` -/
theorem ptZ_local (D : PolyData) (hD : D.Ok) (cc hh : ℤ) (m L : ℕ) (MGL : ℤ)
    (hMGL : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m + L) y| ≤ (MGL : ℝ))
    (hm : m + L ≤ D.LV.length) (hh0 : 0 ≤ hh) (hlow : -TT ≤ cc - hh) (hhigh : cc + hh ≤ TT) :
    ∀ y : ℝ, |y - (cc : ℝ) / TT| ≤ (hh : ℝ) / TT →
      (SC : ℝ) * |ptZ D.Z m y| ≤ (PbV D.N cc hh (polyValsD D cc (m + L)) m L MGL : ℤ) := by
  intro y hy
  have hT : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  have hS : (0 : ℝ) < SC := by exact_mod_cast SC_pos
  have hh0R : (0 : ℝ) ≤ hh := by exact_mod_cast hh0
  set c : ℝ := (cc : ℝ) / TT with hc
  set hR : ℝ := (hh : ℝ) / TT with hhR
  have hhR0 : 0 ≤ hR := by positivity
  have hlow' : (-(TT : ℝ)) ≤ (cc : ℝ) - hh := by exact_mod_cast hlow
  have hhigh' : (cc : ℝ) + hh ≤ TT := by exact_mod_cast hhigh
  have e1 : c - hR = ((cc : ℝ) - hh) / TT := by simp only [hc, hhR]; ring
  have e2 : c + hR = ((cc : ℝ) + hh) / TT := by simp only [hc, hhR]; ring
  have g1 : (-1 : ℝ) ≤ c - hR := by rw [e1, le_div_iff₀ hT]; linarith
  have g2 : c + hR ≤ 1 := by rw [e2, div_le_iff₀ hT]; linarith
  have hyI : ∀ z ∈ Icc (c - hR) (c + hR), |z| ≤ 1 := by
    intro z hz; rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
  have hxI : y ∈ Icc (c - hR) (c + hR) := by
    have := abs_le.mp hy
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hcont : ∀ j ≤ L, ContinuousOn (fun z => ptZ D.Z (m + j) z) (Icc (c - hR) (c + hR)) := by
    intro j _ z _
    exact (hasDerivAt_ptZ D.Z (m + j) z).continuousAt.continuousWithinAt
  have hder : ∀ j < L, ∀ z ∈ Ioo (c - hR) (c + hR),
      HasDerivAt (fun z => ptZ D.Z (m + j) z) ((fun z => ptZ D.Z (m + (j + 1)) z) z) z := by
    intro j _ z _
    exact hasDerivAt_ptZ D.Z (m + j) z
  have hbd : ∀ z ∈ Icc (c - hR) (c + hR), |ptZ D.Z (m + L) z| ≤ (MGL : ℝ) / SC := by
    intro z hz
    rw [le_div_iff₀ hS, mul_comm]
    exact hMGL z (hyI z hz)
  have htay := taylor_tower' c hR ((MGL : ℝ) / SC) L (fun j z => ptZ D.Z (m + j) z)
    hcont hder hbd y hxI
  simp only [add_zero] at htay
  set S : ℝ := ∑ j ∈ Finset.range L, ptZ D.Z (m + j) c * (y - c) ^ j / (j ! : ℝ) with hSdef
  have hdx : |y - c| ≤ hR := abs_le.mpr ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
  have hSb : (SC : ℝ) * |S| ≤ (((List.range L).map (fun k =>
      cdiv ((zabs ((polyValsD D cc (m + L)).getD (m + k) 0 * SC / (K40 * TPN D.N)) + 1) * zpw hh k)
        (tf k))).sum : ℤ) := by
    rw [cast_list_sum_map, list_range_map_sum (fun a => ((cdiv ((zabs ((polyValsD D cc (m + L)).getD (m + a) 0 * SC / (K40 * TPN D.N)) + 1) * zpw hh a) (tf a) : ℤ) : ℝ))]
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hS.le) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hjm => ?_)
    have hj : j < L := Finset.mem_range.mp hjm
    have hf : (0 : ℝ) < (j ! : ℝ) := by positivity
    have hd : (0 : ℤ) < tf j := by
      rw [tf_eq j]
      have := TT_pos
      positivity
    obtain ⟨s1, s2⟩ := ptZ_scaled D hD cc (m + L) (m + j) hm (by omega)
    set q : ℤ := (polyValsD D cc (m + L)).getD (m + j) 0 * SC / (K40 * TPN D.N) with hq
    have hA : (SC : ℝ) * |ptZ D.Z (m + j) c| ≤ ((zabs q + 1 : ℤ) : ℝ) := by
      push_cast; rw [zabs_cast]
      have e : (SC : ℝ) * |ptZ D.Z (m + j) c| = |(SC : ℝ) * ptZ D.Z (m + j) c| := by
        rw [abs_mul, abs_of_pos hS]
      rw [e, abs_le]
      constructor <;> cases abs_cases (q : ℝ) <;>
        linarith [neg_abs_le (q : ℝ), le_abs_self (q : ℝ)]
    have hp : |y - c| ^ j ≤ hR ^ j := pow_le_pow_left₀ (abs_nonneg _) hdx _
    have hAnn : (0 : ℝ) ≤ ((zabs q + 1 : ℤ) : ℝ) := by
      have : 0 ≤ zabs q := by unfold zabs; split_ifs <;> omega
      exact_mod_cast (by omega : (0 : ℤ) ≤ zabs q + 1)
    have h1 : (SC : ℝ) * |ptZ D.Z (m + j) c * (y - c) ^ j / (j ! : ℝ)| ≤
        ((zabs q + 1 : ℤ) : ℝ) * (hh : ℝ) ^ j / ((TT : ℝ) ^ j * (j ! : ℝ)) := by
      rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
      have e : (SC : ℝ) * (|ptZ D.Z (m + j) c| * |y - c| ^ j / (j ! : ℝ)) =
          ((SC : ℝ) * |ptZ D.Z (m + j) c|) * |y - c| ^ j / (j ! : ℝ) := by ring
      rw [e]
      calc ((SC : ℝ) * |ptZ D.Z (m + j) c|) * |y - c| ^ j / (j ! : ℝ)
          ≤ ((zabs q + 1 : ℤ) : ℝ) * hR ^ j / (j ! : ℝ) := by
            apply div_le_div_of_nonneg_right _ hf.le
            exact mul_le_mul hA hp (by positivity) hAnn
        _ = _ := by simp only [hhR]; rw [div_pow]; field_simp
    refine le_trans h1 ?_
    obtain ⟨Cq, hCq⟩ : ∃ Cq : ℤ, Cq = cdiv ((zabs q + 1) * zpw hh j) (tf j) := ⟨_, rfl⟩
    rw [← hCq]
    have hdc := cdiv_cast_ge ((zabs q + 1) * zpw hh j) (tf j) hd
    rw [← hCq, zpw_eq hh j hh0, tf_eq j] at hdc
    push_cast at hdc
    push_cast
    rw [div_le_iff₀ (by positivity)]
    linarith [hdc]
  have hMn : 0 ≤ (MGL : ℝ) / SC := (abs_nonneg _).trans (hbd c ⟨by linarith, by linarith⟩)
  have hrem : (SC : ℝ) * |ptZ D.Z m y - S| ≤ (cdiv (MGL * zpw hh L) (tf L) : ℤ) := by
    have hf : (0 : ℝ) < (L ! : ℝ) := by positivity
    have hd : (0 : ℤ) < tf L := by
      rw [tf_eq L]
      have := TT_pos
      positivity
    obtain ⟨Cq, hCq⟩ : ∃ Cq : ℤ, Cq = cdiv (MGL * zpw hh L) (tf L) := ⟨_, rfl⟩
    rw [← hCq]
    have hdc := cdiv_cast_ge (MGL * zpw hh L) (tf L) hd
    rw [← hCq, zpw_eq hh L hh0, tf_eq L] at hdc
    push_cast at hdc
    have hp : |y - c| ^ L ≤ hR ^ L := pow_le_pow_left₀ (abs_nonneg _) hdx _
    have h2 : |ptZ D.Z m y - S| ≤ ((MGL : ℝ) / SC) * hR ^ L / (L ! : ℝ) := by
      refine htay.trans (div_le_div_of_nonneg_right ?_ hf.le)
      exact mul_le_mul_of_nonneg_left hp hMn
    have h3 : (SC : ℝ) * (((MGL : ℝ) / SC) * hR ^ L / (L ! : ℝ)) =
        (MGL : ℝ) * (hh : ℝ) ^ L / ((TT : ℝ) ^ L * (L ! : ℝ)) := by
      simp only [hhR]; rw [div_pow]; field_simp
    calc (SC : ℝ) * |ptZ D.Z m y - S| ≤ (SC : ℝ) * (((MGL : ℝ) / SC) * hR ^ L / (L ! : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hS.le
      _ = _ := h3
      _ ≤ _ := by
          rw [div_le_iff₀ (by positivity)]
          linarith [hdc]
  have hb1 : |ptZ D.Z m y| ≤ |S| + |ptZ D.Z m y - S| := by
    calc |ptZ D.Z m y| = |S + (ptZ D.Z m y - S)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  unfold PbV
  push_cast
  have := mul_le_mul_of_nonneg_left hb1 hS.le
  push_cast at hSb hrem
  linarith

theorem cellVal_sound (F : ℝ → ℝ) (ev : ℚ → Option (ℚ × ℚ)) (D : PolyData) (hD : D.Ok)
    (poles : List PoleR) (m L : ℕ) (MGL : ℤ)
    (hMGL : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m + L) y| ≤ (MGL : ℝ))
    (pe : Option ℚ) (cap : ℚ)
    (hev : ∀ q v e, ev q = some (v, e) → |(q : ℝ)| ≤ 1 → (∀ p ∈ poles, ((q : ℝ) : ℂ) ≠ p.pc) →
      F q ≤ (v : ℝ) + e)
    (hFc : ContinuousOn F {y : ℝ | |y| ≤ 1 ∧ ∀ q ∈ poles, (y : ℂ) ≠ q.pc})
    (hFd : ∀ y ∈ Ioo (-1 : ℝ) 1, (∀ p : ℚ, pe = some p → y ≠ (p : ℝ)) →
      (∀ q ∈ poles, (y : ℂ) ≠ q.pc) → HasDerivAt F (ftZ D.Z poles 0 y) y)
    (cc hh : ℤ) (h : cellVal ev D poles m L MGL pe cap (cc, hh) = true) :
    ∀ x : ℝ, |x - (cc : ℝ) / TT| ≤ (hh : ℝ) / TT → F x ≤ (cap : ℝ) := by
  intro x hx
  unfold cellVal at h
  simp only at h
  split at h
  · simp at h
  rename_i ve hve
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hmLV, hh0⟩, hlow⟩, hhigh⟩, hpeb⟩, hpos⟩, hineq⟩ := h
  have hT : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  have hS : (0 : ℝ) < SC := by exact_mod_cast SC_pos
  have hh0R : (0 : ℝ) ≤ hh := by exact_mod_cast hh0
  set V := polyValsD D cc (m + L) with hV
  set lo : ℚ := ((cc - hh : ℤ) : ℚ) / (TT : ℚ) with hlo
  set hi : ℚ := ((cc + hh : ℤ) : ℚ) / (TT : ℚ) with hhi
  set c : ℝ := (cc : ℝ) / TT with hc
  set hR : ℝ := (hh : ℝ) / TT with hhR
  have hloR : ((lo : ℚ) : ℝ) = c - hR := by
    simp only [hlo, hc, hhR]; push_cast; ring
  have hhiR : ((hi : ℚ) : ℝ) = c + hR := by
    simp only [hhi, hc, hhR]; push_cast; ring
  have hhR0 : 0 ≤ hR := by positivity
  set PB : ℤ := PbV D.N cc hh V m L MGL with hPB
  have hpe' : ∀ p : ℚ, pe = some p → ∀ y ∈ Ioo (c - hR) (c + hR), y ≠ (p : ℝ) := by
    intro p hp y hy hyp
    subst hp
    simp only [peOK, Bool.or_eq_true, decide_eq_true_eq] at hpeb
    rcases hpeb with h1 | h1
    · have : (p : ℝ) ≤ c - hR := by rw [← hloR]; exact_mod_cast h1
      linarith [hy.1]
    · have : c + hR ≤ (p : ℝ) := by rw [← hhiR]; exact_mod_cast h1
      linarith [hy.2]
  have hxI : x ∈ Icc (c - hR) (c + hR) := by
    have := abs_le.mp hx
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hcI : c ∈ Icc (c - hR) (c + hR) := ⟨by linarith, by linarith⟩
  have hgeo : ∀ y ∈ Icc (c - hR) (c + hR), ∀ q ∈ poles,
      0 < ((poleDl q lo hi : ℚ) : ℝ) ∧ ((poleDl q lo hi : ℚ) : ℝ) ≤ ‖(y : ℂ) - q.pc‖ := by
    intro y hy q hq
    refine ⟨by exact_mod_cast hpos q hq, dl_le_norm q lo hi y ?_ ?_⟩
    · rw [hloR]; exact hy.1
    · rw [hhiR]; exact hy.2
  have hne : ∀ y ∈ Icc (c - hR) (c + hR), ∀ q ∈ poles, (y : ℂ) ≠ q.pc := by
    intro y hy q hq heq
    have := hgeo y hy q hq
    rw [heq, sub_self, norm_zero] at this
    linarith [this.1, this.2]
  have hlow' : (-(TT : ℝ)) ≤ (cc : ℝ) - hh := by exact_mod_cast hlow
  have hhigh' : (cc : ℝ) + hh ≤ TT := by exact_mod_cast hhigh
  have e1 : c - hR = ((cc : ℝ) - hh) / TT := by simp only [hc, hhR]; ring
  have e2 : c + hR = ((cc : ℝ) + hh) / TT := by simp only [hc, hhR]; ring
  have g1 : (-1 : ℝ) ≤ c - hR := by rw [e1, le_div_iff₀ hT]; linarith
  have g2 : c + hR ≤ 1 := by rw [e2, div_le_iff₀ hT]; linarith
  have hyI : ∀ y ∈ Icc (c - hR) (c + hR), |y| ≤ 1 := by
    intro y hy
    rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  have hsub : Icc (c - hR) (c + hR) ⊆ Icc (-1 : ℝ) 1 :=
    fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- the tower
  let fT : ℕ → ℝ → ℝ := fun j => match j with | 0 => F | j + 1 => ftZ D.Z poles j
  have hcontT : ∀ j ≤ m + 1, ContinuousOn (fT j) (Icc (c - hR) (c + hR)) := by
    intro j _
    cases j with
    | zero => exact hFc.mono (fun y hy => ⟨hyI y hy, hne y hy⟩)
    | succ j =>
      intro y hy
      exact (hasDerivAt_ftZ D.Z poles j y (hne y hy)).continuousAt.continuousWithinAt
  have hderT : ∀ j < m + 1, ∀ y ∈ Ioo (c - hR) (c + hR), HasDerivAt (fT j) (fT (j + 1) y) y := by
    intro j _ y hy
    have hyc : y ∈ Icc (c - hR) (c + hR) := ⟨hy.1.le, hy.2.le⟩
    cases j with
    | zero =>
      exact hFd y ⟨by linarith [hy.1], by linarith [hy.2]⟩ (fun p hp => hpe' p hp y hy) (hne y hyc)
    | succ j => exact hasDerivAt_ftZ D.Z poles j y (hne y hyc)
  -- bound on ft m
  have hKm : ∀ y ∈ Icc (c - hR) (c + hR), (SC : ℝ) * |ptZ D.Z m y| ≤ (PB : ℤ) :=
    fun y hy => ptZ_local D hD cc hh m L MGL hMGL hmLV hh0 hlow hhigh y
      (abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  have hKq : ∀ y ∈ Icc (c - hR) (c + hR),
      (SC : ℝ) * |(poles.map (fun q => qt q m y)).sum| ≤ (MpoleV poles m lo hi : ℤ) := by
    intro y hy
    unfold MpoleV
    refine le_trans (mul_le_mul_of_nonneg_left (abs_list_sum_le poles _) hS.le) ?_
    rw [← List.sum_map_mul_left]
    refine list_sum_le_cast poles _ _ (fun q hq => ?_)
    obtain ⟨hdl, hle⟩ := hgeo y hy q hq
    have hb := qt_bound q m y _ hdl hle
    have hc' := le_qceil (SC * (qabs' q.rr + qabs' q.ri) * ((m ! : ℕ) : ℚ) / (poleDl q lo hi) ^ (m + 1))
    have hcR := (Rat.cast_le (K := ℝ)).mpr hc'
    rw [Rat.cast_intCast] at hcR
    refine le_trans ?_ hcR
    push_cast
    rw [qabs'_cast, qabs'_cast]
    have : (SC : ℝ) * (|(q.rr : ℝ)| + |(q.ri : ℝ)|) * (m ! : ℝ) / (((poleDl q lo hi : ℚ) : ℝ)) ^ (m + 1) =
        (SC : ℝ) * ((|(q.rr : ℝ)| + |(q.ri : ℝ)|) * (m ! : ℝ) / (((poleDl q lo hi : ℚ) : ℝ)) ^ (m + 1)) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hb hS.le
  have hMb : ∀ y ∈ Icc (c - hR) (c + hR),
      |fT (m + 1) y| ≤ ((MpoleV poles m lo hi + PB : ℤ) : ℝ) / SC := by
    intro y hy
    have h1 := hKm y hy
    have h2 := hKq y hy
    rw [le_div_iff₀ hS]
    show |ftZ D.Z poles m y| * SC ≤ _
    unfold ftZ
    have := abs_add_le (ptZ D.Z m y) ((poles.map (fun q => qt q m y)).sum)
    push_cast
    nlinarith [this, mul_le_mul_of_nonneg_left this hS.le]
  have htay := taylor_tower' c hR (((MpoleV poles m lo hi + PB : ℤ) : ℝ) / SC) (m + 1) fT hcontT hderT hMb x hxI
  rw [Finset.sum_range_succ'] at htay
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one, div_one] at htay
  set Mre : ℝ := ((MpoleV poles m lo hi + PB : ℤ) : ℝ) / SC with hMre
  set S : ℝ := ∑ j ∈ Finset.range m, ftZ D.Z poles j c * (x - c) ^ (j + 1) / ((j + 1)! : ℝ) with hS'
  have hdx : |x - c| ≤ hR := abs_le.mpr ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
  -- error of fhat
  have herr : ∀ j < m, |(SC : ℝ) * ftZ D.Z poles j c| ≤ |(fhatV D.N poles cc V j : ℝ)| + EcntV poles := by
    intro j hj
    obtain ⟨e1, e2⟩ := fhatV_err D hD poles cc (m + L) j hmLV (by omega)
    have hE : (0 : ℝ) ≤ EcntV poles := by unfold EcntV; positivity
    rw [abs_le]; constructor <;> cases abs_cases (fhatV D.N poles cc V j : ℝ) <;>
      linarith [neg_abs_le (fhatV D.N poles cc V j : ℝ), le_abs_self (fhatV D.N poles cc V j : ℝ)]
  -- bound S
  have hSb : (SC : ℝ) * |S| ≤ (BsumV D.N poles cc hh V m : ℤ) := by
    unfold BsumV
    rw [cast_list_sum_map, list_range_map_sum (fun a => (((cdiv ((zabs (fhatV D.N poles cc V a) + EcntV poles) *
      zpw hh (a + 1)) (tf (a + 1)) : ℤ)) : ℝ))]
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hS.le) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hjm => ?_)
    have hj : j < m := Finset.mem_range.mp hjm
    have hf : (0 : ℝ) < ((j + 1)! : ℝ) := by positivity
    have hd : (0 : ℤ) < tf (j + 1) := by
      rw [tf_eq (j + 1)]
      have := TT_pos
      positivity
    have hdc' : ((|(fhatV D.N poles cc V j : ℝ)| + EcntV poles) * (hh : ℝ) ^ (j + 1)) /
        ((TT : ℝ) ^ (j + 1) * ((j + 1)! : ℝ)) ≤
        ((cdiv ((zabs (fhatV D.N poles cc V j) + EcntV poles) * zpw hh (j + 1)) (tf (j + 1)) : ℤ) : ℝ) := by
      obtain ⟨Cq, hCq⟩ : ∃ Cq : ℤ, Cq = cdiv ((zabs (fhatV D.N poles cc V j) + EcntV poles) * zpw hh (j + 1))
        (tf (j + 1)) := ⟨_, rfl⟩
      rw [← hCq, div_le_iff₀ (by positivity)]
      have e := cdiv_cast_ge ((zabs (fhatV D.N poles cc V j) + EcntV poles) * zpw hh (j + 1))
        (tf (j + 1)) hd
      rw [← hCq, zpw_eq hh (j + 1) hh0, tf_eq (j + 1)] at e
      push_cast at e
      rw [zabs_cast] at e
      linarith [e]
    have h1 : (SC : ℝ) * |ftZ D.Z poles j c * (x - c) ^ (j + 1) / ((j + 1)! : ℝ)| ≤
        (|(fhatV D.N poles cc V j : ℝ)| + EcntV poles) * (hh : ℝ) ^ (j + 1) /
          ((TT : ℝ) ^ (j + 1) * ((j + 1)! : ℝ)) := by
      rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
      have e : (SC : ℝ) * (|ftZ D.Z poles j c| * |x - c| ^ (j + 1) / ((j + 1)! : ℝ)) =
          |(SC : ℝ) * ftZ D.Z poles j c| * |x - c| ^ (j + 1) / ((j + 1)! : ℝ) := by
        rw [abs_mul, abs_of_pos hS]; ring
      have hp : |x - c| ^ (j + 1) ≤ hR ^ (j + 1) := pow_le_pow_left₀ (abs_nonneg _) hdx _
      rw [e]
      calc |(SC : ℝ) * ftZ D.Z poles j c| * |x - c| ^ (j + 1) / ((j + 1)! : ℝ)
          ≤ (|(fhatV D.N poles cc V j : ℝ)| + EcntV poles) * hR ^ (j + 1) / ((j + 1)! : ℝ) := by
            apply div_le_div_of_nonneg_right _ hf.le
            exact mul_le_mul (herr j hj) hp (by positivity) (by
              have := abs_nonneg (fhatV D.N poles cc V j : ℝ)
              have : (0 : ℝ) ≤ EcntV poles := by unfold EcntV; positivity
              linarith)
        _ = _ := by
            simp only [hhR]; rw [div_pow]; field_simp
    exact le_trans h1 hdc'
  -- remainder
  have hMn : 0 ≤ Mre := by
    have := (abs_nonneg (fT (m + 1) c)).trans (hMb c hcI)
    exact this
  have hRb : (SC : ℝ) * |F x - (S + F c)| ≤
      (cdiv ((MpoleV poles m lo hi + PB) * zpw hh (m + 1)) (tf (m + 1)) : ℤ) := by
    have hf : (0 : ℝ) < ((m + 1)! : ℝ) := by positivity
    have hd : (0 : ℤ) < tf (m + 1) := by
      rw [tf_eq (m + 1)]
      have := TT_pos
      positivity
    obtain ⟨Cq, hCq⟩ : ∃ Cq : ℤ, Cq = cdiv ((MpoleV poles m lo hi + PB) * zpw hh (m + 1)) (tf (m + 1)) :=
      ⟨_, rfl⟩
    rw [← hCq]
    have hdc := cdiv_cast_ge ((MpoleV poles m lo hi + PB) * zpw hh (m + 1)) (tf (m + 1)) hd
    rw [← hCq, zpw_eq hh (m + 1) hh0, tf_eq (m + 1)] at hdc
    push_cast at hdc
    have hp : |x - c| ^ (m + 1) ≤ hR ^ (m + 1) := pow_le_pow_left₀ (abs_nonneg _) hdx _
    have h2 : |F x - (S + F c)| ≤ Mre * hR ^ (m + 1) / ((m + 1)! : ℝ) := by
      have : |F x - (S + F c)| ≤ Mre * |x - c| ^ (m + 1) / ((m + 1)! : ℝ) := by
        simpa [fT] using htay
      exact this.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hMn) hf.le)
    have h3 : (SC : ℝ) * (Mre * hR ^ (m + 1) / ((m + 1)! : ℝ)) =
        ((MpoleV poles m lo hi + PB : ℤ) : ℝ) * (hh : ℝ) ^ (m + 1) /
          ((TT : ℝ) ^ (m + 1) * ((m + 1)! : ℝ)) := by
      simp only [hMre, hhR]; push_cast; rw [div_pow]; field_simp
    calc (SC : ℝ) * |F x - (S + F c)| ≤ (SC : ℝ) * (Mre * hR ^ (m + 1) / ((m + 1)! : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hS.le
      _ = _ := h3
      _ ≤ _ := by
          rw [div_le_iff₀ (by positivity)]
          push_cast at hdc ⊢
          linarith [hdc]
  -- the value at the centre
  have hFcv : F c ≤ (ve.1 : ℝ) + ve.2 := by
    have e : (((cc : ℚ) / (TT : ℚ) : ℚ) : ℝ) = c := by simp only [hc]; push_cast; rfl
    have hq : |(((cc : ℚ) / (TT : ℚ) : ℚ) : ℝ)| ≤ 1 := by
      rw [e]; exact hyI c hcI
    have hnp : ∀ p ∈ poles, ((((cc : ℚ) / (TT : ℚ) : ℚ) : ℝ) : ℂ) ≠ p.pc := by
      intro p hp; rw [e]; exact hne c hcI p hp
    have := hev _ ve.1 ve.2 hve hq hnp
    rw [e] at this
    exact this
  have hq1 := le_qceil (SC * (ve.1 + ve.2))
  have hq1R : ((SC * (ve.1 + ve.2) : ℚ) : ℝ) ≤ ((qceil (SC * (ve.1 + ve.2)) : ℤ) : ℝ) := by
    exact_mod_cast hq1
  have hq2 := qfloor_le (SC * cap)
  have hq2R : ((qfloor (SC * cap) : ℤ) : ℝ) ≤ ((SC * cap : ℚ) : ℝ) := by
    have : (((qfloor (SC * cap) : ℤ) : ℚ) : ℝ) ≤ ((SC * cap : ℚ) : ℝ) := by exact_mod_cast hq2
    simpa using this
  have hineqR : ((qceil (SC * (ve.1 + ve.2)) : ℤ) : ℝ) + (BsumV D.N poles cc hh V m : ℤ) +
      (cdiv ((MpoleV poles m lo hi + PB) * zpw hh (m + 1)) (tf (m + 1)) : ℤ) ≤
        ((qfloor (SC * cap) : ℤ) : ℝ) := by exact_mod_cast hineq
  -- conclude
  have hb1 : F x ≤ F c + |S| + |F x - (S + F c)| := by
    have := le_abs_self (F x - (S + F c))
    have := le_abs_self S
    linarith
  have hb2 : (SC : ℝ) * F x ≤ (SC : ℝ) * F c + (SC : ℝ) * |S| + (SC : ℝ) * |F x - (S + F c)| := by
    have := mul_le_mul_of_nonneg_left hb1 hS.le
    nlinarith [this]
  have hb3 : (SC : ℝ) * F c ≤ (SC : ℝ) * ((ve.1 : ℝ) + ve.2) := mul_le_mul_of_nonneg_left hFcv hS.le
  have hb4 : (SC : ℝ) * ((ve.1 : ℝ) + ve.2) = ((SC * (ve.1 + ve.2) : ℚ) : ℝ) := by push_cast; ring
  have hb5 : ((SC * cap : ℚ) : ℝ) = (SC : ℝ) * cap := by push_cast; ring
  have : (SC : ℝ) * F x ≤ (SC : ℝ) * cap := by linarith
  exact le_of_mul_le_mul_left this hS


/-- global sup bound of the `m`-th derivative of the polynomial part, from an exact Chebyshev-T expansion -/
theorem poly_sup_of (Z : List ℤ) (m : ℕ) (Bs : List ℤ) (MG : ℤ) (N' : ℕ)
    (hid : tcomb Bs = zsc (2 ^ N') (wlist m Z))
    (hMG : decide (SC * (Bs.map zabs).sum ≤ MG * (2 ^ N' * K40)) = true)
    (y : ℝ) (hy : |y| ≤ 1) : (SC : ℝ) * |ptZ Z m y| ≤ (MG : ℝ) := by
  have hS : (0 : ℝ) < SC := by exact_mod_cast SC_pos
  have h1 := tcomb_bound Bs y hy
  obtain ⟨Sz, hSz⟩ : ∃ Sz, (Bs.map zabs).sum = Sz := ⟨_, rfl⟩
  rw [hSz] at hMG
  have hw : lev (wlist m Z) y = lev (lder^[m] Z) y := by rw [wlist_eq m Z]
  rw [hid, lev_zsc, hw, zl1_eq, hSz, abs_mul] at h1
  have hpt : ptZ Z m y = lev (lder^[m] Z) y / 1099511627776 := rfl
  have h2 : (SC * Sz : ℤ) ≤ MG * (2 ^ N' * K40) := of_decide_eq_true hMG
  have h2R : (SC : ℝ) * (Sz : ℝ) ≤ (MG : ℝ) * (2 ^ N' * 1099511627776) := by
    have := (Int.cast_le (R := ℝ)).mpr h2
    push_cast at this
    have hK : (K40 : ℝ) = 1099511627776 := by unfold K40; norm_num
    rw [hK] at this
    exact this
  have hp2 : (0 : ℝ) < 2 ^ N' := by positivity
  have h3 : |(2 : ℝ) ^ N'| = 2 ^ N' := abs_of_pos hp2
  push_cast at h1
  rw [h3] at h1
  rw [hpt, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1099511627776)]
  rw [mul_div_assoc', div_le_iff₀ (by norm_num : (0 : ℝ) < 1099511627776)]
  have h4 : (2 : ℝ) ^ N' * |lev (lder^[m] Z) y| * SC ≤ (Sz : ℝ) * SC :=
    mul_le_mul_of_nonneg_right h1 hS.le
  nlinarith [h2R, h4, hp2]

end CatalanMeasure.CellCert
