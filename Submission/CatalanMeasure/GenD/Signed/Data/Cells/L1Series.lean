module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Core

@[expose] public section

/-!
# Series window at an interior centre `c` (lane L1, 31 Oct 2026)

The sibling of `l0_series_sound` (`Data/Cells/Core.lean`) at a centre `c > 0` with the one-sided window
`[c - ρ, c]`.  Paper proof: `LEMMA-SERIES-AT-C.md`.  With `u = (c - x)/c ∈ [0, ρ/c]` and `y = c/x = 1/(1 - u)`:

* `l1_pow` (exact remainder): `y^s = P_s(u) + u^(n+1) R_s(y)` where `P_s` has the coefficients `l1Co n s`
  (`s`-fold prefix sums of `1, 0, ..., 0`, i.e. `C(s+k-1, k)`) and `R_0 = 0`, `R_(s+1) = y (R_s + Σ P_s coefficients)`.
  No binomial coefficients and no hockey-stick identity: one induction on `s` with the prefix-sum identity
  `(1 - u) · prefix(l)(u) = l(u) - u^|l| · Σ l`.
* `l1_laurent`: the Laurent coefficient `Σ a_s x^-s` is the polynomial `l1UAux` in `u` up to `K u^(n+1)`.
* `l1_ent_le`: per Laurent term (factors `1`, regular `log|αx - β|`, singular `log|x - c|`).
* `l1_series_sound`: the reduction of a Laurent field on `[c - ρ, c]` to a plain field (polynomial + plogs + poles).
-/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

/-! ### 1. The binomial series with exact remainder, by prefix sums -/

/-- prefix sums with a running accumulator -/
def l1Pre : ℚ → List ℚ → List ℚ
  | _, [] => []
  | acc, a :: as => (acc + a) :: l1Pre (acc + a) as

theorem l1Pre_length : ∀ (acc : ℚ) (l : List ℚ), (l1Pre acc l).length = l.length
  | _, [] => rfl
  | acc, a :: as => by simp [l1Pre, l1Pre_length (acc + a) as]

theorem l1Pre_eval (u : ℝ) : ∀ (acc : ℚ) (l : List ℚ),
    (1 - u) * polyTow (l1Pre acc l) 0 u =
      polyTow l 0 u + (acc : ℝ) - u ^ l.length * ((acc : ℝ) + ((l.sum : ℚ) : ℝ))
  | acc, [] => by simp [l1Pre, l0_nil]
  | acc, a :: as => by
      have ih := l1Pre_eval u (acc + a) as
      simp only [l1Pre, l0_cons, List.length_cons, List.sum_cons, Rat.cast_add] at ih ⊢
      linear_combination u * ih

theorem l1Pre_nonneg : ∀ (acc : ℚ) (l : List ℚ), 0 ≤ acc → (∀ q ∈ l, 0 ≤ q) →
    ∀ q ∈ l1Pre acc l, 0 ≤ q
  | _, [], _, _ => by simp [l1Pre]
  | acc, a :: as, h0, h => by
      intro q hq
      simp only [l1Pre, List.mem_cons] at hq
      have ha := h a (by simp)
      rcases hq with rfl | hq
      · linarith
      · exact l1Pre_nonneg (acc + a) as (by linarith) (fun r hr => h r (by simp [hr])) q hq

/-- the coefficients (in `u`) of the degree-`n` truncation of `(1 - u)^-s` -/
def l1Co (n : ℕ) : ℕ → List ℚ
  | 0 => 1 :: List.replicate n 0
  | s + 1 => l1Pre 0 (l1Co n s)

theorem l1Co_length (n : ℕ) : ∀ s, (l1Co n s).length = n + 1
  | 0 => by simp [l1Co]
  | s + 1 => by simp [l1Co, l1Pre_length, l1Co_length n s]

theorem l1Co_nonneg (n : ℕ) : ∀ s, ∀ q ∈ l1Co n s, 0 ≤ q
  | 0 => by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · norm_num
      · exact le_of_eq (List.eq_of_mem_replicate hq).symm
  | s + 1 => by
      intro q hq
      exact l1Pre_nonneg 0 _ le_rfl (l1Co_nonneg n s) q hq

/-- the rational remainder bound `R_s(Y)` -/
def l1Rb (Y : ℚ) (n : ℕ) : ℕ → ℚ
  | 0 => 0
  | s + 1 => Y * (l1Rb Y n s + (l1Co n s).sum)

/-- the remainder polynomial `R_s(y)` -/
noncomputable def l1Rr (y : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | s + 1 => y * (l1Rr y n s + (((l1Co n s).sum : ℚ) : ℝ))

theorem l1_pow (y u : ℝ) (n : ℕ) (hy : y * (1 - u) = 1) : ∀ s : ℕ,
    y ^ s = polyTow (l1Co n s) 0 u + u ^ (n + 1) * l1Rr y n s
  | 0 => by
      have h0 : polyTow (List.replicate n 0) 0 u = 0 :=
        l0_zeros _ (fun q hq => List.eq_of_mem_replicate hq) u
      simp [l1Co, l1Rr, l0_cons, h0]
  | s + 1 => by
      have ih := l1_pow y u n hy s
      have hA := l1Pre_eval u 0 (l1Co n s)
      rw [l1Co_length] at hA
      simp only [Rat.cast_zero, zero_add] at hA
      have e : l1Co n (s + 1) = l1Pre 0 (l1Co n s) := rfl
      rw [e]
      simp only [l1Rr]
      linear_combination y * ih + (-y) * hA + (polyTow (l1Pre 0 (l1Co n s)) 0 u) * hy

theorem l1_Rr_bound (y : ℝ) (Y : ℚ) (n : ℕ) (h0 : 0 ≤ y) (hY : y ≤ (Y : ℝ)) :
    ∀ s, 0 ≤ l1Rr y n s ∧ l1Rr y n s ≤ ((l1Rb Y n s : ℚ) : ℝ)
  | 0 => by simp [l1Rr, l1Rb]
  | s + 1 => by
      obtain ⟨a, b⟩ := l1_Rr_bound y Y n h0 hY s
      have ht : (0 : ℝ) ≤ (((l1Co n s).sum : ℚ) : ℝ) := by
        have : (0 : ℚ) ≤ (l1Co n s).sum := List.sum_nonneg (l1Co_nonneg n s)
        exact_mod_cast this
      simp only [l1Rr, l1Rb, Rat.cast_mul, Rat.cast_add]
      exact ⟨mul_nonneg h0 (add_nonneg a ht),
        mul_le_mul hY (add_le_add b le_rfl) (add_nonneg a ht) (h0.trans hY)⟩

theorem l1Rb_nonneg (Y : ℚ) (hY : 0 ≤ Y) (n : ℕ) : ∀ s, 0 ≤ l1Rb Y n s
  | 0 => by simp [l1Rb]
  | s + 1 => by
      have ih := l1Rb_nonneg Y hY n s
      have : (0 : ℚ) ≤ (l1Co n s).sum := List.sum_nonneg (l1Co_nonneg n s)
      simp only [l1Rb]
      exact mul_nonneg hY (add_nonneg ih this)

/-! ### 2. Affine substitution and the Laurent coefficient -/

/-- `q(p0 + p1 X)` as a polynomial in `X` -/
def l1Aff (p0 p1 : ℚ) : List ℚ → List ℚ
  | [] => []
  | q :: qs => vecAdd [q] (pmulQ [p0, p1] (l1Aff p0 p1 qs))

theorem l1Aff_eval (p0 p1 : ℚ) (x : ℝ) : ∀ q : List ℚ,
    polyTow (l1Aff p0 p1 q) 0 x = polyTow q 0 ((p0 : ℝ) + (p1 : ℝ) * x)
  | [] => by simp [l1Aff, l0_nil]
  | q :: qs => by
      rw [l1Aff, l0_vecAdd, l0_pmul, l1Aff_eval p0 p1 x qs, l0_cons q qs]
      simp only [l0_cons, l0_nil]
      ring

/-- the Laurent coefficient `Σ_s a_(s0+s) x^-(s0+s)` as a polynomial in `u = (c - x)/c` -/
def l1UAux (c : ℚ) (n : ℕ) : ℕ → List ℚ → List ℚ
  | _, [] => []
  | s, a :: as => vecAdd ((l1Co n s).map (fun t => (a * (c⁻¹) ^ s) * t)) (l1UAux c n (s + 1) as)

/-- the error constant `Σ |a_s| c^-s R_s(Y)` -/
def l1KAux (Y c : ℚ) (n : ℕ) : ℕ → List ℚ → ℚ
  | _, [] => 0
  | s, a :: as => qabs' a * (c⁻¹) ^ s * l1Rb Y n s + l1KAux Y c n (s + 1) as

theorem l1_laurent (c Y : ℚ) (n : ℕ) (x y u : ℝ) (hc : (0 : ℝ) < c)
    (hyx : y = (c : ℝ) * x⁻¹) (hyu : y * (1 - u) = 1) (hu : 0 ≤ u) (hy0 : 0 ≤ y) (hyY : y ≤ (Y : ℝ)) :
    ∀ (a : List ℚ) (s : ℕ),
      |x⁻¹ ^ s * polyTow a 0 x⁻¹ - polyTow (l1UAux c n s a) 0 u| ≤
        ((l1KAux Y c n s a : ℚ) : ℝ) * u ^ (n + 1)
  | [], s => by simp [l1UAux, l1KAux, l0_nil]
  | a :: as, s => by
      have ih := l1_laurent c Y n x y u hc hyx hyu hu hy0 hyY as (s + 1)
      have hp := l1_pow y u n hyu s
      have hb := l1_Rr_bound y Y n hy0 hyY s
      have hxs : x⁻¹ ^ s = (c : ℝ)⁻¹ ^ s * y ^ s := by
        rw [hyx, ← mul_pow, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      have e1 : polyTow (l1UAux c n s (a :: as)) 0 u =
          (a : ℝ) * (c : ℝ)⁻¹ ^ s * polyTow (l1Co n s) 0 u + polyTow (l1UAux c n (s + 1) as) 0 u := by
        simp only [l1UAux, l0_vecAdd, l0_map_mul]
        first | (push_cast; ring) | push_cast
      have e2 : polyTow (a :: as) 0 x⁻¹ = (a : ℝ) + x⁻¹ * polyTow as 0 x⁻¹ := l0_cons a as x⁻¹
      have key : x⁻¹ ^ s * polyTow (a :: as) 0 x⁻¹ - polyTow (l1UAux c n s (a :: as)) 0 u =
          (a : ℝ) * (c : ℝ)⁻¹ ^ s * (u ^ (n + 1) * l1Rr y n s) +
            (x⁻¹ ^ (s + 1) * polyTow as 0 x⁻¹ - polyTow (l1UAux c n (s + 1) as) 0 u) := by
        rw [e1, e2]
        linear_combination (a : ℝ) * hxs + (a : ℝ) * (c : ℝ)⁻¹ ^ s * hp
      rw [key]
      refine (abs_add_le _ _).trans ?_
      have hcs : 0 ≤ (c : ℝ)⁻¹ ^ s := pow_nonneg (inv_nonneg.mpr hc.le) s
      have hus : 0 ≤ u ^ (n + 1) := pow_nonneg hu _
      have hK : |(a : ℝ) * (c : ℝ)⁻¹ ^ s * (u ^ (n + 1) * l1Rr y n s)| ≤
          ((qabs' a * (c⁻¹) ^ s * l1Rb Y n s : ℚ) : ℝ) * u ^ (n + 1) := by
        have hA : 0 ≤ |(a : ℝ)| * (c : ℝ)⁻¹ ^ s * u ^ (n + 1) :=
          mul_nonneg (mul_nonneg (abs_nonneg _) hcs) hus
        have e3 : |(a : ℝ) * (c : ℝ)⁻¹ ^ s * (u ^ (n + 1) * l1Rr y n s)| =
            |(a : ℝ)| * (c : ℝ)⁻¹ ^ s * (u ^ (n + 1) * l1Rr y n s) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hcs, abs_of_nonneg (mul_nonneg hus hb.1)]
        rw [e3]
        push_cast
        rw [qabs'_cast]
        have := mul_le_mul_of_nonneg_left hb.2 hA
        nlinarith [this]
      have : ((l1KAux Y c n s (a :: as) : ℚ) : ℝ) * u ^ (n + 1) =
          ((qabs' a * (c⁻¹) ^ s * l1Rb Y n s : ℚ) : ℝ) * u ^ (n + 1) +
            ((l1KAux Y c n (s + 1) as : ℚ) : ℝ) * u ^ (n + 1) := by
        simp only [l1KAux, Rat.cast_add]; ring
      rw [this]
      linarith

/-! ### 3. Elementary logarithm bounds -/

theorem l1_abslog_le (z : ℝ) (hz : 0 < z) : |Real.log z| ≤ z + z⁻¹ := by
  have hi := inv_pos.mpr hz
  rw [abs_le]
  constructor
  · have := Real.one_sub_inv_le_log_of_pos hz
    linarith
  · have := Real.log_le_sub_one_of_pos hz
    linarith

theorem l1_conv (p q s v : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hp : 0 < p) (hq : 0 < q)
    (hv : v = (1 - s) * p + s * q) : 0 < v ∧ v ≤ p + q ∧ v⁻¹ ≤ p⁻¹ + q⁻¹ := by
  have h1 : 0 ≤ 1 - s := by linarith
  have hvpos : 0 < v := by
    rw [hv]
    rcases hs0.eq_or_lt with h | h
    · rw [← h]; nlinarith
    · nlinarith [mul_pos h hq, mul_nonneg h1 hp.le]
  refine ⟨hvpos, ?_, ?_⟩
  · rw [hv]; nlinarith [mul_nonneg hs0 hp.le, mul_nonneg h1 hq.le]
  · have hpi := inv_pos.mpr hp
    have hqi := inv_pos.mpr hq
    rcases le_total p q with h | h
    · have : p ≤ v := by rw [hv]; nlinarith [mul_nonneg hs0 (sub_nonneg.2 h)]
      linarith [inv_anti₀ hp this]
    · have : q ≤ v := by rw [hv]; nlinarith [mul_nonneg h1 (sub_nonneg.2 h)]
      linarith [inv_anti₀ hq this]

theorem l1_R (α β c ρ x : ℝ) (hρ : 0 < ρ) (hl : c - ρ ≤ x) (hr : x ≤ c)
    (hpq : 0 < (α * (c - ρ) - β) * (α * c - β)) :
    α * x - β ≠ 0 ∧ |α * x - β| ≤ |α * (c - ρ) - β| + |α * c - β| ∧
      |α * x - β|⁻¹ ≤ |α * (c - ρ) - β|⁻¹ + |α * c - β|⁻¹ := by
  have hρ0 : ρ ≠ 0 := hρ.ne'
  set p := α * (c - ρ) - β with hp
  set q := α * c - β with hq
  set s := (x - (c - ρ)) / ρ with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hρ.le
  have hs1 : s ≤ 1 := by rw [hs, div_le_one hρ]; linarith
  have hv : α * x - β = (1 - s) * p + s * q := by
    have : s * ρ = x - (c - ρ) := by rw [hs]; field_simp
    rw [hp, hq]; linear_combination (-α) * this
  rcases lt_trichotomy p 0 with hp0 | hp0 | hp0
  · have hq0 : q < 0 := by by_contra h; push_neg at h; nlinarith
    obtain ⟨h1, h2, h3⟩ := l1_conv (-p) (-q) s (-(α * x - β)) hs0 hs1 (by linarith) (by linarith)
      (by rw [hv]; ring)
    have e1 : |α * x - β| = -(α * x - β) := abs_of_neg (by linarith)
    have e2 : |p| = -p := abs_of_neg hp0
    have e3 : |q| = -q := abs_of_neg hq0
    rw [e1, e2, e3]
    exact ⟨by intro h; rw [h] at h1; simp at h1, h2, h3⟩
  · rw [hp0] at hpq; simp at hpq
  · have hq0 : 0 < q := by by_contra h; push_neg at h; nlinarith
    obtain ⟨h1, h2, h3⟩ := l1_conv p q s (α * x - β) hs0 hs1 hp0 hq0 hv
    rw [abs_of_pos h1, abs_of_pos hp0, abs_of_pos hq0]
    exact ⟨h1.ne', h2, h3⟩

theorem l1_S_bound (c ρ K : ℝ) (n : ℕ) (E x : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hK : 0 ≤ K) (hl : c - ρ ≤ x) (hr : x ≤ c) (hE : |E| ≤ K * ((c - x) / c) ^ (n + 1)) :
    |E * Real.log (|x - c|)| ≤ K * (c⁻¹) ^ (n + 1) * ρ ^ n := by
  have hRHS : 0 ≤ K * (c⁻¹) ^ (n + 1) * ρ ^ n :=
    mul_nonneg (mul_nonneg hK (pow_nonneg (inv_nonneg.mpr hc.le) _)) (pow_nonneg hρ.le _)
  set t := c - x with ht
  have ht0 : 0 ≤ t := by linarith
  have htρ : t ≤ ρ := by linarith
  have habs : |x - c| = t := by rw [abs_sub_comm, abs_of_nonneg ht0]
  rw [habs]
  rcases ht0.eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using hRHS
  · have hlog1 : Real.log t ≤ 0 := Real.log_nonpos hpos.le (htρ.trans hρ1)
    have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at hi
    have hmul := mul_inv_cancel₀ hpos.ne'
    have hT : t * |Real.log t| ≤ 1 := by
      rw [abs_of_nonpos hlog1]
      nlinarith [mul_le_mul_of_nonneg_left hi hpos.le, hmul]
    have hn : t ^ n ≤ ρ ^ n := pow_le_pow_left₀ ht0 htρ n
    have hcn : 0 ≤ (c⁻¹) ^ (n + 1) := pow_nonneg (inv_nonneg.mpr hc.le) _
    have e : (t / c) ^ (n + 1) = (c⁻¹) ^ (n + 1) * t ^ n * t := by
      rw [div_eq_mul_inv, mul_pow, pow_succ t n]; ring
    rw [abs_mul]
    have h1 : |E| * |Real.log t| ≤ K * (t / c) ^ (n + 1) * |Real.log t| :=
      mul_le_mul_of_nonneg_right hE (abs_nonneg _)
    have h2 : K * (t / c) ^ (n + 1) * |Real.log t| =
        K * (c⁻¹) ^ (n + 1) * t ^ n * (t * |Real.log t|) := by rw [e]; ring
    have h3 : K * (c⁻¹) ^ (n + 1) * t ^ n * (t * |Real.log t|) ≤ K * (c⁻¹) ^ (n + 1) * t ^ n := by
      have hnn : 0 ≤ K * (c⁻¹) ^ (n + 1) * t ^ n :=
        mul_nonneg (mul_nonneg hK hcn) (pow_nonneg ht0 _)
      nlinarith [mul_le_mul_of_nonneg_left hT hnn]
    have h4 : K * (c⁻¹) ^ (n + 1) * t ^ n ≤ K * (c⁻¹) ^ (n + 1) * ρ ^ n :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg hK hcn)
    linarith

/-- the algebraic core of the per-term bound -/
theorem l1_split (Pv E Lg Lx lam eta Pb B : ℝ) (hPv : |Pv| ≤ Pb)
    (hd : |(Lg - Lx) - lam| ≤ eta) (hEL : |E * Lg| ≤ B) :
    (Pv + E) * Lg ≤ Pv * Lx + lam * Pv + (eta * Pb + B) := by
  have h1 : |Pv * ((Lg - Lx) - lam)| ≤ Pb * eta := by
    rw [abs_mul]
    exact mul_le_mul hPv hd (abs_nonneg _) ((abs_nonneg _).trans hPv)
  have h2 := (abs_le.mp h1).2
  have h3 := (abs_le.mp hEL).2
  nlinarith [h2, h3]

/-! ### 4. Terms, the checker and the data of the plain field -/

/-- a Laurent term together with the rational `lam` and its error `eta`
(`|log|α| - lam| ≤ eta` for the factor `log|αx - β|`) -/
abbrev L1Ent := LTerm × ℚ × ℚ

def l1Y (c ρ : ℚ) : ℚ := c / (c - ρ)

/-- the main polynomial of a Laurent coefficient, in the variable `x` -/
def l1Pl (c : ℚ) (n : ℕ) (a : List ℚ) : List ℚ := l1Aff 1 (-(c⁻¹)) (l1UAux c n 0 a)

def l1K (c ρ : ℚ) (n : ℕ) (a : List ℚ) : ℚ := l1KAux (l1Y c ρ) c n 0 a

/-- the bound for `|log z|` on the window, `z + 1/z` over the endpoints -/
def l1Lam (α β c ρ : ℚ) : ℚ :=
  qabs' (α * (c - ρ) - β) + qabs' (α * c - β) + (qabs' (α * (c - ρ) - β))⁻¹ + (qabs' (α * c - β))⁻¹

def l1FOk (c ρ : ℚ) : Option (ℚ × ℚ) → Bool
  | none => true
  | some (α, β) =>
      if α = 0 then decide (β = 1 ∨ β = -1)
      else if α = 1 ∧ β = c then decide (ρ ≤ 1)
      else decide (0 < (α * (c - ρ) - β) * (α * c - β))

def l1EntOk (c ρ : ℚ) (e : L1Ent) : Bool := l1FOk c ρ e.1.2

def l1OK (c ρ : ℚ) (es : List L1Ent) : Bool :=
  decide (0 < ρ) && decide (ρ < c) && es.all (l1EntOk c ρ)

def l1PolyF (c : ℚ) (n : ℕ) (a : List ℚ) (lam : ℚ) : Option (ℚ × ℚ) → List ℚ
  | none => l1Pl c n a
  | some (α, _) => if α = 0 then [] else (l1Pl c n a).map (fun t => lam * t)

def l1PlogF (c : ℚ) (n : ℕ) (a : List ℚ) : Option (ℚ × ℚ) → List (List ℚ × ℚ)
  | none => []
  | some (α, β) => if α = 0 then [] else [(l1Pl c n a, β / α)]

def l1ErrF (c ρ : ℚ) (n : ℕ) (a : List ℚ) (eta : ℚ) : Option (ℚ × ℚ) → ℚ
  | none => l1K c ρ n a * (ρ / c) ^ (n + 1)
  | some (α, β) =>
      if α = 0 then 0 else
      (if α = 1 ∧ β = c then l1K c ρ n a * (c⁻¹) ^ (n + 1) * ρ ^ n
        else l1K c ρ n a * (ρ / c) ^ (n + 1) * l1Lam α β c ρ) + eta * polyAB (l1Pl c n a) c ρ

/-- the polynomial added to the plain field -/
def l1Poly (c : ℚ) (n : ℕ) : List L1Ent → List ℚ
  | [] => []
  | e :: es => vecAdd (l1PolyF c n e.1.1 e.2.1 e.1.2) (l1Poly c n es)

/-- the plogs added to the plain field -/
def l1Plogs (c : ℚ) (n : ℕ) : List L1Ent → List (List ℚ × ℚ)
  | [] => []
  | e :: es => l1PlogF c n e.1.1 e.1.2 ++ l1Plogs c n es

/-- the rational error -/
def l1Err (c ρ : ℚ) (n : ℕ) : List L1Ent → ℚ
  | [] => 0
  | e :: es => l1ErrF c ρ n e.1.1 e.2.2 e.1.2 + l1Err c ρ n es

/-! ### 5. The coefficient approximation on the window -/

theorem l1_E_le (c ρ : ℚ) (n : ℕ) (a : List ℚ) (hρ : 0 < ρ) (hρc : ρ < c) (x : ℝ)
    (hl : (c : ℝ) - ρ ≤ x) (hr : x ≤ c) :
    |polyTow a 0 x⁻¹ - polyTow (l1Pl c n a) 0 x| ≤ (l1K c ρ n a : ℝ) * (((c : ℝ) - x) / c) ^ (n + 1) := by
  have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hρc' : (ρ : ℝ) < c := by exact_mod_cast hρc
  have hc : (0 : ℝ) < c := by linarith
  have hx : 0 < x := by linarith
  have hc0 : (c : ℝ) ≠ 0 := hc.ne'
  have hx0 : x ≠ 0 := hx.ne'
  set u : ℝ := ((c : ℝ) - x) / c with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hc.le
  have hyu : (c : ℝ) * x⁻¹ * (1 - u) = 1 := by
    rw [hu]
    first | (field_simp; done) | (field_simp; ring)
  have hy0 : 0 ≤ (c : ℝ) * x⁻¹ := mul_nonneg hc.le (inv_nonneg.2 hx.le)
  have hyY : (c : ℝ) * x⁻¹ ≤ ((l1Y c ρ : ℚ) : ℝ) := by
    have h1 : x⁻¹ ≤ ((c : ℝ) - ρ)⁻¹ := inv_anti₀ (by linarith) hl
    have h2 := mul_le_mul_of_nonneg_left h1 hc.le
    unfold l1Y
    push_cast
    rw [div_eq_mul_inv]
    exact h2
  have hlau := l1_laurent c (l1Y c ρ) n x ((c : ℝ) * x⁻¹) u hc rfl hyu hu0 hy0 hyY a 0
  simp only [pow_zero, one_mul] at hlau
  have hev : polyTow (l1Pl c n a) 0 x = polyTow (l1UAux c n 0 a) 0 u := by
    unfold l1Pl
    rw [l1Aff_eval]
    congr 1
    rw [hu]
    push_cast
    first | (field_simp; done) | (field_simp; ring)
  rw [hev]
  exact hlau

theorem l1_K_nonneg (c ρ : ℚ) (n : ℕ) (hρ : 0 < ρ) (hρc : ρ < c) (a : List ℚ) :
    0 ≤ l1K c ρ n a := by
  have hc : 0 < c := by linarith
  have hY : 0 ≤ l1Y c ρ := by
    unfold l1Y; exact div_nonneg hc.le (by linarith)
  have key : ∀ (l : List ℚ) (s : ℕ), 0 ≤ l1KAux (l1Y c ρ) c n s l := by
    intro l
    induction l with
    | nil => intro s; simp [l1KAux]
    | cons b bs ih =>
        intro s
        simp only [l1KAux]
        have h1 : 0 ≤ qabs' b := by unfold qabs'; split_ifs <;> linarith
        have h2 : 0 ≤ (c⁻¹) ^ s := pow_nonneg (inv_nonneg.mpr hc.le) s
        exact add_nonneg (mul_nonneg (mul_nonneg h1 h2) (l1Rb_nonneg _ hY n s)) (ih (s + 1))
  exact key a 0

/-! ### 6. One term -/

theorem l1_ent_le (c ρ : ℚ) (n : ℕ) (a : List ℚ) (F : Option (ℚ × ℚ)) (lam eta : ℚ)
    (hρ : 0 < ρ) (hρc : ρ < c) (hok : l1FOk c ρ F = true)
    (hlog : ∀ (α β : ℚ), F = some (α, β) → |Real.log |(α : ℝ)| - (lam : ℝ)| ≤ (eta : ℝ))
    (x : ℝ) (hl : (c : ℝ) - ρ ≤ x) (hr : x ≤ c) :
    polyTow a 0 x⁻¹ * lfTower F 0 x ≤
      polyTow (l1PolyF c n a lam F) 0 x + plogSumTower (l1PlogF c n a F) 0 x +
        ((l1ErrF c ρ n a eta F : ℚ) : ℝ) := by
  have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hρc' : (ρ : ℝ) < c := by exact_mod_cast hρc
  have hc : (0 : ℝ) < c := by linarith
  have hx : 0 < x := by linarith
  have hE := l1_E_le c ρ n a hρ hρc x hl hr
  have hK : (0 : ℝ) ≤ (l1K c ρ n a : ℝ) := by exact_mod_cast l1_K_nonneg c ρ n hρ hρc a
  set P := polyTow (l1Pl c n a) 0 x with hP
  set E := polyTow a 0 x⁻¹ - P with hEdef
  have hax : polyTow a 0 x⁻¹ = P + E := by rw [hEdef]; ring
  have hu0 : 0 ≤ ((c : ℝ) - x) / c := div_nonneg (by linarith) hc.le
  have hu1 : ((c : ℝ) - x) / c ≤ (ρ : ℝ) / c :=
    (div_le_div_iff_of_pos_right hc).mpr (by linarith)
  have hEρ : |E| ≤ (l1K c ρ n a : ℝ) * ((ρ : ℝ) / c) ^ (n + 1) :=
    hE.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0 hu1 _) hK)
  rcases F with _ | ⟨α, β⟩
  · have e1 : lfTower none 0 x = 1 := rfl
    have e2 : plogSumTower (l1PlogF c n a none) 0 x = 0 := by simp [l1PlogF, plogSumTower]
    have e3 : l1PolyF c n a lam none = l1Pl c n a := rfl
    have e4 : ((l1ErrF c ρ n a eta none : ℚ) : ℝ) = (l1K c ρ n a : ℝ) * ((ρ : ℝ) / c) ^ (n + 1) := by
      simp [l1ErrF]
    rw [e1, e2, e3, e4, hax, mul_one, ← hP]
    have := (abs_le.mp hEρ).2
    linarith
  · by_cases hZ : α = 0
    · -- the factor is identically `log 1 = 0`
      subst hZ
      have hβ : β = 1 ∨ β = -1 := by simpa [l1FOk] using hok
      have hlf : lfTower (some (0, β)) 0 x = 0 := by
        show Real.log |((0 : ℚ) : ℝ) * x - (β : ℝ)| = 0
        rcases hβ with rfl | rfl <;> simp
      have e3 : l1PolyF c n a lam (some (0, β)) = [] := by simp [l1PolyF]
      have e4 : l1PlogF c n a (some (0, β)) = [] := by simp [l1PlogF]
      have e5 : l1ErrF c ρ n a eta (some (0, β)) = 0 := by simp [l1ErrF]
      rw [hlf, e3, e4, e5, mul_zero, l0_nil]
      simp [plogSumTower]
    have hpoly : l1PolyF c n a lam (some (α, β)) = (l1Pl c n a).map (fun t => lam * t) := by
      simp only [l1PolyF, if_neg hZ]
    have hplog : plogSumTower (l1PlogF c n a (some (α, β))) 0 x =
        P * Real.log |x - ((β / α : ℚ) : ℝ)| := by
      simp [l1PlogF, hZ, plogSumTower, mulTower_zero, logTower_zero_eq, hP]
    have hlf : lfTower (some (α, β)) 0 x = Real.log |(α : ℝ) * x - (β : ℝ)| := rfl
    have hPab : |P| ≤ ((polyAB (l1Pl c n a) c ρ : ℚ) : ℝ) :=
      (polyTow_range (l1Pl c n a) c ρ x (by rw [abs_le]; constructor <;> linarith)).2
    rw [hpoly, hplog, l0_map_mul, ← hP, hlf, hax]
    by_cases hS : α = 1 ∧ β = c
    · obtain ⟨hα1, hβc⟩ := hS
      subst hα1
      subst β
      have hρ1 : ρ ≤ 1 := by simpa [l1FOk] using hok
      have hlg := hlog 1 c rfl
      have hSS : (1 : ℚ) = 1 ∧ c = c := ⟨rfl, rfl⟩
      have herr : ((l1ErrF c ρ n a eta (some (1, c)) : ℚ) : ℝ) =
          (l1K c ρ n a : ℝ) * ((c : ℝ)⁻¹) ^ (n + 1) * (ρ : ℝ) ^ n +
            (eta : ℝ) * ((polyAB (l1Pl c n a) c ρ : ℚ) : ℝ) := by
        have e0 : l1ErrF c ρ n a eta (some (1, c)) =
            l1K c ρ n a * (c⁻¹) ^ (n + 1) * ρ ^ n + eta * polyAB (l1Pl c n a) c ρ := by
          simp [l1ErrF]
        rw [e0]
        push_cast
        ring
      have eL : Real.log |((1 : ℚ) : ℝ) * x - (c : ℝ)| = Real.log |x - (c : ℝ)| := by simp
      have eX : Real.log |x - (((c / 1 : ℚ)) : ℝ)| = Real.log |x - (c : ℝ)| := by simp
      rw [eL, eX]
      have hd : |(Real.log |x - (c : ℝ)| - Real.log |x - (c : ℝ)|) - (lam : ℝ)| ≤ (eta : ℝ) := by
        simpa using hlg
      have hEL := l1_S_bound c ρ _ n E x hc hρ' (by exact_mod_cast hρ1) hK hl hr hE
      have := l1_split P E (Real.log |x - (c : ℝ)|) (Real.log |x - (c : ℝ)|)
        lam eta (((polyAB (l1Pl c n a) c ρ : ℚ) : ℝ))
        ((l1K c ρ n a : ℝ) * ((c : ℝ)⁻¹) ^ (n + 1) * (ρ : ℝ) ^ n) hPab hd hEL
      rw [herr]
      linarith
    · have hpq : 0 < (α * (c - ρ) - β) * (α * c - β) := by
        simp only [l1FOk, if_neg hZ, if_neg hS, decide_eq_true_eq] at hok
        exact hok
      have hα : α ≠ 0 := hZ
      have hα' : (α : ℝ) ≠ 0 := by exact_mod_cast hα
      have hpq' : 0 < ((α : ℝ) * ((c : ℝ) - ρ) - β) * ((α : ℝ) * c - β) := by exact_mod_cast hpq
      obtain ⟨hne, hM, hm⟩ := l1_R α β c ρ x hρ' hl hr hpq'
      have hxne : x - (β : ℝ) / α ≠ 0 := by
        intro h
        apply hne
        have : (α : ℝ) * (x - (β : ℝ) / α) = 0 := by rw [h]; ring
        have e : (α : ℝ) * (x - (β : ℝ) / α) = α * x - β := by
          first | (field_simp; done) | (field_simp; ring)
        linarith
      have habs : |(α : ℝ) * x - β| = |(α : ℝ)| * |x - (β : ℝ) / α| := by
        rw [← abs_mul]; congr 1
        first | (field_simp; done) | (field_simp; ring)
      have hLg : Real.log |(α : ℝ) * x - (β : ℝ)| =
          Real.log |(α : ℝ)| + Real.log |x - (β : ℝ) / α| := by
        rw [habs, Real.log_mul (abs_ne_zero.mpr hα') (abs_ne_zero.mpr hxne)]
      have hLx : Real.log |x - ((β / α : ℚ) : ℝ)| = Real.log |x - (β : ℝ) / α| := by
        rw [Rat.cast_div]
      have hlg := hlog α β rfl
      have hd : |(Real.log |(α : ℝ) * x - (β : ℝ)| - Real.log |x - ((β / α : ℚ) : ℝ)|) - (lam : ℝ)|
          ≤ (eta : ℝ) := by
        rw [hLx, hLg]
        have : Real.log |(α : ℝ)| + Real.log |x - (β : ℝ) / α| - Real.log |x - (β : ℝ) / α| - lam
            = Real.log |(α : ℝ)| - lam := by ring
        rw [this]; exact hlg
      -- the bound for |E log|αx-β||
      have hz : 0 < |(α : ℝ) * x - β| := abs_pos.mpr hne
      have hlogb := l1_abslog_le _ hz
      have hLam : |(α : ℝ) * x - β| + |(α : ℝ) * x - β|⁻¹ ≤ ((l1Lam α β c ρ : ℚ) : ℝ) := by
        unfold l1Lam
        push_cast
        rw [qabs'_cast, qabs'_cast]
        push_cast
        linarith
      have hEL : |E * Real.log (|(α : ℝ) * x - (β : ℝ)|)| ≤
          (l1K c ρ n a : ℝ) * ((ρ : ℝ) / c) ^ (n + 1) * ((l1Lam α β c ρ : ℚ) : ℝ) := by
        rw [abs_mul]
        exact mul_le_mul hEρ (hlogb.trans hLam) (abs_nonneg _)
          (mul_nonneg hK (pow_nonneg (div_nonneg hρ'.le hc.le) _))
      have herr : ((l1ErrF c ρ n a eta (some (α, β)) : ℚ) : ℝ) =
          (l1K c ρ n a : ℝ) * ((ρ : ℝ) / c) ^ (n + 1) * ((l1Lam α β c ρ : ℚ) : ℝ) +
            (eta : ℝ) * ((polyAB (l1Pl c n a) c ρ : ℚ) : ℝ) := by
        simp only [l1ErrF, if_neg hZ, if_neg hS]
        first | (push_cast; ring) | push_cast
      have := l1_split P E (Real.log |(α : ℝ) * x - (β : ℝ)|) (Real.log |x - ((β / α : ℚ) : ℝ)|)
        lam eta (((polyAB (l1Pl c n a) c ρ : ℚ) : ℝ))
        ((l1K c ρ n a : ℝ) * ((ρ : ℝ) / c) ^ (n + 1) * ((l1Lam α β c ρ : ℚ) : ℝ)) hPab hd hEL
      rw [herr]
      linarith

/-! ### 7. The list of terms and the window theorem -/

theorem l1_plogSum_append (l₁ l₂ : List (List ℚ × ℚ)) (x : ℝ) :
    plogSumTower (l₁ ++ l₂) 0 x = plogSumTower l₁ 0 x + plogSumTower l₂ 0 x := by
  simp [plogSumTower, List.map_append, List.sum_append]

theorem l1_list_le (c ρ : ℚ) (n : ℕ) (hρ : 0 < ρ) (hρc : ρ < c) (x : ℝ)
    (hl : (c : ℝ) - ρ ≤ x) (hr : x ≤ c) :
    ∀ es : List L1Ent, es.all (l1EntOk c ρ) = true →
      (∀ e ∈ es, ∀ (α β : ℚ), e.1.2 = some (α, β) → |Real.log |(α : ℝ)| - (e.2.1 : ℝ)| ≤ (e.2.2 : ℝ)) →
      lfieldTower (es.map Prod.fst) 0 x ≤
        polyTow (l1Poly c n es) 0 x + plogSumTower (l1Plogs c n es) 0 x + ((l1Err c ρ n es : ℚ) : ℝ)
  | [], _, _ => by
      simp [lfieldTower_nil_zero, l1Poly, l1Plogs, l1Err, l0_nil, plogSumTower]
  | e :: es, hall, hlog => by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have ih := l1_list_le c ρ n hρ hρc x hl hr es hall.2 (fun e' he' => hlog e' (by simp [he']))
      have h1 := l1_ent_le c ρ n e.1.1 e.1.2 e.2.1 e.2.2 hρ hρc hall.1
        (fun α β h => hlog e (by simp) α β h) x hl hr
      have e1 : lfieldTower ((e :: es).map Prod.fst) 0 x =
          polyTow e.1.1 0 x⁻¹ * lfTower e.1.2 0 x + lfieldTower (es.map Prod.fst) 0 x := by
        exact lf_cons e.1 (es.map Prod.fst) x
      rw [e1]
      simp only [l1Poly, l1Plogs, l1Err, l0_vecAdd, l1_plogSum_append, Rat.cast_add]
      linarith

/-- **Series window at `c`, soundness, pointwise bound `g`.**  `fq'` is a Laurent-free field with the plogs `fq.plogs ++ l1Plogs`, the
poles of `fq`, and a polynomial within `δ` (on `[c - ρ, c]`) of `fq.poly + l1Poly`.  A bound `T` of `fq'` on a
subset `S ⊆ [c - ρ, c]` gives the bound `T + δ + l1Err` of `fq` plus the Laurent part on `S`.  Every term with a
factor `log|αx - β|` carries a rational `lam` with `|log|α| - lam| ≤ eta` (`lam = eta = 0` when `|α| = 1`). -/
theorem l1_series_soundG (fq fq' : FieldQ) (es : List L1Ent) (c ρ : ℚ) (n : ℕ) (δ : ℚ) (g : ℝ → ℝ)
    (h : l1OK c ρ es = true)
    (hlog : ∀ e ∈ es, ∀ (α β : ℚ), e.1.2 = some (α, β) → |Real.log |(α : ℝ)| - (e.2.1 : ℝ)| ≤ (e.2.2 : ℝ))
    (hpl : fq'.plogs = fq.plogs ++ l1Plogs c n es) (hpo : fq'.poles = fq.poles)
    (hD : polyAB (vecAdd (vecAdd fq.poly (l1Poly c n es)) (fq'.poly.map (fun t => (-1 : ℚ) * t))) c ρ ≤ δ)
    (S : Set ℝ) (hS : ∀ x ∈ S, (c : ℝ) - ρ ≤ x ∧ x ≤ (c : ℝ))
    (hcell : ∀ x ∈ S, fieldTower fq' (poleF fq'.poles) 0 x ≤ g x) :
    ∀ x ∈ S, fieldTower fq (poleF fq.poles) 0 x + lfieldTower (es.map Prod.fst) 0 x ≤
      g x + ((δ + l1Err c ρ n es : ℚ) : ℝ) := by
  unfold l1OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hρ, hρc⟩, hall⟩ := h
  intro x hx
  obtain ⟨hl, hr⟩ := hS x hx
  have h1 := l1_list_le c ρ n hρ hρc x hl hr es hall hlog
  have h2 := hcell x hx
  have h3 := (polyTow_range (vecAdd (vecAdd fq.poly (l1Poly c n es)) (fq'.poly.map (fun t => (-1 : ℚ) * t)))
    c ρ x (by rw [abs_le]; constructor <;> linarith)).2
  have h4 : ((polyAB (vecAdd (vecAdd fq.poly (l1Poly c n es)) (fq'.poly.map (fun t => (-1 : ℚ) * t))) c ρ : ℚ) : ℝ)
      ≤ (δ : ℝ) := by exact_mod_cast hD
  simp only [l0_vecAdd, l0_map_mul] at h3
  have e : fieldTower fq' (poleF fq'.poles) 0 x =
      polyTow fq'.poly 0 x + (plogSumTower fq.plogs 0 x + plogSumTower (l1Plogs c n es) 0 x) +
        poleTower fq.poles (poleF fq.poles) 0 x := by
    unfold fieldTower; rw [hpl, hpo, l1_plogSum_append]
  have e2 : fieldTower fq (poleF fq.poles) 0 x =
      polyTow fq.poly 0 x + plogSumTower fq.plogs 0 x + poleTower fq.poles (poleF fq.poles) 0 x := rfl
  rw [e] at h2
  rw [e2]
  have h5 := (abs_le.mp h3).2
  push_cast at h5 ⊢
  linarith

/-- **Series window at `c`, soundness** (constant bound; `l1_series_soundG`). -/
theorem l1_series_sound (fq fq' : FieldQ) (es : List L1Ent) (c ρ : ℚ) (n : ℕ) (δ T : ℚ)
    (h : l1OK c ρ es = true)
    (hlog : ∀ e ∈ es, ∀ (α β : ℚ), e.1.2 = some (α, β) → |Real.log |(α : ℝ)| - (e.2.1 : ℝ)| ≤ (e.2.2 : ℝ))
    (hpl : fq'.plogs = fq.plogs ++ l1Plogs c n es) (hpo : fq'.poles = fq.poles)
    (hD : polyAB (vecAdd (vecAdd fq.poly (l1Poly c n es)) (fq'.poly.map (fun t => (-1 : ℚ) * t))) c ρ ≤ δ)
    (S : Set ℝ) (hS : ∀ x ∈ S, (c : ℝ) - ρ ≤ x ∧ x ≤ (c : ℝ))
    (hcell : ∀ x ∈ S, fieldTower fq' (poleF fq'.poles) 0 x ≤ (T : ℝ)) :
    ∀ x ∈ S, fieldTower fq (poleF fq.poles) 0 x + lfieldTower (es.map Prod.fst) 0 x ≤
      ((T + δ + l1Err c ρ n es : ℚ) : ℝ) := by
  intro x hx
  have h := l1_series_soundG fq fq' es c ρ n δ (fun _ => (T : ℝ)) h hlog hpl hpo hD S hS hcell x hx
  push_cast at h ⊢
  linarith

#print axioms l1_pow
#print axioms l1_laurent
#print axioms l1_ent_le
#print axioms l1_series_soundG
#print axioms l1_series_sound

end CatalanMeasure.GenD.Signed.Data.Cells
