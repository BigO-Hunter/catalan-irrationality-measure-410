module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.PolyPos

/-!
# D2 constants: integer-coefficient polynomial positivity on dyadic cells

`zNonnegCheck c s A B` checks that the integer polynomial `c` (constant term first) is `>= 0` on
`[A / 2^s, B / 2^s]`: the Mobius coefficients of the rescaled cell polynomial are all `>= 0`.
Only `Int` arithmetic is used in the kernel (all cell endpoints are dyadic).
`zNonnegCov` chains cells over cut points with the common denominator `2^s`.
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert

def zAdd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: zAdd p q

def zSmul (c : ℤ) (p : List ℤ) : List ℤ := p.map (c * ·)

/-- `(A + D t) * r(t)`. -/
def zMulAff (A D : ℤ) (r : List ℤ) : List ℤ := zAdd (zSmul A r) (0 :: zSmul D r)

/-- `2^{s (len L - 1)} L((A + D t) / 2^s)` by Horner (see `zCompS_eval`). -/
def zCompS (s : ℕ) (A D : ℤ) : List ℤ → List ℤ
  | [] => []
  | c :: p => zAdd [c * 2 ^ (s * p.length)] (zMulAff A D (zCompS s A D p))

/-- Evaluation of an integer coefficient list. -/
def zv (L : List ℤ) (x : ℝ) : ℝ := lpEval (L.map (fun n : ℤ => (n : ℚ))) x

theorem zv_nil (x : ℝ) : zv [] x = 0 := rfl
theorem zv_cons (c : ℤ) (L : List ℤ) (x : ℝ) : zv (c :: L) x = (c : ℝ) + x * zv L x := by
  simp [zv]

theorem zv_add (p q : List ℤ) (x : ℝ) : zv (zAdd p q) x = zv p x + zv q x := by
  induction p generalizing q with
  | nil => simp [zAdd, zv_nil]
  | cons a p ih =>
    cases q with
    | nil => simp [zAdd, zv_nil]
    | cons b q => simp only [zAdd, zv_cons, ih]; push_cast; ring

theorem zv_smul (c : ℤ) (p : List ℤ) (x : ℝ) : zv (zSmul c p) x = c * zv p x := by
  induction p with
  | nil => simp [zSmul, zv_nil]
  | cons a p ih =>
    have : zSmul c (a :: p) = (c * a) :: zSmul c p := rfl
    rw [this, zv_cons, zv_cons, ih]; push_cast; ring

theorem zv_mulAff (A D : ℤ) (r : List ℤ) (t : ℝ) :
    zv (zMulAff A D r) t = (A + D * t) * zv r t := by
  unfold zMulAff
  rw [zv_add, zv_smul, zv_cons, zv_smul]; ring

theorem zCompS_eval (s : ℕ) (A D : ℤ) (L : List ℤ) (t : ℝ) :
    (2 : ℝ) ^ s * zv (zCompS s A D L) t =
      (2 : ℝ) ^ (s * L.length) * zv L (((A : ℝ) + D * t) / 2 ^ s) := by
  induction L with
  | nil => simp [zCompS, zv_nil]
  | cons c p ih =>
    simp only [zCompS, zv_add, zv_mulAff, zv_cons, zv_nil, List.length_cons]
    have h2 : (2 : ℝ) ^ s ≠ 0 := by positivity
    set x : ℝ := ((A : ℝ) + D * t) / 2 ^ s with hx
    have hx2 : (A : ℝ) + D * t = 2 ^ s * x := by rw [hx]; field_simp
    have e1 : (2 : ℝ) ^ (s * (p.length + 1)) = 2 ^ s * 2 ^ (s * p.length) := by
      rw [Nat.mul_succ, pow_add]; ring
    rw [hx2, e1]
    push_cast
    linear_combination (2 ^ s * x) * ih

/-- Cell check: `c >= 0` on `[A/2^s, B/2^s]` via the Mobius coefficients of the cell polynomial. -/
def zNonnegCheck (c : List ℤ) (s : ℕ) (A B : ℤ) : Bool :=
  decide (A < B) &&
    (zCompS 0 1 1 (zCompS s A (B - A) c).reverse).all (fun n => decide (0 ≤ n))

theorem zv_nonneg {p : List ℤ} (h : p.all (fun n => decide (0 ≤ n)) = true) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ zv p y := by
  have : (p.map (fun n : ℤ => (n : ℚ))).all (fun c => decide (0 ≤ c)) = true := by
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq] at h ⊢
    intro n hn; exact_mod_cast h n hn
  exact lpEval_nonneg this hy

theorem zNonnegCheck_Ioc {c : List ℤ} {s : ℕ} {A B : ℤ} (h : zNonnegCheck c s A B = true) {x : ℝ}
    (hx : x ∈ Ioc ((A : ℝ) / 2 ^ s) ((B : ℝ) / 2 ^ s)) : 0 ≤ zv c x := by
  unfold zNonnegCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hAB, hs⟩ := h
  have h2 : (0 : ℝ) < 2 ^ s := by positivity
  have hD : (0 : ℝ) < ((B - A : ℤ) : ℝ) := by
    have : (A : ℝ) < B := by exact_mod_cast hAB
    push_cast; linarith
  have hx1 : (A : ℝ) < x * 2 ^ s := by
    have := hx.1; rw [div_lt_iff₀ h2] at this; exact this
  have hx2 : x * 2 ^ s ≤ B := by
    have := hx.2; rw [le_div_iff₀ h2] at this; exact this
  set u : ℝ := (x * 2 ^ s - A) / ((B - A : ℤ) : ℝ) with hu
  have hu0 : 0 < u := div_pos (by linarith) hD
  have hu1 : u ≤ 1 := (div_le_one hD).mpr (by push_cast; linarith)
  set y : ℝ := u⁻¹ - 1 with hy
  have hy0 : 0 ≤ y := by
    have : 1 ≤ u⁻¹ := one_le_inv₀ hu0 |>.mpr hu1
    linarith
  set Z := zCompS s A (B - A) c with hZ
  have hT := zv_nonneg hs hy0
  -- Mobius evaluation
  have hM : zv (zCompS 0 1 1 Z.reverse) y = zv Z.reverse u⁻¹ := by
    have h := zCompS_eval 0 1 1 Z.reverse y
    have e : (((1 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) * y) / 2 ^ 0 = u⁻¹ := by push_cast; rw [hy]; ring
    rw [e] at h
    simpa using h
  have hrev : u⁻¹ * zv Z.reverse u⁻¹ = (u⁻¹) ^ Z.length * zv Z (u⁻¹)⁻¹ := by
    have := lpEval_reverse (Z.map (fun n : ℤ => (n : ℚ))) u⁻¹ (inv_ne_zero hu0.ne')
    simpa [zv, List.map_reverse] using this
  have hZu := zCompS_eval s A (B - A) c u
  rw [inv_inv] at hrev
  have hxu : ((A : ℝ) + ((B - A : ℤ) : ℝ) * u) / 2 ^ s = x := by
    rw [hu]; field_simp; ring
  rw [hxu] at hZu
  have hpos : 0 < (2 : ℝ) ^ (s * c.length) := by positivity
  by_contra hneg
  push_neg at hneg
  have a1 : 0 ≤ u⁻¹ * zv Z.reverse u⁻¹ := mul_nonneg (inv_pos.mpr hu0).le (by rw [← hM]; exact hT)
  rw [hrev] at a1
  have hZ0 : 0 ≤ zv Z u := by
    have : 0 < (u⁻¹) ^ Z.length := pow_pos (inv_pos.mpr hu0) _
    by_contra hh
    push_neg at hh
    have := mul_neg_of_pos_of_neg this hh
    linarith
  have h3 : 2 ^ (s * c.length) * zv c x < 0 := mul_neg_of_pos_of_neg hpos hneg
  have h4 : (0 : ℝ) < 2 ^ s := h2
  have : 2 ^ s * zv Z u < 0 := by rw [hZu]; exact h3
  nlinarith

theorem zNonnegCheck_sound {c : List ℤ} {s : ℕ} {A B : ℤ} (h : zNonnegCheck c s A B = true)
    {x : ℝ} (hx : x ∈ Icc ((A : ℝ) / 2 ^ s) ((B : ℝ) / 2 ^ s)) : 0 ≤ zv c x := by
  have h2 : (0 : ℝ) < 2 ^ s := by positivity
  have hab : (A : ℝ) / 2 ^ s < (B : ℝ) / 2 ^ s := by
    unfold zNonnegCheck at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have : (A : ℝ) < B := by exact_mod_cast h.1
    exact div_lt_div_of_pos_right this h2
  have hcont : Continuous (zv c) := lpEval_continuous _
  have hcl : IsClosed {x : ℝ | 0 ≤ zv c x} := isClosed_le continuous_const hcont
  have hsub : Ioc ((A : ℝ) / 2 ^ s) ((B : ℝ) / 2 ^ s) ⊆ {x : ℝ | 0 ≤ zv c x} :=
    fun z hz => zNonnegCheck_Ioc h hz
  have := closure_minimal hsub hcl
  rw [closure_Ioc hab.ne] at this
  exact this hx

/-- A chain of cells with cut points `(cuts_i) / 2^s`. -/
def zNonnegCov (c : List ℤ) (s : ℕ) : ℤ → List ℤ → ℤ → Bool
  | A, [], B => zNonnegCheck c s A B
  | A, C :: cs, B => zNonnegCheck c s A C && zNonnegCov c s C cs B

theorem zNonnegCov_sound (c : List ℤ) (s : ℕ) : ∀ (cs : List ℤ) (A B : ℤ),
    zNonnegCov c s A cs B = true → ∀ x : ℝ, (A : ℝ) / 2 ^ s ≤ x → x ≤ (B : ℝ) / 2 ^ s →
      0 ≤ zv c x := by
  intro cs
  induction cs with
  | nil => intro A B h x h1 h2; exact zNonnegCheck_sound h ⟨h1, h2⟩
  | cons C cs ih =>
    intro A B h x h1 h2
    simp only [zNonnegCov, Bool.and_eq_true] at h
    by_cases hxc : x ≤ (C : ℝ) / 2 ^ s
    · exact zNonnegCheck_sound h.1 ⟨h1, hxc⟩
    · exact ih C B h.2 x (le_of_not_ge hxc) h2

end CatalanMeasure.Signed.Consts
