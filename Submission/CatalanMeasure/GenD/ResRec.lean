module

public import Submission.CatalanMeasure.GenD.CertMod
public import Submission.CatalanMeasure.Parametric.BaseResidues

@[expose] public section

/-!
# Residue recurrences for `momentRat` and `zetaRat` (generic)

Tables of natural-number residues modulo a prime `p` are checked against the rational
definitions by one-step recurrences (no rational is ever evaluated): `momentScalar`,
`boundaryMinus`, `boundaryPlus`, harmonic numbers, then the diagonal recurrences of
`momentRat` and `zetaRat`.
-/

namespace CatalanMeasure.GenD
namespace ResRec

open OAI.InternalCatalan CatalanMeasure.Parametric

variable {p : ℕ} [Fact p.Prime]

/-- `x` has `p`-integral denominator and residue `r`. -/
def Gd (p : ℕ) [Fact p.Prime] (x : ℚ) (r : ZMod p) : Prop :=
  ((x.den : ℕ) : ZMod p) ≠ 0 ∧ palindromicRatResidue p x = r

theorem Gd.add {x y : ℚ} {a b : ZMod p} (hx : Gd p x a) (hy : Gd p y b) :
    Gd p (x + y) (a + b) :=
  ⟨(rational_residue_add hx.1 hy.1).1, by rw [palindromicRatResidue_add hx.1 hy.1, hx.2, hy.2]⟩

theorem Gd.sub {x y : ℚ} {a b : ZMod p} (hx : Gd p x a) (hy : Gd p y b) :
    Gd p (x - y) (a - b) :=
  ⟨(rational_residue_sub hx.1 hy.1).1, by rw [palindromicRatResidue_sub hx.1 hy.1, hx.2, hy.2]⟩

theorem Gd.mul {x y : ℚ} {a b : ZMod p} (hx : Gd p x a) (hy : Gd p y b) :
    Gd p (x * y) (a * b) :=
  ⟨(rational_residue_mul hx.1 hy.1).1, by rw [palindromicRatResidue_mul hx.1 hy.1, hx.2, hy.2]⟩

theorem Gd.nat (n : ℕ) : Gd p (n : ℚ) (n : ZMod p) := by
  refine ⟨by simp, ?_⟩
  simpa using palindromicRatResidue_intCast p (n : ℤ)

theorem Gd.of_eq {x y : ℚ} {a : ZMod p} (h : x = y) (hy : Gd p y a) : Gd p x a := h ▸ hy

theorem Gd.val {x : ℚ} {a b : ZMod p} (h : a = b) (hx : Gd p x a) : Gd p x b := h ▸ hx

theorem natCast_ne_zero_of_lt {n : ℕ} (h0 : 0 < n) (hn : n < p) : (n : ZMod p) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff n p).mp h
  have := Nat.le_of_dvd h0 this
  omega

theorem Gd.inv_nat {n : ℕ} (h0 : 0 < n) (hn : n < p) :
    Gd p (1 / (n : ℚ)) ((n : ZMod p)⁻¹) := by
  have hv : padicValRat p (n : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt h0 hn)]
  have hq : (n : ℚ) ≠ 0 := by exact_mod_cast h0.ne'
  have h := rational_residue_inv (p := p) hq hv
  refine ⟨by simpa [one_div] using h.1, ?_⟩
  rw [one_div]
  unfold palindromicRatResidue
  rw [h.2]
  simp

theorem cast_eq_of_modeq {a b l : ℕ} (h : (a % l == b % l) = true) :
    (a : ZMod l) = (b : ZMod l) := by
  have : a % l = b % l := by simpa using h
  exact (ZMod.natCast_eq_natCast_iff' a b l).mpr this

/-- Structural list access (kernel-friendly). -/
def nth : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, n + 1 => nth as n

def nthL : List (List ℕ) → ℕ → List ℕ
  | [], _ => []
  | a :: _, 0 => a
  | _ :: as, n + 1 => nthL as n

theorem nth_eq (l : List ℕ) (n : ℕ) : nth l n = l.getD n 0 := by
  induction l generalizing n with
  | nil => cases n <;> simp [nth]
  | cons a as ih => cases n <;> simp [nth, ih]

theorem nthL_eq (l : List (List ℕ)) (n : ℕ) : nthL l n = l.getD n [] := by
  induction l generalizing n with
  | nil => cases n <;> simp [nthL]
  | cons a as ih => cases n <;> simp [nthL, ih]

/-- Table access. -/
def tg (T : List (List ℕ)) (i j : ℕ) : ℕ := nth (nthL T i) j
def tl (T : List ℕ) (i : ℕ) : ℕ := nth T i

theorem tg_cast (T : List (List ℕ)) (i j : ℕ) :
    ((tg T i j : ℕ) : ZMod p) = CertMod.entry p T i j := by
  simp [tg, CertMod.entry, nth_eq, nthL_eq]

/-- Diagonal recurrence soundness. -/
theorem diag_sound (f s : ℕ → ℕ → ℚ) (T S : ℕ → ℕ → ZMod p) (H L : ℕ)
    (hstep : ∀ i j, f i j - f (i + 1) (j + 1) = s i j)
    (hs : ∀ i j, i + 1 < H → j + 1 < L → Gd p (s i j) (S i j))
    (htab : ∀ i j, i + 1 < H → j + 1 < L → T i j - T (i + 1) (j + 1) = S i j)
    (hb0 : ∀ i, i < H → Gd p (f i 0) (T i 0))
    (hb1 : ∀ j, j < L → Gd p (f 0 j) (T 0 j)) :
    ∀ i j, i < H → j < L → Gd p (f i j) (T i j) := by
  intro i
  induction i with
  | zero => intro j _ hj; exact hb1 j hj
  | succ i ih =>
    intro j hi hj
    cases j with
    | zero => exact hb0 _ hi
    | succ j =>
      have h1 := ih j (by omega) (by omega)
      have h2 := hs i j hi hj
      have h3 : f (i + 1) (j + 1) = f i j - s i j := by rw [← hstep]; ring
      exact Gd.of_eq h3 (Gd.val (by rw [← htab i j hi hj]; ring) (Gd.sub h1 h2))

/-- `momentScalar` from its recurrence. -/
theorem ms_sound (N : ℕ) (hN : N + 2 < p) (MS : List ℕ)
    (h0 : (tl MS 0 : ZMod p) = 2)
    (hodd : ∀ i, i < N → i % 2 = 1 → (tl MS i : ZMod p) = 0)
    (hev : ∀ m, 2 * m + 2 < N →
      (((2 * m + 3) * tl MS (2 * m + 2) : ℕ) : ZMod p) =
        (((2 * m + 2) * tl MS (2 * m) : ℕ) : ZMod p)) :
    ∀ i, i < N → Gd p (momentScalar i) (tl MS i : ZMod p) := by
  have even : ∀ m, 2 * m < N → Gd p (momentScalar (2 * m)) (tl MS (2 * m) : ZMod p) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine Gd.of_eq (y := ((2 : ℕ) : ℚ)) (by simp) (Gd.val ?_ (Gd.nat 2))
      simpa using h0.symm
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      have key : momentScalar (2 * (m + 1)) =
          ((2 * m + 2 : ℕ) : ℚ) * momentScalar (2 * m) * (1 / ((2 * m + 3 : ℕ) : ℚ)) := by
        have e : 2 * (m + 1) = 2 * m + 2 := by ring
        rw [momentScalar_even (m + 1), momentScalar_even m]
        have hc := centralCoeff_step m
        have h1 := centralCoeff_ne_zero (m + 1)
        have hc0 : centralCoeff m = ((2 * m + 2 : ℕ) : ℚ) * centralCoeff (m + 1) /
            ((2 * m + 1 : ℕ) : ℚ) := by
          rw [eq_div_iff (by positivity)]
          linarith
        rw [hc0]
        push_cast
        field_simp
        ring
      refine Gd.of_eq key
        (Gd.val ?_ (Gd.mul (Gd.mul (Gd.nat _) ih) (Gd.inv_nat (by omega) (by omega))))
      have hne : ((2 * m + 3 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by omega) (by omega)
      have := hev m (by omega)
      rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hne]
      push_cast at this ⊢
      linear_combination this
  intro i hi
  rcases Nat.even_or_odd' i with ⟨m, rfl | rfl⟩
  · exact even m hi
  · refine Gd.of_eq (y := ((0 : ℕ) : ℚ)) (by rw [momentScalar_odd]; simp) (Gd.val ?_ (Gd.nat 0))
    simpa using (hodd _ hi (by omega)).symm

/-- `boundaryMinus` from its recurrence. -/
theorem bm_sound (N : ℕ) (hN : N + 2 < p) (MS BM : List ℕ)
    (hms : ∀ i, i < N → Gd p (momentScalar i) (tl MS i : ZMod p))
    (h0 : (tl BM 0 : ZMod p) = 0) (h1 : (tl BM 1 : ZMod p) = 2)
    (hstep : ∀ d, d + 2 < N →
      (((d + 2) * tl BM (d + 2) : ℕ) : ZMod p) =
        (((d + 1) * tl BM d + tl MS d + tl MS (d + 1) : ℕ) : ZMod p)) :
    ∀ d, d < N → Gd p (boundaryMinus d) (tl BM d : ZMod p) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    match d, ih, hd with
    | 0, _, _ =>
      refine Gd.of_eq (y := ((0 : ℕ) : ℚ)) (by simp) (Gd.val ?_ (Gd.nat 0))
      simpa using h0.symm
    | 1, _, _ =>
      refine Gd.of_eq (y := ((2 : ℕ) : ℚ)) (by simp) (Gd.val ?_ (Gd.nat 2))
      simpa using h1.symm
    | d + 2, ih, hd =>
      have e : boundaryMinus (d + 2) =
          (((d + 1 : ℕ) : ℚ) * boundaryMinus d + momentScalar d + momentScalar (d + 1)) *
            (1 / ((d + 2 : ℕ) : ℚ)) := by
        rw [boundaryMinus, div_eq_mul_one_div]
      refine Gd.of_eq e (Gd.val ?_ (Gd.mul
        (Gd.add (Gd.add (Gd.mul (Gd.nat _) (ih d (by omega) (by omega))) (hms d (by omega)))
          (hms (d + 1) (by omega))) (Gd.inv_nat (by omega) (by omega))))
      have hne : ((d + 2 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by omega) (by omega)
      have := hstep d hd
      rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hne]
      push_cast at this ⊢
      linear_combination this

/-- `boundaryPlus` from its recurrence (`IV` is the table of inverses). -/
theorem bp_sound (N : ℕ) (hN : N + 2 < p) (BP IV : List ℕ)
    (hIV : ∀ n, 0 < n → n < N → ((n * tl IV n : ℕ) : ZMod p) = 1)
    (h0 : (tl BP 0 : ZMod p) = 0) (h1 : (tl BP 1 : ZMod p) = 0)
    (hstep : ∀ d, d + 2 < N →
      (((d + 1) * tl BP (d + 2) : ℕ) : ZMod p) =
        ((d * tl BP d + 2 * tl IV (d + 1) : ℕ) : ZMod p)) :
    ∀ d, d < N → Gd p (boundaryPlus d) (tl BP d : ZMod p) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    match d, ih, hd with
    | 0, _, _ =>
      refine Gd.of_eq (y := ((0 : ℕ) : ℚ)) (by simp) (Gd.val ?_ (Gd.nat 0))
      simpa using h0.symm
    | 1, _, _ =>
      refine Gd.of_eq (y := ((0 : ℕ) : ℚ)) (by simp) (Gd.val ?_ (Gd.nat 0))
      simpa using h1.symm
    | d + 2, ih, hd =>
      have e : boundaryPlus (d + 2) =
          (((d : ℕ) : ℚ) * boundaryPlus d + ((2 : ℕ) : ℚ) * (1 / ((d + 1 : ℕ) : ℚ))) *
            (1 / ((d + 1 : ℕ) : ℚ)) := by
        rw [boundaryPlus, div_eq_mul_one_div]
        push_cast
        ring
      refine Gd.of_eq e (Gd.val ?_ (Gd.mul
        (Gd.add (Gd.mul (Gd.nat _) (ih d (by omega) (by omega)))
          (Gd.mul (Gd.nat 2) (Gd.inv_nat (by omega) (by omega))))
        (Gd.inv_nat (by omega) (by omega))))
      have hne : ((d + 1 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by omega) (by omega)
      have hiv : (tl IV (d + 1) : ZMod p) = ((d + 1 : ℕ) : ZMod p)⁻¹ :=
        eq_inv_of_mul_eq_one_right
          (by have := hIV (d + 1) (by omega) (by omega); push_cast at this ⊢; exact this)
      have := hstep d hd
      rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hne]
      push_cast at this hiv ⊢
      rw [hiv] at this
      linear_combination this

/-- First harmonic numbers. -/
theorem h1_sound (N : ℕ) (hN : N < p) (H1 IV : List ℕ)
    (hIV : ∀ n, 0 < n → n < N + 1 → ((n * tl IV n : ℕ) : ZMod p) = 1)
    (h0 : (tl H1 0 : ZMod p) = 0)
    (hstep : ∀ n, n + 1 < N + 1 →
      ((tl H1 (n + 1) : ℕ) : ZMod p) = ((tl H1 n + tl IV (n + 1) : ℕ) : ZMod p)) :
    ∀ n, n < N + 1 → Gd p (harmonicRat 1 n) (tl H1 n : ZMod p) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine Gd.of_eq (y := ((0 : ℕ) : ℚ)) (by simp) (Gd.val ?_ (Gd.nat 0))
    simpa using h0.symm
  | succ n ih =>
    intro hn
    have e : harmonicRat 1 (n + 1) = harmonicRat 1 n + 1 / ((n + 1 : ℕ) : ℚ) := by
      rw [harmonicRat_succ]; simp
    refine Gd.of_eq e (Gd.val ?_ (Gd.add (ih (by omega)) (Gd.inv_nat (by omega) (by omega))))
    have hiv : (tl IV (n + 1) : ZMod p) = ((n + 1 : ℕ) : ZMod p)⁻¹ :=
      eq_inv_of_mul_eq_one_right
        (by have := hIV (n + 1) (by omega) (by omega); push_cast at this ⊢; exact this)
    have := hstep n hn
    push_cast at this hiv ⊢
    rw [hiv] at this
    exact this.symm

/-- Moment table. -/
theorem moment_sound (H L : ℕ) (hH : H + 3 < p) (hLH : L ≤ H) (MS BM BP IV : List ℕ)
    (MT : List (List ℕ))
    (hms : ∀ i, i < H → Gd p (momentScalar i) (tl MS i : ZMod p))
    (hbm : ∀ d, d < H → Gd p (boundaryMinus d) (tl BM d : ZMod p))
    (hbp : ∀ d, d < L → Gd p (boundaryPlus d) (tl BP d : ZMod p))
    (hIV : ∀ n, 0 < n → n < H + 1 → ((n * tl IV n : ℕ) : ZMod p) = 1)
    (hcol : ∀ i, i < H → (tg MT i 0 : ZMod p) = tl BM i)
    (hrow : ∀ j, j < L → (tg MT 0 j : ZMod p) = tl BP j)
    (hdiag : ∀ i j, i + 1 < H → j + 1 < L →
      ((tg MT (i + 1) (j + 1) + tl MS i * tl IV (j + 1) : ℕ) : ZMod p) = (tg MT i j : ZMod p)) :
    ∀ i j, i < H → j < L →
      palindromicRatResidue p (momentRat i j) = CertMod.entry p MT i j := by
  intro i j hi hj
  refine Eq.trans (diag_sound (p := p) momentRat (fun i j => momentScalar i / ((j + 1 : ℕ) : ℚ))
    (fun i j => (tg MT i j : ZMod p))
    (fun i j => (tl MS i : ZMod p) * (tl IV (j + 1) : ZMod p)) H L
    momentRat_step ?_ ?_ ?_ ?_ i j hi hj).2 (tg_cast _ _ _)
  · intro i j hi hj
    have hiv : (tl IV (j + 1) : ZMod p) = ((j + 1 : ℕ) : ZMod p)⁻¹ :=
      eq_inv_of_mul_eq_one_right
        (by have := hIV (j + 1) (by omega) (by omega); push_cast at this ⊢; exact this)
    refine Gd.of_eq (div_eq_mul_one_div _ _) (Gd.val ?_ (Gd.mul (hms i (by omega))
      (Gd.inv_nat (by omega) (by omega))))
    rw [hiv]
  · intro i j hi hj
    have := hdiag i j hi hj
    push_cast at this
    show (tg MT i j : ZMod p) - (tg MT (i + 1) (j + 1) : ZMod p) = _
    show _ = (tl MS i : ZMod p) * (tl IV (j + 1) : ZMod p)
    rw [← this]; push_cast; ring
  · intro i hi
    rw [momentRat_zero_right]
    exact Gd.val (hcol i hi).symm (hbm i hi)
  · intro j hj
    rw [momentRat_zero_left]
    exact Gd.val (hrow j hj).symm (hbp j hj)

/-- Zeta table. -/
theorem zeta_sound (H L : ℕ) (hH : H + 3 < p) (hLH : L ≤ H) (H1 IV : List ℕ)
    (ZT : List (List ℕ))
    (hh1 : ∀ n, n < H + 1 → Gd p (harmonicRat 1 n) (tl H1 n : ZMod p))
    (hIV : ∀ n, 0 < n → n < H + 1 → ((n * tl IV n : ℕ) : ZMod p) = 1)
    (hz00 : (tg ZT 0 0 : ZMod p) = 0)
    (hcol : ∀ i, 0 < i → i < H → ((tg ZT i 0 * i : ℕ) : ZMod p) = (tl H1 i : ZMod p))
    (hrow : ∀ j, j < L → (tg ZT 0 j : ZMod p) = (tg ZT j 0 : ZMod p))
    (hdiag : ∀ i j, i + 1 < H → j + 1 < L →
      ((tg ZT (i + 1) (j + 1) + tl IV (i + 1) * tl IV (j + 1) : ℕ) : ZMod p) =
        (tg ZT i j : ZMod p)) :
    ∀ i j, i < H → j < L →
      palindromicRatResidue p (zetaRat i j) = CertMod.entry p ZT i j := by
  have hiv : ∀ n, 0 < n → n < H + 1 → (tl IV n : ZMod p) = (n : ZMod p)⁻¹ := by
    intro n h1 h2
    exact eq_inv_of_mul_eq_one_right (by have := hIV n h1 h2; push_cast at this ⊢; exact this)
  have col0 : ∀ i, i < H → Gd p (zetaRat i 0) (tg ZT i 0 : ZMod p) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · refine Gd.of_eq (y := ((0 : ℕ) : ℚ)) (by simp [zetaRat_diagonal]) (Gd.val ?_ (Gd.nat 0))
      simpa using hz00.symm
    · have e : zetaRat i 0 = harmonicRat 1 i * (1 / (i : ℚ)) := by
        rw [zetaRat_of_ne (by omega)]
        simp [harmonicRat_zero, div_eq_mul_inv]
      refine Gd.of_eq e (Gd.val ?_ (Gd.mul (hh1 i (by omega)) (Gd.inv_nat hpos (by omega))))
      have hne : (i : ZMod p) ≠ 0 := natCast_ne_zero_of_lt hpos (by omega)
      have := hcol i hpos hi
      push_cast at this
      rw [← this, mul_inv_cancel_right₀ hne]
  refine fun i j hi hj => Eq.trans (diag_sound (p := p) zetaRat
    (fun i j => 1 / (((i + 1 : ℕ) : ℚ) * ((j + 1 : ℕ) : ℚ)))
    (fun i j => (tg ZT i j : ZMod p))
    (fun i j => (tl IV (i + 1) : ZMod p) * (tl IV (j + 1) : ZMod p)) H L
    zetaRat_step ?_ ?_ ?_ ?_ i j hi hj).2 (tg_cast _ _ _)
  · intro i j hi hj
    refine Gd.of_eq (by rw [one_div_mul_one_div]) (Gd.val ?_ (Gd.mul
      (Gd.inv_nat (n := i + 1) (by omega) (by omega))
      (Gd.inv_nat (n := j + 1) (by omega) (by omega))))
    rw [hiv (i + 1) (by omega) (by omega), hiv (j + 1) (by omega) (by omega)]
  · intro i j hi hj
    have := hdiag i j hi hj
    push_cast at this
    show (tg ZT i j : ZMod p) - (tg ZT (i + 1) (j + 1) : ZMod p) = _
    show _ = (tl IV (i + 1) : ZMod p) * (tl IV (j + 1) : ZMod p)
    rw [← this]; push_cast; ring
  · intro i hi
    exact col0 i hi
  · intro j hj
    rw [zetaRat_symm]
    exact Gd.val (hrow j hj).symm (col0 j (by omega))

end ResRec
end CatalanMeasure.GenD
