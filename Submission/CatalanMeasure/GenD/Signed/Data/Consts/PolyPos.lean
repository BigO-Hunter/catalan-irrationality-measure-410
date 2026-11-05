module

public import Submission.CatalanMeasure.Cert.ListPoly
public import Submission.CatalanMeasure.GenD.Signed.ArcsineDenominator

/-!
# D2 constants: kernel-checked polynomial positivity and the Chebyshev series as a polynomial

* `lpNonnegCheck p a b`: all Bernstein-type (Mobius) coefficients of `p` on `[a, b]` are `>= 0`;
  then `p >= 0` on `[a, b]` (`lpNonnegCheck_sound`).  `nnCov` chains cells over cut points.
* `chebMono bs`: the monomial coefficient list of `1 + 2 sum_k bs_k T_k`; `chebPs_bSeq` identifies
  it with `chebPs (bSeq bs)` (the Chebyshev series of a finitely supported coefficient list).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert OAI.InternalCatalan

/-! ### Polynomial nonnegativity on an interval -/

theorem lpEval_continuous (p : List ℚ) : Continuous (lpEval p) := by
  induction p with
  | nil => exact continuous_const
  | cons c p ih =>
    have : lpEval (c :: p) = fun x => (c : ℝ) + x * lpEval p x := rfl
    rw [this]
    exact continuous_const.add (continuous_id.mul ih)

/-- All Mobius coefficients of `p` on `(a, b)` are nonnegative. -/
def lpNonnegCheck (p : List ℚ) (a b : ℚ) : Bool :=
  decide (a < b) && (lpMobius p a b).all (fun c => decide (0 ≤ c))

theorem lpNonnegCheck_Ioc {p : List ℚ} {a b : ℚ} (h : lpNonnegCheck p a b = true) {x : ℝ}
    (hx : x ∈ Ioc (a : ℝ) b) : 0 ≤ lpEval p x := by
  unfold lpNonnegCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hab, hs⟩ := h
  have hab' : (0 : ℝ) < (b : ℝ) - a := by
    have : (a : ℝ) < b := by exact_mod_cast hab
    linarith
  set u : ℝ := (x - a) / ((b : ℝ) - a) with hu
  have hu0 : 0 < u := div_pos (by linarith [hx.1]) hab'
  have hu1 : u ≤ 1 := (div_le_one hab').mpr (by linarith [hx.2])
  set y : ℝ := u⁻¹ - 1 with hy
  have hy0 : 0 ≤ y := by
    have : 1 ≤ u⁻¹ := one_le_inv₀ hu0 |>.mpr hu1
    linarith
  have hT := lpEval_nonneg hs hy0
  unfold lpMobius at hT
  rw [lpEval_compAff] at hT
  have hz : ((1 : ℚ) : ℝ) + ((1 : ℚ) : ℝ) * y = u⁻¹ := by push_cast; rw [hy]; ring
  rw [hz] at hT
  have hrev := lpEval_reverse (lpCompAff a (b - a) p) u⁻¹ (inv_ne_zero hu0.ne')
  rw [inv_inv, lpEval_compAff] at hrev
  have hx' : (a : ℝ) + ((b - a : ℚ) : ℝ) * u = x := by
    rw [hu]; push_cast; field_simp; ring
  rw [hx'] at hrev
  by_contra hneg
  push_neg at hneg
  have h1 : 0 < (u⁻¹) ^ (lpCompAff a (b - a) p).length := pow_pos (inv_pos.mpr hu0) _
  have h2 := mul_neg_of_pos_of_neg h1 hneg
  have h3 : 0 ≤ u⁻¹ * lpEval (lpCompAff a (b - a) p).reverse u⁻¹ :=
    mul_nonneg (inv_pos.mpr hu0).le hT
  rw [hrev] at h3
  linarith

theorem lpNonnegCheck_sound {p : List ℚ} {a b : ℚ} (h : lpNonnegCheck p a b = true) {x : ℝ}
    (hx : x ∈ Icc (a : ℝ) b) : 0 ≤ lpEval p x := by
  have hab : (a : ℝ) < b := by
    unfold lpNonnegCheck at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact_mod_cast h.1
  have hcl : IsClosed {x : ℝ | 0 ≤ lpEval p x} :=
    isClosed_le continuous_const (lpEval_continuous p)
  have hsub : Ioc (a : ℝ) b ⊆ {x : ℝ | 0 ≤ lpEval p x} := fun z hz => lpNonnegCheck_Ioc h hz
  have := closure_minimal hsub hcl
  rw [closure_Ioc hab.ne] at this
  exact this hx

/-- A chain of cells `[a, c1], [c1, c2], ..., [cn, b]`. -/
def nnCov (p : List ℚ) : ℚ → List ℚ → ℚ → Bool
  | a, [], b => lpNonnegCheck p a b
  | a, c :: cs, b => lpNonnegCheck p a c && nnCov p c cs b

theorem nnCov_sound (p : List ℚ) : ∀ (cs : List ℚ) (a b : ℚ), nnCov p a cs b = true →
    ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → 0 ≤ lpEval p x := by
  intro cs
  induction cs with
  | nil => intro a b h x h1 h2; exact lpNonnegCheck_sound h ⟨h1, h2⟩
  | cons c cs ih =>
    intro a b h x h1 h2
    simp only [nnCov, Bool.and_eq_true] at h
    by_cases hxc : x ≤ (c : ℝ)
    · exact lpNonnegCheck_sound h.1 ⟨h1, hxc⟩
    · exact ih c b h.2 x (le_of_not_ge hxc) h2

/-! ### The Chebyshev series as a polynomial -/

def lpX2 (p : List ℚ) : List ℚ := 0 :: lpSmul 2 p

theorem lpEval_X2 (p : List ℚ) (x : ℝ) : lpEval (lpX2 p) x = x * (2 * lpEval p x) := by
  simp [lpX2]

def chebGo : List ℚ → List ℚ → List ℚ → List ℚ → List ℚ
  | [], _, _, acc => acc
  | c :: bs, Tk, Tk1, acc =>
    chebGo bs Tk1 (lpAdd (lpX2 Tk1) (lpSmul (-1) Tk)) (lpAdd acc (lpSmul (2 * c) Tk1))

/-- `1 + 2 sum_{j} bs_j T_{j+1}` as a monomial coefficient list. -/
def chebMono (bs : List ℚ) : List ℚ := chebGo bs [1] [0, 1] [1]

theorem chebGo_eval (bs : List ℚ) : ∀ (k : ℕ) (Tk Tk1 acc : List ℚ) (x : ℝ),
    lpEval Tk x = (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x →
    lpEval Tk1 x = (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x →
    lpEval (chebGo bs Tk Tk1 acc) x = lpEval acc x +
      ∑ j ∈ Finset.range bs.length,
        2 * ((bs.getD j 0 : ℚ) : ℝ) * (Polynomial.Chebyshev.T ℝ ((k + 1 + j : ℕ) : ℤ)).eval x := by
  induction bs with
  | nil => intro k Tk Tk1 acc x _ _; simp [chebGo]
  | cons c bs ih =>
    intro k Tk Tk1 acc x h0 h1
    have h2 : lpEval (lpAdd (lpX2 Tk1) (lpSmul (-1) Tk)) x =
        (Polynomial.Chebyshev.T ℝ ((k + 1 + 1 : ℕ) : ℤ)).eval x := by
      rw [lpEval_add, lpEval_X2, lpEval_smul, h0, h1]
      have := Polynomial.Chebyshev.T_add_two ℝ (k : ℤ)
      have e : ((k + 1 + 1 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
      have e1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [e, this, ← e1]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      push_cast
      ring
    have := ih (k + 1) Tk1 _ (lpAdd acc (lpSmul (2 * c) Tk1)) x h1 h2
    rw [chebGo, this, List.length_cons, Finset.sum_range_succ' _ bs.length, lpEval_add, lpEval_smul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, h1]
    have e2 : ∀ j : ℕ, k + 1 + 1 + j = k + 1 + (j + 1) := fun j => by ring
    simp only [e2]
    push_cast
    ring_nf

/-- The finitely supported coefficient sequence `b_k = bs[k-1]` (`b_0 = 0`). -/
def bSeq (bs : List ℚ) (k : ℕ) : ℝ := if k = 0 then 0 else ((bs.getD (k - 1) 0 : ℚ) : ℝ)

theorem chebPs_bSeq (bs : List ℚ) (u : ℝ) : chebPs (bSeq bs) u = lpEval (chebMono bs) u := by
  have hT0 : lpEval [1] u = (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval u := by simp [lpEval]
  have hT1 : lpEval [0, 1] u = (Polynomial.Chebyshev.T ℝ ((0 + 1 : ℕ) : ℤ)).eval u := by
    simp [lpEval, Polynomial.Chebyshev.T_one]
  have h := chebGo_eval bs 0 [1] [0, 1] [1] u hT0 hT1
  unfold chebMono
  rw [h]
  unfold chebPs
  have hsum : (∑' k : ℕ, bSeq bs (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u) =
      ∑ k ∈ Finset.range bs.length, ((bs.getD k 0 : ℚ) : ℝ) *
        (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u := by
    rw [tsum_eq_sum (s := Finset.range bs.length)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp [bSeq]
    · intro k hk
      have : bs.length ≤ k := by simpa using hk
      have h0 : bs.getD k 0 = 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
      have hb : bSeq bs (k + 1) = 0 := by
        unfold bSeq
        rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, h0]
        simp
      rw [hb, zero_mul]
  rw [hsum]
  simp only [lpEval, Rat.cast_one, mul_zero, add_zero]
  have e3 : ∀ j : ℕ, 0 + 1 + j = j + 1 := fun j => by ring
  simp only [e3]
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end CatalanMeasure.Signed.Consts
