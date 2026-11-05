module

public import Submission.CatalanMeasure.CellCert.FieldsSLink

@[expose] public section

/-!
# The integer polynomial `Z` of the derivative fields, by a verified integer Clenshaw recursion

`F' = ptZ Z 0 + Σ_q qt q 0` with `ptZ Z 0 x = lpEval (zl Z) x / 2^40`.  For the three fields
`Z = -4 Σ Pc_k U_k - Σ Vc_k x^k` (row), `2 Σ Vc_k U_k` (column), `-2 Σ Pc_k U_k` (residual); here
`rowZ`, `colZ`, `resZ` compute these integer coefficient lists (Clenshaw recursion for the Chebyshev
`U`-sum, integer list arithmetic only) and `rowZ_spec`, `colZ_spec`, `resZ_spec` are exactly the
`hZ` hypotheses of `rowFieldSP_hasDerivAt`, `colFieldSP_hasDerivAt`, `resFieldS_hasDerivAt`.  The
one-off identity `D.Z = rowZ Pc Vc` is then a `decide +kernel` on lists of integers.
-/

open Polynomial

namespace CatalanMeasure.CellCert
open CatalanMeasure.Cert

/-! ### integer list polynomials -/

def zAdd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: zAdd p q

def zSub : List ℤ → List ℤ → List ℤ
  | [], q => q.map (fun b => -b)
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a - b) :: zSub p q

def zScale (c : ℤ) (p : List ℤ) : List ℤ := p.map (fun a => c * a)

/-- evaluation of an integer coefficient list -/
noncomputable def zev : List ℤ → ℝ → ℝ
  | [], _ => 0
  | c :: p, x => (c : ℝ) + x * zev p x

theorem zev_eq (l : List ℤ) (x : ℝ) : zev l x = lpEval (zl l) x := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [zev, zl, ih]

theorem zev_add (p q : List ℤ) (x : ℝ) : zev (zAdd p q) x = zev p x + zev q x := by
  induction p generalizing q with
  | nil => simp [zAdd, zev]
  | cons a p ih =>
    cases q with
    | nil => simp [zAdd, zev]
    | cons b q => simp [zAdd, zev, ih]; ring

theorem zev_scale (c : ℤ) (p : List ℤ) (x : ℝ) : zev (zScale c p) x = c * zev p x := by
  induction p with
  | nil => simp [zScale, zev]
  | cons a p ih =>
    simp only [zScale, List.map_cons, zev] at ih ⊢
    rw [ih]; push_cast; ring

theorem zev_neg_map (q : List ℤ) (x : ℝ) : zev (q.map (fun b => -b)) x = -zev q x := by
  have := zev_scale (-1) q x
  simp only [zScale, neg_one_mul, Int.cast_neg, Int.cast_one] at this
  simpa using this

theorem zev_sub (p q : List ℤ) (x : ℝ) : zev (zSub p q) x = zev p x - zev q x := by
  induction p generalizing q with
  | nil => simp [zSub, zev, zev_neg_map]
  | cons a p ih =>
    cases q with
    | nil => simp [zSub, zev]
    | cons b q => simp [zSub, zev, ih]; ring

theorem zev_eq_sum (l : List ℤ) (x : ℝ) :
    zev l x = ∑ k ∈ Finset.range l.length, (l.getD k 0 : ℝ) * x ^ k := by
  induction l with
  | nil => simp [zev]
  | cons c l ih =>
    rw [zev, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring

/-! ### Clenshaw recursion for `Σ c_k U_k` -/

/-- one step: `b_k = c_k + 2x b_{k+1} - b_{k+2}`; state `(b_{k+1}, b_{k+2})` -/
def uStep (c : ℤ) (s : List ℤ × List ℤ) : List ℤ × List ℤ :=
  (zAdd [c] (zSub (0 :: zScale 2 s.1) s.2), s.1)

def uClen : List ℤ → List ℤ × List ℤ → List ℤ × List ℤ
  | [], s => s
  | c :: cs, s => uClen cs (uStep c s)

/-- coefficients of `Σ_{k<n} cs_k U_k` -/
def uSum (cs : List ℤ) : List ℤ := (uClen cs.reverse ([], [])).1

/-- `Σ xs_i U_{k-i}` -/
noncomputable def sumU (x : ℝ) : List ℤ → ℤ → ℝ
  | [], _ => 0
  | c :: cs, k => (c : ℝ) * (Chebyshev.U ℝ k).eval x + sumU x cs (k - 1)

theorem uClen_spec (x : ℝ) : ∀ (xs : List ℤ) (k : ℤ) (s : List ℤ × List ℤ) (T : ℝ),
    T = zev s.1 x * (Chebyshev.U ℝ (k + 1)).eval x - zev s.2 x * (Chebyshev.U ℝ k).eval x →
    T + sumU x xs k = zev (uClen xs s).1 x * (Chebyshev.U ℝ (k - xs.length + 1)).eval x -
      zev (uClen xs s).2 x * (Chebyshev.U ℝ (k - xs.length)).eval x := by
  intro xs
  induction xs with
  | nil => intro k s T hT; simpa [uClen, sumU] using hT
  | cons c cs ih =>
    intro k s T hT
    have h := Chebyshev.U_add_two ℝ (k - 1)
    have e1 : k - 1 + 2 = k + 1 := by ring
    have e2 : k - 1 + 1 = k := by ring
    rw [e1, e2] at h
    have hU : (Chebyshev.U ℝ (k + 1)).eval x =
        2 * x * (Chebyshev.U ℝ k).eval x - (Chebyshev.U ℝ (k - 1)).eval x := by
      rw [h]; simp [eval_sub, eval_mul]
    have key := ih (k - 1) (uStep c s) (T + c * (Chebyshev.U ℝ k).eval x) (by
      simp only [uStep, zev_add, zev_sub, zev_scale, zev]
      rw [e2, hT, hU]
      push_cast
      ring)
    simp only [uClen, sumU]
    have e3 : k - ((c :: cs).length : ℤ) = k - 1 - cs.length := by simp; ring
    rw [List.length_cons] at e3 ⊢
    have e4 : k - ((cs.length + 1 : ℕ) : ℤ) + 1 = k - 1 - cs.length + 1 := by push_cast; ring
    have e5 : k - ((cs.length + 1 : ℕ) : ℤ) = k - 1 - cs.length := by push_cast; ring
    rw [e4, e5]
    rw [← key]
    ring

theorem sumU_reverse (x : ℝ) : ∀ (cs : List ℤ) (k0 : ℤ),
    sumU x cs.reverse (cs.length - 1 + k0) =
      ∑ k ∈ Finset.range cs.length, (cs.getD k 0 : ℝ) *
        (Chebyshev.U ℝ ((k : ℤ) + k0)).eval x := by
  intro cs
  induction cs with
  | nil => intro k0; simp [sumU]
  | cons c cs ih =>
    intro k0
    have happ : ∀ (xs : List ℤ) (c : ℤ) (k : ℤ), sumU x (xs ++ [c]) k =
        sumU x xs k + (c : ℝ) * (Chebyshev.U ℝ (k - xs.length)).eval x := by
      intro xs c k
      induction xs generalizing k with
      | nil => simp [sumU]
      | cons a xs ihx =>
        simp only [List.cons_append, sumU, ihx, List.length_cons]
        push_cast
        have : k - 1 - (xs.length : ℤ) = k - ((xs.length : ℤ) + 1) := by ring
        rw [this]; ring
    rw [List.reverse_cons, happ, List.length_cons, Finset.sum_range_succ']
    have e : ((cs.length + 1 : ℕ) : ℤ) - 1 + k0 = (cs.length : ℤ) - 1 + (k0 + 1) := by
      push_cast; ring
    rw [e, ih (k0 + 1)]
    simp only [List.length_reverse, List.getD_cons_zero, List.getD_cons_succ]
    have e6 : (cs.length : ℤ) - 1 + (k0 + 1) - cs.length = k0 := by ring
    rw [e6]
    simp only [Nat.cast_zero, zero_add]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    push_cast
    ring_nf

theorem uSum_spec (cs : List ℤ) (x : ℝ) :
    zev (uSum cs) x = ∑ k ∈ Finset.range cs.length, (cs.getD k 0 : ℝ) *
      (Chebyshev.U ℝ (k : ℤ)).eval x := by
  have h := uClen_spec x cs.reverse ((cs.length : ℤ) - 1) ([], []) 0 (by simp [zev])
  have hs := sumU_reverse x cs 0
  simp only [add_zero, List.length_reverse] at h hs
  rw [hs] at h
  have e1 : (cs.length : ℤ) - 1 - cs.length + 1 = 0 := by ring
  have e2 : (cs.length : ℤ) - 1 - cs.length = -1 := by ring
  rw [e1, e2] at h
  simp only [Chebyshev.U_zero, Chebyshev.U_neg_one, eval_one, eval_zero, mul_one, mul_zero,
    sub_zero, zero_add] at h
  unfold uSum
  rw [← h]

/-! ### the three `Z` lists -/

def rowZ (Pc Vc : List ℤ) : List ℤ := zSub (zScale (-4) (uSum Pc)) Vc
def colZ (Vc : List ℤ) : List ℤ := zScale 2 (uSum Vc)
def resZ (Pc : List ℤ) : List ℤ := zScale (-2) (uSum Pc)

theorem ptZ_zero (Z : List ℤ) (x : ℝ) : ptZ Z 0 x = zev Z x / 1099511627776 := by
  rw [zev_eq]; simp [ptZ]

theorem finUR_eq (cs : List ℤ) (x : ℝ) :
    finUR cs x = (∑ k ∈ Finset.range cs.length, (cs.getD k 0 : ℝ) *
      (Chebyshev.U ℝ (k : ℤ)).eval x) / 1099511627776 := by
  unfold finUR
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem finPR_eq (cs : List ℤ) (x : ℝ) :
    finPR cs x = (∑ k ∈ Finset.range cs.length, (cs.getD k 0 : ℝ) * x ^ k) / 1099511627776 := by
  unfold finPR
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem rowZ_spec (Pc Vc : List ℤ) (x : ℝ) :
    -4 * finUR Pc x - finPR Vc x = ptZ (rowZ Pc Vc) 0 x := by
  rw [finUR_eq, finPR_eq, ptZ_zero, rowZ, zev_sub, zev_scale, uSum_spec, zev_eq_sum]
  push_cast
  ring

theorem colZ_spec (Vc : List ℤ) (x : ℝ) : 2 * finUR Vc x = ptZ (colZ Vc) 0 x := by
  rw [finUR_eq, ptZ_zero, colZ, zev_scale, uSum_spec]
  push_cast
  ring

theorem resZ_spec (Pc : List ℤ) (x : ℝ) : -2 * finUR Pc x = ptZ (resZ Pc) 0 x := by
  rw [finUR_eq, ptZ_zero, resZ, zev_scale, uSum_spec]
  push_cast
  ring

end CatalanMeasure.CellCert
