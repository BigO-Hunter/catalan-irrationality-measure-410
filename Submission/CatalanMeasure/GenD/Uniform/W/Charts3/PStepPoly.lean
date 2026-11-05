module
public import Submission.CatalanMeasure.GenD.Uniform.W.Lucas.PStep
@[expose] public section
set_option Elab.async false

/-!
# The `p`-step kill with a polynomial response (the `B`-graph)

`slot_nullity_pstep` (W/Lucas) kills the `a`-fold `p`-difference of the response outright.  But for
`q = a p + r` the filtered kernel also contains the rows whose `a`-fold `p`-difference is a
**polynomial of degree `< r` in `j`** (`Δ^q = Δ^r Δ_p^a`, and `Δ^r` kills such polynomials): this is the
`B(l)` of paper §3, encoded in the bank packets by the extra coordinates `jet_0`, `@low:raw`.
Ignoring it (as `slot_nullity_raw`/`slot_nullity_pstep` do) loses up to `r` kernel dimensions per
window, which is the entire gap between the Lean frame's killed response and the bank's value.

* `pstep_filter_zero_poly`    : the binomial `q`-filter vanishes if the `a`-fold `p`-difference at
  `j0 + k` equals `G(j0 + k)` for `k ≤ r`, `deg G < r`;
* `gKill_of_pstep_poly`       : kill criterion;
* `slot_nullity_pstep_poly`   : the slot-system count with a polynomial-valued response.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts3
open Finset Module Matrix Polynomial fwdDiff CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Lucas
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem pstep_filter_zero_poly (hp2 : p ≠ 2) {a r : ℕ} (R : ℕ → ZMod p) (j0 : ℕ)
    (G : (ZMod p)[X]) (hG : G.degree < (r : WithBot ℕ))
    (h : ∀ k ≤ r, ∑ v ∈ range (a + 1),
      ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) * R (j0 + k + v * p) =
        G.eval ((j0 + k : ℕ) : ZMod p)) :
    ∑ v ∈ range (a * p + r + 1), (-1 : ZMod p) ^ v * ((a * p + r).choose v : ZMod p) *
      R (j0 + v) = 0 := by
  let S : ℤ → ZMod p := fun z => R z.toNat
  have hS : ∀ n : ℕ, S (n : ℤ) = R n := fun n => by simp [S]
  have hz0 : ∀ n : ℕ, Δ_[(1 : ZMod p)]^[n] (fun _ : ZMod p => (0 : ZMod p)) = fun _ => 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply]
      have : Δ_[(1 : ZMod p)] (fun _ : ZMod p => (0 : ZMod p)) = fun _ => 0 := by
        funext y; simp [fwdDiff]
      rw [this]; exact ih
  have hzG : Δ_[(1 : ZMod p)]^[r] G.eval = 0 := by
    by_cases hG0 : G = 0
    · subst hG0
      simp only [Polynomial.eval_zero]
      exact hz0 r
    · exact Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
        ((Polynomial.natDegree_lt_iff_degree_lt hG0).mpr hG)
  have hz : ∑ k ∈ range (r + 1), ((-1 : ℤ) ^ (r - k) * (r.choose k : ℤ)) •
      G.eval ((j0 : ZMod p) + k • (1 : ZMod p)) = 0 := by
    have := congrFun hzG (j0 : ZMod p)
    rw [fwdDiff_iter_eq_sum_shift] at this
    simpa using this
  have h1 : Δ_[(1 : ℤ)]^[a * p + r] S (j0 : ℤ) = 0 := by
    have e : a * p + r = r + a * p := by ring
    rw [e, Function.iterate_add_apply, fwdDiff_iter_pmul hp2, fwdDiff_iter_eq_sum_shift]
    refine Eq.trans (Finset.sum_congr rfl fun k hk => ?_) hz
    have hkr : k ≤ r := by have := mem_range.mp hk; omega
    rw [fwdDiff_iter_eq_sum_shift]
    have hin : ∑ v ∈ range (a + 1), ((-1 : ℤ) ^ (a - v) * (a.choose v : ℤ)) •
        S ((j0 : ℤ) + k • (1 : ℤ) + v • (p : ℤ)) = G.eval ((j0 : ZMod p) + k • (1 : ZMod p)) := by
      have hk' := h k hkr
      have e4 : (((j0 + k : ℕ)) : ZMod p) = (j0 : ZMod p) + k • (1 : ZMod p) := by
        simp
      rw [e4] at hk'
      rw [← hk']
      refine Finset.sum_congr rfl fun v _ => ?_
      have e2 : (j0 : ℤ) + k • (1 : ℤ) + v • (p : ℤ) = ((j0 + k + v * p : ℕ) : ℤ) := by
        simp only [nsmul_eq_mul, mul_one]; push_cast; ring
      rw [e2, hS]
      simp [zsmul_eq_mul]
    rw [hin]
  have := filter_sum_of_fwdDiff_zero S (a * p + r) (j0 : ℤ) h1
  rw [← this]
  refine Finset.sum_congr rfl fun v _ => ?_
  have e3 : (j0 : ℤ) + (v : ℤ) = ((j0 + v : ℕ) : ℤ) := by push_cast; ring
  rw [e3, hS]

theorem gKill_of_pstep_poly (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) {a r : ℕ}
    (hq : P.q N = a * p + r) (c : Fin (P.n N) → ZMod p) (G : (ZMod p)[X])
    (hG : G.degree < (r : WithBot ℕ))
    (hraw : ∀ j, P.b N ≤ j → j + a * p < P.L N → ∑ v ∈ range (a + 1),
      ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) * uResp P N p (j + v * p) c =
        G.eval (j : ZMod p)) :
    (gMat P N p).transpose.mulVec c = 0 := by
  refine gKill_of_raw_diff hp2 hH c (fun j hj1 hj2 => ?_)
  rw [hq]
  rw [hq] at hj2
  exact pstep_filter_zero_poly hp2 (fun i => uResp P N p i c) j G hG (fun k hk => by
    have := hraw (j + k) (by omega) (by omega)
    simpa using this)

variable (S : SlotSystem P N p)

/-- **Slot count, `p`-step form with polynomial response.** -/
theorem slot_nullity_pstep_poly (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2)
    (hH : P.H N < p ^ 2) {a r : ℕ} (hq : P.q N = a * p + r)
    {A E : Type*} [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    [AddCommGroup E] [Module (ZMod p) E]
    (ξ : A →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p)) (hξ : ∀ a, ξ a ∈ S.dom)
    (hξi : Function.Injective ξ) (Φ : A →ₗ[ZMod p] E)
    (hkill : ∀ x, Φ x = 0 → ∃ G : (ZMod p)[X], G.degree < (r : WithBot ℕ) ∧
      ∀ j, P.b N ≤ j → j + a * p < P.L N → ∑ v ∈ range (a + 1),
      ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) * S.resp (j / p + v) (j % p) (ξ x) =
        G.eval (j : ZMod p)) :
    finrank (ZMod p) A - finrank (ZMod p) (LinearMap.range Φ) ≤ nullity P N p := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have h := w_core_all (gMat P N p) (S.rows.comp ξ) (S.rows_injective_dom ξ hξ hξi) Φ
    (fun x hx => by
      obtain ⟨G, hG, hk⟩ := hkill x hx
      refine gKill_of_pstep_poly hp2 hH hq _ G hG (fun j h1 h2 => ?_)
      rw [← hk j h1 h2]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hjv : j + v * p < P.H N := by
        have hv' : v ≤ a := by have := mem_range.mp hv; omega
        exact SlotSystem.hjH hP hN (show j + v * p < P.L N by nlinarith [Nat.mul_le_mul_right p hv'])
      have e1 : (j + v * p) / p = j / p + v := by
        rw [Nat.add_mul_div_right _ _ hp0]
      have e2 : (j + v * p) % p = j % p := by simp
      show _ * uResp P N p (j + v * p) (S.rows (ξ x)) = _
      rw [S.uResp_slot hP hN hp2 hH (hξ x) hjv, e1, e2])
  rw [nullity_eq]
  exact h

end
end CatalanMeasure.GenD.Uniform.W.Charts3
