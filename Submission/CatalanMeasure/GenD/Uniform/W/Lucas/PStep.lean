module
public import Submission.CatalanMeasure.GenD.Uniform.W.Lucas.Kill
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Core
@[expose] public section
set_option Elab.async false

/-!
# The exact `p`-step kill criterion (Lemma 0(a), general `a_q`)

For `q = a p + r`, in characteristic `p` the `q`-th difference is `Δ^r ∘ Δ_p^a` (`Δ_p` = difference
with step `p`).  Hence a row whose `a`-fold `p`-difference of raw responses vanishes on
`[b, L - a p)` is in the left kernel of the filtered matrix:

* `gKill_of_pstep`     : the criterion for `uResp`;
* `slot_nullity_pstep` : the slot-system count (`SlotSystem.resp (J+v) ℓ`), the `q ≥ p` replacement of
  `slot_nullity_raw`.  W-prof drops its `q < p` restriction by feeding this the chart identification
  whose seen covectors are the `a`-fold `J`-differences `∑_v (-1)^{a-v} C(a,v) ψ(J+v, ·)`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Lucas
open Finset Module Matrix Polynomial fwdDiff CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem fwdDiff_iter_pmul (hp2 : p ≠ 2) (f : ℤ → ZMod p) (a : ℕ) :
    Δ_[(1 : ℤ)]^[a * p] f = Δ_[(p : ℤ)]^[a] f := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : (a + 1) * p = p + a * p := by ring
    rw [e, Function.iterate_add, Function.comp_apply, Function.iterate_succ_apply', ← ih]
    funext z
    rw [fwdDiff_iter_prime hp2]
    rfl

/-- The `q = a p + r` filter vanishes if the `a`-fold `p`-difference vanishes at `j0, …, j0 + r`. -/
theorem pstep_filter_zero (hp2 : p ≠ 2) {a r : ℕ} (R : ℕ → ZMod p) (j0 : ℕ)
    (h : ∀ k ≤ r, ∑ v ∈ range (a + 1),
      ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) * R (j0 + k + v * p) = 0) :
    ∑ v ∈ range (a * p + r + 1), (-1 : ZMod p) ^ v * ((a * p + r).choose v : ZMod p) *
      R (j0 + v) = 0 := by
  let S : ℤ → ZMod p := fun z => R z.toNat
  have hS : ∀ n : ℕ, S (n : ℤ) = R n := fun n => by simp [S]
  have h1 : Δ_[(1 : ℤ)]^[a * p + r] S (j0 : ℤ) = 0 := by
    have e : a * p + r = r + a * p := by ring
    rw [e, Function.iterate_add_apply, fwdDiff_iter_pmul hp2, fwdDiff_iter_eq_sum_shift]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkr : k ≤ r := by have := mem_range.mp hk; omega
    rw [fwdDiff_iter_eq_sum_shift]
    have : ∑ v ∈ range (a + 1), ((-1 : ℤ) ^ (a - v) * (a.choose v : ℤ)) •
        S ((j0 : ℤ) + k • (1 : ℤ) + v • (p : ℤ)) = 0 := by
      have := h k hkr
      rw [← this]
      refine Finset.sum_congr rfl fun v _ => ?_
      have e2 : (j0 : ℤ) + k • (1 : ℤ) + v • (p : ℤ) = ((j0 + k + v * p : ℕ) : ℤ) := by
        simp only [nsmul_eq_mul, mul_one]; push_cast; ring
      rw [e2, hS]
      simp [zsmul_eq_mul]
    simp only [this, smul_zero]
  have := filter_sum_of_fwdDiff_zero S (a * p + r) (j0 : ℤ) h1
  rw [← this]
  refine Finset.sum_congr rfl fun v _ => ?_
  have e3 : (j0 : ℤ) + (v : ℤ) = ((j0 + v : ℕ) : ℤ) := by push_cast; ring
  rw [e3, hS]

/-- **`p`-step kill criterion.**  `q = a p + r`; if the `a`-fold `p`-difference of the raw responses
vanishes at every `j ∈ [b, L - a p)`, the row is in the left kernel. -/
theorem gKill_of_pstep (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) {a r : ℕ} (hq : P.q N = a * p + r)
    (c : Fin (P.n N) → ZMod p)
    (hraw : ∀ j, P.b N ≤ j → j + a * p < P.L N → ∑ v ∈ range (a + 1),
      ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) * uResp P N p (j + v * p) c = 0) :
    (gMat P N p).transpose.mulVec c = 0 := by
  refine gKill_of_raw_diff hp2 hH c (fun j hj1 hj2 => ?_)
  rw [hq]
  rw [hq] at hj2
  exact pstep_filter_zero hp2 (fun i => uResp P N p i c) j (fun k hk =>
    hraw (j + k) (by omega) (by omega))

variable (S : SlotSystem P N p)

/-- **Slot count, `p`-step form** (any `q`): the `a`-fold `p`-difference of the slot response
`S.resp (J+v) ℓ` vanishes on `ker Φ` for all active `j`. -/
theorem slot_nullity_pstep (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {a r : ℕ} (hq : P.q N = a * p + r)
    {A E : Type*} [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    [AddCommGroup E] [Module (ZMod p) E]
    (ξ : A →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p)) (hξ : ∀ a, ξ a ∈ S.dom)
    (hξi : Function.Injective ξ) (Φ : A →ₗ[ZMod p] E)
    (hkill : ∀ x, Φ x = 0 → ∀ j, P.b N ≤ j → j + a * p < P.L N → ∑ v ∈ range (a + 1),
      ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) * S.resp (j / p + v) (j % p) (ξ x) = 0) :
    finrank (ZMod p) A - finrank (ZMod p) (LinearMap.range Φ) ≤ nullity P N p := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have h := w_core_all (gMat P N p) (S.rows.comp ξ) (S.rows_injective_dom ξ hξ hξi) Φ
    (fun x hx => gKill_of_pstep hp2 hH hq _ (fun j h1 h2 => by
      rw [← hkill x hx j h1 h2]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hjv : j + v * p < P.H N := by
        have hv' : v ≤ a := by have := mem_range.mp hv; omega
        have := SlotSystem.hjH hP hN (show j + v * p < P.L N by nlinarith [Nat.mul_le_mul_right p hv'])
        exact this
      have e1 : (j + v * p) / p = j / p + v := by
        rw [Nat.add_mul_div_right _ _ hp0]
      have e2 : (j + v * p) % p = j % p := by simp
      show _ * uResp P N p (j + v * p) (S.rows (ξ x)) = _
      rw [S.uResp_slot hP hN hp2 hH (hξ x) hjv, e1, e2]))
  have hr : finrank (ZMod p) (LinearMap.range Φ) = finrank (ZMod p) (LinearMap.range Φ) := rfl
  rw [nullity_eq]
  exact h

end
end CatalanMeasure.GenD.Uniform.W.Lucas
