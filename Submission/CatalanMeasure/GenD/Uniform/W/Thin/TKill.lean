module
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.TPoly
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.Resp
public import Submission.CatalanMeasure.GenD.Uniform.W.Families
@[expose] public section
set_option Elab.async false

/-!
# Kill step for T-pair atoms: (R) / F3 gives `RawKilled`

For an atom `x` (virtual-pair-free) the raw response at `j = J p + ℓ` is a sum over the monomials
`X^e` of the slot polynomials `lam d` of one source covector per `e`:

    uResp j (tRows x) = Σ_{e < h+D} [p ∣ H-1-ℓ-e] · psiLin H J ((H-1-ℓ-e)/p) (w_e),
    w_e = Σ_d lam_d[e] · x_d     (a profile in `F_p^K`).

If `w_e = 0` for `e < e0` (low-coefficient jets) and `w_e ∈ ker` of the *seen* functionals for
`e ≥ e0`, the response vanishes (`uResp_tRows_eq_zero`).
-/

namespace CatalanMeasure.GenD.Uniform.W.Thin
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem intrinsicCoeff_add' (A B : (ZMod p)[X]) (i : ℤ) :
    intrinsicCoeff (A + B) i = intrinsicCoeff A i + intrinsicCoeff B i := by
  by_cases hi : 0 ≤ i <;> simp [intrinsicCoeff, hi, coeff_add]

theorem intrinsicCoeff_smul' (c : ZMod p) (A : (ZMod p)[X]) (i : ℤ) :
    intrinsicCoeff (c • A) i = c * intrinsicCoeff A i := by
  by_cases hi : 0 ≤ i <;> simp [intrinsicCoeff, hi]

theorem intrinsicResponse_add (H J ell : ℕ) (A1 A2 B1 B2 : (ZMod p)[X]) :
    intrinsicResponse H J ell (A1 + A2) (B1 + B2) =
      intrinsicResponse H J ell A1 B1 + intrinsicResponse H J ell A2 B2 := by
  unfold intrinsicResponse
  simp only [intrinsicCoeff_add', add_mul, Finset.sum_add_distrib, mul_add]
  ring

theorem intrinsicResponse_zero (H J ell : ℕ) :
    intrinsicResponse H J ell (0 : (ZMod p)[X]) 0 = 0 := by
  simp [intrinsicResponse, intrinsicCoeff]

theorem intrinsicResponse_sum {ι : Type*} (H J ell : ℕ) (s : Finset ι)
    (A B : ι → (ZMod p)[X]) :
    intrinsicResponse H J ell (∑ i ∈ s, A i) (∑ i ∈ s, B i) =
      ∑ i ∈ s, intrinsicResponse H J ell (A i) (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [intrinsicResponse_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
      intrinsicResponse_add, ih]

/-- The source covector at `(J, a)` as a linear functional of the profile. -/
def psiLin (p K : ℕ) [Fact p.Prime] (k0 : ℤ) (H J : ℕ) (a : ℤ) :
    (Fin K → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun y := digitPhi H a (sourceM (p := p) J) (sourceZ (p := p) J)
    (gyMap p K k0 y) (tyMap p K k0 y) (3 / 2)
  map_add' y z := by
    simp only [map_add]
    unfold digitPhi
    simp only [intrinsicCoeff_add', add_mul, Finset.sum_add_distrib, mul_add]
    ring
  map_smul' c y := by
    simp only [map_smul, RingHom.id_apply, smul_eq_mul]
    unfold digitPhi
    simp only [intrinsicCoeff_smul', mul_assoc, ← Finset.mul_sum]
    ring

/-- Coefficient `e` of the slot polynomial `lam d`. -/
def lamc (P : Parameters) (N p d e : ℕ) : ZMod p := (lam P N p d).coeff e

/-- `Σ_d lam_d · G_d(Y)` in monomial form. -/
theorem slot_expand (hp2 : p ≠ 2) {D : ℕ} (G : Fin D → (ZMod p)[X]) :
    ∑ d : Fin D, lam P N p (d : ℕ) * (G d).comp (X ^ p) =
      ∑ e ∈ Finset.range (P.h N + D), X ^ e *
        (∑ d : Fin D, C (lamc P N p d e) * G d).comp (X ^ p) := by
  have hlam : ∀ d : Fin D, lam P N p (d : ℕ) =
      ∑ e ∈ Finset.range (P.h N + D), C (lamc P N p d e) * X ^ e := by
    intro d
    have hd := d.isLt
    have hdeg : (lam P N p (d : ℕ)).natDegree < P.h N + D := by
      have := lam_natDegree_le (P := P) (N := N) hp2 (d : ℕ)
      omega
    conv_lhs => rw [Polynomial.as_sum_range' _ _ hdeg]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    rfl
  simp_rw [hlam, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sum_comp', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Polynomial.mul_comp, Polynomial.C_comp]
  ring

/-- Linear combination of profiles. -/
def wvec (P : Parameters) (N p : ℕ) {K D : ℕ} (x : Fin D → Fin K → ZMod p) (e : ℕ) :
    Fin K → ZMod p := ∑ d : Fin D, lamc P N p d e • x d

theorem tyMap_wvec {K D : ℕ} (k0 : ℤ) (x : Fin D → Fin K → ZMod p) (e : ℕ) :
    tyMap p K k0 (wvec P N p x e) = ∑ d : Fin D, C (lamc P N p d e) * tyMap p K k0 (x d) := by
  simp [wvec, map_sum, Polynomial.smul_eq_C_mul]

theorem gyMap_wvec {K D : ℕ} (k0 : ℤ) (x : Fin D → Fin K → ZMod p) (e : ℕ) :
    gyMap p K k0 (wvec P N p x e) = ∑ d : Fin D, C (lamc P N p d e) * gyMap p K k0 (x d) := by
  simp [wvec, map_sum, Polynomial.smul_eq_C_mul]

/-- **Response of a T-pair atom** (formula (R) evaluated on the slots). -/
theorem uResp_tRows (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K D : ℕ} (k0 : ℤ) (x : Fin D → Fin K → ZMod p)
    (hx : ∀ d k, ¬ Good P N p k0 d k → x d k = 0) {j : ℕ} (hj : j < P.H N) :
    uResp P N p j (tRows P N p K D k0 x) =
      ∑ e ∈ Finset.range (P.h N + D),
        if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then
          psiLin p K k0 (P.H N) (j / p)
            (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (wvec P N p x e)
        else 0 := by
  rw [uResp_intrinsicResponse hP hN hp2 hH hj, intrinsicT_tRows hp2 k0 x hx,
    intrinsicU_tRows hp2 k0 x hx, slot_expand hp2 (fun d => gyMap p K k0 (x d)),
    slot_expand hp2 (fun d => tyMap p K k0 (x d)), intrinsicResponse_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← gyMap_wvec, ← tyMap_wvec, intrinsicResponse_monomial]
  split_ifs <;> rfl

/-- **Kill criterion for T-pair atoms.** -/
theorem uResp_tRows_eq_zero (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2)
    (hH : P.H N < p ^ 2) {K D : ℕ} (k0 : ℤ) (x : Fin D → Fin K → ZMod p)
    (hx : ∀ d k, ¬ Good P N p k0 d k → x d k = 0) {j : ℕ} (hj : j < P.H N)
    (hterm : ∀ e, e < P.h N + D → ∀ a : ℤ, (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e = a * p →
      psiLin p K k0 (P.H N) (j / p) a (wvec P N p x e) = 0) :
    uResp P N p j (tRows P N p K D k0 x) = 0 := by
  rw [uResp_tRows hP hN hp2 hH k0 x hx hj]
  refine Finset.sum_eq_zero fun e he => ?_
  split_ifs with hd
  · obtain ⟨a, ha⟩ := hd
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have : ((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p = a := by
      rw [ha]; exact Int.mul_ediv_cancel_left _ hp0
    rw [this]
    exact hterm e (Finset.mem_range.mp he) a (by rw [ha]; ring)
  · rfl

#print axioms uResp_tRows_eq_zero
end
end CatalanMeasure.GenD.Uniform.W.Thin
