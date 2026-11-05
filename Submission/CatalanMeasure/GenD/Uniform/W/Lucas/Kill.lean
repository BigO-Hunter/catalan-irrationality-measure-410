module
public import Submission.CatalanMeasure.GenD.Uniform.W.Nullity
public import Submission.CatalanMeasure.GenD.Uniform.W.Lucas.Seq
@[expose] public section
set_option Elab.async false

/-!
# The `Δ^q` kill criterion (Lucas, `q ≥ p`)

`gKill_of_raw_poly` (W/Nullity) requires the raw response to be a polynomial of degree `< q` in `j`.
The filtered response at column `k` is only the `q`-fold alternating binomial filter of the raw
responses at `b+k, …, b+k+q`, so the exact kernel criterion is the vanishing of that filter on the
active interval:

* `gKill_of_raw_diff` : for every `j ∈ [b, L-q)`,
  `∑_{v ≤ q} (-1)^v C(q,v) uResp (j+v) c = 0` puts `c` in the left kernel (any `q`).
* `gKill_of_lucas`    : `q ≥ p`; if the raw response is `A(j) + ⌊j/p⌋ B(j)` with `B` a polynomial of
  degree `< q - p` (and `A` arbitrary on `ZMod p`), then `c` is in the left kernel.
  (Lucas: `Δ^p = E^p - 1` in characteristic `p`.)

Both are drop-in replacements of `gKill_of_raw_poly` in `w_core_all`-type theorems:
`w_raw_diff`, `w_raw_lucas`, and the family forms `le_nullity_of_lucas`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Lucas
open Module Matrix Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- **Kill criterion (difference form).**  The `q`-fold binomial filter of the raw responses
vanishes on the active interval. -/
theorem gKill_of_raw_diff (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (c : Fin (P.n N) → ZMod p)
    (hraw : ∀ j, P.b N ≤ j → j + P.q N < P.L N →
      ∑ v ∈ Finset.range (P.q N + 1),
        (-1 : ZMod p) ^ v * ((P.q N).choose v : ZMod p) * uResp P N p (j + v) c = 0) :
    (gMat P N p).transpose.mulVec c = 0 := by
  classical
  funext k
  have hzp : ((((p : ℚ) * 0).den : ℕ) : ZMod p) ≠ 0 := by simp
  change (∑ r : Fin (P.n N),
    palindromicRatResidue p ((p : ℚ) ^ 2 * filteredEntryRat P 0 N r.val k.val) * c r) = 0
  simp_rw [(filteredEntry_scaled_residue_sum_general hp2 hH k.isLt 0 hzp).2, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h := hraw (P.b N + k.val) (by omega) (by
    have := k.isLt
    have := rawColumn_lt_L (P := P) (N := N) (k := k.val) k.isLt (le_refl (P.q N))
    omega)
  rw [← h]
  apply Finset.sum_congr rfl
  intro v hv
  have hvq : v ≤ P.q N := by have := Finset.mem_range.mp hv; omega
  rw [filterCoeff_residue]
  rw [show P.b N + k.val + v = P.b N + k.val + v from rfl]
  simp only [uResp, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [add_assoc]
  ring

/-- **Kill criterion (Lucas, `q ≥ p`).** -/
theorem gKill_of_lucas (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (hpq : p ≤ P.q N)
    (c : Fin (P.n N) → ZMod p) (A : ZMod p → ZMod p) (B : (ZMod p)[X])
    (hB : B.degree < ((P.q N - p : ℕ) : WithBot ℕ))
    (hraw : ∀ j, P.b N ≤ j → j < P.L N →
      uResp P N p j c = A (j : ZMod p) + ((j / p : ℕ) : ZMod p) * B.eval (j : ZMod p)) :
    (gMat P N p).transpose.mulVec c = 0 := by
  refine gKill_of_raw_diff hp2 hH c (fun j hj1 hj2 => ?_)
  exact lucas_filter_zero hp2 hpq A B hB (fun j => uResp P N p j c) j
    (fun i hi1 hi2 => hraw i (by omega) (by omega))

/-- **Theorem W, raw form, Lucas kill**: an injective family all of whose members have
Lucas-shaped raw responses lies in the left kernel. -/
theorem le_nullity_of_lucas (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (hpq : p ≤ P.q N)
    {A : Type*} [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    (ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (hι : Function.Injective ι)
    (hraw : ∀ a, ∃ (Af : ZMod p → ZMod p) (B : (ZMod p)[X]),
      B.degree < ((P.q N - p : ℕ) : WithBot ℕ) ∧
      ∀ j, P.b N ≤ j → j < P.L N →
        uResp P N p j (ι a) = Af (j : ZMod p) + ((j / p : ℕ) : ZMod p) * B.eval (j : ZMod p)) :
    finrank (ZMod p) A ≤ nullity P N p := by
  have h := w_core_all (gMat P N p) ι hι (0 : A →ₗ[ZMod p] ZMod p) (fun a _ => by
    obtain ⟨Af, B, hB, h⟩ := hraw a
    exact gKill_of_lucas hp2 hH hpq (ι a) Af B hB h)
  have hr : finrank (ZMod p) (LinearMap.range (0 : A →ₗ[ZMod p] ZMod p)) = 0 := by simp
  rw [hr] at h
  rw [nullity_eq]
  omega

end
end CatalanMeasure.GenD.Uniform.W.Lucas
