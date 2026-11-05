module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar2.Diff
@[expose] public section
set_option Elab.async false

/-!
# The generalized raw response `ownResp` (lane G6d)

`ownResp P N p e j c` is the right-hand side of `raw_response_intrinsic` with the exponent `P.h N`
replaced by an arbitrary `e`.  The `m`-th difference of `ownResp e` in the residue is
`ownResp (e + m)` (`own_diff`).
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar2
open Polynomial Polynomial.Chebyshev CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.Parametric
  OAI.InternalCatalan CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The raw response formula with a free exponent `e` of `X - 1`. -/
def ownResp (P : Parameters) (N p e j : ℕ) [Fact p.Prime] (c : Fin (P.n N) → ZMod p) : ZMod p :=
  (∑ v ∈ Finset.range (P.H N + 1),
      intrinsicCoeff ((X - 1) ^ e * (X ^ 2 - 1) ^ ((p - 1) / 2) * intrinsicT P N p c)
        ((P.H N : ℤ) - 1 - (j % p : ℕ) - ((v : ℤ) - 1) * p) *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) (j / p))) -
    (3 / 2 : ZMod p) * (∑ v ∈ Finset.range (P.H N),
      intrinsicCoeff ((X - 1) ^ e * intrinsicU P N p c)
        ((P.H N : ℤ) - 1 - (j % p : ℕ) - (v : ℤ) * p) *
        palindromicRatResidue p (zetaRat v (j / p)))

theorem uResp_eq_own (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {j : ℕ} (hj : j < P.H N) (c : Fin (P.n N) → ZMod p) :
    uResp P N p j c = ownResp P N p (P.h N) j c :=
  raw_response_intrinsic hP hN hp2 hH hj c

/-- **`m`-th difference in the residue.** -/
theorem own_diff (m : ℕ) {e J ℓ : ℕ} (hℓ : ℓ + m < p) (c : Fin (P.n N) → ZMod p) :
    ∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) * ownResp P N p e (J * p + (ℓ + s)) c =
      ownResp P N p (e + m) (J * p + ℓ) c := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hmod : ∀ s ∈ Finset.range (m + 1), (J * p + (ℓ + s)) % p = ℓ + s := fun s hs => by
    have : ℓ + s < p := by have := Finset.mem_range.mp hs; omega
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt this]
  have hdiv : ∀ s ∈ Finset.range (m + 1), (J * p + (ℓ + s)) / p = J := fun s hs => by
    have : ℓ + s < p := by have := Finset.mem_range.mp hs; omega
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt this, zero_add]
  have hmod0 : (J * p + ℓ) % p = ℓ := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hdiv0 : (J * p + ℓ) / p = J := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt (by omega), zero_add]
  set FT : ℕ → (ZMod p)[X] := fun e => (X - 1) ^ e * (X ^ 2 - 1) ^ ((p - 1) / 2) * intrinsicT P N p c
    with hFT
  set FU : ℕ → (ZMod p)[X] := fun e => (X - 1) ^ e * intrinsicU P N p c with hFU
  set palA : ℕ → ZMod p := fun v => palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) J)
    with hpalA
  set palB : ℕ → ZMod p := fun v => palindromicRatResidue p (zetaRat v J) with hpalB
  set iT : ℕ → ℤ := fun v => (P.H N : ℤ) - 1 - ℓ - ((v : ℤ) - 1) * p with hiT
  set iU : ℕ → ℤ := fun v => (P.H N : ℤ) - 1 - ℓ - (v : ℤ) * p with hiU
  have hs : ∀ s ∈ Finset.range (m + 1), ownResp P N p e (J * p + (ℓ + s)) c =
      (∑ v ∈ Finset.range (P.H N + 1), intrinsicCoeff (FT e) (iT v - s) * palA v) -
        (3 / 2 : ZMod p) * ∑ v ∈ Finset.range (P.H N), intrinsicCoeff (FU e) (iU v - s) * palB v := by
    intro s hs
    unfold ownResp
    rw [hmod s hs, hdiv s hs]
    congr 1
    · refine Finset.sum_congr rfl fun v _ => ?_
      simp only [hFT, hiT, hpalA]
      congr 2
      push_cast
      ring
    · congr 1
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [hFU, hiU, hpalB]
      congr 2
      push_cast
      ring
  have hTT : ∀ i : ℤ, ∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) *
      intrinsicCoeff (FT e) (i - s) = intrinsicCoeff (FT (e + m)) i := by
    intro i
    rw [← intrinsicCoeff_xsub_pow_mul]
    congr 1
    simp only [hFT]
    ring
  have hUU : ∀ i : ℤ, ∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) *
      intrinsicCoeff (FU e) (i - s) = intrinsicCoeff (FU (e + m)) i := by
    intro i
    rw [← intrinsicCoeff_xsub_pow_mul]
    congr 1
    simp only [hFU]
    ring
  rw [Finset.sum_congr rfl fun s hs' => by rw [hs s hs']]
  have hX : ∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) *
      ∑ v ∈ Finset.range (P.H N + 1), intrinsicCoeff (FT e) (iT v - s) * palA v =
      ∑ v ∈ Finset.range (P.H N + 1), intrinsicCoeff (FT (e + m)) (iT v) * palA v := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hTT (iT v), Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hY : ∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) *
      ∑ v ∈ Finset.range (P.H N), intrinsicCoeff (FU e) (iU v - s) * palB v =
      ∑ v ∈ Finset.range (P.H N), intrinsicCoeff (FU (e + m)) (iU v) * palB v := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hUU (iU v), Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hsplit : ∀ (a b : ℕ → ZMod p) , ∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) *
      (a s - (3 / 2 : ZMod p) * b s) = ∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) * a s -
        (3 / 2 : ZMod p) * ∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) * b s := by
    intro a b
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsplit (fun s => ∑ v ∈ Finset.range (P.H N + 1), intrinsicCoeff (FT e) (iT v - s) * palA v)
    (fun s => ∑ v ∈ Finset.range (P.H N), intrinsicCoeff (FU e) (iU v - s) * palB v), hX, hY]
  unfold ownResp
  rw [hmod0, hdiv0]
#print axioms own_diff
end
end CatalanMeasure.GenD.Uniform.W.LStar2
