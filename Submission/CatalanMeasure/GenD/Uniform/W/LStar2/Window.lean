module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar2.OwnResp
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Rank
@[expose] public section
set_option Elab.async false

/-!
# The window relation (lane G6d, Theorem L* for `h < p`)

For `h + m = p`, the `m`-th difference of the raw residue responses along the `m + 1` consecutive
residues `ℓ, …, ℓ + m` (fixed digit `J`) is the response of exponent `p`, which has a single live
position `e0 = idxRes H p ℓ` and therefore the column form `[Q1_d]_{e0} · Sresp`.
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar2
open Polynomial Polynomial.Chebyshev CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.Parametric
  OAI.InternalCatalan CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Column formula for `ownResp` at the exponent `p + dh`. -/
theorem ownResp_single (hp2 : p ≠ 2) {e dh ℓ J : ℕ} (hdh : e = p + dh) (hℓ : ℓ < p)
    (he : dh + (p - 1) / 2 ≤ idxRes (P.H N) p ℓ) (r : Fin (P.n N)) (k d : ℤ)
    (hrd : (r.val : ℤ) - P.g N = k * p + d) (hd : d.natAbs ≤ (p - 1) / 2) :
    ownResp P N p e (J * p + ℓ) (Pi.single r 1) =
      (qOne p dh d).coeff (idxRes (P.H N) p ℓ) * Sresp (P.H N) p ℓ J k := by
  subst hdh
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hmod : (J * p + ℓ) % p = ℓ := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hℓ]
  have hdiv : (J * p + ℓ) / p = J := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hℓ, zero_add]
  unfold ownResp
  rw [hmod, hdiv, intrinsicT_single, intrinsicU_single, hrd]
  have he0 := idxRes_lt hp0 (P.H N) ℓ
  set e0 := idxRes (P.H N) p ℓ with he0def
  have hA := blockT hp2 dh k d
  have hB := blockU hp2 dh k d
  have hq1 := natDegree_qOne_lt hp2 (e0 := e0) hd he
  have hq2 := natDegree_qTwo_lt hp2 (e0 := e0) hd he
  have hz : (qTwo p dh d).coeff e0 = 0 := coeff_eq_zero_of_natDegree_lt hq2
  have hidx := idx_eq hp0 (P.H N) ℓ
  rw [← he0def] at hidx
  have cA : ∀ v : ℕ, intrinsicCoeff ((X - 1) ^ (p + dh) * (X ^ 2 - 1) ^ ((p - 1) / 2) *
        T (ZMod p) (k * p + d)) ((P.H N : ℤ) - 1 - ((ℓ : ℕ) : ℤ) - ((v : ℤ) - 1) * p) =
      intrinsicCoeff ((X - 1) * T (ZMod p) k) (idxQuo (P.H N) p ℓ - v + 1) *
        (qOne p dh d).coeff e0 := by
    intro v
    have hi : (P.H N : ℤ) - 1 - ((ℓ : ℕ) : ℤ) - ((v : ℤ) - 1) * p =
        e0 + p * (idxQuo (P.H N) p ℓ - v + 1) := by linarith
    rw [hi]
    have := hA
    simp only [wt] at this
    rw [this, intrinsicCoeff_add', intrinsicCoeff_expand_mul_live hp0 _ _ he0 hq1,
      intrinsicCoeff_expand_mul_live hp0 _ _ he0 (by omega), hz]
    ring
  have cB : ∀ v : ℕ, intrinsicCoeff ((X - 1) ^ (p + dh) * U (ZMod p) (k * p + d - 1))
        ((P.H N : ℤ) - 1 - ((ℓ : ℕ) : ℤ) - (v : ℤ) * p) =
      intrinsicCoeff ((X - 1) * U (ZMod p) (k - 1)) (idxQuo (P.H N) p ℓ - v) *
        (qOne p dh d).coeff e0 := by
    intro v
    have hi : (P.H N : ℤ) - 1 - ((ℓ : ℕ) : ℤ) - (v : ℤ) * p =
        e0 + p * (idxQuo (P.H N) p ℓ - v) := by linarith
    rw [hi, hB, intrinsicCoeff_add', intrinsicCoeff_expand_mul_live hp0 _ _ he0 hq1,
      intrinsicCoeff_expand_mul_live hp0 _ _ he0 (by omega), hz]
    ring
  simp only [cA, cB, Sresp]
  rw [sum_mul_const_mul, sum_mul_const_mul]
  ring

/-- **Window relation.**  `h + m = p`, residues `ℓ … ℓ + m < p`, fixed digit `J`. -/
theorem window_resp (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {m ℓ J : ℕ} (hhm : P.h N + m = p) (hℓ : ℓ + m < p)
    (hJ : ∀ s ≤ m, J * p + (ℓ + s) < P.H N) (he : (p - 1) / 2 ≤ idxRes (P.H N) p ℓ)
    (c : Fin (P.n N) → ZMod p) :
    ∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) * uResp P N p (J * p + (ℓ + s)) c =
      ∑ r : Fin (P.n N), c r * ((qOne p 0 (blkD p (P.g N) r.val)).coeff (idxRes (P.H N) p ℓ) *
        Sresp (P.H N) p ℓ J (blkK p (P.g N) r.val)) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  let Λ : (Fin (P.n N) → ZMod p) →ₗ[ZMod p] ZMod p :=
    ∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) • uResp P N p (J * p + (ℓ + s))
  have hΛ : ∀ c, Λ c = ownResp P N p p (J * p + ℓ) c := by
    intro c
    have h1 : Λ c = ∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) *
        ownResp P N p (P.h N) (J * p + (ℓ + s)) c := by
      simp only [Λ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [uResp_eq_own hP hN hp2 hH (hJ s (by have := Finset.mem_range.mp hs; omega)) c]
    rw [h1, own_diff m hℓ c, hhm]
  have hdec : c = ∑ r, c r • (Pi.single r 1 : Fin (P.n N) → ZMod p) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hsum : ∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) * uResp P N p (J * p + (ℓ + s)) c =
      Λ c := by
    simp only [Λ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hsum]
  conv_lhs => rw [hdec]
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, smul_eq_mul, hΛ]
  congr 1
  have hrd := blk_eq hp2 (P.g N) r.val
  have hdle := blkD_natAbs_le hp2 (P.g N) r.val
  exact ownResp_single hp2 (dh := 0) (by omega) (by omega) (by omega) r _ _ hrd hdle

#print axioms window_resp
end
end CatalanMeasure.GenD.Uniform.W.LStar2
