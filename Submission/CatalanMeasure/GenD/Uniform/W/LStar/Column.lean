module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Block
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponse
@[expose] public section
set_option Elab.async false

/-!
# The column formula of Theorem L* (lane G6c)

For an admissible residue `ℓ` (single live position `e0`), the raw residue response of the single
row `r` (with signed index `r - g = k p + d`, `|d| ≤ (p-1)/2`) at column `J p + ℓ` factors as

    uResp (J p + ℓ) (e_r) = [Q1_d]_{e0} * Sresp H p ℓ J k ,

where `Sresp` depends on the block `k` and the column, but not on the offset `d`, and
`[Q1_d]_{e0} = 0` for `|d| > D := p - 1 - e0 + dh`.  Hence the responses of all rows in a block
span a line, and the rows of a `D`-virtual block respond by `0`.
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar
open Polynomial Polynomial.Chebyshev CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.Parametric
  OAI.InternalCatalan CatalanMeasure.GenD
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The live position `e0 = (H - 1 - ℓ) mod p` of the residue `ℓ`. -/
def idxRes (H p ℓ : ℕ) : ℕ := (((H : ℤ) - 1 - ℓ) % p).toNat

/-- The quotient `(H - 1 - ℓ) / p`. -/
def idxQuo (H p ℓ : ℕ) : ℤ := ((H : ℤ) - 1 - ℓ) / p

theorem idxRes_lt (hp : 0 < p) (H ℓ : ℕ) : idxRes H p ℓ < p := by
  unfold idxRes
  have h1 := Int.emod_nonneg ((H : ℤ) - 1 - ℓ) (by omega : (p : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos ((H : ℤ) - 1 - ℓ) (by omega : (0 : ℤ) < p)
  omega

theorem idx_eq (hp : 0 < p) (H ℓ : ℕ) :
    (H : ℤ) - 1 - ℓ = (idxRes H p ℓ : ℕ) + p * idxQuo H p ℓ := by
  unfold idxRes idxQuo
  have h1 := Int.emod_nonneg ((H : ℤ) - 1 - ℓ) (by omega : (p : ℤ) ≠ 0)
  have h2 := Int.emod_add_mul_ediv ((H : ℤ) - 1 - ℓ) p
  rw [Int.toNat_of_nonneg h1]
  linarith

/-- The block factor of the response of block `k` at the column `J p + ℓ`. -/
def Sresp (H p : ℕ) [Fact p.Prime] (ℓ J : ℕ) (k : ℤ) : ZMod p :=
  (∑ v ∈ Finset.range (H + 1),
      intrinsicCoeff ((X - 1) * T (ZMod p) k) (idxQuo H p ℓ - v + 1) *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) J)) -
    (3 / 2 : ZMod p) * ∑ v ∈ Finset.range H,
      intrinsicCoeff ((X - 1) * U (ZMod p) (k - 1)) (idxQuo H p ℓ - v) *
        palindromicRatResidue p (zetaRat v J)

theorem intrinsicCoeff_add' {R : Type*} [Semiring R] (a b : R[X]) (i : ℤ) :
    intrinsicCoeff (a + b) i = intrinsicCoeff a i + intrinsicCoeff b i := by
  unfold intrinsicCoeff
  split_ifs <;> simp

theorem sum_mul_const_mul {R : Type*} [CommRing R] (s : Finset ℕ) (f g : ℕ → R) (c : R) :
    ∑ x ∈ s, f x * c * g x = c * ∑ x ∈ s, f x * g x := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem intrinsicT_single (r : Fin (P.n N)) :
    intrinsicT P N p (Pi.single r 1) = T (ZMod p) ((r.val : ℤ) - P.g N) := by
  classical
  unfold intrinsicT
  rw [Finset.sum_eq_single r]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ r) h

theorem intrinsicU_single (r : Fin (P.n N)) :
    intrinsicU P N p (Pi.single r 1) = U (ZMod p) ((r.val : ℤ) - P.g N - 1) := by
  classical
  unfold intrinsicU
  rw [Finset.sum_eq_single r]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ r) h

/-- **Column formula.**  Single live position `e0 = idxRes`, `h = p + dh`, `dh + (p-1)/2 ≤ e0`. -/
theorem uResp_single (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {dh ℓ J : ℕ} (hh : P.h N = p + dh) (hℓ : ℓ < p) (hJ : J * p + ℓ < P.H N)
    (he : dh + (p - 1) / 2 ≤ idxRes (P.H N) p ℓ) (r : Fin (P.n N)) (k d : ℤ)
    (hrd : (r.val : ℤ) - P.g N = k * p + d) (hd : d.natAbs ≤ (p - 1) / 2) :
    uResp P N p (J * p + ℓ) (Pi.single r 1) =
      (qOne p dh d).coeff (idxRes (P.H N) p ℓ) * Sresp (P.H N) p ℓ J k := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hmod : (J * p + ℓ) % p = ℓ := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hℓ]
  have hdiv : (J * p + ℓ) / p = J := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hℓ, zero_add]
  rw [raw_response_intrinsic hP hN hp2 hH hJ, hmod, hdiv, intrinsicT_single, intrinsicU_single,
    hrd, hh]
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

#print axioms uResp_single
end
end CatalanMeasure.GenD.Uniform.W.LStar
