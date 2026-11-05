module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic
public import Submission.CatalanMeasure.Parametric.BlockAlgebra
public import Submission.CatalanMeasure.Parametric.IntegerRows

@[expose] public section

/-!
# Residue-matrix certificates modulo a prime (generic)

A certificate that a square matrix over `ZMod ℓ` is invertible is a matrix `B` with
`M * B = 1`, checked once row by row (`mul_eq_one_of_rows`).  Entries are stored as lists of
natural-number residues.  `c3_of_certificate` turns three such certificates for the base
matrices `B0`, `B0 + B1`, `B0 - B1` of a design `P` into the C3 statement (the three residue
determinants are nonzero).  Nothing here depends on the design, the prime, or the size.
-/

namespace CatalanMeasure.GenD
namespace CertMod

open Matrix CatalanMeasure.Parametric OAI.InternalCatalan

/-- Entry `(r, k)` of a table of residues (zero outside the table). -/
def entry (ℓ : ℕ) (rows : List (List ℕ)) (r k : ℕ) : ZMod ℓ :=
  (((rows.getD r []).getD k 0 : ℕ) : ZMod ℓ)

/-- The square matrix of a residue table. -/
def mat (n ℓ : ℕ) (rows : List (List ℕ)) : Matrix (Fin n) (Fin n) (ZMod ℓ) :=
  Matrix.of fun r k => entry ℓ rows r.val k.val

/-- `B0 + σ B1` from the table of the `(n+1) × n` base rows. -/
def caseMat (n ℓ : ℕ) (rows : List (List ℕ)) (σ : ZMod ℓ) : Matrix (Fin n) (Fin n) (ZMod ℓ) :=
  Matrix.of fun r k => entry ℓ rows r.val k.val + σ * entry ℓ rows (r.val + 1) k.val

theorem det_ne_zero_of_mul_eq_one {n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    {M B : Matrix (Fin n) (Fin n) R} (h : M * B = 1) : M.det ≠ 0 := by
  have hh := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hh
  exact left_ne_zero_of_mul_eq_one hh

/-- Row-by-row check of `M * B = 1`. -/
theorem mul_eq_one_of_rows {n : ℕ} {R : Type*} [CommRing R] [DecidableEq R]
    {M B : Matrix (Fin n) (Fin n) R}
    (h : ∀ r k : Fin n, (∑ j : Fin n, M r j * B j k) = if r = k then 1 else 0) :
    M * B = 1 := by
  ext r k
  simpa [Matrix.mul_apply, Matrix.one_apply] using h r k

/-- The product check for one row of `caseMat σ` against the inverse table, as a statement
about the tables only (this is what each per-row declaration proves). -/
def RowOK (n ℓ : ℕ) (rows inv : List (List ℕ)) (σ : ZMod ℓ) (r : Fin n) : Prop :=
  ∀ k : Fin n, (∑ j : Fin n, caseMat n ℓ rows σ r j * mat n ℓ inv j k) = if r = k then 1 else 0

theorem caseMat_mul_eq_one {n ℓ : ℕ} {rows inv : List (List ℕ)} {σ : ZMod ℓ}
    (h : ∀ r : Fin n, RowOK n ℓ rows inv σ r) : caseMat n ℓ rows σ * mat n ℓ inv = 1 :=
  mul_eq_one_of_rows fun r k => h r k


/-- The base entry `(r, k)` recomputed from residue tables of `momentRat` and `zetaRat`. -/
def tabEntry (P : Parameters) (ℓ : ℕ) [Fact ℓ.Prime] (MT ZT : List (List ℕ)) (r k : ℕ) :
    ZMod ℓ :=
  ∑ v ∈ Finset.range (P.q0 + 1), baseFilterWeight P ℓ v *
    ((∑ u ∈ Finset.range (P.H 1),
        (((intRowP P 1 r).getD u 0 : ℤ) : ZMod ℓ) * entry ℓ MT u (P.b0 + k + v)) -
      (3 / 2 : ZMod ℓ) * ∑ u ∈ Finset.range (P.H 1),
        (((intRowD P 1 r).getD u 0 : ℤ) : ZMod ℓ) * entry ℓ ZT u (P.b0 + k + v))

/-- **Table bridge.**  If the tables hold the residues of `momentRat u j` and `zetaRat u j`
for `u < H(1)`, `j < L(1)`, the base contraction equals `tabEntry` (a rational-free
computation).  The tables are verified once, row by row, against the rational definitions. -/
theorem baseFilteredContraction_eq_tabEntry (P : Parameters) (ℓ : ℕ) [Fact ℓ.Prime]
    (MT ZT : List (List ℕ))
    (hM : ∀ u j : ℕ, u < P.H 1 → j < P.L 1 →
      palindromicRatResidue ℓ (momentRat u j) = entry ℓ MT u j)
    (hZ : ∀ u j : ℕ, u < P.H 1 → j < P.L 1 →
      palindromicRatResidue ℓ (zetaRat u j) = entry ℓ ZT u j)
    (r : ℕ) (k : Fin P.n0) :
    baseFilteredContraction P ℓ r k = tabEntry P ℓ MT ZT r k.val := by
  unfold baseFilteredContraction tabEntry
  apply Finset.sum_congr rfl
  intro v hv
  have hv' := Finset.mem_range.mp hv
  have hk := k.isLt
  have hj : P.b0 + k.val + v < P.L 1 := by
    simp only [Parameters.L, Parameters.n, Parameters.b, Parameters.q, Nat.mul_one]
    omega
  unfold baseRawContraction
  simp_rw [rowP_coeff_algorithm, rowD_coeff_algorithm]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro u hu
    rw [hM u _ (Finset.mem_range.mp hu) hj]
  · congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [hZ u _ (Finset.mem_range.mp hu) hj]

/-- **C3 from three inverse tables.**  If the table `rows` computes the base contractions
modulo the prime `ℓ` and `B0`, `B0 + B1`, `B0 - B1` have the stated inverse tables, the three
residue determinants are nonzero. -/
theorem c3_of_certificate (P : Parameters) (ℓ : ℕ) [Fact ℓ.Prime] (rows i0 ip im : List (List ℕ))
    (hE : ∀ (r k : ℕ) (hk : k < P.n0), r < P.n0 + 1 →
      baseFilteredContraction P ℓ r ⟨k, hk⟩ = entry ℓ rows r k)
    (h0 : caseMat P.n0 ℓ rows 0 * mat P.n0 ℓ i0 = 1)
    (hp : caseMat P.n0 ℓ rows 1 * mat P.n0 ℓ ip = 1)
    (hm : caseMat P.n0 ℓ rows (-1) * mat P.n0 ℓ im = 1) :
    (baseB0Residue P ℓ).det ≠ 0 ∧
      (baseB0Residue P ℓ + baseB1Residue P ℓ).det ≠ 0 ∧
      (baseB0Residue P ℓ - baseB1Residue P ℓ).det ≠ 0 := by
  have key : ∀ σ : ZMod ℓ, baseB0Residue P ℓ + σ • baseB1Residue P ℓ = caseMat P.n0 ℓ rows σ := by
    intro σ
    ext r k
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, caseMat, Matrix.of_apply,
      baseB0Residue, baseB1Residue]
    rw [hE r.val k.val k.isLt (by omega), hE (r.val + 1) k.val k.isLt (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · have := key 0
    rw [zero_smul, add_zero] at this
    rw [this]; exact det_ne_zero_of_mul_eq_one h0
  · have := key 1
    rw [one_smul] at this
    rw [this]; exact det_ne_zero_of_mul_eq_one hp
  · have := key (-1)
    rw [neg_one_smul, ← sub_eq_add_neg] at this
    rw [this]; exact det_ne_zero_of_mul_eq_one hm

end CertMod
end CatalanMeasure.GenD
