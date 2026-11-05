module

public import Submission.CatalanMeasure.GenD.RankT
public import Submission.CatalanMeasure.GenD.RankU
public import Submission.CatalanMeasure.GenD.RankS
public import Submission.CatalanMeasure.GenD.RankU6
public import Submission.CatalanMeasure.GenD.Normalizer
public import Submission.CatalanMeasure.Parametric.ResidueRank

@[expose] public section

/-!
# Interface: the nullity lower bound `kap` (modules 4 and 5 of the G-displacement plan)

* `nullity P N p`: left nullity (mod `p`) of the filtered matrix at `z = 0`.
* `famKap P N p`: the maximum of the four proved families T, U, S, U6g, each used only inside its
  own linear window; `famKap_le_nullity` is the single statement that combines the four rank
  theorems.
* `NullityLB P`: an instance-supplied `kap` (for the displaced design: the ramp list `segExp`) with
  `kap ≤ nullity` for every prime `p ≠ 2` with `H < p²`.  `NullityLB.ofFam` builds it from
  `kap ≤ famKap`, which is a purely linear (omega) comparison.
* `det_valuation_of_nullity`: for every `z` with `p`-integral denominator, `v_p(Δ(z)) ≥ kap - 2 n`
  (the rank-valuation lemma, applied to the scaled residue matrix, which does not depend on `z`).
-/

namespace CatalanMeasure.GenD

open Polynomial Matrix CatalanMeasure.Parametric OAI.InternalCatalan

noncomputable section

/-- Left nullity of the scaled residue matrix of the base filtered matrix. -/
def nullity (P : Parameters) (N p : ℕ) [Fact p.Prime] : ℕ :=
  P.n N - (scaledResidueMatrix (p := p)
    (Matrix.of fun r k : Fin (P.n N) => Parametric.filteredEntryRat P 0 N r.val k.val)).rank

/-! ### The four families -/

/-- Window of Theorem T. -/
def TApp (P : Parameters) (N p : ℕ) : Prop :=
  2 * P.g N < p ∧ P.H N ≤ 4 * p ∧ 1 ≤ tentD P N p

def tVal (P : Parameters) (N p : ℕ) : ℕ :=
  tentD P N p - (P.n N + P.q N + P.g N + P.h N - 3 * p)

def UApp (P : Parameters) (N p : ℕ) : Prop := UWindow P N p

def uVal (P : Parameters) (N p : ℕ) : ℕ := uStar P N p - P.g N - 2 * p - 1

/-- Windows of Theorems S and U6g. -/
def SApp (P : Parameters) (N p : ℕ) : Prop :=
  P.q N + P.h N ≤ (p + 1) / 2 ∧ P.n N ≤ 4 * p + 2 * P.g N + 1

def sVal (P : Parameters) (N p : ℕ) : ℕ := sM1 P N p - sM0 P N p - sE P N p

def U6App (P : Parameters) (N p : ℕ) : Prop :=
  P.q N + P.h N ≤ (p + 1) / 2 ∧ P.n N ≤ 4 * p + 2 * P.g N + 1 ∧
    P.L N ≤ 6 * p ∧ P.b N + P.q N ≤ p + uM0 P N p

def u6Val (P : Parameters) (N p : ℕ) : ℕ := uM1 P N p - uM0 P N p - sE P N p

open Classical in
/-- The maximum of the four families, each inside its own window. -/
def famKap (P : Parameters) (N p : ℕ) : ℕ :=
  max (max (if TApp P N p then tVal P N p else 0) (if UApp P N p then uVal P N p else 0))
    (max (if SApp P N p then sVal P N p else 0) (if U6App P N p then u6Val P N p else 0))

/-- **The combined nullity bound.** -/
theorem famKap_le_nullity (P : Parameters) (hP : Admissible P) {N p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) : famKap P N p ≤ nullity P N p := by
  classical
  unfold famKap
  have hrk : (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => Parametric.filteredEntryRat P 0 N r.val k.val)).rank ≤
        P.n N := Matrix.rank_le_width _
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  · split_ifs with h
    · have := t_rank hP hN hp2 hH h.1 h.2.1 h.2.2
      unfold nullity tVal
      omega
    · exact Nat.zero_le _
  · split_ifs with h
    · have := u_rank hP hN hp2 hH h
      unfold nullity uVal
      omega
    · exact Nat.zero_le _
  · split_ifs with h
    · have := s_rank hP hN hp2 hH h.1 h.2
      unfold nullity sVal
      omega
    · exact Nat.zero_le _
  · split_ifs with h
    · have := u6_rank hP hN hp2 hH h.1 h.2.1 h.2.2.1 h.2.2.2
      unfold nullity u6Val
      omega
    · exact Nat.zero_le _

/-- An instance-supplied nullity lower bound (the `kap` of the ledger). -/
structure NullityLB (P : Parameters) where
  kap : ℕ → ℕ → ℕ
  ok : ∀ N p : ℕ, 0 < N → ∀ hp : p.Prime, p ≠ 2 → P.H N < p ^ 2 →
    haveI : Fact p.Prime := ⟨hp⟩
    kap N p ≤ nullity P N p

/-- A bound dominated by `famKap` is a nullity lower bound. -/
def NullityLB.ofFam (P : Parameters) (hP : Admissible P) (kap : ℕ → ℕ → ℕ)
    (h : ∀ N p : ℕ, 0 < N → p.Prime → p ≠ 2 → P.H N < p ^ 2 → kap N p ≤ famKap P N p) :
    NullityLB P where
  kap := kap
  ok := fun N p hN hp hp2 hH => by
    haveI : Fact p.Prime := ⟨hp⟩
    exact (h N p hN hp hp2 hH).trans (famKap_le_nullity P hP hN hp2 hH)

/-! ### From nullity to valuation -/

theorem scaledResidue_affine (P : Parameters) {N p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hH : P.H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) (r k : Fin (P.n N)) :
    palindromicRatResidue p ((p : ℚ) ^ 2 * Parametric.filteredEntryRat P z N r.val k.val) =
      palindromicRatResidue p ((p : ℚ) ^ 2 * Parametric.filteredEntryRat P 0 N r.val k.val) := by
  rw [Parametric.filteredEntryRat_affine]
  have hA := scaled_base_den P hp2 hH r k
  have hC := catalan_matrix_den P (N := N) (q := p) hp2 r k
  have hA' : (((p : ℚ) ^ 2 * Parametric.filteredEntryRat P 0 N r.val k.val).den : ZMod p) ≠ 0 := hA
  have hzc : ((z * Parametric.filteredCatalanCoeffRat P N r.val k.val).den : ZMod p) ≠ 0 :=
    (rational_residue_mul hz hC).1
  have hsplit : (p : ℚ) ^ 2 * (Parametric.filteredEntryRat P 0 N r.val k.val +
        z * Parametric.filteredCatalanCoeffRat P N r.val k.val) =
      (p : ℚ) ^ 2 * Parametric.filteredEntryRat P 0 N r.val k.val +
        (p : ℚ) ^ 2 * (z * Parametric.filteredCatalanCoeffRat P N r.val k.val) := by ring
  have hpp : (((p : ℚ) ^ 2 * (z * Parametric.filteredCatalanCoeffRat P N r.val k.val)).den :
      ZMod p) ≠ 0 :=
    (rational_residue_mul (by simpa using (one_ne_zero : (1 : ZMod p) ≠ 0)) hzc).1
  rw [hsplit, palindromicRatResidue_add hA' hpp,
    palindromicRatResidue_mul (by simp) hzc]
  have h0 : palindromicRatResidue p ((p : ℚ) ^ 2) = 0 := by
    have : ((p : ℚ) ^ 2) = (((p ^ 2 : ℕ) : ℤ) : ℚ) := by push_cast; ring
    rw [this, palindromicRatResidue_intCast]
    simp
  rw [h0]
  simp

theorem nat_aux {n k r : ℕ} (h : k ≤ n - r) (hr : r ≤ n) : r ≤ n - k := by omega

/-- **Valuation from nullity.** -/
theorem det_valuation_of_nullity (P : Parameters) {N p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hH : P.H N < p ^ 2) {kap : ℕ} (hk : kap ≤ nullity P N p) (z : ℚ)
    (hz : (z.den : ZMod p) ≠ 0) :
    -((2 * P.n N - kap : ℕ) : ℤ) ≤ padicValRat p (Parametric.determinantRat P z N) := by
  let M : Matrix (Fin (P.n N)) (Fin (P.n N)) ℚ :=
    Matrix.of fun r k => Parametric.filteredEntryRat P z N r.val k.val
  have hM : ∀ i j, ((((p : ℚ) ^ 2 * M i j).den : ℕ) : ZMod p) ≠ 0 := by
    intro r k
    simp only [M, Matrix.of_apply]
    rw [Parametric.filteredEntryRat_affine]
    have hsplit : (p : ℚ) ^ 2 * (Parametric.filteredEntryRat P 0 N r.val k.val +
          z * Parametric.filteredCatalanCoeffRat P N r.val k.val) =
        (p : ℚ) ^ 2 * Parametric.filteredEntryRat P 0 N r.val k.val +
          (p : ℚ) ^ 2 * (z * Parametric.filteredCatalanCoeffRat P N r.val k.val) := by ring
    have hC := catalan_matrix_den P (N := N) (q := p) hp2 r k
    have hzc : ((z * Parametric.filteredCatalanCoeffRat P N r.val k.val).den : ZMod p) ≠ 0 :=
      (rational_residue_mul hz hC).1
    have hpp : (((p : ℚ) ^ 2 * (z * Parametric.filteredCatalanCoeffRat P N r.val k.val)).den :
        ZMod p) ≠ 0 :=
      (rational_residue_mul (by simpa using (one_ne_zero : (1 : ZMod p) ≠ 0)) hzc).1
    rw [hsplit]
    exact (rational_residue_add (scaled_base_den P hp2 hH r k) hpp).1
  have hmat : scaledResidueMatrix (p := p) M = scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => Parametric.filteredEntryRat P 0 N r.val k.val) := by
    ext r k
    simp only [scaledResidueMatrix, M, Matrix.of_apply]
    exact scaledResidue_affine P hp2 hH z hz r k
  have hkn : kap ≤ P.n N := hk.trans (Nat.sub_le _ _)
  have hr : (scaledResidueMatrix (p := p) M).rank ≤ P.n N - kap := by
    rw [hmat]
    exact nat_aux hk (Matrix.rank_le_width _)
  have h := residue_rank_valuation_lower (p := p) M hM hkn hr
  have hd : Parametric.determinantRat P z N = M.det := rfl
  rw [hd]
  exact h

end

end CatalanMeasure.GenD
