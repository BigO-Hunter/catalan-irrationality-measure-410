module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar2.Theorem3
@[expose] public section
set_option Elab.async false

/-!
# Counting lemmas and cells for Theorem L\* with `h ≤ p` (lane G6d)

* `jSet_eq_Icc`: the digit set of a residue from linear data;
* `lstar2Kap_ge`: per-residue gaps give `Σ gg ≤ lstar2Kap` (for `q ≤ p`);
* `gap2_ge`: the per-residue inequality (window at `ℓ' - m`);
* `lstar2LB`: Theorem L\* as a `NullityLB`.
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar2
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section
variable {P : Parameters} {N p : ℕ}

/-- **`lstar2LB`**: Theorem L\* (all `h`) as a nullity lower bound. -/
def lstar2LB (P : Parameters) (hP : Admissible P) : NullityLB P where
  kap := lstar2Kap P
  ok := fun N p hN hp hp2 hH => by
    haveI : Fact p.Prime := ⟨hp⟩
    exact lstar2Kap_le_nullity hP hN hp2 hH

theorem jSet_eq_Icc (hp : 0 < p) {ℓ u1 u2 : ℕ} (h1 : 1 ≤ u2) (h2 : u1 * p + ℓ < P.L N)
    (h3 : P.b N ≤ u2 * p + ℓ) (h4 : P.L N ≤ (u1 + 1) * p + ℓ) (h5 : (u2 - 1) * p + ℓ < P.b N) :
    jSet P N p ℓ = Finset.Icc u2 u1 := by
  ext J
  rw [mem_jSet hp, Finset.mem_Icc]
  constructor
  · intro ⟨ha, hb⟩
    constructor
    · by_contra hc
      have : J ≤ u2 - 1 := by omega
      have := Nat.mul_le_mul_right p this
      omega
    · by_contra hc
      have : u1 + 1 ≤ J := by omega
      have := Nat.mul_le_mul_right p this
      omega
  · intro ⟨ha, hb⟩
    have a1 := Nat.mul_le_mul_right p ha
    have a2 := Nat.mul_le_mul_right p hb
    constructor <;> omega

/-- **From residue gaps to a bound on `lstar2Kap`** (`q ≤ p`). -/
theorem lstar2Kap_ge (hp : 0 < p) (hqp : P.q N ≤ p) (gg : ℕ → ℕ)
    (h : ∀ ℓ < p, gg ℓ + lrank2 P N p ℓ + 1 ≤ (jSet P N p ℓ).card) :
    ∑ ℓ ∈ Finset.range p, gg ℓ ≤ lstar2Kap P N p := by
  have hs := sum_jCard_le (P := P) (N := N) hp
  have h1 : ∑ ℓ ∈ Finset.range p, (gg ℓ + lrank2 P N p ℓ + 1) ≤
      ∑ ℓ ∈ Finset.range p, (jSet P N p ℓ).card :=
    Finset.sum_le_sum fun ℓ hℓ => h ℓ (Finset.mem_range.mp hℓ)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one] at h1
  have hL : P.L N = P.n N + P.b N + P.q N := rfl
  unfold lstar2Kap
  omega

/-- The per-residue inequality of a window cell.  `ℓ0 = ℓ' - (p - h)`, `e0 = H - 1 - ℓ0 - μ p`. -/
theorem gap2_ge (P : Parameters) (N p ℓ : ℕ) (hp : 0 < p) (hℓ : ℓ < p) (hhp : P.h N ≤ p)
    (μ u1 u2 : ℕ) (u3 u4 : ℤ) (g0 : ℕ)
    (hm : p - P.h N ≤ ℓ)
    (hJ : ∀ ℓ'', ℓ - (p - P.h N) ≤ ℓ'' → ℓ'' ≤ ℓ → jSet P N p ℓ'' = Finset.Icc u2 u1)
    (hm1 : μ * p + (ℓ - (p - P.h N)) + 1 ≤ P.H N)
    (hm2 : P.H N ≤ μ * p + p + (ℓ - (p - P.h N)))
    (hadm : (p - 1) / 2 + μ * p + (ℓ - (p - P.h N)) + 1 ≤ P.H N)
    (hC3 : (P.n N : ℤ) - P.g N - 1 +
      ((p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ((ℓ - (p - P.h N) : ℕ) : ℤ) - μ * p)) < (u3 + 1) * p)
    (hC4 : (P.g N : ℤ) +
      ((p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ((ℓ - (p - P.h N) : ℕ) : ℤ) - μ * p)) < (1 - u4) * p)
    (hu : u4 ≤ u3 + 1) (h12 : u2 ≤ u1) (hg : (g0 : ℤ) + u3 + 1 ≤ u1 - u2 + u4) :
    g0 + lrank2 P N p ℓ + 1 ≤ (jSet P N p ℓ).card := by
  classical
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  set ℓ0 := ℓ - (p - P.h N) with hℓ0
  have hres : idxRes (P.H N) p ℓ0 = P.H N - 1 - ℓ0 - μ * p := by
    unfold idxRes
    have e : (P.H N : ℤ) - 1 - ℓ0 = ((P.H N : ℤ) - 1 - ℓ0 - μ * p) + (μ : ℤ) * p := by ring
    have h1 : (0 : ℤ) ≤ (P.H N : ℤ) - 1 - ℓ0 - μ * p := by
      have : ((μ * p + ℓ0 + 1 : ℕ) : ℤ) ≤ (P.H N : ℤ) := by exact_mod_cast hm1
      push_cast at this; linarith
    have h2 : (P.H N : ℤ) - 1 - ℓ0 - μ * p < p := by
      have : (P.H N : ℤ) ≤ ((μ * p + p + ℓ0 : ℕ) : ℤ) := by exact_mod_cast hm2
      push_cast at this; linarith
    have : ((P.H N : ℤ) - 1 - ℓ0) % p = (P.H N : ℤ) - 1 - ℓ0 - μ * p := by
      conv_lhs => rw [e]
      rw [Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt h1 h2
    rw [this]
    omega
  have hJc : jSet P N p ℓ = Finset.Icc u2 u1 := hJ ℓ (by omega) le_rfl
  have hwin : wOK P N p ℓ := by
    refine ⟨hhp, hm, ?_, ?_⟩
    · rw [hres]; omega
    · intro s hs
      rw [hJc]
      exact hJ (ℓ0 + s) (by omega) (by omega)
  have hcard : (jSet P N p ℓ).card = u1 + 1 - u2 := by
    rw [hJc, Nat.card_Icc]
  have hN : (nvSet P N p ℓ0).card ≤ (u3 + 1 - u4).toNat := by
    have hD : ((lD P N p ℓ0 : ℕ) : ℤ) =
        (p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ℓ0 - μ * p) := by
      unfold lD
      rw [hres]
      have : P.H N - 1 - ℓ0 - μ * p + 1 ≤ p := by omega
      have h6 : P.h N - p = 0 := by omega
      rw [h6]
      omega
    have hsub : nvSet P N p ℓ0 ⊆ Finset.Icc u4 u3 := by
      intro k hk
      unfold nvSet at hk
      rw [Finset.mem_Icc] at hk ⊢
      rw [hD] at hk
      constructor
      · have h1 := Int.ediv_lt_of_lt_mul hpz (by linarith [hC4] :
          (P.g N : ℤ) + ((p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ℓ0 - μ * p)) < (1 - u4) * p)
        linarith [hk.1]
      · have h1 := Int.ediv_lt_of_lt_mul hpz (by linarith [hC3] :
          (P.n N : ℤ) - P.g N - 1 + ((p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ℓ0 - μ * p)) <
            (u3 + 1) * p)
        linarith [hk.2]
    have := Finset.card_le_card hsub
    rw [Int.card_Icc] at this
    exact this
  unfold lrank2
  rw [if_pos hwin, ← hℓ0]
  have := min_le_left (nvSet P N p ℓ0).card ((jSet P N p ℓ).card - 1)
  omega

#print axioms gap2_ge
#print axioms lstar2Kap_ge
#print axioms jSet_eq_Icc
end
end CatalanMeasure.GenD.Uniform.W.LStar2
