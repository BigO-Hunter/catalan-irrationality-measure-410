module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Rank
@[expose] public section
set_option Elab.async false

/-!
# Theorem L*: the explicit nullity bound `lstarKap` (lane G6c)

For a design `P`, `N`, and an odd prime `p`, put (for a residue `ℓ < p`)

* `jSet ℓ = {J : b ≤ J p + ℓ < L}`, `jCard ℓ = |jSet ℓ|`;
* `ℓ` *admissible* when `p ≤ h` and `(h - p) + (p-1)/2 ≤ e0 := (H-1-ℓ) mod p`; then
  `D = p - 1 - e0 + (h-p)` and `nvSet ℓ` is the set of blocks `k` with a real row `k p + d`,
  `|d| ≤ D`;
* `lrank ℓ = min (|nvSet ℓ|, jCard ℓ - 1)` for admissible `ℓ`, and `jCard ℓ - 1` otherwise;
* `lstarKap = n - Σ_{ℓ<p} lrank ℓ - (p-q)`.

`lstarKap_le_nullity` is Theorem L*: `lstarKap ≤ ν`.
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Tier3
noncomputable section

/-- The digits of the residue `ℓ`. -/
def jSet (P : Parameters) (N p ℓ : ℕ) : Finset ℕ :=
  (Finset.range (P.L N / p + 1)).filter fun J => P.b N ≤ J * p + ℓ ∧ J * p + ℓ < P.L N

theorem mem_jSet {P : Parameters} {N p ℓ J : ℕ} (hp : 0 < p) :
    J ∈ jSet P N p ℓ ↔ P.b N ≤ J * p + ℓ ∧ J * p + ℓ < P.L N := by
  unfold jSet
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have : J * p < P.L N := by omega
    have := (Nat.le_div_iff_mul_le hp).mpr this.le
    omega

/-- Admissibility of a residue (single live position, `h ≥ p`). -/
def lAdm (P : Parameters) (N p ℓ : ℕ) : Prop :=
  p ≤ P.h N ∧ (P.h N - p) + (p - 1) / 2 ≤ idxRes (P.H N) p ℓ

instance (P : Parameters) (N p ℓ : ℕ) : Decidable (lAdm P N p ℓ) := by
  unfold lAdm; infer_instance

/-- The offset bound `D = p - 1 - e0 + (h - p)` of an admissible residue. -/
def lD (P : Parameters) (N p ℓ : ℕ) : ℕ := p - 1 - idxRes (P.H N) p ℓ + (P.h N - p)

/-- The blocks of an admissible residue that meet the real rows within offset `D`. -/
def nvSet (P : Parameters) (N p ℓ : ℕ) : Finset ℤ :=
  Finset.Icc (-(((P.g N : ℤ) + lD P N p ℓ) / p))
    (((P.n N : ℤ) - P.g N - 1 + lD P N p ℓ) / p)

open Classical in
/-- The rank bound at the residue `ℓ`. -/
def lrank (P : Parameters) (N p ℓ : ℕ) : ℕ :=
  if lAdm P N p ℓ then min (nvSet P N p ℓ).card ((jSet P N p ℓ).card - 1)
  else (jSet P N p ℓ).card - 1

/-- **The Theorem L\* bound.** -/
def lstarKap (P : Parameters) (N p : ℕ) : ℕ :=
  P.n N - ∑ ℓ ∈ Finset.range p, lrank P N p ℓ - (p - P.q N)

theorem sum_zmod_val (p : ℕ) [Fact p.Prime] (f : ℕ → ℕ) :
    ∑ ℓ : ZMod p, f ℓ.val = ∑ i ∈ Finset.range p, f i := by
  refine Finset.sum_bij (fun ℓ _ => ℓ.val) (fun ℓ _ => Finset.mem_range.mpr (ZMod.val_lt ℓ))
    (fun a _ b _ h => ZMod.val_injective p h) (fun i hi => ?_) (fun _ _ => rfl)
  refine ⟨(i : ZMod p), Finset.mem_univ _, ?_⟩
  exact ZMod.val_cast_of_lt (Finset.mem_range.mp hi)

end
end CatalanMeasure.GenD.Uniform.W.LStar
