module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PhysicalCoordinates
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RowSupport
public import Submission.CatalanMeasure.Parametric.Parameters
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
@[expose] public section
set_option Elab.async false

/-!
# Block geometry of a design at a prime `p`

`k0 = ⌊-g/p⌋`, `k1 = ⌊(n-1-g)/p⌋`, `b = k1-k0+1` blocks, `ja = -g - k0 p` (the offset of the first
physical row inside the first block).  The enlarged row space has `b p + 1` coordinates and the actual
rows are the interval `[ja, ja+n)`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.Prefix
noncomputable section

def gk0 (g p : ℕ) : ℤ := (-(g : ℤ)) / p
def gk1 (n g p : ℕ) : ℤ := ((n : ℤ) - 1 - g) / p
def gb (n g p : ℕ) : ℕ := (gk1 n g p - gk0 g p + 1).toNat
def gja (g p : ℕ) : ℕ := ((-(g : ℤ)) - gk0 g p * p).toNat

theorem gja_spec {g p : ℕ} (hp : 0 < p) : ((gja g p : ℕ) : ℤ) = -(g : ℤ) - gk0 g p * p ∧ gja g p < p := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have h1 := Int.emod_add_mul_ediv (-(g : ℤ)) p
  have h2 := Int.emod_nonneg (-(g : ℤ)) hp'.ne'
  have h3 := Int.emod_lt_of_pos (-(g : ℤ)) hp'
  have hc : (-(g : ℤ)) / p * p = p * ((-(g : ℤ)) / p) := mul_comm _ _
  have hnn : 0 ≤ -(g : ℤ) - (-(g : ℤ)) / p * p := by linarith
  unfold gja gk0
  constructor
  · rw [Int.toNat_of_nonneg hnn]
  · have hlt : -(g : ℤ) - (-(g : ℤ)) / p * p < p := by linarith
    omega

theorem gb_spec {n g p : ℕ} (hp : 0 < p) (hn : 1 ≤ n) :
    gk0 g p ≤ gk1 n g p ∧ ((gb n g p : ℕ) : ℤ) = gk1 n g p - gk0 g p + 1 := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hle : gk0 g p ≤ gk1 n g p := by
    unfold gk0 gk1
    apply Int.ediv_le_ediv hp'
    omega
  refine ⟨hle, ?_⟩
  unfold gb
  rw [Int.toNat_of_nonneg (by omega)]

theorem gja_len {n g p : ℕ} (hp : 0 < p) (hn : 1 ≤ n) : gja g p + n ≤ gb n g p * p + 1 := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  obtain ⟨hja, _⟩ := gja_spec (g := g) hp
  obtain ⟨_, hb⟩ := gb_spec (g := g) hp hn
  have h1 := Int.emod_add_mul_ediv ((n : ℤ) - 1 - g) p
  have h3 := Int.emod_lt_of_pos ((n : ℤ) - 1 - g) hp'
  have h4 : gk1 n g p = ((n : ℤ) - 1 - g) / p := rfl
  have : ((gja g p + n : ℕ) : ℤ) ≤ ((gb n g p * p + 1 : ℕ) : ℤ) := by
    push_cast
    rw [hb, hja]
    nlinarith
  exact_mod_cast this

/-- The extension-by-zero of physical rows to the enlarged tiling. -/
def rowsExt (n g p : ℕ) [Fact p.Prime] (hp : 0 < p) (hn : 1 ≤ n) :
    (Fin n → ZMod p) →ₗ[ZMod p] (Fin (gb n g p * p + 1) → ZMod p) :=
  (Submodule.subtype _).comp
    (intervalRowsEquiv (K := ZMod p) (gja g p) n (gb n g p * p + 1) (gja_len hp hn)).toLinearMap

theorem rowsExt_apply (n g p : ℕ) [Fact p.Prime] (hp : 0 < p) (hn : 1 ≤ n) (c : Fin n → ZMod p)
    (i : Fin (gb n g p * p + 1)) :
    rowsExt n g p hp hn c i = if h : gja g p ≤ i.val ∧ i.val < gja g p + n then
      c ⟨i.val - gja g p, by omega⟩ else 0 := by
  simp [rowsExt, intervalRowsEquiv]

theorem rowsExt_injective (n g p : ℕ) [Fact p.Prime] (hp : 0 < p) (hn : 1 ≤ n) :
    Function.Injective (rowsExt n g p hp hn) := by
  intro c d h
  funext j
  have := congrFun h ⟨gja g p + j.val, by have := gja_len (g := g) hp hn; have := j.isLt; omega⟩
  simp only [rowsExt_apply] at this
  have hc : gja g p ≤ gja g p + j.val ∧ gja g p + j.val < gja g p + n := by
    have := j.isLt; omega
  rw [dif_pos hc, dif_pos hc] at this
  simpa using this

/-- Sum over enlarged rows of a family supported in the actual interval. -/
theorem rowsExt_sum (n g p : ℕ) [Fact p.Prime] {R : Type*} [AddCommGroup R] [Module (ZMod p) R] (hp : 0 < p)
    (hn : 1 ≤ n) (c : Fin n → ZMod p) (G : ℕ → R) :
    ∑ i : Fin (gb n g p * p + 1), rowsExt n g p hp hn c i • G i =
      ∑ r : Fin n, c r • G (gja g p + r) := by
  have hlen := gja_len (g := g) hp hn
  let ι : Fin n → Fin (gb n g p * p + 1) := fun r => ⟨gja g p + r.val, by have := r.isLt; omega⟩
  have hι : Function.Injective ι := by
    intro r s h
    apply Fin.ext
    have := congrArg Fin.val h
    simp only [ι] at this
    omega
  have h1 : ∑ r : Fin n, c r • G (gja g p + r) =
      ∑ i ∈ Finset.univ.image ι, rowsExt n g p hp hn c i • G i := by
    rw [Finset.sum_image (fun x _ y _ h => hι h)]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hc : gja g p ≤ (ι r).val ∧ (ι r).val < gja g p + n := by
      simp only [ι]; have := r.isLt; omega
    rw [rowsExt_apply, dif_pos hc]
    congr 2
    apply Fin.ext
    simp [ι]
  rw [h1]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hc : ¬ (gja g p ≤ i.val ∧ i.val < gja g p + n) := by
    intro hc
    apply hi
    rw [Finset.mem_image]
    refine ⟨⟨i.val - gja g p, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp only [ι]
    omega
  rw [rowsExt_apply, dif_neg hc, zero_smul]

end
end CatalanMeasure.GenD.Uniform.W.Charts4
