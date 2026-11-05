module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.ZPoly

/-!
# D2 constants: the (P') polynomial certificate of the spike classes (generic soundness)

For a trial with Chebyshev coefficients `bs` (dyadic, denominator `2^60`), `Pn` the integer
numerators of the monomial form of `chebPs (bSeq bs)` (checked once by `chebMono bs = Pn / 2^60`),
and one `q`-piece with `rho = r / 2^11`, `kappa = K / 2^14`, `c1 = 2^-j`:

* `floor_sound`: `1/4 <= chebPs (bSeq bs)` on `[-1, 1]` from a cell chain for `Pn - 2^58`;
* `SpikePolyOK`, `spikePolyOK_between`, `floor_between`: the hypotheses `hb`, `hpoly` of `SpikeTrialCert` at the count
  parameter `l = s_r / x` are affine in `l` (`chebPs_withCount`), so the two endpoints of a block suffice.
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert OAI.InternalCatalan

theorem lpEval_dyadic (ns : List ℤ) (sh : ℕ) (x : ℝ) :
    lpEval (ns.map (fun n : ℤ => (n : ℚ) / 2 ^ sh)) x = zv ns x / 2 ^ sh := by
  induction ns with
  | nil => simp [zv_nil]
  | cons c L ih =>
    simp only [List.map_cons, lpEval_cons, zv_cons]
    rw [ih]; push_cast; field_simp

theorem chebPs_of_int (bs : List ℚ) (Pn : List ℤ) (sh : ℕ)
    (h : chebMono bs = Pn.map (fun n : ℤ => (n : ℚ) / 2 ^ sh)) (u : ℝ) :
    chebPs (bSeq bs) u = zv Pn u / 2 ^ sh := by
  rw [chebPs_bSeq, h, lpEval_dyadic]

/-- Cut-chain from `-1` to `1` on the grid `2^-S`. -/
def covM1P1 (c : List ℤ) (S : ℕ) (cs : List ℤ) : Bool := zNonnegCov c S (-(2 : ℤ) ^ S) cs (2 ^ S)

theorem covM1P1_sound {c : List ℤ} {S : ℕ} {cs : List ℤ} (h : covM1P1 c S cs = true) :
    ∀ u ∈ Icc (-1 : ℝ) 1, 0 ≤ zv c u := by
  intro u hu
  have h2 : (0 : ℝ) < 2 ^ S := by positivity
  refine zNonnegCov_sound c S cs _ _ h u ?_ ?_
  · push_cast; rw [neg_div, div_self h2.ne']; exact hu.1
  · push_cast; rw [div_self h2.ne']; exact hu.2

theorem floor_sound {Pn : List ℤ} {S : ℕ} {cs : List ℤ}
    (h : covM1P1 (zAdd Pn [-(2 : ℤ) ^ 58]) S cs = true) :
    ∀ u ∈ Icc (-1 : ℝ) 1, 1 / 4 ≤ zv Pn u / 2 ^ 60 := by
  intro u hu
  have := covM1P1_sound h u hu
  rw [zv_add, zv_cons, zv_nil] at this
  push_cast at this
  have e : (2 : ℝ) ^ 60 = 4 * 2 ^ 58 := by norm_num
  rw [le_div_iff₀ (by positivity), e]
  nlinarith

/-- **The (P') inequality of a spike class at the count parameter `l = s_r / x`**, for the
denominator trial `chebPs (b_x) = 1 + l (F - 1)` (`F = chebPs b`, `chebPs_withCount`):
`κ (1 - ρ²) ≤ (1 + l (F - 1) - (1 - κ) c1) (1 + 2 ρ u + ρ²)`. -/
def SpikePolyOK (F κ ρ c1 l u : ℝ) : Prop :=
  κ * (1 - ρ ^ 2) ≤ (1 + l * (F - 1) - (1 - κ) * c1) * (1 + 2 * ρ * u + ρ ^ 2)

/-- **Interpolation in the count parameter.**  The (P') inequality is affine in `l`, so it holds on
`[l1, l2]` as soon as it holds at the two endpoints (the generic step that lets the certificates
cover every Heine count `x` of a block by its two ends). -/
theorem spikePolyOK_between {F κ ρ c1 l1 l2 l u : ℝ} (h1 : SpikePolyOK F κ ρ c1 l1 u)
    (h2 : SpikePolyOK F κ ρ c1 l2 u) (hl1 : l1 ≤ l) (hl2 : l ≤ l2) : SpikePolyOK F κ ρ c1 l u := by
  unfold SpikePolyOK at *
  set W : ℝ := 1 + 2 * ρ * u + ρ ^ 2 with hW
  rcases eq_or_lt_of_le (hl1.trans hl2) with h | h
  · have : l = l1 := by linarith
    rw [this]; exact h1
  · have e : ((1 + l * (F - 1) - (1 - κ) * c1) * W - κ * (1 - ρ ^ 2)) * (l2 - l1) =
        (l2 - l) * ((1 + l1 * (F - 1) - (1 - κ) * c1) * W - κ * (1 - ρ ^ 2)) +
          (l - l1) * ((1 + l2 * (F - 1) - (1 - κ) * c1) * W - κ * (1 - ρ ^ 2)) := by ring
    have a1 : 0 ≤ (l2 - l) * ((1 + l1 * (F - 1) - (1 - κ) * c1) * W - κ * (1 - ρ ^ 2)) :=
      mul_nonneg (by linarith) (by linarith)
    have a2 : 0 ≤ (l - l1) * ((1 + l2 * (F - 1) - (1 - κ) * c1) * W - κ * (1 - ρ ^ 2)) :=
      mul_nonneg (by linarith) (by linarith)
    have h3 : 0 ≤ ((1 + l * (F - 1) - (1 - κ) * c1) * W - κ * (1 - ρ ^ 2)) * (l2 - l1) := by
      rw [e]; linarith
    have := nonneg_of_mul_nonneg_left h3 (by linarith : (0 : ℝ) < l2 - l1)
    linarith

/-- The floor `F ≥ 1/4` gives `chebPs b_x ≥ 1/4` for every count parameter `0 ≤ l ≤ 1`
(`chebPs b_x = 1 + l (F - 1)`); so `hb` needs the floor at the reference count only. -/
theorem floor_between {F l : ℝ} (hF : 1 / 4 ≤ F) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    1 / 4 ≤ 1 + l * (F - 1) := by nlinarith

theorem floor_chebPs {bs : List ℚ} {Pn : List ℤ} {S : ℕ} {cs : List ℤ}
    (hc : chebMono bs = Pn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60))
    (h : covM1P1 (zAdd Pn [-(2 : ℤ) ^ 58]) S cs = true) :
    ∀ u ∈ Icc (-1 : ℝ) 1, 1 / 4 ≤ chebPs (bSeq bs) u := by
  intro u hu
  rw [chebPs_of_int bs Pn 60 hc]
  exact floor_sound h u hu

end CatalanMeasure.Signed.Consts
