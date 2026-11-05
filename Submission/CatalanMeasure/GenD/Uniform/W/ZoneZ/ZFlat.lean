module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZXpoly
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.CellsRank1
@[expose] public section
set_option Elab.async false

/-!
# J-flatness of a Theorem Z atom (Law_H, `s = 4`, no cap: `η < p`)

`dotv J r = Σ_c v_J[c] seq_c[r]` with `seq[r] = (π1[r+p], π2[r+p], λ1[r], λ2[r])`.  In the window
`s = 4` (`ℓ ≤ η`, `r = η - ℓ`) the response is

    resp J ℓ = ψ+(J,4)(u) fold(π1)[r] + dotv J r        (`regionI_eq`).

With the cell facts (`ψ+(J,4)(u) = 1`, `v_J ∝ w`, (P*)) and the explicit conditions
(main, digit 0, digit `s`, window `s-1`), the response is `fold(π1)[r]` for every column.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem divmod_eq (T q r p : ℤ) (hp : 0 < p) (hT : T = p * q + r) (h0 : 0 ≤ r) (h1 : r < p) :
    T / p = q ∧ T % p = r :=
  (Int.ediv_emod_unique hp).mpr ⟨by rw [hT]; ring, h0, h1⟩

/-- The covector values of a cell, window `s = 4`. -/
def fuV (p K H : ℕ) [Fact p.Prime] (u : Fin K → ZMod p) (J : ℕ) (σ : ℤ) : ZMod p :=
  (profTp' p K).psi H J σ u

/-- The window-`s` response vector `v_J` of a general set of cell vectors (`s = 4`). -/
def vv (p K H : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) (J : ℕ) (c : ℕ) : ZMod p :=
  match c with
  | 0 => (profTp' p K).psi H J (3 : ℕ) u - (profTp' p K).psi H J (4 : ℕ) u
  | 1 => (profTp' p K).psi H J (3 : ℕ) u2 - (profTp' p K).psi H J (4 : ℕ) u2
  | 2 => (profTm' p K).psi H J (4 : ℕ) y1
  | 3 => (profTm' p K).psi H J (4 : ℕ) y2
  | _ => 0

/-- Top-block and block-`0` vectors. -/
def topv {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (k : Fin K) (c : ℕ) : ZMod p :=
  match c with
  | 0 => u k | 1 => u2 k | 2 => y1 k | 3 => y2 k | _ => 0

def zerov {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (k : Fin K) (c : ℕ) : ZMod p :=
  match c with
  | 0 => u k | 1 => u2 k | 2 => - y1 k | 3 => - y2 k | _ => 0

/-- The cell facts used by the flatness proof (Law_H, `s = 4`). -/
structure CellHyp (p K H : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p)
    (μ2 μ3 ν ρ : ZMod p) (ktop k0 : Fin K) : Prop where
  fold : ∀ J, J ∈ [1, 2, 3, 4] → fuV p K H u J ((4 : ℕ) : ℤ) = 1
  r1 : ∀ c < 4, vv p K H u u2 y1 y2 1 c = -3 * (vv p K H u u2 y1 y2 2 c - vv p K H u u2 y1 y2 1 c)
  r3 : ∀ c < 4, vv p K H u u2 y1 y2 3 c =
    (-3 / 2) * (vv p K H u u2 y1 y2 2 c - vv p K H u u2 y1 y2 1 c)
  ps : ∀ c < 4, vv p K H u u2 y1 y2 4 c - vv p K H u u2 y1 y2 1 c =
    μ2 * (vv p K H u u2 y1 y2 2 c - vv p K H u u2 y1 y2 1 c) +
    μ3 * (vv p K H u u2 y1 y2 3 c - vv p K H u u2 y1 y2 1 c) +
    ν * topv u u2 y1 y2 ktop c + ρ * zerov u u2 y1 y2 k0 c

/-- The four sequences at position `r`. -/
def seqc (π1 π2 l1 l2 : ℕ → ZMod p) (p' r : ℕ) (c : ℕ) : ZMod p :=
  match c with
  | 0 => π1 (r + p') | 1 => π2 (r + p') | 2 => l1 r | 3 => l2 r | _ => 0

def dotc (v : ℕ → ZMod p) (π1 π2 l1 l2 : ℕ → ZMod p) (p' r : ℕ) : ZMod p :=
  ∑ c ∈ Finset.range 4, v c * seqc π1 π2 l1 l2 p' r c

theorem dotc_expand (v : ℕ → ZMod p) (π1 π2 l1 l2 : ℕ → ZMod p) (p' r : ℕ) :
    dotc v π1 π2 l1 l2 p' r = v 0 * π1 (r + p') + v 1 * π2 (r + p') + v 2 * l1 r + v 3 * l2 r := by
  simp [dotc, Finset.sum_range_succ, seqc]

theorem dotc_sub (v w : ℕ → ZMod p) (π1 π2 l1 l2 : ℕ → ZMod p) (p' r : ℕ) :
    dotc (fun c => v c - w c) π1 π2 l1 l2 p' r =
      dotc v π1 π2 l1 l2 p' r - dotc w π1 π2 l1 l2 p' r := by
  simp only [dotc_expand]; ring

theorem dotc_smul (m : ZMod p) (v : ℕ → ZMod p) (π1 π2 l1 l2 : ℕ → ZMod p) (p' r : ℕ) :
    dotc (fun c => m * v c) π1 π2 l1 l2 p' r = m * dotc v π1 π2 l1 l2 p' r := by
  simp only [dotc_expand]; ring

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
