module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZVirt
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ2.CellsLZ
@[expose] public section
set_option Elab.async false

/-!
# Law_L virtual rows (G2h)

In the Law_L(4) design the top block `4` has *no* `+` members (`d = 0` included) and no `-`
members for `δ < d₀`.  The virtual-row subspace is `ker virtL` (the `+` family `d > rt`,
`rt = 0`, and block `0`) together with the extra family `S_δ - A_δ = 0`, `δ < d₀` of the top
block (for `δ = 0` this is `S_0 = 0`, since `A_0 = 0`).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p hp : ℕ} [Fact p.Prime]

/-- The extra family: `S_δ - A_δ` of the top block, `δ < d0`. -/
def extraL {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (ktop : Fin K) (d0 : ℕ) (hd : d0 ≤ hp + 1) :
    ZPar p hp →ₗ[ZMod p] (Fin d0 → ZMod p) :=
  LinearMap.pi fun j => blkL u u2 y1 y2 ktop (-1) ⟨j, by have := j.isLt; omega⟩


/-- The full virtual-row map of Law_L. -/
def virtL2 {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (ktop k0 : Fin K) (rt g d0 : ℕ)
    (ht : rt + 1 + (hp - rt) ≤ hp + 1) (hg : g + 1 + (hp - g) ≤ hp + 1) (hd : d0 ≤ hp + 1) :
    ZPar p hp →ₗ[ZMod p] ((Fin (hp - rt) → ZMod p) × (Fin (hp - g) → ZMod p)) × (Fin d0 → ZMod p) :=
  (virtL u u2 y1 y2 ktop k0 rt g ht hg).prod (extraL u u2 y1 y2 ktop d0 hd)

/-- **Virtual rows of Law_L**: membership in `ker virtL2` gives `ZCons`. -/
theorem zcons_of_virt2 {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (ktop k0 : Fin K) (rt g d0 : ℕ)
    (hrt : rt ≤ hp) (hg0 : g ≤ hp) (hd0 : 1 ≤ d0) (hd0' : d0 ≤ hp)
    (ht : rt + 1 + (hp - rt) ≤ hp + 1) (hg : g + 1 + (hp - g) ≤ hp + 1)
    (hvtop : ∀ d : ℕ, d ≤ hp → ¬ InRange P N ((((0 : ℤ) + (ktop : ℕ)) * p) + d) → rt < d ∨ d = 0)
    (hvtopm : ∀ d : ℕ, d ≤ hp → ¬ InRange P N ((((0 : ℤ) + (ktop : ℕ)) * p) - d) → d < d0)
    (hv0 : ∀ d : ℕ, d ≤ hp → ¬ InRange P N ((((0 : ℤ) + (k0 : ℕ)) * p) - d) → g < d)
    (hoth : ∀ (k : Fin K) (d : ℕ), d ≤ hp → k ≠ ktop → InRange P N ((((0 : ℤ) + (k : ℕ)) * p) + d))
    (hoth' : ∀ (k : Fin K) (d : ℕ), d ≤ hp → k ≠ k0 → k ≠ ktop →
      InRange P N ((((0 : ℤ) + (k : ℕ)) * p) - d))
    (a : ZPar p hp) (ha : virtL2 u u2 y1 y2 ktop k0 rt g d0 ht hg (by omega) a = 0) :
    ZCons P N p 0 (Sdata u u2 a.1 a.2.1) (Adata y1 y2 a.2.2.1 a.2.2.2) := by
  have hv : virtL u u2 y1 y2 ktop k0 rt g ht hg a = 0 := congrArg Prod.fst ha
  have hE : ∀ j : Fin d0, blkL u u2 y1 y2 ktop (-1) ⟨j, by have := j.isLt; omega⟩ a = 0 :=
    fun j => congrFun (congrArg Prod.snd ha) j
  have h1 := virt_top u u2 y1 y2 ktop k0 rt g ht hg a hv
  have h2 := virt_zero u u2 y1 y2 ktop k0 rt g ht hg a hv
  intro d k
  have hd := d.isLt
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have hk : k = ktop := by
      by_contra hne; exact hn (hoth k d (by omega) hne)
    subst hk
    rcases hvtop d (by omega) hn with hr | hz
    · have := h1 d hr
      simp only [Sdata, Adata]
      linear_combination this
    · have hd0' : (d : ℕ) < d0 := by omega
      have := hE ⟨d, hd0'⟩
      rw [blkL_apply] at this
      have hdz : d = 0 := Fin.ext hz
      subst hdz
      have hA1 : Aext a.2.2.1 (0 : Fin (hp + 1)) = 0 := by simp [Aext]
      have hA2 : Aext a.2.2.2 (0 : Fin (hp + 1)) = 0 := by simp [Aext]
      simp only [Sdata, Adata, hA1, hA2] at this ⊢
      linear_combination this
  · by_cases hkt : k = ktop
    · subst hkt
      have hdl := hvtopm d (by omega) hn
      have := hE ⟨d, hdl⟩
      rw [blkL_apply] at this
      simp only [Sdata, Adata]
      linear_combination this
    · have hk : k = k0 := by
        by_contra hne; exact hn (hoth' k d (by omega) hne hkt)
      subst hk
      have hr := hv0 d (by omega) hn
      have := h2 d hr
      simp only [Sdata, Adata]
      linear_combination this

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
