module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZAtomLin
@[expose] public section
set_option Elab.async false

/-!
# The virtual-row subspace

`a ∈ ker virtL` makes the atom data `ZCons`, provided the only missing pair members are the
`+` members of the top block beyond `rt` and the `-` members of block `0` beyond `g`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p hp : ℕ} [Fact p.Prime]

theorem virtL_apply {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (ktop k0 : Fin K) (rt g : ℕ)
    (ht : rt + 1 + (hp - rt) ≤ hp + 1) (hg : g + 1 + (hp - g) ≤ hp + 1) (a : ZPar p hp) :
    virtL u u2 y1 y2 ktop k0 rt g ht hg a =
      ((fun j => blkL u u2 y1 y2 ktop 1 (idxFin hp (rt + 1) (hp - rt) ht j) a),
       (fun j => blkL u u2 y1 y2 k0 (-1) (idxFin hp (g + 1) (hp - g) hg j) a)) := rfl

/-- **Virtual rows**: membership in the kernel of `virtL` gives `ZCons`. -/
theorem zcons_of_virt {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (ktop k0 : Fin K) (rt g : ℕ)
    (hrt : rt ≤ hp) (hg0 : g ≤ hp)
    (ht : rt + 1 + (hp - rt) ≤ hp + 1) (hg : g + 1 + (hp - g) ≤ hp + 1)
    (hvtop : ∀ d : ℕ, d ≤ hp → ¬ InRange P N ((((0 : ℤ) + (ktop : ℕ)) * p) + d) → rt < d)
    (hv0 : ∀ d : ℕ, d ≤ hp → ¬ InRange P N ((((0 : ℤ) + (k0 : ℕ)) * p) - d) → g < d)
    (hoth : ∀ (k : Fin K) (d : ℕ), d ≤ hp → k ≠ ktop → InRange P N ((((0 : ℤ) + (k : ℕ)) * p) + d))
    (hoth' : ∀ (k : Fin K) (d : ℕ), d ≤ hp → k ≠ k0 → InRange P N ((((0 : ℤ) + (k : ℕ)) * p) - d))
    (a : ZPar p hp) (ha : virtL u u2 y1 y2 ktop k0 rt g ht hg a = 0) :
    ZCons P N p 0 (Sdata u u2 a.1 a.2.1) (Adata y1 y2 a.2.2.1 a.2.2.2) := by
  have h1 : ∀ j : Fin (hp - rt), blkL u u2 y1 y2 ktop 1 (idxFin hp (rt + 1) (hp - rt) ht j) a = 0 := by
    intro j
    have := congrArg Prod.fst ha
    exact congrFun this j
  have h2 : ∀ j : Fin (hp - g), blkL u u2 y1 y2 k0 (-1) (idxFin hp (g + 1) (hp - g) hg j) a = 0 := by
    intro j
    have := congrArg Prod.snd ha
    exact congrFun this j
  intro d k
  have hd := d.isLt
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have hk : k = ktop := by
      by_contra hne; exact hn (hoth k d (by omega) hne)
    subst hk
    have hr := hvtop d (by omega) hn
    have := h1 ⟨(d : ℕ) - (rt + 1), by omega⟩
    rw [blkL_apply] at this
    have e : idxFin hp (rt + 1) (hp - rt) ht ⟨(d : ℕ) - (rt + 1), by omega⟩ = d := by
      apply Fin.ext; simp only [idxFin]; omega
    rw [e] at this
    simp only [Sdata, Adata]
    linear_combination this
  · have hk : k = k0 := by
      by_contra hne; exact hn (hoth' k d (by omega) hne)
    subst hk
    have hr := hv0 d (by omega) hn
    have := h2 ⟨(d : ℕ) - (g + 1), by omega⟩
    rw [blkL_apply] at this
    have e : idxFin hp (g + 1) (hp - g) hg ⟨(d : ℕ) - (g + 1), by omega⟩ = d := by
      apply Fin.ext; simp only [idxFin]; omega
    rw [e] at this
    simp only [Sdata, Adata]
    linear_combination this

theorem virt_top {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (ktop k0 : Fin K) (rt g : ℕ)
    (ht : rt + 1 + (hp - rt) ≤ hp + 1) (hg : g + 1 + (hp - g) ≤ hp + 1) (a : ZPar p hp)
    (ha : virtL u u2 y1 y2 ktop k0 rt g ht hg a = 0) :
    ∀ d : Fin (hp + 1), rt < (d : ℕ) →
      (u ktop * a.1 d + u2 ktop * a.2.1 d) + (y1 ktop * Aext a.2.2.1 d + y2 ktop * Aext a.2.2.2 d) = 0 := by
  intro d hd
  have hdl := d.isLt
  have e : idxFin hp (rt + 1) (hp - rt) ht ⟨(d : ℕ) - (rt + 1), by omega⟩ = d := by
    apply Fin.ext; simp only [idxFin]; omega
  have this : blkL u u2 y1 y2 ktop 1 (idxFin hp (rt + 1) (hp - rt) ht ⟨(d : ℕ) - (rt + 1), by omega⟩) a = 0 :=
    congrFun (congrArg Prod.fst ha) ⟨(d : ℕ) - (rt + 1), by omega⟩
  rw [blkL_apply, e] at this
  linear_combination this

theorem virt_zero {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (ktop k0 : Fin K) (rt g : ℕ)
    (ht : rt + 1 + (hp - rt) ≤ hp + 1) (hg : g + 1 + (hp - g) ≤ hp + 1) (a : ZPar p hp)
    (ha : virtL u u2 y1 y2 ktop k0 rt g ht hg a = 0) :
    ∀ d : Fin (hp + 1), g < (d : ℕ) →
      (u k0 * a.1 d + u2 k0 * a.2.1 d) - (y1 k0 * Aext a.2.2.1 d + y2 k0 * Aext a.2.2.2 d) = 0 := by
  intro d hd
  have hdl := d.isLt
  have e : idxFin hp (g + 1) (hp - g) hg ⟨(d : ℕ) - (g + 1), by omega⟩ = d := by
    apply Fin.ext; simp only [idxFin]; omega
  have this : blkL u u2 y1 y2 k0 (-1) (idxFin hp (g + 1) (hp - g) hg ⟨(d : ℕ) - (g + 1), by omega⟩) a = 0 :=
    congrFun (congrArg Prod.snd ha) ⟨(d : ℕ) - (g + 1), by omega⟩
  rw [blkL_apply, e] at this
  linear_combination this

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
