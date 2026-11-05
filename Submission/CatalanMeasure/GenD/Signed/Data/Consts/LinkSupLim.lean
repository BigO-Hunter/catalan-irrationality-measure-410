module

public import Submission.CatalanMeasure.GenD.Analytic.Glue
public import Submission.CatalanMeasure.GenD.Signed.Brackets
public import Submission.CatalanMeasure.LogFieldStability

@[expose] public section

/-!
# D2 constants: the finite-`N` limit passage for `LinkCert.hgap` / `LinkCert.hsup`

The existing `rowFieldG_corrected_eventually` takes the cap on the whole of `(-1,0) ∪ (0,1)`; the
link sups need a *lower* cap on a window `S` only.  `freeRowX_eventually_of_region` is the same
proof with `log_field_correction_eventually` applied to an arbitrary window `S`:
if the limit field `rowFieldG α β γ u v` is `≤ M` on `S`, then eventually in `N`
`freeRowX P N u v ≤ M + ε` on `S`.  `link_cap_of_region` converts to the shape of the hypotheses.
-/

namespace CatalanMeasure.Signed.Consts
open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric CatalanMeasure.CellCert
  OAI.InternalCatalan Filter Set
open scoped Topology

noncomputable section

theorem freeRowX_eventually_of_region {P : Parameters} (hP : Admissible P) {u v : ℕ → ℝ}
    (hu : Summable (fun k => |u k|)) (hv : Summable (fun k => |v k|)) {α β γ : ℝ}
    (hα : α = ((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0) (hβ : β = 2 * (P.h0 : ℝ) / P.n0)
    (hγ : γ = ((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0)
    {S : Set ℝ} (hS : S ⊆ Ico (-1 : ℝ) 0 ∪ Ioo 0 1) {M ε : ℝ}
    (hM : ∀ x ∈ S, rowFieldG α β γ u v x ≤ M) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ S,
      freeRowX P N u v x ≤ M + ε := by
  have hα0 : 0 ≤ α := by rw [hα]; have := n0_pos hP; positivity
  have hβ0 : 0 < β := by
    rw [hβ]; have := n0_pos hP; have : (0 : ℝ) < P.h0 := by exact_mod_cast hP.2.2.2.1
    positivity
  obtain ⟨K, hK⟩ := rowFieldG_endpoint_bound (γ := γ) (β := β) hu hv hα0
  have hh := CatalanMeasure.log_field_correction_eventually (S := S)
    (F := rowFieldG α β γ u v) (a := 2) (b := 1 / 2) hβ0 (by norm_num) (by norm_num)
    (fun x hx => by
      rcases hS hx with h | h
      · exact ⟨h.1, by linarith only [h.2]⟩
      · exact ⟨by linarith only [h.1], h.2⟩)
    hM (fun x hx => hK x (hS hx)) (fun N : ℕ => 1 / ((P.n0 : ℝ) * N))
    (fun N => by have := n0_pos hP; positivity) (invScale_tendsto hP) hε
  filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc hN x hx
  have e : freeRowX P N u v x =
      populationPhysicalFreeField P N x - 4 * barrierTrialT u x - barrierTrialS v x -
        Real.log (1 - x) / (2 * (P.n N : ℝ)) := by
    unfold freeRowX; ring
  rw [e, physical_free_row_identity, param_row_field_eq hP hN]
  have hb' := hc x hx
  rw [rowFieldG_eq, hα, hβ, hγ] at hb'
  linarith only [hb']

/-- The window cap in the form of the `LinkCert` hypotheses: a limit cap `Mx - d0` on `S` gives, for
every `d < d0` and `δ ≥ 0`, eventually `freeRowX ≤ Mx + δ/4 - d` on `S`. -/
theorem link_cap_of_region {P : Parameters} (hP : Admissible P) {u v : ℕ → ℝ}
    (hu : Summable (fun k => |u k|)) (hv : Summable (fun k => |v k|)) {α β γ : ℝ}
    (hα : α = ((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0) (hβ : β = 2 * (P.h0 : ℝ) / P.n0)
    (hγ : γ = ((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0)
    {S : Set ℝ} (hS : S ⊆ Ico (-1 : ℝ) 0 ∪ Ioo 0 1) {Mx d0 d δ : ℝ}
    (hM : ∀ x ∈ S, rowFieldG α β γ u v x ≤ Mx - d0) (hd : d < d0) (hδ : 0 ≤ δ) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ S, freeRowX P N u v x ≤ Mx + δ / 4 - d := by
  have := freeRowX_eventually_of_region hP hu hv hα hβ hγ hS hM (ε := d0 - d) (by linarith)
  filter_upwards [this] with N hN x hx
  have := hN x hx
  linarith

end

end CatalanMeasure.Signed.Consts
