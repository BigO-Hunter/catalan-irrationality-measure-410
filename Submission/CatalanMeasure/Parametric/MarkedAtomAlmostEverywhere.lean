module

public import Submission.CatalanMeasure.MixedArbitraryAtoms
public import Submission.OAI.NumberTheory.Catalan.Estimates.RealCoordinateProduct

/-!
# Almost-everywhere geometry for marked atoms

Free integration nodes avoid one another and every fixed atom because the
underlying measures have no atoms. No assertion about a determinant vanishing
on a free/marked collision is used.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open MeasureTheory Set Filter OAI.InternalCatalan

noncomputable section

instance realPlaceMeasure_nullSingletonClass : NullSingletonClass realPlaceMeasure := by
  unfold realPlaceMeasure
  infer_instance

/-- Distinct coordinates in a finite product of an atomless real measure
are almost surely unequal. -/
theorem ae_pi_fin_coord_ne (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {p : ℕ} (i j : Fin p) (hij : i ≠ j) :
    ∀ᵐ t ∂Measure.pi (fun _ : Fin p => μ), t i ≠ t j := by
  classical
  cases p with
  | zero => exact Fin.elim0 i
  | succ p =>
    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
    have hp : ∀ᵐ z ∂μ.prod (Measure.pi (fun _ : Fin p => μ)),
        z.1 ≠ z.2 j' := by
      apply (Measure.ae_prod_iff_ae_ae ?_).mpr
      · exact Eventually.of_forall fun a =>
          (Measure.ae_eval_ne (fun _ : Fin p => μ) j' a).mono fun t ht => ht.symm
      · exact (measurableSet_eq_fun measurable_fst
          ((measurable_pi_apply j' : Measurable (fun t : Fin p → ℝ => t j')).comp
            measurable_snd)).compl
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (p+1) => μ) i
    have hm := hmp.quasiMeasurePreserving.tendsto_ae.eventually hp
    simpa only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_symm_mk, Fin.removeNth_apply, hj'] using hm

theorem ae_pi_fin_injective (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (p : ℕ) : ∀ᵐ t ∂Measure.pi (fun _ : Fin p => μ), Function.Injective t := by
  have h : ∀ᵐ t ∂Measure.pi (fun _ : Fin p => μ),
      ∀ i j : Fin p, i ≠ j → t i ≠ t j :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => by
      by_cases hij : i = j
      · exact Eventually.of_forall fun t hne => False.elim (hne hij)
      · exact (ae_pi_fin_coord_ne μ i j hij).mono fun t ht _ => ht
  filter_upwards [h] with t ht
  intro i j hij
  by_contra hne
  exact ht i j hne hij

theorem ae_pi_fin_avoid (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (p : ℕ) {m : ℕ} (a : Fin m → ℝ) :
    ∀ᵐ t ∂Measure.pi (fun _ : Fin p => μ), ∀ i j, t i ≠ a j :=
  eventually_all.mpr fun i => eventually_all.mpr fun j =>
    Measure.ae_eval_ne (fun _ : Fin p => μ) i (a j)

/-- The seven geometry properties needed for integrating actual free rows and
P-only fixed atoms. Valid also when either node list is empty. -/
theorem ae_marked_atom_geometry (p : ℕ) {m : ℕ} (y : Fin m → ℝ)
    (hy : Function.Injective y) :
    ∀ᵐ w ∂(CatalanMeasure.pairMeasure realPlaceMeasure
        (volume.restrict (Ioo (0 : ℝ) 1)) p),
      (∀ i, w.1 i ∈ Ioo (-1 : ℝ) 1) ∧
      (∀ i, w.1 i ≠ 0) ∧
      (∀ i, (realCoordinate ∘ w.1) i ∈ Ioo (-1 : ℝ) 1) ∧
      (∀ i, (realCoordinate ∘ w.1) i ≠ 0) ∧
      (∀ j, w.2 j ∈ Ioo (0 : ℝ) 1) ∧
      Function.Injective (Fin.append (realCoordinate ∘ w.1) y) ∧
      Function.Injective w.2 := by
  have ht : ∀ᵐ t ∂Measure.pi (fun _ : Fin p => realPlaceMeasure),
      (∀ i, t i ∈ Ioo (-1 : ℝ) 1) ∧ (∀ i, t i ≠ 0) ∧
      Function.Injective t ∧ (∀ i j, t i ≠ realCoordinateInv (y j)) := by
    have hmem : ∀ᵐ t ∂Measure.pi (fun _ : Fin p => realPlaceMeasure),
        ∀ i, t i ∈ Ioo (-1 : ℝ) 1 :=
      eventually_all.mpr fun _ => Measure.tendsto_eval_ae_ae.eventually ae_realPlace_mem
    have hzero : ∀ᵐ t ∂Measure.pi (fun _ : Fin p => realPlaceMeasure), ∀ i, t i ≠ 0 :=
      eventually_all.mpr fun i => Measure.ae_eval_ne (fun _ : Fin p => realPlaceMeasure) i 0
    filter_upwards [hmem, hzero, ae_pi_fin_injective realPlaceMeasure p,
      ae_pi_fin_avoid realPlaceMeasure p (realCoordinateInv ∘ y)] with t hm hz hi ha
    exact ⟨hm, hz, hi, ha⟩
  have hs : ∀ᵐ s ∂Measure.pi (fun _ : Fin p => volume.restrict (Ioo (0 : ℝ) 1)),
      (∀ j, s j ∈ Ioo (0 : ℝ) 1) ∧ Function.Injective s := by
    have hmem : ∀ᵐ s ∂Measure.pi (fun _ : Fin p => volume.restrict (Ioo (0 : ℝ) 1)),
        ∀ j, s j ∈ Ioo (0 : ℝ) 1 :=
      eventually_all.mpr fun _ => Measure.tendsto_eval_ae_ae.eventually
        (ae_restrict_mem measurableSet_Ioo)
    exact hmem.and (ae_pi_fin_injective (volume.restrict (Ioo (0 : ℝ) 1)) p)
  have hfst := Measure.quasiMeasurePreserving_fst
    (μ := Measure.pi (fun _ : Fin p => realPlaceMeasure))
    (ν := Measure.pi (fun _ : Fin p => volume.restrict (Ioo (0 : ℝ) 1)))
  have hsnd := Measure.quasiMeasurePreserving_snd
    (μ := Measure.pi (fun _ : Fin p => realPlaceMeasure))
    (ν := Measure.pi (fun _ : Fin p => volume.restrict (Ioo (0 : ℝ) 1)))
  have htf := hfst.tendsto_ae.eventually ht
  have hss := hsnd.tendsto_ae.eventually hs
  unfold CatalanMeasure.pairMeasure
  filter_upwards [htf, hss] with w htw hsw
  have hxmem (i : Fin p) : (realCoordinate ∘ w.1) i ∈ Ioo (-1 : ℝ) 1 :=
    realCoordinate_mem (htw.1 i)
  have hx0 (i : Fin p) : (realCoordinate ∘ w.1) i ≠ 0 := by
    dsimp only [Function.comp_apply, realCoordinate]
    exact div_ne_zero (htw.2.1 i) (by positivity)
  have hxi : Function.Injective (realCoordinate ∘ w.1) := by
    intro i j hij
    apply htw.2.2.1
    have h := congrArg realCoordinateInv hij
    simpa only [Function.comp_apply, realCoordinate_right_inverse (htw.1 i),
      realCoordinate_right_inverse (htw.1 j)] using h
  have hxy : ∀ i j, (realCoordinate ∘ w.1) i ≠ y j := by
    intro i j hij
    apply htw.2.2.2 i j
    have h := congrArg realCoordinateInv hij
    simpa only [Function.comp_apply, realCoordinate_right_inverse (htw.1 i)] using h
  exact ⟨htw.1, htw.2.1, hxmem, hx0, hsw.1,
    Fin.append_injective_iff.mpr ⟨hxi, hy, hxy⟩, hsw.2⟩

end
end CatalanMeasure.Parametric
