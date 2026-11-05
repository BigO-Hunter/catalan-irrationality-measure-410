module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMerge
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Symmetry of the reference bilinear energy (Theorem A, lane E1b, route (g))

`refBilLF R S` and `refBilLF S R` have the same value.  The pair-level step is Fubini for the
logarithmic kernel `log |y - x|` (same species) or `log |y + x|` (opposite species, reflection) on a
rectangle of two pieces with polynomial densities:

* `integrableOn_kernel`: `(x, y) ↦ log |y - ctr r x|` is integrable on `[a,b] × [c,d]`.  The shear
  `(x, y) ↦ (x, y ∓ x)` is measure preserving (`measurePreserving_prod_sub/add_right`) and sends the
  rectangle into `[a,b] × [c ∓ b, d ∓ a]`, where `log |y|` is integrable.
* `fubini_log`: the two iterated integrals agree (`integral_integral_swap`; the density product is
  continuous, hence bounded on the compact rectangle).
* `pairLF_symm`: `(pairLF qa qb r).eval = (pairLF qb qa r).eval`; `ent_symm`, `bil_symm`,
  `refBilLF_symm`: the symmetry of the log forms; `refBil_symm : refBil μ ν = refBil ν μ`.
* Consumers: `refBil_enc_swap`, `refBil_enc_merged_swap` (the enclosure of `refBil (A,B)` also
  encloses `refBil (B,A)`: one plan serves both), and the unordered-pair plan `refPlanSym T F` of
  `refEnergy` for a merged reference `⟨T, F, [], []⟩` (`refEnergy_enc_merged_sym`): the two mixed
  blocks `(T,F)` and `(F,T)` are one block of jobs with weight `-2`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.Cert (qabs)
open MeasureTheory Set

noncomputable section

/-! ### 1. Integrability of the logarithmic kernel on a rectangle -/

theorem integrableOn_comp_shear {T : ℝ × ℝ → ℝ × ℝ}
    (hT : MeasurePreserving T (volume.prod volume) (volume.prod volume))
    {g : ℝ × ℝ → ℝ} {S R : Set (ℝ × ℝ)} (hS : MeasurableSet S) (hR : R ⊆ T ⁻¹' S)
    (hg : IntegrableOn g S (volume.prod volume)) :
    IntegrableOn (g ∘ T) R (volume.prod volume) := by
  have h : IntegrableOn (g ∘ T) (T ⁻¹' S) (volume.prod volume) :=
    (hT.restrict_preimage hS).integrable_comp_of_integrable hg
  exact IntegrableOn.mono_set h hR

theorem integrableOn_logsnd {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    IntegrableOn (fun w : ℝ × ℝ => Real.log |w.2|) (Icc a b ×ˢ Icc c d) (volume.prod volume) := by
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc a b) volume :=
    continuousOn_const.integrableOn_Icc
  have h2 : IntegrableOn (fun t : ℝ => Real.log |t|) (Icc c d) volume := by
    simpa using integrableOn_log_abs_sub 0 hcd
  have h3 := Integrable.mul_prod (L := ℝ) h1 h2
  rw [Measure.prod_restrict] at h3
  have h4 : Integrable (fun w : ℝ × ℝ => Real.log |w.2|)
      ((volume.prod volume).restrict (Icc a b ×ˢ Icc c d)) := by
    simpa only [one_mul] using h3
  exact h4

theorem integrableOn_kernel (r : Bool) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    IntegrableOn (fun z : ℝ × ℝ => Real.log |z.2 - ctr r z.1|) (Icc a b ×ˢ Icc c d)
      (volume.prod volume) := by
  cases r
  · have hT : MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.2 - z.1)) (volume.prod volume)
        (volume.prod volume) := measurePreserving_prod_sub volume volume
    have hg := integrableOn_logsnd (a := a) (b := b) (c := c - b) (d := d - a) hab (by linarith)
    have hsub : Icc a b ×ˢ Icc c d ⊆
        (fun z : ℝ × ℝ => (z.1, z.2 - z.1)) ⁻¹' (Icc a b ×ˢ Icc (c - b) (d - a)) := by
      intro z hz
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
      simp only [mem_preimage, mem_prod, mem_Icc]
      exact ⟨⟨h1, h2⟩, by linarith, by linarith⟩
    exact integrableOn_comp_shear hT (measurableSet_Icc.prod measurableSet_Icc) hsub hg
  · have hT : MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.2 + z.1)) (volume.prod volume)
        (volume.prod volume) := measurePreserving_prod_add_right volume volume
    have hg := integrableOn_logsnd (a := a) (b := b) (c := c + a) (d := d + b) hab (by linarith)
    have hsub : Icc a b ×ˢ Icc c d ⊆
        (fun z : ℝ × ℝ => (z.1, z.2 + z.1)) ⁻¹' (Icc a b ×ˢ Icc (c + a) (d + b)) := by
      intro z hz
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
      simp only [mem_preimage, mem_prod, mem_Icc]
      exact ⟨⟨h1, h2⟩, by linarith, by linarith⟩
    exact (integrableOn_comp_shear hT (measurableSet_Icc.prod measurableSet_Icc) hsub hg).congr_fun
      (fun z _ => by simp [ctr, sub_neg_eq_add]) (measurableSet_Icc.prod measurableSet_Icc)

/-! ### 2. Fubini for two polynomial densities against the kernel -/

theorem ctr_swap (r : Bool) (x y : ℝ) :
    Real.log |x - ctr r y| = Real.log |y - ctr r x| := by
  cases r
  · show Real.log |x - y| = Real.log |y - x|
    rw [abs_sub_comm]
  · show Real.log |x - -y| = Real.log |y - -x|
    rw [sub_neg_eq_add, sub_neg_eq_add, add_comm]

theorem fubini_log (r : Bool) {pa pb : ℝ → ℝ} (hpa : Continuous pa) (hpb : Continuous pb)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, pa x * ∫ y in c..d, pb y * Real.log |y - ctr r x| =
      ∫ y in c..d, pb y * ∫ x in a..b, pa x * Real.log |x - ctr r y| := by
  have hint : Integrable (Function.uncurry
      (fun x y : ℝ => pa x * (pb y * Real.log |y - ctr r x|)))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    have hk := integrableOn_kernel r hab hcd
    have hc : ContinuousOn (fun z : ℝ × ℝ => pa z.1 * pb z.2) (Icc a b ×ˢ Icc c d) :=
      ((hpa.comp continuous_fst).mul (hpb.comp continuous_snd)).continuousOn
    have h2 := IntegrableOn.continuousOn_mul hc hk (isCompact_Icc.prod isCompact_Icc)
    have h3 : IntegrableOn (Function.uncurry
        (fun x y : ℝ => pa x * (pb y * Real.log |y - ctr r x|)))
        (Icc a b ×ˢ Icc c d) (volume.prod volume) := by
      refine h2.congr_fun (fun z _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
      show (pa z.1 * pb z.2) * Real.log |z.2 - ctr r z.1| =
        pa z.1 * (pb z.2 * Real.log |z.2 - ctr r z.1|)
      ring
    exact IntegrableOn.mono_set h3 (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have key := integral_integral_swap hint
  have hL : (∫ x in a..b, pa x * ∫ y in c..d, pb y * Real.log |y - ctr r x|) =
      ∫ x in Ioc a b, ∫ y in Ioc c d, pa x * (pb y * Real.log |y - ctr r x|) := by
    rw [intervalIntegral.integral_of_le hab]
    congr 1
    funext x
    rw [intervalIntegral.integral_of_le hcd, integral_const_mul]
  have hR : (∫ y in c..d, pb y * ∫ x in a..b, pa x * Real.log |x - ctr r y|) =
      ∫ y in Ioc c d, ∫ x in Ioc a b, pa x * (pb y * Real.log |y - ctr r x|) := by
    rw [intervalIntegral.integral_of_le hcd]
    congr 1
    funext y
    rw [intervalIntegral.integral_of_le hab, ← integral_const_mul]
    congr 1
    funext x
    rw [ctr_swap r x y]
    ring
  rw [hL, hR]
  exact key

/-! ### 3. Pairs of pieces -/

theorem pairLF_eval (qa qb : PieceQ) (r : Bool) (ha : qa.lo ≤ qa.hi) (hb : qb.lo ≤ qb.hi) :
    (pairLF qa qb r).eval = ∫ x in (qa.lo : ℝ)..(qa.hi : ℝ), polyTow qa.p 0 x *
      ∫ y in (qb.lo : ℝ)..(qb.hi : ℝ), polyTow qb.p 0 y * Real.log |y - ctr r x| := by
  have h := int_dens_field qa ha (fieldOf r qb)
  have e : ∀ x : ℝ, fieldTower (fieldOf r qb) (fun _ => 0) 0 x =
      ∫ y in (qb.lo : ℝ)..(qb.hi : ℝ), polyTow qb.p 0 y * Real.log |y - ctr r x| := by
    intro x
    have h1 := Gsum_eq_Sfun r [qb] (fun q hq => by rw [List.mem_singleton.mp hq]; exact hb) x
    have h2 : Gsum r [qb] x = fieldTower (fieldOf r qb) (fun _ => 0) 0 x := by
      simp [Gsum]
    rw [← h2, h1, Sfun_cons]
    simp [Sfun]
  show (pieceFieldLF qa (fieldOf r qb)).eval = _
  rw [← h]
  simp only [e]

theorem pairLF_symm (qa qb : PieceQ) (r : Bool) (ha : qa.lo ≤ qa.hi) (hb : qb.lo ≤ qb.hi) :
    (pairLF qa qb r).eval = (pairLF qb qa r).eval := by
  rw [pairLF_eval qa qb r ha hb, pairLF_eval qb qa r hb ha]
  exact fubini_log r (continuous_polyTow0 qa.p) (continuous_polyTow0 qb.p)
    (cast_le_of qa ha) (cast_le_of qb hb)

/-! ### 4. Lists of pieces, four species blocks, `refBilLF` -/

theorem rowLF_eval (qa : PieceQ) (r : Bool) : ∀ B : List PieceQ,
    (rowLF qa B r).eval = (B.map fun qb => (pairLF qa qb r).eval).sum
  | [] => by simp [rowLF, LF.sumL, LF.eval, termsEval]
  | qb :: B => by
    have hc : rowLF qa (qb :: B) r = (pairLF qa qb r).add (rowLF qa B r) := rfl
    rw [hc, LF.eval_add, rowLF_eval qa r B, List.map_cons, List.sum_cons]

theorem entLF_eval_sum (B : List PieceQ) (r : Bool) : ∀ A : List PieceQ,
    (entLF A B r).eval = (A.map fun qa => (B.map fun qb => (pairLF qa qb r).eval).sum).sum
  | [] => by simp [entLF, LF.sumL, LF.eval, termsEval]
  | qa :: A => by
    have hc : entLF (qa :: A) B r = (rowLF qa B r).add (entLF A B r) := rfl
    rw [hc, LF.eval_add, rowLF_eval qa r B, entLF_eval_sum B r A, List.map_cons, List.sum_cons]

theorem list_sum_swap {α β : Type*} (f : α → β → ℝ) : ∀ (A : List α) (B : List β),
    (A.map fun a => (B.map fun b => f a b).sum).sum =
      (B.map fun b => (A.map fun a => f a b).sum).sum
  | [], B => by
    induction B with
    | nil => simp
    | cons b B ih =>
      simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at ih ⊢
      linarith
  | a :: A, B => by
    rw [List.map_cons, List.sum_cons, list_sum_swap f A B]
    simp only [List.map_cons, List.sum_cons]
    rw [List.sum_map_add]

theorem ent_symm (A B : List PieceQ) (r : Bool) (hA : ∀ q ∈ A, q.lo ≤ q.hi)
    (hB : ∀ q ∈ B, q.lo ≤ q.hi) : (entLF A B r).eval = (entLF B A r).eval := by
  rw [entLF_eval_sum B r A, entLF_eval_sum A r B, list_sum_swap (fun a b => (pairLF a b r).eval) A B]
  congr 1
  apply List.map_congr_left
  intro qb hqb
  show (A.map fun qa => (pairLF qa qb r).eval).sum = (A.map fun qa => (pairLF qb qa r).eval).sum
  congr 1
  apply List.map_congr_left
  intro qa hqa
  exact pairLF_symm qa qb r (hA qa hqa) (hB qb hqb)

theorem bil_symm (A1 A0 B1 B0 : List PieceQ) (hA1 : ∀ q ∈ A1, q.lo ≤ q.hi)
    (hA0 : ∀ q ∈ A0, q.lo ≤ q.hi) (hB1 : ∀ q ∈ B1, q.lo ≤ q.hi) (hB0 : ∀ q ∈ B0, q.lo ≤ q.hi) :
    (bilLF A1 A0 B1 B0).eval = (bilLF B1 B0 A1 A0).eval := by
  rw [bil_eval, bil_eval, ent_symm A1 B1 false hA1 hB1, ent_symm A1 B0 true hA1 hB0,
    ent_symm A0 B1 true hA0 hB1, ent_symm A0 B0 false hA0 hB0]
  ring

/-- **Symmetry of the reference bilinear form (log-form level).** -/
theorem refBilLF_symm (R S : RefQ) (hR : R.LE) (hS : S.LE) :
    (refBilLF R S).eval = (refBilLF S R).eval := by
  rw [refBilLF_eval_expand R S, refBilLF_eval_expand S R,
    bil_symm R.pT R.pF S.pT S.pF hR.1 hR.2.1 hS.1 hS.2.1,
    bil_symm R.pT R.pF S.nT S.nF hR.1 hR.2.1 hS.2.2.1 hS.2.2.2,
    bil_symm R.nT R.nF S.pT S.pF hR.2.2.1 hR.2.2.2 hS.1 hS.2.1,
    bil_symm R.nT R.nF S.nT S.nF hR.2.2.1 hR.2.2.2 hS.2.2.1 hS.2.2.2]
  ring

theorem RefQ.OK.toLE {R : RefQ} (h : R.OK) : R.LE := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun q hq => pieceOK_le_rat (h1 q hq), fun q hq => pieceOK_le_rat (h2 q hq),
    fun q hq => pieceOK_le_rat (h3 q hq), fun q hq => pieceOK_le_rat (h4 q hq)⟩

/-! ### 5. Consumers -/

/-- `refBil μ ν = refBil ν μ`. -/
theorem refBil_symm (μ ν : SRef) (R S : RefQ) (hμ : IsRefQ μ R) (hν : IsRefQ ν S)
    (hR : R.OK) (hS : S.OK) : refBil μ ν = refBil ν μ := by
  rw [refBil_eval μ ν R S hμ hν hR hS, refBil_eval ν μ S R hν hμ hS hR]
  exact refBilLF_symm R S hR.toLE hS.toLE

/-- The enclosure of `refBil μ ν` from the plan of `(R, S)` also encloses `refBil ν μ`: the jobs of
`(B, A)` are not needed. -/
theorem refBil_enc_swap (μ ν : SRef) (R S : RefQ) (hμ : IsRefQ μ R) (hν : IsRefQ ν S)
    (hR : R.OK) (hS : S.OK)
    {lits : List LF} (hl : List.Forall₂ (fun (j : Job) (l : LF) => j.lf = l) (refPlan R S) lits)
    (n : ℕ) {p : ℚ × ℚ} (h : (LF.sumL lits).enc n = some p) : Enc (refBil ν μ) p := by
  rw [← refBil_symm μ ν R S hμ hν hR hS]
  exact refBil_enc μ ν R S hμ hν hR hS hl n h

/-- Merged version of `refBil_enc_swap`: the plan `refPlan Rm Sm` serves `refBil μ ν` and `refBil ν μ`. -/
theorem refBil_enc_merged_swap (μ ν : SRef) (R S Rm Sm : RefQ) {cT cF cT' cF' : List ℚ}
    (hμ : IsRefQ μ R) (hν : IsRefQ ν S) (hR : R.OK) (hS : S.OK)
    (hm : MergeOK cT cF R Rm) (hn : MergeOK cT' cF' S Sm)
    {lits : List LF} (hl : List.Forall₂ (fun (j : Job) (l : LF) => j.lf = l) (refPlan Rm Sm) lits)
    (n : ℕ) {p : ℚ × ℚ} (h : (LF.sumL lits).enc n = some p) : Enc (refBil ν μ) p := by
  rw [← refBil_symm μ ν R S hμ hν hR hS]
  exact refBil_enc_merged μ ν R S Rm Sm hμ hν hR hS hm hn hl n h

/-- The plan of `refEnergy` for a merged reference `⟨T, F, [], []⟩` with the two mixed blocks
`(T, F)` and `(F, T)` collapsed into one block of weight `-2` (`ent T F` = `ent F T`). -/
def refPlanSym (T F : List PieceQ) : List Job :=
  jobsEnt (-1) false T T ++ jobsEnt (-2) true F T ++ jobsEnt (-1) false F F

theorem eval_refPlanSym (T F : List PieceQ) (hT : ∀ q ∈ T, q.lo ≤ q.hi)
    (hF : ∀ q ∈ F, q.lo ≤ q.hi) :
    (LF.sumL ((refPlanSym T F).map Job.lf)).eval = (refBilLF ⟨T, F, [], []⟩ ⟨T, F, [], []⟩).eval := by
  rw [← eval_refPlan, refPlan_merged, eval_jobsBil]
  simp only [refPlanSym, List.map_append, LF.eval_sumL_append, eval_jobsEnt, bil_eval]
  rw [ent_symm F T true hF hT]
  push_cast
  ring

/-- `refEnergy_enc_merged` with the unordered-pair plan `refPlanSym T F` (the number of jobs is
`|T|² + |T||F| + |F|²` instead of `(|T| + |F|)²`). -/
theorem refEnergy_enc_merged_sym (μ : SRef) (R : RefQ) (T F : List PieceQ) {cT cF : List ℚ}
    (hμ : IsRefQ μ R) (hR : R.OK) (hm : MergeOK cT cF R ⟨T, F, [], []⟩)
    {lits : List LF} (hl : List.Forall₂ (fun (j : Job) (l : LF) => j.lf = l) (refPlanSym T F) lits)
    (n : ℕ) {p : ℚ × ℚ} (h : (LF.sumL lits).enc n = some p) : Enc (refEnergy μ) p := by
  have hv := LF.enc_spec n _ p h
  rw [← map_lf_eq hl, eval_refPlanSym T F hm.leR.1 hm.leR.2.1,
    ← refBilLF_merge R R ⟨T, F, [], []⟩ ⟨T, F, [], []⟩ hm hm] at hv
  rwa [refEnergy_eval μ R hμ hR]

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef

#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.fubini_log
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.refBilLF_symm
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.refBil_enc_merged_swap
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.refEnergy_enc_merged_sym
