module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefSym
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.Hid

@[expose] public section

/-!
# E1b instances: Boolean one-shot enclosure checks for the merged references

For a merged reference `Rm` (one signed piece per species) and a trial reference `R = ofTrial T`,
`refBil_le_merged` / `refBil_ge_merged` / `refEnergy_le_merged` / `refEnergy_ge_merged` turn ONE kernel check
`encUpper n (LF.sumL (planLits Rm Sm)) U = true` (or `encLower`) into a rational bound of `refBil μ ν`.
No per-job literal is needed: the log forms are recomputed by the kernel (`planLits` is the plan itself).
-/

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.LogEval CatalanMeasure.GenD.Signed.Data.Trial

noncomputable section

/-- The reference lists of a trial datum. -/
def ofTrial (T : TrialQ) : RefQ := ⟨T.qT, T.qF, T.qTn, T.qFn⟩

/-- The log forms of the plan. -/
def planLits (R S : RefQ) : List LF := (refPlan R S).map Job.lf

theorem forall2_map_lf : ∀ js : List Job,
    List.Forall₂ (fun (j : Job) (l : LF) => j.lf = l) js (js.map Job.lf)
  | [] => List.Forall₂.nil
  | j :: js => List.Forall₂.cons rfl (forall2_map_lf js)

theorem planLits_forall2 (R S : RefQ) :
    List.Forall₂ (fun (j : Job) (l : LF) => j.lf = l) (refPlan R S) (planLits R S) :=
  forall2_map_lf _

def encUpper (n : ℕ) (f : LF) (U : ℚ) : Bool :=
  match f.enc n with
  | some p => decide (p.1 + p.2 ≤ U)
  | none => false

def encLower (n : ℕ) (f : LF) (L : ℚ) : Bool :=
  match f.enc n with
  | some p => decide (L ≤ p.1 - p.2)
  | none => false

theorem refBil_le_merged (μ ν : SRef) (R S Rm Sm : RefQ) {cT cF cT' cF' : List ℚ}
    (hμ : IsRefQ μ R) (hν : IsRefQ ν S) (hR : R.OK) (hS : S.OK)
    (hm : MergeOK cT cF R Rm) (hn : MergeOK cT' cF' S Sm) (n : ℕ) (U : ℚ)
    (h : encUpper n (LF.sumL (planLits Rm Sm)) U = true) : refBil μ ν ≤ (U : ℝ) := by
  unfold encUpper at h
  rcases hp : (LF.sumL (planLits Rm Sm)).enc n with _ | p
  · rw [hp] at h; simp at h
  · rw [hp] at h
    have hE := refBil_enc_merged μ ν R S Rm Sm hμ hν hR hS hm hn (planLits_forall2 Rm Sm) n hp
    have hle : p.1 + p.2 ≤ U := by simpa using h
    calc refBil μ ν ≤ ((p.1 + p.2 : ℚ) : ℝ) := hE.le_upper
      _ ≤ (U : ℝ) := by exact_mod_cast hle

theorem refBil_ge_merged (μ ν : SRef) (R S Rm Sm : RefQ) {cT cF cT' cF' : List ℚ}
    (hμ : IsRefQ μ R) (hν : IsRefQ ν S) (hR : R.OK) (hS : S.OK)
    (hm : MergeOK cT cF R Rm) (hn : MergeOK cT' cF' S Sm) (n : ℕ) (L : ℚ)
    (h : encLower n (LF.sumL (planLits Rm Sm)) L = true) : (L : ℝ) ≤ refBil μ ν := by
  unfold encLower at h
  rcases hp : (LF.sumL (planLits Rm Sm)).enc n with _ | p
  · rw [hp] at h; simp at h
  · rw [hp] at h
    have hE := refBil_enc_merged μ ν R S Rm Sm hμ hν hR hS hm hn (planLits_forall2 Rm Sm) n hp
    have hle : L ≤ p.1 - p.2 := by simpa using h
    calc (L : ℝ) ≤ ((p.1 - p.2 : ℚ) : ℝ) := by exact_mod_cast hle
      _ ≤ refBil μ ν := hE.ge_lower

theorem refEnergy_le_merged (μ : SRef) (R Rm : RefQ) {cT cF : List ℚ} (hμ : IsRefQ μ R) (hR : R.OK)
    (hm : MergeOK cT cF R Rm) (n : ℕ) (U : ℚ)
    (h : encUpper n (LF.sumL (planLits Rm Rm)) U = true) : refEnergy μ ≤ (U : ℝ) := by
  rw [refEnergy_eq_refBil]
  exact refBil_le_merged μ μ R R Rm Rm hμ hμ hR hR hm hm n U h

theorem refEnergy_ge_merged (μ : SRef) (R Rm : RefQ) {cT cF : List ℚ} (hμ : IsRefQ μ R) (hR : R.OK)
    (hm : MergeOK cT cF R Rm) (n : ℕ) (L : ℚ)
    (h : encLower n (LF.sumL (planLits Rm Rm)) L = true) : (L : ℝ) ≤ refEnergy μ := by
  rw [refEnergy_eq_refBil]
  exact refBil_ge_merged μ μ R R Rm Rm hμ hμ hR hR hm hm n L h

/-- `IsRefQ`/`OK` of the reference of a trial from `DataOK` and the four measure equations. -/
theorem ofTrial_OK {T : TrialQ} {C : ℝ} (h : T.DataOK C) : (ofTrial T).OK :=
  ⟨h.pT, h.pF, h.pTn, h.pFn⟩

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.refBil_le_merged
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.refBil_ge_merged
