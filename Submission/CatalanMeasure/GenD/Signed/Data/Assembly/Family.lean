module

public import Submission.CatalanMeasure.GenD.Signed.Glue410
public import Submission.CatalanMeasure.GenD.Signed.Interp
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.Hid
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.PolyPos
public import Submission.CatalanMeasure.GenD.D58.OddProfile
public import Submission.CatalanMeasure.Parametric.PopulationPhysicalValue

@[expose] public section

/-!
# 410 assembly: the concrete trial family `famD X N : SignedData`

The trial data modules (`Data/Trial/T{t}Data`, `T{t}Spec`) and the spike/E1b/cell lanes state their
results about an ABSTRACT family member `D` ("`ν = 58 N`, `sp = 20 N`, `θ = 1/1024`, ..."); nothing
defined the family.  This module does, once, for any rational trial datum `X : FamPar`:

* `famD X N`: `ν = 58 N`, `e = dampE N` (`2^-30/(N+1)`), `sp = 20 N`, `g = 5 N`, `v, a, p` from the trial,
  `b = bSeq X.bs`, `K = X.bs.length`, `R = fQ R.f (· + 1)`, `μ = ⟨polyMeas qT/qF, polyMeas qTn/qFn⟩`,
  `t = mneg μ τ`, `cs = CSP / 58`, `kph = 14`, `θ = 1/1024`, `constant = 0` (only the difference
  `constTotal - constant` is used), `Rf, Cf` the problem's population fields of `Odd.design`.
* `famD_spec` (`TrialForm.Spec`), `famD_family` (`Family`), `famD_regular` (`SignedRegular`),
  `famD_compat` (`InterpCompat`), `famD_ends` (`IntervalEnds`).
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.Consts
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Cert OAI.InternalCatalan

noncomputable section

/-- The rational datum of one trial of the family. -/
structure FamPar where
  T : TrialQ
  /-- coefficients of the denominator trial `b` (`TrialB`) -/
  bs : List ℚ
  /-- the per-spike charge `CSP` (`D.cs = CSP / 58`) -/
  CSP : ℚ
  /-- the density cap of `T{t}Spec` -/
  Cb : ℚ

/-- The signed reference `P - N` of the trial as an `SRef`. -/
def famMu (X : FamPar) : SRef :=
  ⟨fun τ => cond τ (polyMeas (X.T.qT.map PieceQ.toPiece)) (polyMeas (X.T.qF.map PieceQ.toPiece)),
   fun τ => cond τ (polyMeas (X.T.qTn.map PieceQ.toPiece)) (polyMeas (X.T.qFn.map PieceQ.toPiece))⟩

/-- The trial family member at scale `N`. -/
def famD (X : FamPar) (N : ℕ) : SignedData where
  ν := 58 * (N : ℝ)
  e := dampE N
  sp := 20 * N
  g := 5 * N
  v := tseq (fQ X.T.v.f) (X.T.v.tail.map TailQ.toC)
  a := tseq (fQ X.T.a.f) (X.T.a.tail.map TailQ.toC)
  b := bSeq X.bs
  K := X.bs.length
  R := fun n => fQ X.T.R.f (n + 1)
  t := mneg (famMu X) (realEnergyTau (dampE N))
  μ := famMu X
  Cb := (X.Cb : ℝ)
  η := (X.T.η : ℝ)
  p := tseq (fQ X.T.p.f) (X.T.p.tail.map TailQ.toC)
  Sup := (X.T.Sup : ℝ)
  constant := 0
  Rf := CatalanMeasure.Parametric.populationPhysicalFreeField CatalanMeasure.GenD.D58.Odd.design N
  Cf := CatalanMeasure.Parametric.populationPhysicalColumnField CatalanMeasure.GenD.D58.Odd.design N (0 + 0)
  θ := 1 / 1024
  cs := (X.CSP : ℝ) / 58
  kph := 14

theorem famD_tau (X : FamPar) (N : ℕ) : (famD X N).τ = 1 - dampE N := rfl

theorem famD_tau_mem (X : FamPar) (N : ℕ) : (famD X N).τ ∈ Ioo (0 : ℝ) 1 :=
  realEnergyTau_bounds (dampE_mem N)

/-- `TrialForm.Spec` of the family member (`hok`: the data checks of `T{t}Spec.dataOK`). -/
theorem famD_spec (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (N : ℕ) :
    X.T.form.Spec (famD X N) :=
  TrialQ.spec X.T (famD X N) (famD_tau_mem X N) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hok _ le_rfl)

/-- `Family (famD X) F`. -/
theorem famD_family (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) :
    Family (famD X) X.T.form where
  spec := famD_spec X hok
  hτ := by
    show Tendsto (fun N : ℕ => 1 - dampE N) atTop (𝓝 1)
    exact dampE_tau_tendsto
  hν := by
    show Tendsto (fun N : ℕ => 58 * (N : ℝ)) atTop atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  hℓ := by
    show Tendsto (fun N : ℕ => Real.log (1 / (1 - (1 - dampE N) ^ 2)) / (58 * (N : ℝ))) atTop (𝓝 0)
    exact dampE_hℓ (by norm_num)
  hasum := Glue410.hasum_of_spec (famD_spec X hok 0)

/-- `SignedRegular` of every member (needs `0 ≤ Cb`). -/
theorem famD_regular (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hCb : (0 : ℝ) ≤ X.Cb) (N : ℕ) : SignedRegular (famD X N) := by
  have h := famD_spec X hok N
  exact
    { he := dampE_mem N
      hv := Glue410.Spec_summable_v h
      ha := Glue410.Spec_summable_a h
      hR := h.hRg
      ht := TrialForm.isGeom_t h
      hμ := h.bd
      hC := hCb
      hp := Glue410.Spec_summable_p h
      hη0 := by rw [h.hη]; exact h.hηI.1 }

/-- Two trials of the family can be interpolated when their `b`-lengths and `η` agree. -/
theorem famD_compat (X Y : FamPar) (hK : X.bs.length = Y.bs.length) (hη : (X.T.η : ℝ) = Y.T.η)
    (N : ℕ) : InterpCompat (famD X N) (famD Y N) where
  ν := rfl
  e := rfl
  sp := rfl
  g := rfl
  K := hK.symm
  Rf := rfl
  Cf := rfl
  θ := rfl
  kph := rfl
  η := hη.symm

/-- `IntervalEnds` of the endpoint families of one α-interval. -/
theorem famD_ends (X Y : FamPar) (hokX : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hokY : ∀ C : ℝ, (Y.Cb : ℝ) ≤ C → Y.T.DataOK C) (hCX : (0 : ℝ) ≤ X.Cb) (hCY : (0 : ℝ) ≤ Y.Cb)
    (hK : X.bs.length = Y.bs.length) (hη : (X.T.η : ℝ) = Y.T.η) {αA αB lo hi : ℝ}
    (hlt : αA < αB) (hlo : αA ≤ lo) (hhi : hi ≤ αB) :
    IntervalEnds αA αB lo hi (famD X) (famD Y) where
  lt := hlt
  lo_ge := hlo
  hi_le := hhi
  compat := famD_compat X Y hK hη
  regA := Eventually.of_forall (famD_regular X hokX hCX)
  regB := Eventually.of_forall (famD_regular Y hokY hCY)

end

end CatalanMeasure.GenD.Signed.Data.Assembly
